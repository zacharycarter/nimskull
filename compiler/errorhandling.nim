#
#
#           The Nim Compiler
#        (c) Copyright 2021 Andreas Rumpf
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module contains support code for new-styled error
## handling via an `nkError` node kind.
## 
## An nkError node is used where an error occurs within the AST. Wrap the ast
## node with `newError` and typically take over the position of the wrapped
## node in whatever AST it was in.
## 
## Internally an nkError node stores these children:
## * 0 - wraps an AST node that has the error
## * 1 - any prior errors (picks the first child from a depth first search)
## * 2 - nkIntLit with a value corresponding to `ord(ErrorKind)`
## * _ - zero or more nodes with data for the error message
## 
## The rest of the compiler should watch for nkErrors and mostly no-op or wrap
## further errors as needed.
## 
## # Future Considerations/Improvements:
## * accomodate for compiler related information like site of node creation to
##   make it easier to debug the compiler itself, so we know where a node was
##   created
## * rework internals to store actual error information in a lookup data
##   structure on the side instead of directly in the node

import ast
from options import ConfigRef

type
  ErrorKind* {.pure.} = enum ## expand as you need.
    CustomError
    CustomPrintMsgAndNodeError
      ## just like custom error, prints a message and renders wrongNode
    RawTypeMismatchError

    # Call
    CallTypeMismatch
    ExpressionCannotBeCalled
    WrongNumberOfArguments
    AmbiguousCall
    CallingConventionMismatch

    # ParameterTypeMismatch

    # Identifier Lookup
    ExpectedIdentifier
    ExpectedIdentifierInExpr

    # Object and Object Construction
    FieldNotAccessible 
      ## object field is not accessible
    FieldAssignmentInvalid
      ## object field assignment invalid syntax
    FieldOkButAssignedValueInvalid
      ## object field assignment, where the field name is ok, but value is not
    ObjectConstructorIncorrect
      ## one or more issues encountered with object constructor
    
    # General Type Checks
    ExpressionHasNoType
      ## an expression has not type or is ambiguous
    
    # Pragma
    InvalidPragma
      ## supllied user pragma is invalid

    WrappedError
      ## there is no meaningful error to construct, but there is an error
      ## further down the AST that invalidates the whole

type InstantiationInfo* = typeof(instantiationInfo())
  ## type alias for instantiation information
template instLoc(): InstantiationInfo = instantiationInfo(-2, fullPaths = true)
  ## grabs where in the compiler an error was instanced to ease debugging

proc errorSubNode*(n: PNode): PNode =
  case n.kind
  of nkEmpty..nkNilLit:
    result = nil
  of nkError:
    result = n
  else:
    result = nil
    for s in n.items:
      if s.isNil: continue
      result = errorSubNode(s)
      if result != nil: break

let noPrevError = newNode(nkEmpty)
  ## sentinil value to mark no previous errors

const
  wrongNodePos*    = 0
  prevErrorPos*    = 1
  errorKindPos*    = 2
  compilerInfoPos* = 3
  firstArgPos*     = 4

func errorKind*(e: PNode): ErrorKind {.inline.} =
  ## property to retrieve the error kind
  assert e != nil, "can't have a nil error node"
  assert e.kind == nkError, "must be an error node to have an ErrorKind"

  result = ErrorKind(e[errorKindPos].intVal)

func compilerInstInfo*(e: PNode): InstantiationInfo {.inline.} =
  ## return where the error was instantiated in the compiler
  let i = e[compilerInfoPos]
  assert i != nil, "we should always have compiler diagnositics"
  (filename: i.strVal, line: i.info.line.int, column: i.info.col.int)

proc newErrorAux(
    wrongNode: PNode;
    k: ErrorKind;
    inst: InstantiationInfo;
    args: varargs[PNode]
  ): PNode =
  ## create an `nkError` node with error `k`, with additional error `args` and
  ## given `inst` as to where it was instanced int he compiler.
  assert wrongNode != nil, "can't have a nil node for `wrongNode`"

  result = newNodeIT(nkError, wrongNode.info,
                     newType(tyError, ItemId(module: -2, item: -1), nil))

  result.add wrongNode
  let prevError = errorSubNode(wrongNode) # find buried errors
  result.add:
    if prevError.isNil:
      noPrevError
    else:
      prevError
  result.add newIntNode(nkIntLit, ord(k)) # errorKindPos
  result.add newStrNode(inst.filename, wrongNode.info) # compilerInfoPos

  # save the compiler's line and column information here for reporting
  result[compilerInfoPos].info.line = uint16 inst.line 
  result[compilerInfoPos].info.col = int16 inst.column

  for a in args: result.add a

proc newErrorActual(
    wrongNode: PNode;
    k: ErrorKind;
    inst: InstantiationInfo,
    args: varargs[PNode]
  ): PNode =
  ## create an `nkError` node with error `k`, with additional error `args` and
  ## given `inst` as to where it was instanced int he compiler.
  assert wrongNode != nil, "can't have a nil node for `wrongNode`"

  result = newErrorAux(wrongNode, k, inst, args)

proc newErrorActual(
    wrongNode: PNode;
    msg: string,
    inst: InstantiationInfo
  ): PNode =
  ## create an `nkError` node with a `CustomError` message `msg`
  newErrorAux(
    wrongNode, CustomError, inst, newStrNode(msg, wrongNode.info))

template newError*(wrongNode: PNode; k: ErrorKind; args: varargs[PNode]): PNode =
  ## create an `nkError` node with error `k`, with additional error `args` and
  ## given `inst` as to where it was instanced int he compiler.
  newErrorActual(wrongNode, k, instantiationInfo(-1, fullPaths = true), args)

template newError*(wrongNode: PNode; msg: string): PNode =
  ## create an `nkError` node with a `CustomError` message `msg`
  newErrorActual(wrongNode, msg, instantiationInfo(-1, fullPaths = true))

template newCustomErrorMsgAndNode*(wrongNode: PNode; msg: string): PNode =
  ## create an `nkError` node with a `CustomMsgError` message `msg`
  newErrorActual(
    wrongNode,
    CustomPrintMsgAndNodeError,
    instantiationInfo(-1, fullPaths = true),
    newStrNode(msg, wrongNode.info)
  )

proc wrapErrorInSubTree*(wrongNodeContainer: PNode): PNode =
  ## `wrongNodeContainer` doesn't directly have an error but one exists further
  ## down the tree, this is used to wrap the `wrongNodeContainer` in an nkError
  ## node but no message will be reported for it.
  var e = errorSubNode(wrongNodeContainer)
  assert e != nil, "there must be an error node within"
  result = newErrorAux(wrongNodeContainer, WrappedError, instLoc())

proc buildErrorList(n: PNode, errs: var seq[PNode]) =
  ## creates a list (`errs` seq) from least specific to most specific
  case n.kind
  of nkEmpty..nkNilLit:
    discard
  of nkError:
    errs.add n
    buildErrorList(n[wrongNodePos], errs)
  else:
    for i in countdown(n.len - 1, 0):
      buildErrorList(n[i], errs)

iterator walkErrors*(config: ConfigRef; n: PNode): PNode =
  ## traverses previous errors and yields errors from  innermost to outermost.
  ## this is a linear traversal and two, or more, sibling errors will result in
  ## only the first error (per `PNode.sons`) being yielded.
  assert n != nil
  var errNodes: seq[PNode] = @[]
  buildErrorList(n, errNodes)
  
  # report from last to first (deepest in tree to highest)
  for i in 1..errNodes.len:
    # reverse index so we go from the innermost to outermost
    let e = errNodes[^i]
    if e.errorKind == WrappedError: continue
    yield e