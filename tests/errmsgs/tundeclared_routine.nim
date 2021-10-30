discard """
cmd: '''nim check --hints:off $file'''
action: reject
nimout: '''
tundeclared_routine.nim(34, 17) Error: attempting to call routine: 'myiter'
  found tundeclared_routine.myiter(a: string) [iterator declared in tundeclared_routine.nim(32, 12)]
  found tundeclared_routine.myiter() [iterator declared in tundeclared_routine.nim(33, 12)]
tundeclared_routine.nim(39, 28) Error: invalid pragma: myPragma
tundeclared_routine.nim(46, 14) Error: undeclared field: 'bar3' for type tundeclared_routine.Foo [type declared in tundeclared_routine.nim(43, 8)]
tundeclared_routine.nim(51, 14) Error: undeclared field: 'bar4' for type tundeclared_routine.Foo [type declared in tundeclared_routine.nim(49, 8)]
tundeclared_routine.nim(54, 11) Error: undeclared identifier: 'bad5'
tundeclared_routine.nim(54, 15) Error: attempting to call routine: 'bad5'
  found 'bad5' [unknown declared in tundeclared_routine.nim(54, 11)]
tundeclared_routine.nim(34, 17) Error: expression 'myiter' cannot be called
tundeclared_routine.nim(34, 17) Error: expression 'myiter(1)' has no type (or is ambiguous)
tundeclared_routine.nim(46, 13) Error: expression '.' cannot be called
tundeclared_routine.nim(46, 13) Error: expression 'a.bar3' has no type (or is ambiguous)
tundeclared_routine.nim(51, 13) Error: expression '.' cannot be called
tundeclared_routine.nim(51, 13) Error: expression 'a.bar4' has no type (or is ambiguous)
tundeclared_routine.nim(54, 15) Error: expression 'bad5' cannot be called
tundeclared_routine.nim(54, 15) Error: expression 'bad5(1)' has no type (or is ambiguous)
'''
"""






# line 30
block:
  iterator myiter(a:string): int = discard
  iterator myiter(): int = discard
  let a = myiter(1)

block:
  proc myPragma():int=discard
  iterator myPragma():int=discard
  proc myfun(a:int): int {.myPragma.} = 1
  let a = myfun(1)

block:
  type Foo = object
  var a = Foo()
  iterator bar3():int=discard
  let a2 = a.bar3

block:
  type Foo = object
  var a = Foo()
  let a2 = a.bar4

block:
  let a = bad5(1)
