discard """
  cmd: "nim check $file"
  errormsg: ""
  nimout: '''
t10734.nim(17, 1) Error: invalid indentation
t10734.nim(17, 6) Error: invalid indentation
t10734.nim(18, 7) Error: expression expected, but found '[EOF]'
t10734.nim(16, 5) Error: 'proc' is not a concrete type; for a callback without parameters use 'proc()'
t10734.nim(17, 6) Error: expression 'p' has no type (or is ambiguous)
t10734.nim(15, 3) Hint: 'T' is declared but not used [XDeclaredButNotUsed]
'''
"""

type
  T = object
    a:
proc p =
  case