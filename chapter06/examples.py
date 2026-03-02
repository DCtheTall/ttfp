"""
Chapter 6 Examples
===================

"""

from calculus_of_constructions import *


def RunExamples():
  print(AllKinds())
  print(Star())
  A = TypeVar('A', Star())
  B = TypeVar('B', PiKind(A, Star()))
  C = TypeVar('C', Star())
  print(KindExpression(PiKind(A, PiKind(A, Star()))))
  print(KindExpression(PiKind(B, Star())))

  print(A)
  print(TypeExpression(B))
  print(C)

  a = Var('a', A)
  b = Var('b', B)
  print(a)
  print(b)
  print(KindExpression(PiKind(a, Star())))
  print(KindExpression(PiKind(b, Star())))

  print(TypeExpression(PiType(A, C)))
  print(TypeExpression(PiType(A, B)))
  print(TypeExpression(PiType(B, A)))
  print(TypeExpression(PiType(a, B)))
  print(TypeExpression(PiType(a, PiType(b, C))))
  ab = Var('ab', PiType(a, B))
  print(TypeExpression(PiType(ab, C)))


if __name__ == '__main__':
  RunExamples()