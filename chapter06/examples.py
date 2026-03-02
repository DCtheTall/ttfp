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
  print(A)
  print(TypeExpression(B))
  print(KindExpression(PiKind(B, Star())))

  a = Var('a', A)
  b = Var('b', B)
  print(a)
  print(b)
  print(KindExpression(PiKind(a, Star())))
  print(KindExpression(PiKind(b, Star())))


if __name__ == '__main__':
  RunExamples()