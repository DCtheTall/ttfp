"""
Chapter 6 Examples
===================

"""

from calculus_of_constructions import *


def RunExamples():
  print(AllKinds())
  print(Star())
  A = TypeVar('A', Star())
  print(A)
  a = Var('a', A)
  print(a)


if __name__ == '__main__':
  RunExamples()