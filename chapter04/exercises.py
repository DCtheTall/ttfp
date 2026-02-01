"""
Chapter 4 Exercises
===================

"""

from dependent_types_lambda_calculus import *


def RunExercises():
  print('Exercise 4.2a')
  jdgmnt = Judgement(
      Context(), Statement(KArrow(KArrow(Star(), Star()), Star()))
  )
  line = str(jdgmnt)
  print(line)
  print('-' * len(line))
  deriv = DeriveKind(jdgmnt)
  print(deriv.FlagFormat())

  print('Exercise 4.2b')
  alpha = TypeVar('α', Star())
  beta = TypeVar('β', Star())
  jdgmnt = Judgement(
      Context(alpha, beta),
      Statement(TypeExpression(TArrow(TArrow(alpha, beta), alpha)))
  )
  line = str(jdgmnt)
  print(line)
  print('-' * len(line))
  deriv = DeriveType(jdgmnt)
  print(deriv.FlagFormat())


if __name__ == '__main__':
  RunExercises()