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

  
  print('\nExercise 4.3a')
  alpha = TypeVar('α', Star())
  beta = TypeVar('β', Star())
  x = Var('x', alpha)
  y = Var('y', TArrow(alpha, beta))
  jdgmnt = Judgement(
      Context(alpha, beta, x, y), Statement(Expression(Apply(y, x)))
  )
  line = str(jdgmnt)
  print(line)
  print('-' * len(line))
  deriv = DeriveTerm(jdgmnt)
  print(deriv.FlagFormat())
  # TODO 4.3b

  
  print('\nExercise 4.4a')
  alpha = TypeVar('α', Star())
  beta = TypeVar('β', KArrow(Star(), Star()))
  jdgmnt = Judgement(
      Context(alpha, beta),
      Statement(TypeExpression(TApply(beta, TApply(beta, alpha))))
  )
  print(line)
  print('-' * len(line))
  deriv = DeriveType(jdgmnt)
  print(deriv.FlagFormat())
  # TODO rest


if __name__ == '__main__':
  RunExercises()