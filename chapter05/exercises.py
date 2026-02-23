"""
Chapter 4 Exercises
===================

"""

from predicate_lambda_calculus import *


def RunExercises():
  print('Exercise 5.2b')
  S = TypeVar('S', Star())
  x = Var('x', S)
  y = Var('y', S)
  K = KindExpression(PiKind(x, PiKind(y, Star())))
  jdgmnt = Judgement(Context(S), Statement(K))
  line = f'Derive {jdgmnt}'
  print(line)
  print('-' * len(line))
  print(DeriveKind(jdgmnt).FlagFormat())


  print('\nExercise 5.3')
  S = TypeVar('S', Star())
  x = Var('x', S)
  y = Var('y', S)
  Q = TypeVar('Q', PiKind(x, PiKind(y, Star())))
  T = TypeExpression(PiType(x, PiType(y, TApply(TApply(Q, x), y))))
  jdgmnt = Judgement(Context(S, Q), Statement(T))
  line = f'Derive {jdgmnt}'
  print(line)
  print('-' * len(line))
  print(DeriveType(jdgmnt).FlagFormat())


if __name__ == '__main__':
  RunExercises()
