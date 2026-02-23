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
  line = f'Derive {T}'
  print(line)
  print('-' * len(line))
  jdgmnt = Judgement(Context(), Statement(T))
  print(DeriveType(jdgmnt).FlagFormat())


  print('\nExercise 5.5')
  print('Prove (A => ((A => B) => B)) is a tautology')
  A = TypeVar('A', Star())
  B = TypeVar('B', Star())
  x = Var('x', A)
  y = Var('y', A)
  z = Var('z', TypeExpression(PiType(y, B)))
  T = TypeExpression(PiType(x, PiType(z, B)))
  print('Find an inhabitant of', T)
  u = Var('u', A)
  v = Var('v', TypeExpression(PiType(y, B)))
  inhab = Expression(Abstract(u, Abstract(v, Apply(v, u))))
  line = f'Derive {inhab}'
  print(line)
  print('-' * len(line))
  jdgmnt = Judgement(Context(), Statement(inhab))
  print(DeriveTerm(jdgmnt).ShortenedFlagFormat())
  


if __name__ == '__main__':
  RunExercises()
