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


  print('\nExercise 5.6')
  print('Prove ((A => (A => B)) => (A => B)) is a tautology')
  A = TypeVar('A', Star())
  B = TypeVar('B', Star())
  x = Var('x', A)
  y = Var('y', A)
  z = Var('z', TypeExpression(PiType(x, PiType(y, B))))
  T = TypeExpression(PiType(z, PiType(x, B)))
  print('Find an inhabitant of', T)
  u = Var('u', A)
  v = Var('v', z.typ)
  inhab = Expression(Abstract(v, Abstract(u, Apply(Apply(v, u), u))))
  line = f'Derive {inhab}'
  print(line)
  print('-' * len(line))
  jdgmnt = Judgement(Context(), Statement(inhab))
  print(DeriveTerm(jdgmnt).ShortenedFlagFormat())  


  print('\nExericse 5.7a')
  print('Prove ((A => B) => ((B => C) => (A => C))) is a tautology')
  A = TypeVar('A', Star())
  B = TypeVar('B', Star())
  C = TypeVar('C', Star())
  a = Var('a', A)
  b = Var('b', B)
  x = Var('x', TypeExpression(PiType(a, C)))
  y = Var('y', TypeExpression(PiType(b, C)))
  T = TypeExpression(PiType(x, PiType(y, PiType(a, C))))
  print('Find an inhabitant of', T)
  u = Var('u', TypeExpression(PiType(a, B)))
  v = Var('v', TypeExpression(PiType(b, C)))
  w = Var('w', A)
  inhab = Expression(
      Abstract(u, Abstract(v, Abstract(w, Apply(v, Apply(u, w)))))
  )
  line = f'Derive {inhab}'
  print(line)
  print('-' * len(line))
  jdgmnt = Judgement(Context(), Statement(inhab))
  print(DeriveTerm(jdgmnt).ShortenedFlagFormat())

  print('Exercise 5.7b')
  print('Prove (((A => B) => A) => ((A => B) => B)) is a tautology')
  A = TypeVar('A', Star())
  B = TypeVar('B', Star())
  a = Var('a', A)
  b = Var('b', B)
  y = Var('y', TypeExpression(PiType(a, B)))
  x = Var('x', TypeExpression(PiType(y, A)))
  T = TypeExpression(PiType(x, PiType(y, B)))
  print('Find an inhabitant of', T)
  u = Var('u', TypeExpression(PiType(y, A)))
  v = Var('v', TypeExpression(PiType(a, B)))
  inhab = Expression(Abstract(u, Abstract(v, Apply(v, Apply(u, v)))))
  line = f'Derive {inhab}'
  print(line)
  print('-' * len(line))
  jdgmnt = Judgement(Context(), Statement(inhab))
  print(DeriveTerm(jdgmnt).ShortenedFlagFormat())

  print('Exercise 5.7c')
  print('Prove ((A => (B => C)) => ((A => B) => (A => C))) is a tautology')
  A = TypeVar('A', Star())
  B = TypeVar('B', Star())
  C = TypeVar('C', Star())
  x = Var('x', TypeExpression(PiType(a, PiType(b, C))))
  y = Var('y', TypeExpression(PiType(a, B)))
  T = TypeExpression(PiType(x, PiType(y, PiType(a, C))))
  print('Find an inhabitant of', T)
  u = Var('u', TypeExpression(PiType(a, PiType(b, C))))
  v = Var('v', TypeExpression(PiType(a, B)))
  w = Var('w', A)
  inhab = Expression(
      Abstract(u, Abstract(v, Abstract(w, Apply(Apply(u, w), Apply(v, w)))))
  )
  line = f'Derive {inhab}'
  print(line)
  print('-' * len(line))
  jdgmnt = Judgement(Context(), Statement(inhab))
  print(DeriveTerm(jdgmnt).ShortenedFlagFormat())


if __name__ == '__main__':
  RunExercises()
