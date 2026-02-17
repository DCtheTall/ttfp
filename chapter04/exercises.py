"""
Chapter 4 Exercises
===================

"""

from dependent_types_lambda_calculus import (
    Abstract,
    Apply,
    Context,
    DeriveKind,
    DeriveType,
    # DeriveTerm,
    Expression,
    Judgement,
    KArrow,
    Star,
    Statement,
    TAbstract,
    TApply,
    TArrow,
    TypeExpression,
    TypeVar,
    Var,
)


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


#   print('\nExercise 4.3a')
#   alpha = TypeVar('α', Star())
#   beta = TypeVar('β', Star())
#   x = Var('x', alpha)
#   y = Var('y', TArrow(alpha, beta))
#   jdgmnt = Judgement(
#       Context(alpha, beta, x, y), Statement(Expression(Apply(y, x)))
#   )
#   line = str(jdgmnt)
#   print(line)
#   print('-' * len(line))
#   deriv = DeriveTerm(jdgmnt)
#   print(deriv.FlagFormat())
  
#   print('\nExercise 4.3b')
#   alpha = TypeVar('α', Star())
#   beta = TypeVar('β', Star())
#   x = Var('x', alpha)
#   y = Var('y', TArrow(alpha, beta))
#   z = Var('z', TArrow(beta, alpha))
#   jdgmnt = Judgement(
#       Context(alpha, beta, x, y, z),
#       Statement(Expression(Apply(z, Apply(y, x))))
#   )
#   line = str(jdgmnt)
#   print(line)
#   print('-' * len(line))
#   deriv = DeriveTerm(jdgmnt)
#   print(deriv.FlagFormat())

  
#   print('\nExercise 4.4a')
#   alpha = TypeVar('α', Star())
#   beta = TypeVar('β', KArrow(Star(), Star()))
#   jdgmnt = Judgement(
#       Context(alpha, beta),
#       Statement(TypeExpression(TApply(beta, TApply(beta, alpha))))
#   )
#   line = str(jdgmnt)
#   print(line)
#   print('-' * len(line))
#   deriv = DeriveType(jdgmnt)
#   print(deriv.FlagFormat())
  
#   print('Exercise 4.4b')
#   alpha = TypeVar('α', Star())
#   beta = TypeVar('β', KArrow(Star(), Star()))
#   bba = TypeExpression(TApply(beta, TApply(beta, alpha)))
#   x = Var('x', bba)
#   y = Var('y', alpha)
#   jdgmnt = Judgement(
#       Context(alpha, beta, x), Statement(Expression(Abstract(y, x)))
#   )
#   line = str(jdgmnt)
#   print(line)
#   print('-' * len(line))
#   deriv = DeriveTerm(jdgmnt)
#   print(deriv.FlagFormat())

#   print('Exercise 4.4c')
#   alpha = TypeVar('α', Star())
#   beta = TypeVar('β', KArrow(Star(), Star()))
#   jdgmnt = Judgement(
#       Context(),
#       Statement(
#           TypeExpression(
#               TAbstract(
#                   alpha, TAbstract(beta, TApply(beta, TApply(beta, alpha)))
#               )
#           )
#       )
#   )
#   line = str(jdgmnt)
#   print(line)
#   print('-' * len(line))
#   deriv = DeriveType(jdgmnt)
#   print(deriv.FlagFormat())

#   print('Exercise 4.4d')
#   alpha = TypeVar('α', Star())
#   beta = TypeVar('β', KArrow(Star(), Star()))
#   gamma = TypeVar('γ', Star())
#   nat = TypeVar('nat', Star())
#   jdgmnt = Judgement(
#       Context(nat),
#       Statement(
#           TypeExpression(
#               TApply(
#                   TApply(
#                       TAbstract(
#                           alpha,
#                           TAbstract(beta, TApply(beta, TApply(beta, alpha)))
#                       ),
#                       nat
#                   ),
#                   TAbstract(gamma, gamma)
#               )
#           )
#       )
#   )
#   line = str(jdgmnt)
#   print(line)
#   print('-' * len(line))
#   deriv = DeriveType(jdgmnt)
#   print(deriv.FlagFormat())


#   print('\nExercise 4.5')
#   alpha = TypeVar('α', Star())
#   beta = TypeVar('β', Star())
#   x = Var('x', alpha)
#   y = Var('y', alpha)
#   M = Expression(Abstract(y, x))
#   M.SetType(TypeExpression(TApply(TAbstract(beta, TArrow(beta, beta)), alpha)))
#   jdgmnt = Judgement(Context(alpha, x), Statement(M))
#   line = str(jdgmnt)
#   print(line)
#   print('-' * len(line))
#   deriv = DeriveTerm(jdgmnt)
#   print(deriv.FlagFormat())


if __name__ == '__main__':
  RunExercises()