"""
Chapter 3 Examples
==================

"""


from second_order_typed_lambda_calculus import *


def RunExamples():
  # Declare type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')
  gamma = TypeVar('γ')


  print('Examples from 3.2')
  x = Var('x', alpha)
  y = Var('y', beta)
  print('Polymorphic identity:')
  M = Expression(TAbstract(alpha, Abstract(x, x)))
  print(M)
  N = Expression(TAbstract(beta, Abstract(y, y)))
  print(f'{M} =α {N}:', M == N)
  print(f'{M.typ} =α {N.typ}:', M.typ == N.typ)


  print('\nExamples from 3.3')
  x = Var('x', alpha)
  y = Var('y', Arrow(alpha, beta))
  print('Type abstraction')
  M = Expression(Abstract(x, x))
  print('M:', M)
  print(f'λ{alpha}:*.M:', Expression(TAbstract(alpha, M)))
  print('Type application')
  M = Expression(TAbstract(alpha, Abstract(x, x)))
  print('Polymorphic identity:', M)
  N = Expression(TApply(M, beta))
  print(f'Applied to {beta}:', N)
  print(
      f'{N.typ} =α {M.Type().body}[{alpha} := {beta}]:',
      N.typ == SubstituteType(
          M.Type().body,
          M.Type().arg.typ,
          ExpressionType(beta),
          [],
          M.Type().arg,
      )
  )
  N = Expression(TApply(M, gamma))
  print(f'Applied to {gamma}:', N)
  z = Var('z', gamma)
  print('Applied to term:', Expression(Apply(N, z)))


  print('\nExample 3.4.5')
  ctx = Context()
  print('Empty context:', ctx)
  print(f'Dom({ctx}):', ctx.Dom())
  ctx = ctx.PushTypeVar(alpha)
  print('Add type variable:', ctx)
  x = Var('x', Arrow(alpha, alpha))
  ctx = ctx.PushVar(x)
  print('Add variable:', ctx)
  y = Var('y', Arrow(Arrow(alpha, alpha), beta))
  ctx = ctx.PushTypeVar(beta).PushVar(y)
  print(f'Add {beta} and {y}:', ctx)


if __name__ == '__main__':
  RunExamples()
