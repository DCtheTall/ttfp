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
  N = Expression(TApply(M, gamma))
  print(N)
  print(
      f'{N.typ} =α {M.Type().body}[{alpha} := {gamma}]:',
      N.typ == SubstituteType(
          M.Type().body, M.Type().arg.typ, ExpressionType(gamma), [], M.Type().arg,
      )
  )


if __name__ == '__main__':
  RunExamples()
