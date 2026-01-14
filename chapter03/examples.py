"""
Chapter 3 Examples
==================

"""


from second_order_typed_lambda_calculus import *


def RunExamples():
  # Declare type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')


  print('Examples from 3.2')
  x = Var('x', alpha)
  print('Polymorphic identity:', Expression(TAbstract(alpha, Abstract(x, x))))
  # Mt = TExpression(PiType(alpha, alpha))
  # Nt = TExpression(PiType(beta, beta))
  # print(f'{M} =α {N}:', M == N)


if __name__ == '__main__':
  RunExamples()
