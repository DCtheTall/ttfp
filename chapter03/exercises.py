"""
Chapter 3 Exercises
===================

"""

import itertools

from second_order_typed_lambda_calculus import *



def RunExercises():
  # Declate type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')


  print('Exercise 3.1')
  f = Var('f', Arrow(alpha, beta))
  x = Var('x', alpha)
  valid_contexts = []
  for p in itertools.permutations([alpha, beta, f, x]):
    try:
      valid_contexts.append(Context(*p))
    except ValueError:
      pass
  for i, ctx in enumerate(valid_contexts):
    print(f'{i + 1}:', ctx)

if __name__ == '__main__':
  RunExercises()