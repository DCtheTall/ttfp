"""
Chapter 2 Exercises
===================

"""


from simply_typed_lambda_calculus import *
import untyped



def RunExercises():
  # Declate type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')
  gamma = TypeVar('γ')
  rho = TypeVar('ρ')
  sigma = TypeVar('σ')
  tau = TypeVar('τ')

  print('Exercise 1a.')
  x_untyped = untyped.Var('x')
  y_untyped = untyped.Var('y')
  M = untyped.Expression(
      untyped.Apply(untyped.Apply(x_untyped, x_untyped), y_untyped)
  )
  print(M)
  try:
    InferTypes(M, [alpha, beta])
  except TypeError as e:
    print(e)
  
  print('Exercise 1b.')
  M = untyped.Expression(
      untyped.Apply(untyped.Apply(x_untyped, y_untyped), y_untyped)
  )
  print(M)
  print({str(k): str(v) for k, v in InferTypes(M, [alpha, beta])})

  print('Exercise 1c.')
  M = untyped.Expression(
      untyped.Apply(untyped.Apply(x_untyped, y_untyped), x_untyped)
  )
  print(M)
  try:
    InferTypes(M, [alpha, beta])
  except TypeError as e:
    print(e)

  print('Exercise 1d.')
  M = untyped.Expression(
      untyped.Apply(x_untyped, untyped.Apply(x_untyped, y_untyped))
  )
  print(M)
  print({str(k): str(v) for k, v in InferTypes(M, [alpha])})

  print('Exercise 1e.')
  M = untyped.Expression(
      untyped.Apply(x_untyped, untyped.Apply(y_untyped, x_untyped))
  )
  print(M)
  print({str(k): str(v) for k, v in InferTypes(M, [alpha, beta])})


  print('\nExericse 2.')
  zero = untyped.Expression(
      untyped.Abstract(y_untyped, untyped.Abstract(x_untyped, x_untyped))
  )
  zero_t = InferTypes(zero, [alpha, beta])[0][1]
  print(f'zero: ({zero}):{zero_t}')
  one = untyped.Expression(
      untyped.Abstract(
          y_untyped,
          untyped.Abstract(x_untyped, untyped.Apply(y_untyped, x_untyped))
      )
  )
  one_t = InferTypes(one, [alpha, beta])[0][1]
  print(f'one: ({one}):{one_t}')
  two = untyped.Expression(
      untyped.Abstract(
          y_untyped,
          untyped.Abstract(
              x_untyped,
              untyped.Apply(y_untyped, untyped.Apply(y_untyped, x_untyped))
          )
      )
  )
  two_t = InferTypes(two, [alpha])[0][1]
  print(f'two: ({two}):{two_t}')

  
  print('\nExercise 3.')
  K = untyped.Expression(
      untyped.Abstract(x_untyped, untyped.Abstract(y_untyped, x_untyped))
  )
  K_t = InferTypes(K, [alpha, beta])[0][1]
  print(f'K: ({K}):{K_t}')
  z_untyped = untyped.Var('z')
  S = untyped.Expression(
      untyped.Abstract(
          x_untyped,
          untyped.Abstract(
              y_untyped,
              untyped.Abstract(
                  z_untyped, untyped.Apply(
                      untyped.Apply(x_untyped, z_untyped),
                      untyped.Apply(y_untyped, z_untyped)
                  )
              )
          )
      )
  )
  S_t = InferTypes(S, [alpha, beta, gamma])[0][1]
  print(f'S: ({S}):{S_t}')


if __name__ == '__main__':
  RunExercises()
