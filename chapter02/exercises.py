"""
Chapter 2 Exercises
===================

"""


from simply_typed_lambda_calculus import *
import untyped as ut



def RunExercises():
  # Declate type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')
  gamma = TypeVar('γ')
  A = TypeVar('A')
  B = TypeVar('B')
  C = TypeVar('C')

  print('Exercise 2.1a')
  x_ut = ut.Var('x')
  y_ut = ut.Var('y')
  M = ut.Expression(ut.Apply(ut.Apply(x_ut, x_ut), y_ut))
  print(M)
  try:
    InferTypes(M, [alpha, beta])
  except TypeError as e:
    print(e)
  
  print('Exercise 2.1b')
  M = ut.Expression(ut.Apply(ut.Apply(x_ut, y_ut), y_ut))
  print(M)
  print({str(k): str(v) for k, v in InferTypes(M, [alpha, beta])})

  print('Exercise 2.1c')
  M = ut.Expression(
      ut.Apply(ut.Apply(x_ut, y_ut), x_ut)
  )
  print(M)
  try:
    InferTypes(M, [alpha, beta])
  except TypeError as e:
    print(e)

  print('Exercise 2.1d')
  M = ut.Expression(ut.Apply(x_ut, ut.Apply(x_ut, y_ut)))
  print(M)
  print({str(k): str(v) for k, v in InferTypes(M, [alpha])})

  print('Exercise 2.1e')
  M = ut.Expression(
      ut.Apply(x_ut, ut.Apply(y_ut, x_ut))
  )
  print(M)
  print({str(k): str(v) for k, v in InferTypes(M, [alpha, beta])})


  print('\nExericse 2.2')
  zero = ut.Expression(ut.Abstract(y_ut, ut.Abstract(x_ut, x_ut)))
  zero_t = InferType(zero, [alpha, beta])
  print(f'zero: ({zero}):{zero_t}')
  one = ut.Expression(
      ut.Abstract(y_ut, ut.Abstract(x_ut, ut.Apply(y_ut, x_ut)))
  )
  one_t = InferType(one, [alpha, beta])
  print(f'one: ({one}):{one_t}')
  two = ut.Expression(
      ut.Abstract(
          y_ut, ut.Abstract(x_ut, ut.Apply(y_ut, ut.Apply(y_ut, x_ut)))
      )
  )
  two_t = InferType(two, [alpha])
  print(f'two: ({two}):{two_t}')

  
  print('\nExercise 2.3')
  K = ut.Expression(ut.Abstract(x_ut, ut.Abstract(y_ut, x_ut)))
  K_t = InferType(K, [alpha, beta])
  print(f'K: ({K}):{K_t}')
  z_ut = ut.Var('z')
  S = ut.Expression(
      ut.Abstract(
          x_ut,
          ut.Abstract(
              y_ut,
              ut.Abstract(
                  z_ut, ut.Apply(ut.Apply(x_ut, z_ut), ut.Apply(y_ut, z_ut))
              )
          )
      )
  )
  S_t = InferType(S, [alpha, beta, gamma])
  print(f'S: ({S}):{S_t}')


  print('\nExercise 2.4a')
  M = ut.Expression(
      ut.Abstract(
          x_ut, ut.Abstract(
              y_ut, ut.Abstract(z_ut, ut.Apply(x_ut, ut.Apply(y_ut, z_ut)))
          )
      )
  )
  print(M)
  M_types = InferTypes(M, [gamma, beta, alpha])
  M_typemap = {str(k): str(v) for k, v in M_types}
  print('x:', M_typemap[str(x_ut)])
  print('y:', M_typemap[str(y_ut)])
  print('z:', M_typemap[str(z_ut)])
  print(f'{M}:', M_types[0][1])

  print('Exercise 2.4b')
  M = ut.Expression(
      ut.Abstract(
          x_ut, ut.Abstract(
              y_ut,
              ut.Abstract(
                  z_ut,
                  ut.Apply(
                      ut.Apply(
                          y_ut, ut.Apply(x_ut, z_ut)
                      ),
                      x_ut,
                  )
              )
          )
      )
  )
  print(M)
  M_types = InferTypes(M, [gamma, beta, alpha])
  M_typemap = {str(k): str(v) for k, v in M_types}
  print('x:', M_typemap[str(x_ut)])
  print('y:', M_typemap[str(y_ut)])
  print('z:', M_typemap[str(z_ut)])
  print(f'{M}:', M_types[0][1])


  print('Exercise 2.5a')
  M = ut.Expression(
      ut.Abstract(
          x_ut,
          ut.Abstract(
              y_ut, ut.Apply(ut.Apply(x_ut, ut.Abstract(z_ut, y_ut)), y_ut)
          )
      )
  )
  M_types = InferTypes(M, [gamma, beta, alpha])
  M_typemap = {str(k): str(v) for k, v in M_types}
  print('x:', M_typemap[str(x_ut)])
  print('y:', M_typemap[str(y_ut)])
  print('z:', M_typemap[str(z_ut)])
  print(f'{M}:', M_types[0][1])

  print('Exercise 2.5b')
  M = ut.Expression(
      ut.Abstract(
          x_ut,
          ut.Abstract(
              y_ut, ut.Apply(ut.Apply(x_ut, ut.Abstract(z_ut, x_ut)), y_ut)
          )
      )
  )
  print(M)
  try:
    M_types = InferTypes(M, [gamma, beta, alpha])
  except TypeError as e:
    print(e)
  

  print('\nExercise 2.6')
  x = Var('x', Arrow(Arrow(alpha, beta), alpha))
  z = Var('z', alpha)
  y = Var('y', beta)
  M = Expression(Abstract(x, Apply(x, Abstract(z, y))))
  jdgmnt = Judgement(Context(y), Statement(M, M.typ))
  print(jdgmnt)
  print('----------')
  deriv = DeriveTerm(jdgmnt)
  print(deriv.FlagFormat())


  print('\nExercise 2.7a')
  f = Var('f', Arrow(A, B))
  g = Var('g', Arrow(B, C))
  x = Var('x', A)
  fog = Expression(Abstract(x, Apply(g, Apply(f, x))))
  jdgmnt = Judgement(Context(f, g), Statement(fog, Arrow(A, C)))
  print(jdgmnt)
  print('----------')
  deriv = DeriveTerm(jdgmnt)
  print(deriv.LinearFormat())

  print('Exercise 2.7b')
  x = Var('x', Arrow(A, B))
  y = Var('y', Arrow(B, C))
  a = Var('a', A)
  goal_t = Arrow(Arrow(A, B), Arrow(Arrow(B, C), Arrow(A, C)))
  term, deriv = FindTerm(Context(), goal_t, [x, y, a])
  print(deriv.LinearFormat())

  print('Exercise 2.7c')
  z = Var('z', alpha)
  x = Var('x', Arrow(alpha, beta))
  y = Var('y', Arrow(beta, gamma))
  M = Expression(Abstract(z, Apply(y, Apply(x, z))))
  deriv = DeriveTerm(Judgement(Context(x, y), Statement(M, Arrow(alpha, gamma))))
  print(deriv.LinearFormat())


if __name__ == '__main__':
  RunExercises()
