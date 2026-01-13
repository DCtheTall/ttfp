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
  delta = TypeVar('δ')
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
                  z_ut, ut.Apply(ut.Apply(y_ut, ut.Apply(x_ut, z_ut)), x_ut)
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


  print('\nExercise 2.8a')
  x = Var('x', Arrow(gamma, beta))
  y = Var('y', Arrow(Arrow(gamma, beta), beta))
  z = Var('z', gamma)
  print(x, y, z)
  M = Expression(Abstract(x, Abstract(y, Apply(y, Abstract(z, Apply(y, x))))))
  print(M)

  print('Exercise 2.8d')
  deriv = DeriveTerm(Judgement(Context(), Statement(M, M.typ)))
  print(deriv.FlagFormat())


  print('\nExercise 2.9a')
  x = Var('x', Arrow(delta, Arrow(delta, alpha)))
  y = Var('y', Arrow(gamma, alpha))
  z = Var('z', Arrow(alpha, beta))
  u = Var('u', delta)
  v = Var('v', gamma)
  jdgmnt = Judgement(
      Context(x, y, z),
      Statement(
          Expression(Abstract(u, Abstract(v, Apply(z, Apply(y, v))))),
          Arrow(delta, Arrow(gamma, beta))
      )
  )
  deriv = DeriveTerm(jdgmnt)
  print(jdgmnt)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.9b')
  jdgmnt = Judgement(
      Context(x, y, z),
      Statement(
          Expression(Abstract(u, Abstract(v, Apply(z, Apply(Apply(x, u), u))))),
          Arrow(delta, Arrow(gamma, beta))
      )
  )
  deriv = DeriveTerm(jdgmnt)
  print(jdgmnt)
  print('------')
  print(deriv.FlagFormat())


  print('\nExercise 2.10a')
  M = ut.Expression(ut.Apply(ut.Apply(x_ut, z_ut), ut.Apply(y_ut, z_ut)))
  M_t = InferType(M, [gamma, beta, alpha])
  M_types = InferTypes(M, [gamma, beta, alpha])
  M_typemap = {str(k): str(v) for k, v in M_types}
  print('x:', M_typemap[str(x_ut)])
  print('y:', M_typemap[str(y_ut)])
  print('z:', M_typemap[str(z_ut)])
  print(f'{M}:', M_types[0][1])
  x = Var('x', Arrow(gamma, Arrow(beta, alpha)))
  y = Var('y', Arrow(gamma, beta))
  z = Var('z', gamma)
  M = Expression(Apply(Apply(x, z), Apply(y, z)))
  jdgmnt = Judgement(Context(x, y, z), Statement(M, alpha))
  deriv = DeriveTerm(jdgmnt)
  print('------')
  print(jdgmnt)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.10b')
  x = Var('x', Arrow(Arrow(alpha, beta), beta))
  y = Var('y', Arrow(gamma, Arrow(alpha, beta)))
  z = Var('z', gamma)
  print('x:', x.typ)
  print('y:', y.typ)
  print('z:', z.typ)
  M = Expression(Abstract(x, Apply(x, Apply(y, z))))
  print(M)
  jdgmnt = Judgement(Context(y, z), Statement(M, M.typ))
  deriv = DeriveTerm(jdgmnt)
  print('------')
  print(jdgmnt)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.10c')
  x = Var('x', Arrow(alpha, Arrow(alpha, beta)))
  y = Var('y', alpha)
  z = Var('z', Arrow(beta, gamma))
  print('x:', x.typ)
  print('y:', y.typ)
  print('z:', z.typ)
  M = Expression(Abstract(y, Abstract(z, Apply(z, Apply(Apply(x, y), y)))))
  print(M)
  jdgmnt = Judgement(Context(x), Statement(M, M.typ))
  deriv = DeriveTerm(jdgmnt)
  print('------')
  print(jdgmnt)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.10d')
  x = Var('x', Arrow(alpha, beta))
  y = Var('y', Arrow(beta, Arrow(alpha, gamma)))
  z = Var('z', alpha)
  print('x:', x.typ)
  print('y:', y.typ)
  print('z:', z.typ)
  M = Expression(Abstract(x, Apply(Apply(y, Apply(x, z)), z)))
  print(M)
  jdgmnt = Judgement(Context(y, z), Statement(M, M.typ))
  deriv = DeriveTerm(jdgmnt)
  print('------')
  print(jdgmnt)
  print('------')
  print(deriv.FlagFormat())


  print('\nExercise 2.11a')
  goal_t = Arrow(
        Arrow(alpha, Arrow(alpha, gamma)), Arrow(alpha, Arrow(beta, gamma))
  )
  x = Var('x', Arrow(alpha, Arrow(alpha, gamma)))
  y = Var('y', alpha)
  z = Var('z', beta)
  M, deriv = FindTerm(Context(), goal_t, [x, y, z])
  print(M)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.11b')
  goal_t = Arrow(
      Arrow(Arrow(alpha, gamma), alpha),
      Arrow(Arrow(alpha, gamma), Arrow(beta, gamma))
  )
  x = Var('x', Arrow(Arrow(alpha, gamma), alpha))
  y = Var('y', Arrow(alpha, gamma))
  z = Var('z', beta)
  M, deriv = FindTerm(Context(), goal_t, [x, y, z])
  print(M)
  print('------')
  print(deriv.FlagFormat())


  print('\nExercise 2.12a')
  goal_t = Arrow(
      Arrow(Arrow(alpha, beta), alpha),
      Arrow(Arrow(alpha, Arrow(alpha, beta)), alpha)
    )
  x = Var('x', Arrow(Arrow(alpha, beta), alpha))
  y = Var('y', Arrow(alpha, Arrow(alpha, beta)))
  z = Var('z', alpha)
  M, deriv = FindTerm(Context(), goal_t, [x, y, z])
  print(M)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.12b')
  goal_t = Arrow(
      Arrow(Arrow(alpha, beta), alpha),
      Arrow(Arrow(alpha, Arrow(alpha, beta)), beta)
    )
  x = Var('x', Arrow(Arrow(alpha, beta), alpha))
  y = Var('y', Arrow(alpha, Arrow(alpha, beta)))
  z = Var('z', alpha)
  u = Var('u', alpha)
  M, deriv = FindTerm(Context(), goal_t, [x, y, z, u])
  print(M)
  print('------')
  print(deriv.FlagFormat())


  print('\nExercise 2.13a')
  goal_t = Arrow(Arrow(alpha, beta), Arrow(alpha, gamma))
  print('τ:', goal_t)
  x = Var('x', Arrow(alpha, Arrow(beta, gamma)))
  ctx = Context(x)
  print('Γ:', ctx)
  y = Var('y', Arrow(alpha, beta))
  z = Var('z', alpha)
  M, deriv = FindTerm(ctx, goal_t, [y, z])
  print(M)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.13b')
  goal_t = Arrow(alpha, Arrow(Arrow(alpha, beta), gamma))
  print('τ:', goal_t)
  x = Var('x', Arrow(alpha, Arrow(beta, Arrow(alpha, gamma))))
  ctx = Context(x)
  print('Γ:', ctx)
  y = Var('y', Arrow(alpha, beta))
  z = Var('z', alpha)
  M, deriv = FindTerm(ctx, goal_t, [y, z])
  print(M)
  print('------')
  print(deriv.FlagFormat())

  print('Exercise 2.13c')
  goal_t = Arrow(Arrow(alpha, gamma), Arrow(Arrow(beta, alpha), gamma))
  print('τ:', goal_t)
  x = Var('x', Arrow(Arrow(beta, gamma), gamma))
  ctx = Context(x)
  print('Γ:', ctx)
  y = Var('y', Arrow(alpha, gamma))
  z = Var('z', Arrow(beta, alpha))
  u = Var('u', beta)
  M, deriv = FindTerm(ctx, goal_t, [y, z, u, v])
  print(M)
  print('------')
  print(deriv.FlagFormat())


  print('\nExercise 2.14')
  goal_t = Arrow(alpha, Arrow(beta, gamma))
  print('τ:', goal_t)
  x = Var('x', Arrow(Arrow(gamma, beta), Arrow(alpha, gamma)))
  ctx = Context(x)
  print('Γ:', ctx)
  y = Var('y', alpha)
  z = Var('z', beta)
  u = Var('u', gamma)
  M, deriv = FindTerm(ctx, goal_t, [y, z, u])
  print(M)
  print('------')
  print(deriv.FlagFormat())


if __name__ == '__main__':
  RunExercises()
