"""
Chapter 1 Exercises
===================

"""


from untyped_lambda_calculus import (
    Abstract,
    Apply,
    BetaReduce,
    Expression,
    FreeVars,
    OneStepBetaReduce,
    Redexes,
    SimulSubstitute,
    Substitute,
    Subterms,
    Var,
)


def RunExercises():
  # Declare variables.
  x = Var('x')
  y = Var('y')
  z = Var('z')

  u = Var('u')
  v = Var('v')
  w = Var('w')

  p = Var('p')
  q = Var('q')
  r = Var('r')

  print('Exercise 1.1a')
  a = Expression(
      Abstract(x, Apply(Apply(Apply(x, z), y), Apply(x, x)))
  )
  print(a)
  print('Exercise 1.1b')
  b = Expression(
      Apply(
          Abstract(x, Abstract(y, Abstract(z, Apply(z, Apply(Apply(x, y), z))))),
          Abstract(u, u)
      )
  )
  print(b)


  print('\nExercise 1.2a')
  comp = Expression(Abstract(x, Apply(x, Abstract(x, x))))
  a = Expression(Abstract(y, Apply(y, Abstract(x, x))))
  print(f'{a} =α {comp}:', a == comp)
  print('Exercise 1.2b')
  b = Expression(Abstract(y, Apply(y, Abstract(x, y))))
  print(f'{b} =α {comp}:', b == comp)
  print('Exercise 1.2c')
  c = Expression(Abstract(y, Apply(y, Abstract(y, x))))
  print(f'{c} =α {comp}:', c == comp)


  print('\nExercise 1.3')
  a = Expression(Abstract(x, Apply(x, Abstract(z, y))))
  b = Expression(Abstract(z, Apply(z, Abstract(z, y))))
  print(f'{a} =α {b}:', a == b)


  print('\nExercise 1.4a')
  U = Expression(
      Apply(
          Abstract(z, Apply(Apply(z, x), z)),
          Apply(Abstract(y, Apply(x, y)), x)
      )
  )
  print(f'Sub({U}):', Subterms(U))
  print('Exercise 1.4c')
  print(f'FV({U}):', FreeVars(U))
  print('Exercise 1.4d')
  a = Expression(
      Apply(
          Abstract(y, Apply(Apply(y, x), y)),
          Apply(Abstract(z, Apply(x, z)), x)
      )
  )
  print(f'{U} =α {a}:', U == a)
  b = Expression(
      Apply(
          Abstract(x, Apply(Apply(x, y), x)),
          Apply(Abstract(z, Apply(y, z)), y)
      )
  )
  print(f'{U} =α {b}:', U == b)
  c = Expression(
      Apply(
          Abstract(y, Apply(Apply(y, x), y)),
          Apply(Abstract(y, Apply(x, y)), x)
      )
  )
  print(f'{U} =α {c}:', U == c)
  d = Expression(
      Apply(
          Abstract(v, Apply(Apply(v, x), v)),
          Apply(Abstract(u, Apply(u, v)), x)
      )
  )
  print(f'{U} =α {d}:', U == d)


  print('\nExercise 1.5a')
  M = Expression(Abstract(x, Apply(y, Abstract(y, Apply(x, y)))))
  N = Expression(Abstract(z, Apply(z, x)))
  print(f'{M}[{y} := {N}]:', Substitute(M, y, N, [u]))
  print('Exercise 1.5b')
  a = Expression(Apply(Apply(x, y), z))
  b = Expression(y)
  c = Expression(z)
  print(
      f'({a}[{x} := {b}])[{y} := {c}]:',
      Substitute(Substitute(a, x, b, []), y, c, [])
  )
  print('Exercise 1.5c')
  a = Expression(Abstract(x, Apply(Apply(x, y), z)))
  b = Expression(y)
  c = Expression(z)
  print(
      f'({a}[{x} := {b}])[{y} := {c}]:',
      Substitute(Substitute(a, x, b, []), y, c, [])
  )
  print('Exercise 1.5d')
  M = Expression(Abstract(y, Apply(Apply(y, y), x)))
  N = Expression(Apply(y, z))
  print(f'{M}[{x} := {N}]:', Substitute(M, x, N, [u]))


  print('\nExercise 1.6')
  a = Expression(Apply(x, Abstract(z, y)))
  b = Expression(y)
  c = Expression(z)
  print(
      f'{a}[{x} := {b}][{y} := {c}]:',
      Substitute(Substitute(a, x, b, []), y, c, [u])
  )
  print(
      f'{a}[{y} := {c}][{x} := {b}]:',
      Substitute(Substitute(a, y, c, [u]), x, b, [])
  )
  print(
      f'{a}[{x} := {b}, {y} := {c}]:',
      SimulSubstitute(a, {x: b, y: c}, [u])
  )


  print('\nExercise 1.7a')
  print(f'Redexes({U}):', Redexes(U))
  print('Exercise 1.7b')
  print(U, '->>', BetaReduce(U))


  print('\nExercise 1.8')
  M = Expression(Apply(Abstract(x, Apply(x, x)), y))
  N = Expression(Apply(Apply(Abstract(x, Abstract(y, Apply(y, x))), x), x))
  print(M, '->>', BetaReduce(M))
  print(N, '->>', BetaReduce(N))
  print(f'{M} =β {N}:', M >> N)


  print('\nExercise 1.9')
  K = Expression(Abstract(x, Abstract(y, x)))
  S = Expression(
      Abstract(x, Abstract(y, Abstract(z, Apply(Apply(x, z), Apply(y, z)))))
  )
  print(f'K: {K}')
  print(f'S: {S}')

  print('Exercise 1.9a')
  M = Expression(Apply(Apply(K, p), q))
  print(M, '->>', BetaReduce(M))
  M = Expression(Apply(Apply(Apply(S, p), q), r))
  print(M, '->>', BetaReduce(M))

  print('Exercise 1.9b')
  identity = Expression(Abstract(x, x))
  M = Expression(Apply(Apply(S, K), K))
  print(f'{M} =β {identity}:', M >> identity)

  print('Exercise 1.9c')
  B = Expression(Apply(Apply(S, Apply(K, S)), K))
  print('(S (K S) K):', B)
  M = Expression(Apply(Apply(Apply(B, u), v), w))
  N = Expression(Apply(u, Apply(v, w)))
  print(f'{M} =β {N}:', M >> N)

  print('Exercise 1.9d')
  M = Expression(Apply(Apply(Apply(Apply(S, S), S), K), K))
  print('(S S S K K):', M)
  N = Expression(Apply(Apply(Apply(S, K), K), K))
  print('(S K K K):', N)
  print('(S S S K K) =β (S K K K):', M >> N)

  print('\nExercise 1.10')
  zero = Expression(Abstract(y, Abstract(x, x)))
  print('zero:', zero)
  one = Expression(Abstract(y, Abstract(x, Apply(y, x))))
  print('one:', one)
  two = Expression(Abstract(y, Abstract(x, Apply(y, Apply(y, x)))))
  print('two:', two)
  add = Expression(
      Abstract(
          u,
          Abstract(
              v,
              Abstract(
                  y,
                  Abstract(x, Apply(Apply(u, y), Apply(Apply(v, y), x))))
          )
      )
  )
  print('add:', add)
  mult = Expression(
      Abstract(
          u,
          Abstract(
              v,
              Abstract(
                  y,
                  Abstract(x, Apply(Apply(u, Apply(v, y)), x)))
          )
      )
  )
  print('mult:', mult)

  print('Exercise 1.10a')
  print(
      '(add one one) =β two:', Expression(Apply(Apply(add, one), one)) >> two
  )

  print('Exercise 1.10b')
  print(
    '(add one one) =β (mult one zero):',
    Expression(Apply(Apply(add, one), one)) 
    >> Expression(Apply(Apply(mult, one), zero))
  )
  print(
      '(mult one zero) =β zero:',
      Expression(Apply(Apply(mult, one), zero)) >> zero
  )


  print('\nExercise 1.11')
  succ = Expression(Abstract(u, Abstract(y, Abstract(x, Apply(y, Apply(Apply(u, y), x))))))
  print('succ:', succ)

  print('Exercise 1.11a')
  print('(succ zero) =β one:', Expression(Apply(succ, zero)) >> one)

  print('Exercise 1.11b')
  print('(succ one) =β two:', Expression(Apply(succ, one)) >> two)


  print('\nExercise 1.12')
  true = Expression(Abstract(x, Abstract(y, x)))
  print('true:', true)
  print('true =α K:', true == K)
  false = Expression(Abstract(x, Abstract(y, y)))
  print('false:', false)
  print('false =α zero:', false == zero)
  nott = Expression(Abstract(z, Apply(Apply(z, false), true)))
  print('not:', nott)
  print(
      '(not (not true) =β true:',
      Expression(Apply(nott, Apply(nott, true))) >> true
  )
  print(
      '(not (not false)) =β false:',
      Expression(Apply(nott, Apply(nott, false))) >> false
  )


  print('\nExercise 1.13')
  iszero = Expression(Abstract(z, Apply(Apply(z, Abstract(x, false)), true)))
  print('iszero:', iszero)

  print('Exercise 1.13a')
  print('(iszero zero) =β true:', Expression(Apply(iszero, zero)) >> true)

  print('Exercise 1.13b')
  three = BetaReduce(Expression(Apply(succ, two)))
  print('three:', three)
  four = BetaReduce(Expression(Apply(succ, three)))
  print('four:', four)
  print('(iszero one) =β false:', Expression(Apply(iszero, one)) >> false)
  print('(iszero two) =β false:', Expression(Apply(iszero, two)) >> false)
  print('(iszero three) =β false:', Expression(Apply(iszero, three)) >> false)
  print('(iszero four) =β false:', Expression(Apply(iszero, four)) >> false)
  print(
      '(iszero (succ (succ four))) =β false:',
      Expression(Apply(iszero, Apply(succ, Apply(succ, four)))) >> false
  )

  print('\nExercise 1.14')
  if_x_then_u_else_v = Expression(Abstract(x, Apply(Apply(x, u), v)))
  print('if x then u else v:', if_x_then_u_else_v)
  a = BetaReduce(Expression(Apply(if_x_then_u_else_v, true)))
  print('((if x then u else v) true) ->>', a)


  print('\nExercise 1.19')
  U = Expression(Abstract(z, Abstract(x, Apply(x, Apply(Apply(z, z), x)))))
  print('U:', U)
  Z = Expression(Apply(U, U))
  print('Z:', Z)
  a = Expression(Apply(Z, u))
  print('(Z u):', a)
  a = OneStepBetaReduce(a)
  print('  ->', a)
  a = OneStepBetaReduce(a)
  print('  ->', a)
  print('  =α (u (Z u)):', a == Expression(Apply(u, Apply(Z, u))))

  
  print('\nExercise 1.20a')
  F = Expression(Abstract(u, Abstract(x, Abstract(y, Apply(Apply(x, u), y)))))
  print('F:', F)
  Y = Expression(
      Abstract(
          u,
          Apply(
              Abstract(z, Apply(u, Apply(z, z))),
              Abstract(z, Apply(u, Apply(z, z)))
          )
      )
  )
  print('Y:', Y)
  M = Expression(Apply(Y, F))
  print('M = (Y F):', M)
  H = OneStepBetaReduce(M)
  print('  -> H:', H)
  FH = OneStepBetaReduce(H)
  print('  ->', FH)
  print('  =α (F H):', FH == Expression(Apply(F, H)))
  N = Expression(Apply(F, M))
  print('(F M) = (F (Y F)):', N)
  N = Expression(Apply(F, OneStepBetaReduce(M)))
  print('  ->', N)
  print('  =α (F H):', N == FH)
  N = Expression(Apply(F, M))
  print('(F M):', N)
  N = OneStepBetaReduce(N)
  print('  ->', N)
  print(
      '  =α λxy.(x M y):',
      N == Expression(Abstract(x, Abstract(y, Apply(Apply(x, M), y))))
  )

  print('Exercise 1.20b')
  F = Expression(
      Abstract(
          u,
          Abstract(
              x, Abstract(y, Abstract(z, Apply(Apply(Apply(x, y), z), u)))
          )
      )
  )
  print('F:', F)
  print('Y:', Y)
  M = Expression(Apply(Y, F))
  print('M = (Y F):', M)
  H = OneStepBetaReduce(M)
  print('  -> H:', H)
  FH = OneStepBetaReduce(H)
  print('  ->', FH)
  print('  =α (F H):', FH == Expression(Apply(F, H)))
  N = Expression(Apply(F, M))
  print('(F M) = (F (Y F)):', N)
  N = Expression(Apply(F, OneStepBetaReduce(M)))
  print('  ->', N)
  print('  =α (F H):', N == FH)
  N = Expression(Apply(Apply(Apply(Apply(F, M), x), y), z))
  print('(F M x y z):', N)
  N = OneStepBetaReduce(N)
  print('  ->', N)
  N = OneStepBetaReduce(N, [p])
  print('  ->', N)
  N = OneStepBetaReduce(N, [q])
  print('  ->', N)
  N = OneStepBetaReduce(N, [r, v, w])
  print('  ->', N)
  print(
      '  =α (x y z M):',
      N == Expression(Apply(Apply(Apply(x, y), z), M))
  )


if __name__ == '__main__':
  RunExercises()
