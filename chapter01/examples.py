"""
Chapter 1 Examples
==================

"""


from untyped_lambda_calculus import (
    Abstract,
    Apply,
    BetaReduce,
    BindingVar,
    BoundVar,
    Expression,
    FreeVars,
    OneStepBetaReduce,
    Redexes,
    Substitute,
    Subterms,
    Var,
)


def RunExamples():
  # Declare variables
  x = Var('x')
  y = Var('y')
  z = Var('z')

  u = Var('u')
  v = Var('v')
  w = Var('w')

  print('1.3.7 Examples')
  a = Expression(Apply(x, z))
  b = Expression(Abstract(x, Apply(x, x)))
  c = Expression(Apply(b, b))
  print(f'Sub({a}):', Subterms(a))
  print(f'Sub({b}):', Subterms(b))
  print(f'Sub({c}):', Subterms(c))


  print('\n1.4.2 Examples')
  a = Expression(Abstract(x, Apply(x, y)))
  b = Expression(Apply(x, a))
  print(f'FV({a}):', FreeVars(a))
  print(f'FV({b}):', FreeVars(b))


  print('1.4.3 Examples')
  a = Expression(
      Abstract(
          x,
          Abstract(y, Abstract(z, Apply(Apply(x, x), y)))
      )
  )
  b = Expression(
      Abstract(x, Abstract(y, Apply(Apply(x, x), y)))
  )
  c = Expression(Abstract(x, Apply(Apply(x, x), y)))
  print(f'Closed({a}):', a.Closed())
  print(f'Closed({b}):', b.Closed())
  print(f'Closed({c}):', c.Closed())


  print('\n1.5.3 Examples')
  a = Expression(
      Apply(
          Abstract(x, Apply(x, Abstract(z, Apply(x, y)))),
          z
      )
  )
  b = Expression(
      Apply(
          Abstract(u, Apply(u, Abstract(z, Apply(u, y)))),
          z
      )
  )
  c = Expression(
      Apply(
          Abstract(z, Apply(z, Abstract(x, Apply(z, y)))),
          z
      )
  )
  d = Expression(
      Apply(
          Abstract(y, Apply(y, Abstract(z, Apply(y, y)))),
          z
      )
  )
  e = Expression(
      Apply(
          Abstract(z, Apply(z, Abstract(z, Apply(z, y)))),
          z
      )
  )
  f = Expression(
      Apply(
          Abstract(u, Apply(u, Abstract(z, Apply(u, y)))),
          v
      )
  )
  print(f'{a} =α {a}:', a == a)
  print(f'{a} =α {b}:', a == b)
  print(f'{a} =α {c}:', a == c)
  print('RHS after renames:', c)
  print(f'{a} =α {d}:', a == d)
  print(f'{a} =α {e}:', a == e)
  print(f'{a} =α {f}:', a == f)

  a = Expression(
      Abstract(x, Abstract(y, Apply(Apply(x, z), y)))
  )
  b = Expression(
      Abstract(v, Abstract(y, Apply(Apply(v, z), y)))
  )
  c = Expression(
      Abstract(v, Abstract(u, Apply(Apply(v, z), u)))
  )
  d = Expression(
      Abstract(y, Abstract(y, Apply(Apply(y, z), y)))
  )
  e = Expression(
      Abstract(z, Abstract(y, Apply(Apply(z, z), y)))
  )
  print(f'{a} =α {b}:', a == b)
  print(f'{a} =α {c}:', a == c)
  print(f'{a} =α {d}:', a == d)
  print(f'{a} =α {e}:', a == e)


  print('\n1.6.4 Examples')
  M = Expression(Abstract(y, Apply(y, x)))
  N = Expression(Apply(x, y))
  print(f'{M}[{x} := {N}]:', Substitute(M, x, N, [z]))

  M = Expression(Abstract(x, Apply(y, x)))
  a = Substitute(M, x, N, [z])
  print(f'{M}[{x} := {N}]:', a)
  print(f'{M}[{x} := {N}] == {M}:', a == M)

  M = Expression(Abstract(x, Abstract(y, Apply(Apply(z, z), x))))
  N = Expression(y)
  b = Substitute(M, z, N, [u, v])
  print(f'{M}[{z} := {N}]:', b)
  c = Expression(Abstract(x, Abstract(y, Apply(Apply(y, y), x))))
  print(f'{b} == {c}:', b == c)


  print('\n1.8.2 Examples')
  M = Expression(Apply(Abstract(x, Apply(x, Apply(x, y))), z))
  print(f'{M} ->', OneStepBetaReduce(M))

  M = Expression(Apply(Abstract(x, Apply(Abstract(y, Apply(y, x)), z)), v))
  print('Normal order')
  N = OneStepBetaReduce(M)
  print(f'{M} ->', N, '->', OneStepBetaReduce(N))
  print('Applicative order')
  N = OneStepBetaReduce(M, applicative=True)
  print(f'{M} ->', N, '->', OneStepBetaReduce(N, applicative=True))

  xx = Abstract(x, Apply(x, x))
  M = Expression(Apply(xx, xx))
  print('Self application')
  print(f'{M} ->', OneStepBetaReduce(M))


  print('\n1.8.6 Lemma Example')
  M = Expression(Apply(Abstract(x, Apply(Abstract(y, Apply(y, x)), z)), v))
  N = Expression(Apply(z, v))
  print(f'{M} =β {N}:', M >> N)
  print(f'{N} =β {M}:', N >> M)


  print('\n1.9.3 Examples')
  M = Expression(Apply(Abstract(x, Apply(Abstract(y, Apply(y, x)), z)), v))
  print(f'{M} ->>', BetaReduce(M))
  print(f'{BetaReduce(M)} in β-nf:', BetaReduce(M).BetaNormal())
  print(f'Redexes({M}):', Redexes(BetaReduce(M)))

  xx = Abstract(x, Apply(x, x))
  omega = Expression(Apply(xx, xx))
  print(f'{omega} in β-nf:', omega.BetaNormal())
  print(f'Redexes({omega}):', Redexes(omega))
  print(f'{omega} ->', OneStepBetaReduce(omega))

  delta = Abstract(x, Apply(Apply(x, x), x))
  two_deltas = Expression(Apply(delta, delta))
  print(f'{two_deltas} -> {OneStepBetaReduce(two_deltas)}')
  three_deltas = Expression(Apply(Apply(delta, delta), delta))
  print(f'{three_deltas} -> {OneStepBetaReduce(three_deltas)}')


  print('\n1.10.3 Example')
  a = Abstract(y, Abstract(x, Apply(Apply(x, y), x)))
  b = Abstract(y, Apply(y, y))
  M = Expression(Apply(a, b))
  print(f'{M} ->', OneStepBetaReduce(M))


if __name__ == '__main__':
  RunExamples()
