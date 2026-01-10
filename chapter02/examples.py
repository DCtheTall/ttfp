"""
Chapter 2 Examples
==================

"""


from simply_typed_lambda_calculus import *


def RunExamples():
  # Declare type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')
  gamma = TypeVar('γ')
  rho = TypeVar('ρ')
  sigma = TypeVar('σ')
  tau = TypeVar('τ')


  print('Example 2.2.6')
  x = Var('x', sigma)
  print(x)
  print(Expression(Abstract(x, x)))
  y = Var('y', Arrow(sigma, tau))
  print(y)
  print(Expression(Apply(y, x)))


  print('\nExample 2.3.1')
  x = Var('x', Arrow(alpha, alpha))
  y = Var('y', Arrow(Arrow(alpha, alpha), gamma))
  print(x)
  print(y)
  print(Expression(Apply(y, x)))


  print('\nExample 2.4.6')
  y = Var('y', Arrow(alpha, beta))
  z = Var('z', alpha)
  ctx = Context(y, z)
  deriv = Derivation(ctx)
  a = deriv.VarRule(y)
  b = deriv.VarRule(z)
  i = deriv.ApplRule(a, b)
  ii = deriv.AbstRule(z, i)
  iii = deriv.AbstRule(y, ii)
  print('Linear:')
  print(deriv.LinearFormat())
  print('Flag:')
  print(deriv.FlagFormat())


  print('\nExample 2.7')
  y = Var('y', Arrow(alpha, beta))
  z = Var('z', alpha)
  M = Expression(Abstract(z, Abstract(y, Apply(y, z))))
  ctx = Context()
  jdgmnt = Judgement(ctx, Statement(M, M.typ))
  print('Derivation of:', jdgmnt, '\n')
  print(DeriveTerm(jdgmnt).FlagFormat())


  print('\nExample 2.8')
  x = Var('x', Arrow(alpha, alpha))
  y = Var('y', Arrow(Arrow(alpha, alpha), beta))
  z = Var('z', beta)
  u = Var('u', gamma)
  M = Expression(Apply(Abstract(z, Abstract(u, z)), Apply(y, x)))
  ctx = Context(x, y)
  jdgmnt = Judgement(ctx, Statement(M, Arrow(gamma, beta)))
  print('Derivation of:', jdgmnt, '\n')
  print(DeriveTerm(jdgmnt).FlagFormat())

  print('\nExample 2.9')
  x = Var('x', alpha)
  y = Var('y', beta)
  goal_t = Arrow(alpha, Arrow(beta, alpha))
  print('Finding term with type:', goal_t)
  term, deriv = FindTerm(Context(), goal_t, [x, y])
  print('Term:', term)
  print('Derivation:')
  print(deriv.FlagFormat())

  print('\nExample 2.10.2')
  x = Var('x', rho)
  y = Var('y', sigma)
  z = Var('z', tau)
  u = Var('u', gamma)
  ctx = Context(x, y, z)
  print('Dom(Ø):', Context())
  print('Γ:', ctx)
  print(f'Ø < [{x}, {z}] < Γ:', Context() < Context(x, z) < ctx)
  print(f'[{z}, {y}, {x}] == Γ:', Context(z, y, x) == ctx)
  print(f'Γ | [{z}, {u}, {x}]:', ctx | [z, u, x])
  # x = Var('x', alpha)
  # y = Var('y', beta)
  # z = Var('z', Arrow(alpha, beta))
  # u = Var('u', gamma)
  # ctx = Context(x, y, z)
  # print('Γ:', ctx)
  # print('Dom(Γ):', ctx.Dom())
  # ctx_prime = Context(x, y)
  # print('Γ\':', ctx_prime)
  # print('Γ\' ⊆ Γ:', ctx_prime < ctx)
  # ctx_d_prime = Context(u)
  # print('Γ":', ctx_d_prime)
  # print('Γ" ⊆ Γ:', ctx_d_prime < ctx)
  # print(f'Γ | [{x}, {y}]:', ctx | [x, y])


if __name__ == '__main__':
  RunExamples()
