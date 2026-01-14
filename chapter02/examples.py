"""
Chapter 2 Examples
==================

"""


from simply_typed_lambda_calculus import (
    Abstract,
    Apply,
    Arrow,
    BetaReduce,
    Context,
    Derivation,
    DeriveTerm,
    Expression,
    FindTerm,
    Judgement,
    OneStepBetaReduce,
    Redexes,
    Statement,
    Substitute,
    TypeVar,
    Var,
)
import untyped


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


  print('\nExamples of topics in 2.11')
  print('Rename')
  x = Var('x', alpha)
  y = Var('y', Arrow(alpha, beta))
  z = Var('z', alpha)
  u = Var('u', Arrow(alpha, Arrow(alpha, beta)))
  v = Var('v', alpha)
  w = Var('w', Arrow(alpha, beta))
  a = Expression(Abstract(x, Apply(y, x)))
  print(a)
  b = Expression(Abstract(z, Apply(y, z)))
  print(b)
  print('α-Equivalence')
  print(f'{a} =α {b}:', a == b)
  print('Substitution')
  ux = Expression(Apply(u, x))
  print(f'{a}[{y} := {ux}]:', Substitute(a, y, ux, [v]))
  print('β-Reduction')
  c = Expression(Apply(a, v))
  print(f'Redex({c}):', Redexes(c))
  print(c, '->', OneStepBetaReduce(c))
  d = Expression(Abstract(w, Apply(Abstract(y, c), w)))
  print(d, '->>', BetaReduce(d))
  print('β-Equivalence')
  e = Expression(Abstract(y, Apply(Abstract(w, c), y)))
  print(f'{d}\n    β= {e}:', d >> e)


if __name__ == '__main__':
  RunExamples()
