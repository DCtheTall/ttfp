"""
Chapter 3 Examples
==================

"""


from second_order_typed_lambda_calculus import (
    Abst2Rule,
    AbstRule,
    Abstract,
    AbstractT,
    Appl2Rule,
    ApplRule,
    Apply,
    ApplyT,
    Arrow,
    Context,
    Derivation,
    Expression,
    ExpressionType,
    FormRule,
    Judgement,
    OneStepBetaReduce,
    PiType,
    Statement,
    SubstituteType,
    TypeVar,
    Var,
    VarRule,
)


def RunExamples():
  # Declare type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')
  gamma = TypeVar('γ')
  sigma = TypeVar('σ')
  tau = TypeVar('τ')
  nat = TypeVar('nat')


  print('Examples from 3.2')
  x = Var('x', alpha)
  y = Var('y', beta)
  print('Polymorphic identity:')
  M = Expression(AbstractT(alpha, Abstract(x, x)))
  print(M)
  N = Expression(AbstractT(beta, Abstract(y, y)))
  print(f'{M} =α {N}:', M == N)
  print(f'{M.typ} =α {N.typ}:', M.typ == N.typ)


  print('\nExamples from 3.3')
  x = Var('x', alpha)
  y = Var('y', Arrow(alpha, beta))
  print('Type abstraction')
  M = Expression(Abstract(x, x))
  print('M:', M)
  print(f'λ{alpha}:*.M:', Expression(AbstractT(alpha, M)))
  print('Type application')
  M = Expression(AbstractT(alpha, Abstract(x, x)))
  print('Polymorphic identity:', M)
  N = Expression(ApplyT(M, beta))
  print(f'Applied to {beta}:', N)
  print(
      f'{N.typ} =α {M.Type().body}[{alpha} := {beta}]:',
      N.typ == SubstituteType(
          M.Type().body,
          M.Type().arg.typ,
          ExpressionType(beta),
          [],
          M.Type().arg,
      )
  )
  N = Expression(ApplyT(M, gamma))
  print(f'Applied to {gamma}:', N)
  z = Var('z', gamma)
  print('Applied to term:', Expression(Apply(N, z)))


  print('\nExample 3.4.5')
  ctx = Context()
  print('Empty context:', ctx)
  print(f'Dom({ctx}):', ctx.Dom())
  ctx = ctx.PushTypeVar(alpha)
  print('Add type variable:', ctx)
  x = Var('x', Arrow(alpha, alpha))
  ctx = ctx.PushVar(x)
  print('Add variable:', ctx)
  y = Var('y', Arrow(Arrow(alpha, alpha), beta))
  ctx = ctx.PushTypeVar(beta).PushVar(y)
  print(f'Add {beta} and {y}:', ctx)


  print('\nExamples from 3.4.7')
  print('Var rule:')
  x = Var('x', Arrow(alpha, beta))
  print(VarRule(Context(alpha, beta, x), x).Conclusion())
  print('Appl rule:')
  x = Var('x', Arrow(alpha, beta))
  y = Var('y', alpha)
  ctx = Context(alpha, beta, x, y)
  premiss1 = Judgement(ctx, Statement(Expression(x), Arrow(alpha, beta)))
  premiss2 = Judgement(ctx, Statement(Expression(y), alpha))
  rule = ApplRule(premiss1, premiss2)
  line = f'{premiss1}, {premiss2}'
  print(line)
  print('-' * len(line))
  print(rule.Conclusion())
  print('Abst rule:')
  x = Var('x', alpha)
  ctx = Context(alpha, x)
  premiss = Judgement(ctx, Statement(Expression(x), alpha))
  rule = AbstRule(x, premiss)
  line = str(premiss)
  print(line)
  print('-' * len(line))
  print(rule.Conclusion())
  print('Form rule:')
  ctx = Context(alpha, beta)
  print(FormRule(ctx, Arrow(alpha, beta)).Conclusion())
  ctx = Context(sigma, tau)
  rule = FormRule(ctx, PiType(alpha, Arrow(sigma, tau)))
  print(rule.Conclusion())
  print('Appl2 rule:')
  x = Var('x', alpha)
  M = Expression(AbstractT(alpha, Abstract(x, x)))
  ctx = Context(beta)
  premiss1 = Judgement(ctx, Statement(M, M.Type()))
  premiss2 = Judgement(ctx, Statement(ExpressionType(beta), beta))
  rule = Appl2Rule(premiss1, premiss2)
  line = f'{premiss1}, {premiss2}'
  print(line)
  print('-' * len(line))
  print(rule.Conclusion())
  print('Abst2 rule:')
  M = Expression(Abstract(x, x))
  ctx = Context(alpha)
  premiss = Judgement(ctx, Statement(M, Arrow(alpha, alpha)))
  rule = Abst2Rule(alpha, premiss)
  line = str(premiss)
  print(line)
  print('-' * len(line))
  print(rule.Conclusion())


  print('\nExample from 3.5')
  f = Var('f', Arrow(alpha, alpha))
  x = Var('x', alpha)
  ctx = Context(alpha, f, x)
  deriv = Derivation()
  i = deriv.VarRule(ctx, f)
  ii = deriv.VarRule(i.ctx, x)
  iii = deriv.ApplRule(i, ii)
  iv = deriv.ApplRule(i, iii)
  v = deriv.AbstRule(x, iv)
  vi = deriv.AbstRule(f, v)
  vii = deriv.Abst2Rule(alpha, vi)
  print(deriv.FlagFormat())
  print('Example application:')
  succ = Var('succ', Arrow(nat, nat))
  two = Var('two', nat)
  M = vii.stmt.subj
  print('Start with term:')
  print(M)
  M = Expression(ApplyT(M, nat))
  print('Apply type nat:')
  print(M)
  M = Expression(Apply(M, succ))
  print('Apply term succ:')
  print(M)
  M = Expression(Apply(M, two))
  print('Apply term two:')
  print(M)


  print('\nExample 3.6.3')
  print(M)
  M = OneStepBetaReduce(M, [], [])
  print('    ->', M)
  M = OneStepBetaReduce(M, [], [])
  print('    ->', M)
  M = OneStepBetaReduce(M, [], [])
  print('    ->', M)


if __name__ == '__main__':
  RunExamples()
