"""
Chapter 4 Examples
==================

"""

from dependent_types_lambda_calculus import *


def RunExamples():
  print('Examples from 4.1.1')
  alpha = TypeVar('α', KArrow(Star(), Star()))
  gamma = TypeVar('γ', Star())
  print(alpha)
  print(gamma)
  ag = TypeExpression(TApply(alpha, gamma))
  print(ag)
  aag = TypeExpression(TAbstract(alpha, ag))
  print(aag)
  beta = TypeVar('β', Star())
  aagbb = TypeExpression(TApply(aag, TAbstract(beta, beta)))
  print(aagbb)
  aa = TypeExpression(TAbstract(alpha, alpha))
  print(aa)


  print('\nExample of 4.2.1')
  print('Sort rule:')
  print(SortRule(Context()))


  print('\nExample of 4.2.2')
  print('Var rule for type:')
  alpha = TypeVar('α', Star())
  ctx = Context(Star(), alpha)
  premiss = SortRule(ctx).Conclusion()
  print(VarRule(ctx, premiss, alpha))
  print('Var rule for term:')
  x = Var('x', alpha)
  ctx = ctx.PushVar(x)
  premiss1 = SortRule(ctx).Conclusion()
  premiss2 = VarRule(ctx, premiss1, alpha).Conclusion()
  print(VarRule(ctx, premiss2, x))


if __name__ == '__main__':
  RunExamples()
