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
  ctx = Context()
  premiss = SortRule(ctx).Conclusion()
  print(VarRule(premiss, alpha))
  print('Var rule for term:')
  ctx = Context()
  x = Var('x', alpha)
  premiss1 = SortRule(ctx).Conclusion()
  premiss2 = VarRule(premiss1, alpha).Conclusion()
  print(VarRule(premiss2, x))


  print('\nExample 4.2.3')
  deriv = Derivation(Context())
  i = deriv.VarRule(alpha)
  ii = deriv.VarRule(x)
  print(deriv.LinearFormat())
  # TODO flag format


  print('\nExamples from 4.3.2')
  print('First derivation (?1):')
  deriv = Derivation(Context())
  i = deriv.VarRule(alpha)
  ii = deriv.WeakRule(x, i, i)
  print(deriv.LinearFormat())
  print('Second derivation (?2):')
  deriv = Derivation(Context())
  i = deriv.VarRule(alpha)
  beta = TypeVar('β', Star())
  ii = deriv.WeakRule(beta, i, i)
  print(deriv.LinearFormat())
  print('Third derivation (?3):')
  deriv = Derivation(Context())
  i = deriv.WeakRule(
      alpha, deriv.SortRulePremiss(), deriv.SortRulePremiss()
  )
  ii = deriv.VarRule(beta)
  print(deriv.LinearFormat())
  print('Fourth derivation (?4):')
  deriv = Derivation(Context())
  i = deriv.WeakRule(
      alpha, deriv.SortRulePremiss(), deriv.SortRulePremiss()
  )
  print(deriv.LinearFormat())


  print('\nExample from 4.4.1')
  deriv = Derivation(Context())
  i = deriv.VarRule(alpha)
  ii = deriv.VarRule(beta)
  iii = deriv.FormRule(i, ii)
  iv = deriv.FormRule(deriv.SortRulePremiss(), deriv.SortRulePremiss())
  print(deriv.LinearFormat())


  print('\nExamples from 4.5')
  deriv = Derivation(Context())
  i = deriv.VarRule(alpha)
  ii = deriv.VarRule(beta)
  iii = deriv.FormRule(deriv.SortRulePremiss(), deriv.SortRulePremiss())
  iv = deriv.AbstRule(alpha, i, iii)
  v = deriv.ApplRule(iv, ii)
  print(deriv.LinearFormat())


if __name__ == '__main__':
  RunExamples()
