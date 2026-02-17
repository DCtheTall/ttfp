"""
Chapter 4 Examples
==================

"""

from dependent_types_lambda_calculus import (
    Context,
    ConvRule,
    Derivation,
    Expression,
    FormRule,
    Judgement,
    KArrow,
    SortRule,
    Star,
    Statement,
    TAbstract,
    TApply,
    TArrow,
    TypeExpression,
    TypeVar,
    Var,
    VarRule,
)


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
  print(SortRule())


  print('\nExample of 4.2.2')
  print('Var rule for type:')
  alpha = TypeVar('α', Star())
  ctx = Context()
  premiss = SortRule().Conclusion()
  print(VarRule(premiss, alpha))
  print('Var rule for term:')
  ctx = Context()
  x = Var('x', alpha)
  premiss1 = SortRule().Conclusion()
  premiss2 = VarRule(premiss1, alpha).Conclusion()
  print(VarRule(premiss2, x))


  print('\nExample 4.2.3')
  ctx = Context()
  deriv = Derivation()
  i = deriv.VarRule(deriv.SortRulePremiss(), alpha)
  ii = deriv.VarRule(i, x)
  print(deriv.LinearFormat())


  print('\nExamples from 4.3.2')
  print('First derivation (?1):')
  deriv = Derivation()
  i = deriv.VarRule(deriv.SortRulePremiss(), alpha)
  ii = deriv.WeakRule(x, i, i)
  print(deriv.LinearFormat())
  print('Second derivation (?2):')
  deriv = Derivation()
  i = deriv.VarRule(deriv.SortRulePremiss(), alpha)
  beta = TypeVar('β', Star())
  ii = deriv.WeakRule(alpha, deriv.SortRulePremiss(), deriv.SortRulePremiss())
  iii = deriv.WeakRule(beta, i, ii)
  print(deriv.LinearFormat())
  print('Third derivation (?3):')
  deriv = Derivation()
  i = deriv.WeakRule(
      alpha, deriv.SortRulePremiss(), deriv.SortRulePremiss()
  )
  ii = deriv.VarRule(i, beta)
  print(deriv.LinearFormat())
  print('Fourth derivation (?4):')
  deriv = Derivation()
  i = deriv.WeakRule(
      alpha, deriv.SortRulePremiss(), deriv.SortRulePremiss()
  )
  print(deriv.LinearFormat())


  print('\nExample from 4.4.1')
  ctx = Context(alpha, beta)
  p_a = Judgement(ctx, Statement(TypeExpression(alpha)))
  p_b = Judgement(ctx, Statement(TypeExpression(beta)))
  print(FormRule(p_a, p_b))
  print('---')
  ctx = Context(alpha)
  p_a = Judgement(ctx, Statement(Star()))
  p_b = Judgement(ctx, Statement(Star()))
  print(FormRule(p_a, p_b))


  print('\nExamples from 4.5')
  deriv = Derivation()
  i = deriv.VarRule(deriv.SortRulePremiss(), beta)
  ii = deriv.VarRule(deriv.SortRulePremiss(), alpha)
  iii = deriv.FormRule(deriv.SortRulePremiss(), deriv.SortRulePremiss())
  iv = deriv.FormRule(ii, ii)
  v = deriv.WeakRule(alpha, iii, deriv.SortRulePremiss())
  vi = deriv.AbstRule(alpha, iv, v)
  vii = deriv.WeakRule(beta, vi, deriv.SortRulePremiss())
  viii = deriv.ApplRule(vii, i)
  print(deriv.FlagFormat())


  print('\nExample from 4.6')
  deriv = Derivation()
  i = deriv.VarRule(deriv.SortRulePremiss(), beta)
  ii = deriv.VarRule(deriv.SortRulePremiss(), alpha)
  iii = deriv.FormRule(deriv.SortRulePremiss(), deriv.SortRulePremiss())
  iv = deriv.FormRule(ii, ii)
  v = deriv.WeakRule(alpha, iii, deriv.SortRulePremiss())
  vi = deriv.AbstRule(alpha, iv, v)
  vii = deriv.WeakRule(beta, vi, deriv.SortRulePremiss())
  viii = deriv.ApplRule(vii, i)
  print(deriv.FlagFormat(shorten=True))

  print('\nExample from 4.7')
  x = Var('x', TApply(TAbstract(alpha, TArrow(alpha, alpha)), beta))
  ctx = Context(beta, x)
  p_a = Judgement(ctx, Statement(Expression(x)))
  p_b = Judgement(ctx, Statement(TypeExpression(TArrow(beta, beta))))
  print(ConvRule(p_a, p_b))


if __name__ == '__main__':
  RunExamples()
