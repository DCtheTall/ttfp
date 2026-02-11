"""
Chapter 4 Examples
==================

"""

from predicate_lambda_calculus import *


def RunExamples():
  print('Examples from 5.1')
  nat = TypeVar('nat', Star())
  n = Var('n', nat)
  S = TypeExpression(TypeVar('S', PiKind(n, Star())))
  print('Indexed sets:', S)
  print(TypeExpression(TAbstract(n, TApply(S, n))))
  V = TypeExpression(TypeVar('V', PiKind(n, Star())))
  print('Vectors of length n:', V)
  Vt = TypeExpression(TAbstract(n, TApply(V, n)))
  print(Vt)
  P = TypeExpression(TypeVar('P', PiKind(n, Star())))
  print('Proposition for each number n:', P)
  Pt = TypeExpression(TAbstract(n, TApply(P, n)))
  print(Pt)
  three = Var('3', nat)
  print(TypeExpression(TApply(Vt, three)))
  print(TypeExpression(TApply(Pt, three)))


  print('\nExamples from 5.2')
  print('Sort rule:')
  sr = SortRule(Context())
  print(sr)
  print('Var rule for type:')
  alpha = TypeVar('α', Star())
  vt = VarRule(alpha, sr.Conclusion())
  vtc = vt.Conclusion()
  print(vt)
  print('Var rule for term:')
  x = Var('x', alpha)
  vr = VarRule(x, vtc)
  vrc = vr.Conclusion()
  print(vr)
  print('Weak rule for type:')
  beta = TypeVar('β', Star())
  print(WeakRule(beta, vtc, SortRule(vtc.ctx).Conclusion()))
  print('Weak rule for term:')
  print(WeakRule(x, vtc, vtc))
  print('Form rule for kind:')
  print(FormRule(x, vtc, SortRule(vtc.ctx).Conclusion()))
  print('Form rule for type:')
  print(FormRule(x, vtc, vtc))
  print('Appl rule for type:')
  F = TypeVar('F', KindExpression(PiKind(x, Star())))
  src = SortRule(Context()).Conclusion()
  vtc = VarRule(alpha, src).Conclusion()
  wtc = WeakRule(x, vtc, vtc).Conclusion()
  vrc = VarRule(x, vtc).Conclusion()
  ftc = FormRule(x, wtc, SortRule(wtc.ctx).Conclusion()).Conclusion()
  vfc = VarRule(F, ftc).Conclusion()
  print(ApplRule(vfc, vrc))
  print('Appl rule for term:')
  f = Var('f', TypeExpression(PiType(x, alpha)))
  src = SortRule(Context()).Conclusion()
  vtc = VarRule(alpha, src).Conclusion()
  wtc = WeakRule(x, vtc, vtc).Conclusion()
  vrc = VarRule(x, vtc).Conclusion()
  ftc = FormRule(x, wtc, wtc).Conclusion()
  vfc = VarRule(f, ftc).Conclusion()
  print(ApplRule(vfc, vrc))
  # TODO
  print('Abst rule:')
  # TODO
  print('Conv rule:')
  # TODO


if __name__ == '__main__':
  RunExamples()
