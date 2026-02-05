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
  print(vt)
  print('Var rule for term:')
  x = Var('x', alpha)
  vr = VarRule(x, vt.Conclusion())
  print(vr)
  print('Weak rule:')
  # TODO
  print('Form rule:')
  # TODO
  print('Appl rule:')
  # TODO
  print('Abst rule:')
  # TODO
  print('Conv rule:')
  # TODO


if __name__ == '__main__':
  RunExamples()
