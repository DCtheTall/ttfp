"""
Chapter 6 Examples
===================

"""

from calculus_of_constructions import *


def RunExamples():
  print(AllKinds())
  print(Star())
  A = TypeVar('A', Star())
  B = TypeVar('B', PiKind(A, Star()))
  C = TypeVar('C', Star())
  print(KindExpression(PiKind(A, PiKind(A, Star()))))
  print(KindExpression(PiKind(B, Star())))

  print(A)
  print(TypeExpression(B))
  print(C)

  a = Var('a', A)
  b = Var('b', B)
  print(a)
  print(b)
  print(KindExpression(PiKind(a, Star())))
  print(KindExpression(PiKind(b, Star())))

  print(TypeExpression(PiType(A, C)))
  print(TypeExpression(PiType(A, B)))
  print(TypeExpression(PiType(B, A)))
  print(TypeExpression(PiType(a, PiType(b, C))))
  ab = Var('ab', PiType(a, B))
  print(TypeExpression(PiType(ab, C)))

  print(TypeExpression(TAbstract(A, PiType(a, A))))
  print(TypeExpression(TAbstract(B, A)))
  print(TypeExpression(TAbstract(a, A)))
  print(TypeExpression(TAbstract(a, B)))

  print(TypeExpression(TApply(B, A)))
  print(TypeExpression(TAbstract(A, TAbstract(B, TApply(B, A)))))

  P = TypeVar('P', PiKind(a, Star()))
  print(P)
  print(TypeExpression(TApply(P, a)))
  print(TypeExpression(TAbstract(a, TAbstract(P, TApply(P, a)))))

  F = Var('F', TypeExpression(PiType(A, PiType(a, A))))
  print(Expression(F))
  print(Expression(Apply(F, A)))
  # TODO substitute type
  # print(Expression(Apply(F, C)))
  f = Var('f', TypeExpression(PiType(a, A)))
  print(Expression(f))
  print(Expression(Apply(f, a)))


if __name__ == '__main__':
  RunExamples()