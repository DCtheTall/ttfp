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

  kx = KindExpression(PiKind(A, Star()))
  ky = KindExpression(PiKind(C, Star()))
  print(f'{kx} α= {ky}:', kx == ky)
  x = Var('x', A)
  y = Var('y', A)
  kx = KindExpression(PiKind(x, Star()))
  ky = KindExpression(PiKind(y, Star()))
  print(f'{kx} α= {ky}:', kx == ky)

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
  print(TypeExpression(TApply(P, a)))
  print(TypeExpression(TAbstract(a, TAbstract(P, TApply(P, a)))))

  tx = TypeExpression(PiType(A, A))
  ty = TypeExpression(PiType(C, C))
  print(f'{tx} α= {ty}:', tx == ty)
  tx = TypeExpression(PiType(x, A))
  ty = TypeExpression(PiType(y, A))
  print(f'{tx} α= {ty}:', tx == ty)
  tx = TypeExpression(TAbstract(A, TApply(B, A)))
  ty = TypeExpression(TAbstract(C, TApply(B, C)))
  print(f'{tx} α= {ty}:', tx == ty)
  Q = TypeVar('Q', PiKind(a, Star()))
  tx = TypeExpression(TAbstract(P, TAbstract(x, TApply(P, x))))
  ty = TypeExpression(TAbstract(Q, TAbstract(y, TApply(Q, y))))
  print(f'{tx} α= {ty}:', tx == ty)


  f = Var('f', PiType(A, PiType(a, A)))
  print(Expression(Abstract(f, Abstract(A, Apply(f, A)))))
  g = Var('g', PiType(a, A))
  print(Expression(Abstract(g, Abstract(a, Apply(g, a)))))


  c = Var('c', C)
  u = Var('u', PiType(C, PiType(c, C)))
  v = Var('v', PiType(c, C))
  mx = Expression(Abstract(f, Abstract(A, Apply(f, A))))
  my = Expression(Abstract(u, Abstract(C, Apply(u, C))))
  print(f'{mx}\n    α= {my}:', mx == my)
  mx = Expression(Abstract(A, Abstract(g, Abstract(a, Apply(g, a)))))
  my = Expression(Abstract(C, Abstract(v, Abstract(c, Apply(v, c)))))
  print(f'{mx}\n    α= {my}:', mx == my)

  # TODO substitute type
  # print(Expression(Apply(f, C)))


if __name__ == '__main__':
  RunExamples()