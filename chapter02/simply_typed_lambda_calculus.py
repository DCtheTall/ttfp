"""
Chapter 1: Simply Lambda Calculus
=================================

"""


class Type:
  def __str__(self):
    raise NotImplementedError('Not implemented')


class TypeVar(Type):
  def __init__(self, name: str):
    self.name = name

  def __str__(self):
    return self.name


class Arrow(Type):
  def __init__(self, arg: TypeVar, ret: TypeVar):
    self.arg = arg
    self.ret = ret
  
  def __str__(self):
    # Right associative, Apply is left associative.
    # TODO Expression support
    ret = self.ret
    ret_str = str(ret)
    if isinstance(ret, Arrow):
      ret_str = ret_str[1:-1]
    return f'({self.arg} -> {ret_str})'


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Not implemented')


class Var(Term):
  def __init__(self, name: str, typ: Type):
    self.name = name
    self.typ = typ

  def __str__(self):
    return f'{self.name}:{self.typ}'


class Apply(Term):
  def __init__(self, fn: Term, arg: Term):
    self.fn = fn
    self.arg = arg
    if not isinstance(fn.typ, Arrow):
      raise TypeError(f'Left term of Apply must be Arrow type {fn.typ}')
    if fn.typ.arg != arg.typ:
      raise TypeError(f'Expected type {fn.typ.arg} got {arg.typ}')
    self.typ = self.fn.typ.ret

  def __str__(self):
    fn = self.fn
    # if isinstance(fn, Expression):
    #   fn = fn.term
    fn_str = str(fn)
    if isinstance(fn, Apply):
      fn_str = '):'.join(fn_str.split('):')[:-1])[1:]
    return f'({fn_str} {self.arg}):{self.typ}'

  def FuncTerm(self) -> Term:
    fn = self.fn
    # if isinstance(fn, Expression):
    #   fn = fn.term
    return fn


alpha = TypeVar('α')
beta = TypeVar('β')
gamma = TypeVar('γ')
sigma = TypeVar('σ')
tau = TypeVar('τ')
print(alpha, beta, Arrow(alpha, beta), Arrow(Arrow(alpha, beta), Arrow(gamma, tau)))
a = Var('a', Arrow(beta, alpha))
b = Var('b', beta)
# b = Var('b', Arrow(gamma, Arrow(alpha, beta)))
# c = Var('c', gamma)
print(a, b, Apply(a, b))
a = Var('a', Arrow(beta, Arrow(gamma, alpha)))
b = Var('b', beta)
c = Var('c', gamma)
print(a, b, c, Apply(Apply(a, b), c))
