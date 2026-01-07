"""
Chapter 1: Untyped Lambda Calculus
==================================

"""


"""
1.3: Lambda Terms
-----------------

"""

from typing import Optional, Union


class Term:
  def __str__(self):
    raise NotImplementedError('Not implemented')


class Var(Term):
  def __init__(self, name: str):
    self.name = name

  def __str__(self):
    return self.name


class Occurrence:
  def __init__(self, u: Var):
    assert isinstance(u, Var)
    self.var = u

  def __str__(self):
    return str(self.var)

  def __eq__(self, other):
    if isinstance(other, Occurrence):
      return self.var == other.var
    if isinstance(other, Var):
      return self.var == other
    raise Exception(f'Unexpected RHS {other}')


class FreeVar(Occurrence):
  pass


class BindingVar(Occurrence):
  def __eq__(self, other):
    return id(self) == id(other)

  def __init__(self, u: Var):
    assert isinstance(u, Var)
    self.var = u

  def ShouldBind(self, fv: FreeVar) -> bool:
    return self.var == fv


class BoundVar(Occurrence):
  def __init__(self, bv: BindingVar, fv: FreeVar):
    assert isinstance(bv, BindingVar)
    self.bv = bv
    self.var = fv.var

  def BoundTo(self, bv: BindingVar) -> bool:
    return self.bv == bv


class Apply(Term):
  def __init__(self, fn: Term, arg: Term):
    self.fn = fn
    self.arg = arg

  def __str__(self):
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    fn_str = str(fn)
    if isinstance(fn, Apply):
      fn_str = fn_str[1:-1]
    return f'({fn_str} {self.arg})'

  def FuncTerm(self) -> Term:
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    return fn


class Abstract(Term):
  def __init__(self, arg: Union[Var, BindingVar], body: Term):
    self.arg = arg
    self.body = body

  def __str__(self):
    body = self.BodyTerm()
    args = str(self.arg)
    if isinstance(body, Abstract):
      while isinstance(body, Abstract):
        args += str(body.arg)
        body = body.BodyTerm()
    return f'λ{args}.{body}'

  def BodyTerm(self) -> Term:
    if isinstance(self.body, Expression):
      return self.body.term
    return self.body


class Expression(Term):
  def __init__(self, u: Term):
    if isinstance(u, Expression):
      self.term = u.Copy().term
    elif isinstance(u, Var):
      self.term = FreeVar(u)
    elif isinstance(u, FreeVar):
      self.term = u
    elif isinstance(u, BoundVar):
      self.term = u
    elif isinstance(u, Apply):
      self.term = Apply(Expression(u.fn), Expression(u.arg))
    elif isinstance(u, Abstract):
      v = u.arg
      if not isinstance(v, BindingVar):
        v = BindingVar(v)
      M = Expression(u.body)
      M.MaybeBindFreeVarsTo(v)
      self.term = Abstract(v, M)
    else:
      raise NotImplementedError(f'Unexpected input to Expression {type(u)}')

  def __str__(self):
    return str(self.term)

  def __eq__(self, other):
    return AlphaEquiv(self, other)

  def __rshift__(self, other):
    return BetaEquiv(self, other)

  def MaybeBindFreeVarsTo(self, v: BindingVar):
    if isinstance(self.term, Var):
      raise Exception('Should not store Var in Expression')
    elif isinstance(self.term, BindingVar):
      raise Exception('Should not store BindingVar in Expression')
    elif isinstance(self.term, FreeVar):
      if v.ShouldBind(self.term):
        self.term = BoundVar(v, self.term)
    elif isinstance(self.term, BoundVar):
      pass
    elif isinstance(self.term, Apply):
      self.term.fn.MaybeBindFreeVarsTo(v)
      self.term.arg.MaybeBindFreeVarsTo(v)
    elif isinstance(self.term, Abstract):
      self.term.body.MaybeBindFreeVarsTo(v)
    else:
      raise NotImplementedError(f'Unexpected member of Expression {self.term}')

  def Closed(self) -> bool:
    return len(FreeVars(self)) == 0

  def Copy(self):
    if isinstance(self.term, FreeVar) or isinstance(self.term, BoundVar):
      return Expression(self.term.var)
    if isinstance(self.term, Apply):
      return Expression(Apply(self.term.fn.Copy(), self.term.arg.Copy()))
    if isinstance(self.term, Abstract):
      bv = self.term.arg
      return Expression(Abstract(bv.var, self.term.body.Copy()))
    raise NotImplementedError(f'Unexpected member of Expression {self.term}')


class Multiset:
  terms: list[Term]

  def Contains(self, x: Term) -> bool:
    return x in self.terms

  def __str__(self):
    if len(self) == 0:
      return 'Ø'
    terms = ', '.join([str(x) for x in self.terms])
    return f'[{terms}]'

  def __len__(self):
    return len(self.terms)


class Subterms(Multiset):
  def __init__(self, x: Term):
    if isinstance(x, Expression):
      self.terms = Subterms(x.term).terms
    elif isinstance(x, Occurrence):
      self.terms = [x]
    elif isinstance(x, Apply):
      self.terms = [x] + Subterms(x.fn).terms + Subterms(x.arg).terms
    elif isinstance(x, Abstract):
      self.terms = [x] + Subterms(x.body).terms
    else:
      raise NotImplementedError(f'Unexpected Subterms argument {x}')


class FreeVars(Multiset):
  def __init__(self, e: Expression):
    if isinstance(e.term, Var):
      raise Exception('Should not store Var in Expression')
    elif isinstance(e.term, BindingVar):
      raise Exception('Should not store BindingVar in Expression')
    elif isinstance(e.term, FreeVar):
      self.terms = [e.term.var]
    elif isinstance(e.term, BoundVar):
      self.terms = []
    elif isinstance(e.term, Apply):
      self.terms = FreeVars(e.term.fn).terms + FreeVars(e.term.arg).terms
    elif isinstance(e.term, Abstract):
      self.terms = FreeVars(e.term.body).terms
    else:
      raise NotImplementedError(f'Unexpected member of Expression {e.term}')


class RenameFreeVarError(Exception):
  pass


class RenameBindingVarError(Exception):
  pass


def _HasBindingVar(M: Expression, y: Var) -> bool:
  if isinstance(M.term, Var):
    raise Exception('Should not store Var in Expression')
  if isinstance(M.term, BindingVar):
    raise Exception('Should not store BindingVar in Expression')
  if (
      isinstance(M.term, BoundVar)
      or isinstance(M.term, FreeVar)
  ):
    return False
  if isinstance(M.term, Apply):
    return _HasBindingVar(M.term.fn, y) or _HasBindingVar(M.term.arg, y)
  if isinstance(M.term, Abstract):
    bv = M.term.arg
    if bv.var == y:
      return True
    return _HasBindingVar(M.term.body, y)
  raise NotImplementedError(f'Unexpected input to HasBindingVar {M}')


def _RenameBoundVars(
    M: Expression, x: BindingVar, y: BindingVar
) -> Expression:
  assert isinstance(x, BindingVar) and isinstance(y, BindingVar)
  if isinstance(M.term, FreeVar):
    return M
  if isinstance(M.term, BoundVar):
    if M.term.bv == x:
      return BoundVar(y, FreeVar(y.var))
    return M
  if isinstance(M.term, Apply):
    return Expression(
        Apply(
            _RenameBoundVars(M.term.fn, x, y),
            _RenameBoundVars(M.term.arg, x, y)
        )
    )
  if isinstance(M.term, Abstract):
    return Expression(
        Abstract(M.term.arg, _RenameBoundVars(M.term.body, x, y))
    )
  raise NotImplementedError(f'Unexpected input to RenameBoundVars {M}')


def Rename(M: Expression, x: Var, y: Var) -> Expression:
  if isinstance(M.term, FreeVar):
    if M.term.var == x:
      return Expression(y)
    return Expression(M.term.var)
  if isinstance(M.term, BoundVar):
    return M
  if isinstance(M.term, Apply):
    return Expression(Apply(Rename(M.term.fn, x, y), Rename(M.term.arg, x, y)))
  if isinstance(M.term, Abstract):
    if FreeVars(M.term.body).Contains(y):
      raise RenameFreeVarError(f'{y} in FV({M.term})')
    if _HasBindingVar(M.term.body, y):
      raise RenameBindingVarError(f'{y} is a binding variable in {M.term}')
    u = M.term.arg
    N = M.term.body
    if u == x:
      v = BindingVar(y)
      N = _RenameBoundVars(N, u, v)
      N.MaybeBindFreeVarsTo(v)
    else:
      v = u
    return Expression(Abstract(v, Rename(N, x, y)))
  raise NotImplementedError(f'Unexpected input to Rename {M}')


def AlphaEquiv(x: Expression, y: Expression) -> bool:
  def _Helper(x: Expression, y: Expression, de_brujin: dict[Var, int]):
    if isinstance(x.term, FreeVar):
      return isinstance(y.term, FreeVar) and x.term == y.term
    if isinstance(x.term, BoundVar):
      if not isinstance(y.term, BoundVar):
        return False
      xu = x.term.var
      yu = y.term.var
      if xu in de_brujin and yu in de_brujin:
        return de_brujin[xu] == de_brujin[yu]
      if xu not in de_brujin and yu not in de_brujin:
        return xu == yu
      return False
    if isinstance(x.term, Apply):
      ret = (
          isinstance(y.term, Apply)
          and _Helper(x.term.fn, y.term.fn, de_brujin)
          and _Helper(x.term.arg, y.term.arg, de_brujin)
      )
      return ret
    if isinstance(x.term, Abstract):
      if not isinstance(y.term, Abstract):
        return False
      xu = x.term.arg
      yu = y.term.arg
      new_de_brujin = de_brujin.copy()
      new_de_brujin[xu.var] = new_de_brujin[yu.var] = len(de_brujin)
      return _Helper(x.term.body, y.term.body, new_de_brujin)
    raise NotImplementedError(f'Unexpected input to AlphaEquiv {x}')
  return _Helper(x, y, de_brujin={})


def Substitute(
    M: Expression, x: Var, N: Expression, zs: list[Var],
    binding: Optional[BindingVar] = None,
) -> Expression:
  if isinstance(M.term, FreeVar):
    if M.term == x:
      return N
    return M
  if isinstance(M.term, BoundVar):
    if binding is not None and M.term.BoundTo(binding):
      return N
    return M
  if isinstance(M.term, Apply):
    return Expression(
        Apply(
            Substitute(M.term.fn, x, N, zs, binding),
            Substitute(M.term.arg, x, N, zs, binding)
        )
    )
  if isinstance(M.term, Abstract):
    if FreeVars(N).Contains(M.term.arg.var):
      if not zs:
        raise Exception('Need more variables for substitution')
      z = zs.pop()
      assert not FreeVars(N).Contains(z)
      M = Rename(M, M.term.arg, z)
    return Expression(
        Abstract(M.term.arg, Substitute(M.term.body, x, N, zs, binding))
    )
  raise NotImplementedError(f'Unexpected term in input for Substitute {M}')


def SimulSubstitute(
    M: Expression, subs: dict[Var, Expression], zs: list[Var]
) -> Expression:
  if isinstance(M.term, FreeVar):
    if M.term.var in subs:
      return subs[M.term.var]
    return M
  if isinstance(M.term, BoundVar):
    return M
  if isinstance(M.term, Apply):
    return Expression(
        Apply(
            SimulSubstitute(M.term.fn, subs, zs),
            SimulSubstitute(M.term.arg, subs, zs)
        )
    )
  if isinstance(M.term, Abstract):
    for N in subs.values():
      if FreeVars(N).Contains(M.term.arg):
        if not zs:
          raise Exception('Need more variables for substitution')
        z = zs.pop()
        assert not FreeVars(N).Contains(z)
        M = Rename(M, M.term.arg, z)
    return Expression(Abstract(M.term.arg, SimulSubstitute(M.term.body, subs, zs)))
  raise NotImplementedError(
      f'Unexpected term in input for SimulSubstitute {M}'
  )


class Redexes(Multiset):
  def __init__(self, M: Expression):
    if isinstance(M.term, Occurrence):
      self.terms = []
    elif isinstance(M.term, Apply):
      self.terms = []
      if isinstance(M.term.FuncTerm(), Abstract):
        self.terms.append(M.term)
      self.terms.extend(Redexes(M.term.fn).terms)
      self.terms.extend(Redexes(M.term.arg).terms)
    elif isinstance(M.term, Abstract):
      self.terms = Redexes(M.term.body).terms
    else:
      raise NotImplementedError(f'Unexpected input to Redexes {M}')


def BetaNormal(M: Expression) -> bool:
  return len(Redexes(M)) == 0


def OneStepBetaReduce(M: Expression, zs: list[Var] = []):
  if isinstance(M.term, Occurrence):
    return M
  if isinstance(M.term, Apply):
    if isinstance(M.term.FuncTerm(), Abstract):
      M, N = M.term.fn, M.term.arg
      return Substitute(M.term.body, M.term.arg.var, N, zs, M.term.arg)
    if BetaNormal(M.term.fn):
      return Expression(Apply(M.term.fn, OneStepBetaReduce(M.term.arg, zs)))
    return Expression(Apply(OneStepBetaReduce(M.term.fn, zs), M.term.arg))
  if isinstance(M.term, Abstract):
    return Expression(Abstract(M.term.arg, OneStepBetaReduce(M.term.body, zs)))
  raise NotImplementedError(f'Unexpected input to OneStepBetaReduce {M}')
  

def BetaReduce(M: Expression):
  # Keep beta-reducing. Will infinite loop for non-halting terms.
  while not BetaNormal(M):
    M = OneStepBetaReduce(M)
  return M


def BetaEquiv(M: Expression, N: Expression):
  return BetaReduce(M) == BetaReduce(N)


"""
Examples from the book to serve as tests
----------------------------------------

"""


# Declare variables.
x = Var('x')
y = Var('y')
z = Var('z')

u = Var('u')
v = Var('v')
w = Var('w')

p = Var('p')
q = Var('q')
r = Var('r')


def RunExamples():
  print('1.3.7 Examples')
  a = Expression(Apply(x, z))
  b = Expression(Abstract(x, Apply(x, x)))
  c = Expression(Apply(b, b))
  print(f'Sub({a}):', Subterms(a))
  print(f'Sub({b}):', Subterms(b))
  print(f'Sub({c}):', Subterms(c))


  print('\n1.4.2 Examples')
  a = Expression(Abstract(x, Apply(x, y)))
  b = Expression(Apply(x, a))
  print(f'FV({a}):', FreeVars(a))
  print(f'FV({b}):', FreeVars(b))


  print('1.4.3 Examples')
  a = Expression(
      Abstract(
          x,
          Abstract(y, Abstract(z, Apply(Apply(x, x), y)))
      )
  )
  b = Expression(
      Abstract(x, Abstract(y, Apply(Apply(x, x), y)))
  )
  c = Expression(Abstract(x, Apply(Apply(x, x), y)))
  print(f'Closed({a}):', a.Closed())
  print(f'Closed({b}):', b.Closed())
  print(f'Closed({c}):', c.Closed())


  print('\n1.5.3 Examples')
  a = Expression(
      Apply(
          Abstract(x, Apply(x, Abstract(z, Apply(x, y)))),
          z
      )
  )
  b = Expression(
      Apply(
          Abstract(u, Apply(u, Abstract(z, Apply(u, y)))),
          z
      )
  )
  c = Expression(
      Apply(
          Abstract(z, Apply(z, Abstract(x, Apply(z, y)))),
          z
      )
  )
  d = Expression(
      Apply(
          Abstract(y, Apply(y, Abstract(z, Apply(y, y)))),
          z
      )
  )
  e = Expression(
      Apply(
          Abstract(z, Apply(z, Abstract(z, Apply(z, y)))),
          z
      )
  )
  f = Expression(
      Apply(
          Abstract(u, Apply(u, Abstract(z, Apply(u, y)))),
          v
      )
  )
  print(f'{a} =α {a}:', a == a)
  print(f'{a} =α {b}:', a == b)
  print(f'{a} =α {c}:', a == c)
  print('RHS after renames:', c)
  print(f'{a} =α {d}:', a == d)
  print(f'{a} =α {e}:', a == e)
  print(f'{a} =α {f}:', a == f)

  a = Expression(
      Abstract(x, Abstract(y, Apply(Apply(x, z), y)))
  )
  b = Expression(
      Abstract(v, Abstract(y, Apply(Apply(v, z), y)))
  )
  c = Expression(
      Abstract(v, Abstract(u, Apply(Apply(v, z), u)))
  )
  d = Expression(
      Abstract(y, Abstract(y, Apply(Apply(y, z), y)))
  )
  e = Expression(
      Abstract(z, Abstract(y, Apply(Apply(z, z), y)))
  )
  print(f'{a} =α {b}:', a == b)
  print(f'{a} =α {c}:', a == c)
  print(f'{a} =α {d}:', a == d)
  print(f'{a} =α {e}:', a == e)


  print('\n1.6.4 Examples')
  M = Expression(Abstract(y, Apply(y, x)))
  N = Expression(Apply(x, y))
  print(f'{M}[{x} := {N}]:', Substitute(M, x, N, [z]))

  M = Expression(Abstract(x, Apply(y, x)))
  a = Substitute(M, x, N, [z])
  print(f'{M}[{x} := {N}]:', a)
  print(f'{M}[{x} := {N}] == {M}:', a == M)

  M = Expression(Abstract(x, Abstract(y, Apply(Apply(z, z), x))))
  N = Expression(y)
  b = Substitute(M, z, N, [u, v])
  print(f'{M}[{z} := {N}]:', b)
  c = Expression(Abstract(x, Abstract(y, Apply(Apply(y, y), x))))
  print(f'{b} == {c}:', b == c)


  print('\n1.8.2 Examples')
  M = Expression(Apply(Abstract(x, Apply(x, Apply(x, y))), z))
  print(f'{M} ->', OneStepBetaReduce(M))

  M = Expression(Apply(Abstract(x, Apply(Abstract(y, Apply(y, x)), z)), v))
  N = OneStepBetaReduce(M)
  print(f'{M} ->', N, '->', OneStepBetaReduce(N))

  xx = Abstract(x, Apply(x, x))
  M = Expression(Apply(xx, xx))
  print(f'{M} ->', OneStepBetaReduce(M))


  print('\n1.8.6 Lemma Example')
  M = Expression(Apply(Abstract(x, Apply(Abstract(y, Apply(y, x)), z)), v))
  N = Expression(Apply(z, v))
  print(f'{M} =β {N}:', M >> N)
  print(f'{N} =β {M}:', N >> M)


  print('\n1.9.3 Examples')
  M = Expression(Apply(Abstract(x, Apply(Abstract(y, Apply(y, x)), z)), v))
  print(f'{M} ->>', BetaReduce(M))
  print(f'{BetaReduce(M)} in β-nf:', BetaNormal(BetaReduce(M)))
  print(f'Redexes({M}):', Redexes(BetaReduce(M)))

  xx = Abstract(x, Apply(x, x))
  omega = Expression(Apply(xx, xx))
  print(f'{omega} in β-nf:', BetaNormal(omega))
  print(f'Redexes({omega}):', Redexes(omega))
  print(f'{omega} ->', OneStepBetaReduce(omega))

  delta = Abstract(x, Apply(Apply(x, x), x))
  two_deltas = Expression(Apply(delta, delta))
  print(f'{two_deltas} -> {OneStepBetaReduce(two_deltas)}')
  three_deltas = Expression(Apply(Apply(delta, delta), delta))
  print(f'{three_deltas} -> {OneStepBetaReduce(three_deltas)}')


  print('\n1.10.3 Example')
  a = Abstract(y, Abstract(x, Apply(Apply(x, y), x)))
  b = Abstract(y, Apply(y, y))
  M = Expression(Apply(a, b))
  print(f'{M} ->', OneStepBetaReduce(M))


"""
Selected Exercises
------------------

"""


def RunExercises():
  print('\nExercise 1.1a')
  a = Expression(
      Abstract(x, Apply(Apply(Apply(x, z), y), Apply(x, x)))
  )
  print(a)
  print('Exercise 1.1b')
  b = Expression(
      Apply(
          Abstract(x, Abstract(y, Abstract(z, Apply(z, Apply(Apply(x, y), z))))),
          Abstract(u, u)
      )
  )
  print(b)


  print('\nExercise 1.2a')
  comp = Expression(Abstract(x, Apply(x, Abstract(x, x))))
  a = Expression(Abstract(y, Apply(y, Abstract(x, x))))
  print(f'{a} =α {comp}:', a == comp)
  print('Exercise 1.2b')
  b = Expression(Abstract(y, Apply(y, Abstract(x, y))))
  print(f'{b} =α {comp}:', b == comp)
  print('Exercise 1.2c')
  c = Expression(Abstract(y, Apply(y, Abstract(x, y))))
  print(f'{c} =α {comp}:', c == comp)


  print('\nExercise 1.3')
  a = Expression(Abstract(x, Apply(x, Abstract(z, y))))
  b = Expression(Abstract(z, Apply(z, Abstract(z, y))))
  print(f'{a} =α {b}:', a == b)


  print('\nExercise 1.4a')
  U = Expression(
      Apply(
          Abstract(z, Apply(Apply(z, x), z)),
          Apply(Abstract(y, Apply(x, y)), x)
      )
  )
  print(f'Sub({U}):', Subterms(U))
  print('Exercise 1.4c')
  print(f'FV({U}):', FreeVars(U))
  print('Exercise 1.4d')
  a = Expression(
      Apply(
          Abstract(y, Apply(Apply(y, x), y)),
          Apply(Abstract(z, Apply(x, z)), x)
      )
  )
  print(f'{U} =α {a}:', U == a)
  b = Expression(
      Apply(
          Abstract(x, Apply(Apply(x, y), x)),
          Apply(Abstract(z, Apply(y, z)), y)
      )
  )
  print(f'{U} =α {b}:', U == b)
  c = Expression(
      Apply(
          Abstract(y, Apply(Apply(y, x), y)),
          Apply(Abstract(y, Apply(x, y)), x)
      )
  )
  print(f'{U} =α {c}:', U == c)
  d = Expression(
      Apply(
          Abstract(v, Apply(Apply(v, x), v)),
          Apply(Abstract(u, Apply(u, v)), x)
      )
  )
  print(f'{U} =α {d}:', U == d)


  print('\nExercise 1.5a')
  M = Expression(Abstract(x, Apply(y, Abstract(y, Apply(x, y)))))
  N = Expression(Abstract(z, Apply(z, x)))
  print(f'{M}[{y} := {N}]:', Substitute(M, y, N, [u]))
  print('Exercise 1.5b')
  a = Expression(Apply(Apply(x, y), z))
  b = Expression(y)
  c = Expression(z)
  print(
      f'({a}[{x} := {b}])[{y} := {c}]:',
      Substitute(Substitute(a, x, b, []), y, c, [])
  )
  print('Exercise 1.5c')
  a = Expression(Abstract(x, Apply(Apply(x, y), z)))
  b = Expression(y)
  c = Expression(z)
  print(
      f'({a}[{x} := {b}])[{y} := {c}]:',
      Substitute(Substitute(a, x, b, []), y, c, [])
  )
  print('Exercise 1.5d')
  M = Expression(Abstract(y, Apply(Apply(y, y), x)))
  N = Expression(Apply(y, z))
  print(f'{M}[{x} := {N}]:', Substitute(M, x, N, [u]))


  print('\nExercise 1.6')
  a = Expression(Apply(x, Abstract(z, y)))
  b = Expression(y)
  c = Expression(z)
  print(
      f'{a}[{x} := {b}][{y} := {c}]:',
      Substitute(Substitute(a, x, b, []), y, c, [u])
  )
  print(
      f'{a}[{y} := {c}][{x} := {b}]:',
      Substitute(Substitute(a, y, c, [u]), x, b, [])
  )
  print(
      f'{a}[{x} := {b}, {y} := {c}]:',
      SimulSubstitute(a, {x: b, y: c}, [u])
  )


  print('\nExercise 1.7a')
  print(f'Redexes({U}):', Redexes(U))
  print('Exercise 1.7b')
  print(U, '->>', BetaReduce(U))


  print('\nExercise 1.8')
  M = Expression(Apply(Abstract(x, Apply(x, x)), y))
  N = Expression(Apply(Apply(Abstract(x, Abstract(y, Apply(y, x))), x), x))
  print(M, '->>', BetaReduce(M))
  print(N, '->>', BetaReduce(N))
  print(f'{M} =β {N}:', M >> N)


  print('\nExercise 1.9')
  K = Expression(Abstract(x, Abstract(y, x)))
  S = Expression(
      Abstract(x, Abstract(y, Abstract(z, Apply(Apply(x, z), Apply(y, z)))))
  )
  print(f'K: {K}')
  print(f'S: {S}')

  print('Exercise 1.9a')
  M = Expression(Apply(Apply(K, p), q))
  print(M, '->>', BetaReduce(M))
  M = Expression(Apply(Apply(Apply(S, p), q), r))
  print(M, '->>', BetaReduce(M))

  print('Exercise 1.9b')
  identity = Expression(Abstract(x, x))
  M = Expression(Apply(Apply(S, K), K))
  print(f'{M} =β {identity}:', M >> identity)

  print('Exercise 1.9c')
  B = Expression(Apply(Apply(S, Apply(K, S)), K))
  print('(S (K S) K):', B)
  M = Expression(Apply(Apply(Apply(B, u), v), w))
  N = Expression(Apply(u, Apply(v, w)))
  print(f'{M} =β {N}:', M >> N)

  print('Exercise 1.9d')
  M = Expression(Apply(Apply(Apply(Apply(S, S), S), K), K))
  print('(S S S K K):', M)
  N = Expression(Apply(Apply(Apply(S, K), K), K))
  print('(S K K K):', N)
  print('(S S S K K) =β (S K K K):', M >> N)

  print('\nExercise 1.10')
  zero = Expression(Abstract(y, Abstract(x, x)))
  print('zero:', zero)
  one = Expression(Abstract(y, Abstract(x, Apply(y, x))))
  print('one:', one)
  two = Expression(Abstract(y, Abstract(x, Apply(y, Apply(y, x)))))
  print('two:', two)
  add = Expression(
      Abstract(
          u,
          Abstract(
              v,
              Abstract(
                  y,
                  Abstract(x, Apply(Apply(u, y), Apply(Apply(v, y), x))))
          )
      )
  )
  print('add:', add)
  mult = Expression(
      Abstract(
          u,
          Abstract(
              v,
              Abstract(
                  y,
                  Abstract(x, Apply(Apply(u, Apply(v, y)), x)))
          )
      )
  )
  print('mult:', mult)

  print('Exercise 1.10a')
  print(
      '(add one one) =β two:', Expression(Apply(Apply(add, one), one)) >> two
  )

  print('Exercise 1.10b')
  print(
    '(add one one) =β (mult one zero):',
    Expression(Apply(Apply(add, one), one)) 
    >> Expression(Apply(Apply(mult, one), zero))
  )
  print(
      '(mult one zero) =β zero:',
      Expression(Apply(Apply(mult, one), zero)) >> zero
  )


  print('\nExercise 1.11')
  succ = Expression(Abstract(u, Abstract(y, Abstract(x, Apply(y, Apply(Apply(u, y), x))))))
  print('succ:', succ)

  print('Exercise 1.11a')
  print('(succ zero) =β one:', Expression(Apply(succ, zero)) >> one)

  print('Exercise 1.11b')
  print('(succ one) =β two:', Expression(Apply(succ, one)) >> two)


  print('\nExercise 1.12')
  true = Expression(Abstract(x, Abstract(y, x)))
  print('true:', true)
  print('true =α K:', true == K)
  false = Expression(Abstract(x, Abstract(y, y)))
  print('false:', false)
  print('false =α zero:', false == zero)
  nott = Expression(Abstract(z, Apply(Apply(z, false), true)))
  print('not:', nott)
  print(
      '(not (not true) =β true:',
      Expression(Apply(nott, Apply(nott, true))) >> true
  )
  print(
      '(not (not false)) =β false:',
      Expression(Apply(nott, Apply(nott, false))) >> false
  )


  print('\nExercise 1.13')
  iszero = Expression(Abstract(z, Apply(Apply(z, Abstract(x, false)), true)))
  print('iszero:', iszero)

  print('Exercise 1.13a')
  print('(iszero zero) =β true:', Expression(Apply(iszero, zero)) >> true)

  print('Exercise 1.13b')
  three = BetaReduce(Expression(Apply(succ, two)))
  print('three:', three)
  four = BetaReduce(Expression(Apply(succ, three)))
  print('four:', four)
  print('(iszero one) =β false:', Expression(Apply(iszero, one)) >> false)
  print('(iszero two) =β false:', Expression(Apply(iszero, two)) >> false)
  print('(iszero three) =β false:', Expression(Apply(iszero, three)) >> false)
  print('(iszero four) =β false:', Expression(Apply(iszero, four)) >> false)
  print(
      '(iszero (succ (succ four))) =β false:',
      Expression(Apply(iszero, Apply(succ, Apply(succ, four)))) >> false
  )

  print('\nExercise 1.14')
  if_x_then_u_else_v = Expression(Abstract(x, Apply(Apply(x, u), v)))
  print('if x then u else v:', if_x_then_u_else_v)
  a = BetaReduce(Expression(Apply(if_x_then_u_else_v, true)))
  print('((if x then u else v) true) ->>', a)


  print('\nExercise 1.19')
  U = Expression(Abstract(z, Abstract(x, Apply(x, Apply(Apply(z, z), x)))))
  print('U:', U)
  Z = Expression(Apply(U, U))
  print('Z:', Z)
  a = Expression(Apply(Z, u))
  print('(Z u):', a)
  a = OneStepBetaReduce(a)
  print('  ->', a)
  a = OneStepBetaReduce(a)
  print('  ->', a)
  print('  =α (u (Z u)):', a == Expression(Apply(u, Apply(Z, u))))

  
  print('\nExercise 1.20a')
  F = Expression(Abstract(u, Abstract(x, Abstract(y, Apply(Apply(x, u), y)))))
  print('F:', F)
  Y = Expression(
      Abstract(
          u,
          Apply(
              Abstract(z, Apply(u, Apply(z, z))),
              Abstract(z, Apply(u, Apply(z, z)))
          )
      )
  )
  print('Y:', Y)
  M = Expression(Apply(Y, F))
  print('M = (Y F):', M)
  H = OneStepBetaReduce(M)
  print('  -> H:', H)
  FH = OneStepBetaReduce(H)
  print('  ->', FH)
  print('  =α (F H):', FH == Expression(Apply(F, H)))
  N = Expression(Apply(F, M))
  print('(F M) = (F (Y F)):', N)
  N = Expression(Apply(F, OneStepBetaReduce(M)))
  print('  ->', N)
  print('  =α (F H):', N == FH)
  N = Expression(Apply(F, M))
  print('(F M):', N)
  N = OneStepBetaReduce(N)
  print('  ->', N)
  print(
      '  =α λxy.(x M y):',
      N == Expression(Abstract(x, Abstract(y, Apply(Apply(x, M), y))))
  )

  print('Exercise 1.20b')
  F = Expression(Abstract(u, Abstract(x, Abstract(y, Abstract(z, Apply(Apply(Apply(x, y), z), u))))))
  print('F:', F)
  print('Y:', Y)
  M = Expression(Apply(Y, F))
  print('M = (Y F):', M)
  H = OneStepBetaReduce(M)
  print('  -> H:', H)
  FH = OneStepBetaReduce(H)
  print('  ->', FH)
  print('  =α (F H):', FH == Expression(Apply(F, H)))
  N = Expression(Apply(F, M))
  print('(F M) = (F (Y F)):', N)
  N = Expression(Apply(F, OneStepBetaReduce(M)))
  print('  ->', N)
  print('  =α (F H):', N == FH)
  N = Expression(Apply(Apply(Apply(Apply(F, M), x), y), z))
  print('(F M x y z):', N)
  N = OneStepBetaReduce(N)
  print('  ->', N)
  N = OneStepBetaReduce(N, [p])
  print('  ->', N)
  N = OneStepBetaReduce(N, [q])
  print('  ->', N)
  N = OneStepBetaReduce(N, [r, v, w])
  print('  ->', N)
  print(
      '  =α (x y z M):',
      N == Expression(Apply(Apply(Apply(x, y), z), M))
  )


if __name__ == '__main__':
  RunExamples()
  RunExercises()
