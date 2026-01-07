"""
Chapter 1: Untyped Lambda Calculus
==================================

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

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0

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

  def ContainsBindingVar(self, bv: BindingVar):
    return self.Contains(bv.var)


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
    if FreeVars(N).ContainsBindingVar(M.term.arg):
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
      if FreeVars(N).ContainsBindingVar(M.term.arg):
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


def OneStepBetaReduce(M: Expression, zs: list[Var] = []):
  if isinstance(M.term, Occurrence):
    return M
  if isinstance(M.term, Apply):
    if isinstance(M.term.FuncTerm(), Abstract):
      M, N = M.term.fn, M.term.arg
      return Substitute(M.term.body, M.term.arg.var, N, zs, M.term.arg)
    if M.term.fn.BetaNormal():
      return Expression(Apply(M.term.fn, OneStepBetaReduce(M.term.arg, zs)))
    return Expression(Apply(OneStepBetaReduce(M.term.fn, zs), M.term.arg))
  if isinstance(M.term, Abstract):
    return Expression(Abstract(M.term.arg, OneStepBetaReduce(M.term.body, zs)))
  raise NotImplementedError(f'Unexpected input to OneStepBetaReduce {M}')
  

def BetaReduce(M: Expression):
  # Keep beta-reducing. Will infinite loop for non-halting terms.
  while not M.BetaNormal():
    M = OneStepBetaReduce(M)
  return M


def BetaEquiv(M: Expression, N: Expression):
  return BetaReduce(M) == BetaReduce(N)
