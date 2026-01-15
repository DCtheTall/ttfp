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
    match other:
      case Occurrence():
        return self.var == other.var
      case Var():
        return self.var == other
      case _:
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
    match u:
      case Expression():
        self.term = u.Copy().term
      case Var():
        self.term = FreeVar(u)
      case FreeVar() | BoundVar():
        self.term = u
      case Apply():
        self.term = Apply(Expression(u.fn), Expression(u.arg))
      case Abstract():
        v = u.arg
        if not isinstance(v, BindingVar):
          v = BindingVar(v)
        body = Expression(u.body)
        body.MaybeBindFreeVarsTo(v)
        self.term = Abstract(v, body)
      case _:
        raise NotImplementedError(f'Unexpected input to Expression {type(u)}')

  def __str__(self):
    return str(self.term)

  def __eq__(self, other):
    return AlphaEquiv(self, other)

  def __rshift__(self, other):
    return BetaEquiv(self, other)

  def MaybeBindFreeVarsTo(self, v: BindingVar):
    match self.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case FreeVar():
        if v.ShouldBind(self.term):
          self.term = BoundVar(v, self.term)
      case BoundVar():
        pass
      case Apply():
        self.term.fn.MaybeBindFreeVarsTo(v)
        self.term.arg.MaybeBindFreeVarsTo(v)
      case Abstract():
        self.term.body.MaybeBindFreeVarsTo(v)
      case _:
        raise NotImplementedError(
            f'Unexpected member of Expression {self.term}'
        )

  def Closed(self) -> bool:
    return len(FreeVars(self)) == 0

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0

  def Copy(self):
    match self.term:
      case FreeVar() | BoundVar():
        return Expression(self.term.var)
      case Apply():
        return Expression(Apply(self.term.fn.Copy(), self.term.arg.Copy()))
      case Abstract():
        bv = self.term.arg
        return Expression(Abstract(bv.var, self.term.body.Copy()))
      case _:
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
    match x:
      case Expression():
        self.terms = Subterms(x.term).terms
      case Occurrence():
        self.terms = [x]
      case Apply():
        self.terms = [x] + Subterms(x.fn).terms + Subterms(x.arg).terms
      case Abstract():
        self.terms = [x] + Subterms(x.body).terms
      case _:
        raise NotImplementedError(f'Unexpected Subterms argument {x}')


class FreeVars(Multiset):
  def __init__(self, e: Expression):
    match e.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case FreeVar():
        self.terms = [e.term.var]
      case BoundVar():
        self.terms = []
      case Apply():
        self.terms = FreeVars(e.term.fn).terms + FreeVars(e.term.arg).terms
      case Abstract():
        self.terms = FreeVars(e.term.body).terms
      case _:
        raise NotImplementedError(f'Unexpected member of Expression {e.term}')

  def ContainsBindingVar(self, bv: BindingVar):
    return self.Contains(bv.var)


class RenameFreeVarError(Exception):
  pass


class RenameBindingVarError(Exception):
  pass


def Rename(M: Expression, x: Var, y: Var) -> Expression:
  def _HasBindingVar(M: Expression, y: Var) -> bool:
    match M.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case FreeVar() | BoundVar():
        return False
      case Apply():
        return _HasBindingVar(M.term.fn, y) or _HasBindingVar(M.term.arg, y)
      case Abstract():
        bv = M.term.arg
        if bv.var == y:
          return True
        return _HasBindingVar(M.term.body, y)
      case _:
        raise NotImplementedError(f'Unexpected input to HasBindingVar {M}')

  def _RenameBoundVars(
      M: Expression, x: BindingVar, y: BindingVar
  ) -> Expression:
    assert isinstance(x, BindingVar) and isinstance(y, BindingVar)
    match M.term:
      case FreeVar():
        return M
      case BoundVar():
        if M.term.bv == x:
          return Expression(BoundVar(y, FreeVar(y.var)))
        return M
      case Apply():
        return Expression(
            Apply(
                _RenameBoundVars(M.term.fn, x, y),
                _RenameBoundVars(M.term.arg, x, y)
            )
        )
      case Abstract():
        return Expression(
            Abstract(M.term.arg, _RenameBoundVars(M.term.body, x, y))
        )
      case _:
        raise NotImplementedError(f'Unexpected input to RenameBoundVars {M}')

  match M.term:
    case FreeVar():
      if M.term.var == x:
        return Expression(y)
      return Expression(M.term.var)
    case BoundVar():
      return M
    case Apply():
      return Expression(Apply(Rename(M.term.fn, x, y), Rename(M.term.arg, x, y)))
    case Abstract():
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
    case _:
      raise NotImplementedError(f'Unexpected input to Rename {M}')


def AlphaEquiv(x: Expression, y: Expression) -> bool:
  def _Helper(x: Expression, y: Expression, de_brujin: dict[Var, int]):
    match x.term:
      case FreeVar():
        return isinstance(y.term, FreeVar) and x.term == y.term
      case BoundVar():
        if not isinstance(y.term, BoundVar):
          return False
        xu = x.term.var
        yu = y.term.var
        if xu in de_brujin and yu in de_brujin:
          return de_brujin[xu] == de_brujin[yu]
        if xu not in de_brujin and yu not in de_brujin:
          return xu == yu
        return False
      case Apply():
        return (
            isinstance(y.term, Apply)
            and _Helper(x.term.fn, y.term.fn, de_brujin)
            and _Helper(x.term.arg, y.term.arg, de_brujin)
        )
      case Abstract():
        if not isinstance(y.term, Abstract):
          return False
        xu = x.term.arg
        yu = y.term.arg
        new_de_brujin = de_brujin.copy()
        new_de_brujin[xu.var] = new_de_brujin[yu.var] = len(de_brujin)
        return _Helper(x.term.body, y.term.body, new_de_brujin)
      case _:
        raise NotImplementedError(f'Unexpected input to AlphaEquiv {x}')
  return _Helper(x, y, de_brujin={})


def Substitute(
    M: Expression, x: Union[BindingVar, Var], N: Expression, zs: list[Var],
    binding: Optional[BindingVar] = None,
) -> Expression:
  match M.term:
    case FreeVar():
      if M.term == x:
        return N
      return M
    case BoundVar():
      if binding is not None and M.term.BoundTo(binding):
        return N
      return M
    case Apply():
      return Expression(
          Apply(
              Substitute(M.term.fn, x, N, zs, binding),
              Substitute(M.term.arg, x, N, zs, binding)
          )
      )
    case Abstract():
      if FreeVars(N).ContainsBindingVar(M.term.arg):
        if not zs:
          raise Exception('Need more variables for substitution')
        z = zs.pop()
        assert not FreeVars(N).Contains(z)
        M = Rename(M, M.term.arg, z)
      return Expression(
          Abstract(M.term.arg, Substitute(M.term.body, x, N, zs, binding))
      )
    case _:
      raise NotImplementedError(f'Unexpected term in input for Substitute {M}')


def SimulSubstitute(
    M: Expression, subs: dict[Var, Expression], zs: list[Var]
) -> Expression:
  match M.term:
    case FreeVar():
      if M.term.var in subs:
        return subs[M.term.var]
      return M
    case BoundVar():
      return M
    case Apply():
      return Expression(
          Apply(
              SimulSubstitute(M.term.fn, subs, zs),
              SimulSubstitute(M.term.arg, subs, zs)
          )
      )
    case Abstract():
      for N in subs.values():
        if FreeVars(N).ContainsBindingVar(M.term.arg):
          if not zs:
            raise Exception('Need more variables for substitution')
          z = zs.pop()
          assert not FreeVars(N).Contains(z)
          M = Rename(M, M.term.arg, z)
      return Expression(Abstract(M.term.arg, SimulSubstitute(M.term.body, subs, zs)))
    case _:
      raise NotImplementedError(
          f'Unexpected term in input for SimulSubstitute {M}'
      )


class Redexes(Multiset):
  def __init__(self, M: Expression):
    match M.term:
      case Occurrence():
        self.terms = []
      case Apply():
        self.terms = []
        if isinstance(M.term.FuncTerm(), Abstract):
          self.terms.append(M.term)
        self.terms.extend(Redexes(M.term.fn).terms)
        self.terms.extend(Redexes(M.term.arg).terms)
      case Abstract():
        self.terms = Redexes(M.term.body).terms
      case _:
        raise NotImplementedError(f'Unexpected input to Redexes {M}')


def OneStepBetaReduce(M: Expression, zs: list[Var] = [], applicative=False):
  match M.term:
    case Occurrence():
      return M
    case Apply():
      # Applicative order: evaluate innermost-leftmost redex first.
      if applicative:
        if not M.term.fn.BetaNormal():
          return Expression(
              Apply(OneStepBetaReduce(M.term.fn, zs, applicative), M.term.arg)
          )
        if not M.term.arg.BetaNormal():
          return Expression(
              Apply(M.term.fn, OneStepBetaReduce(M.term.arg, zs, applicative))
          )
        if isinstance(M.term.FuncTerm(), Abstract):
          M, N = M.term.fn, M.term.arg
          return Substitute(M.term.body, M.term.arg.var, N, zs, M.term.arg)
        return M
      # Normal order: evaluate outermost-leftmost redex first.
      if isinstance(M.term.FuncTerm(), Abstract):
        M, N = M.term.fn, M.term.arg
        return Substitute(M.term.body, M.term.arg.var, N, zs, M.term.arg)
      if M.term.fn.BetaNormal():
        return Expression(
            Apply(M.term.fn, OneStepBetaReduce(M.term.arg, zs, applicative))
        )
      return Expression(
          Apply(OneStepBetaReduce(M.term.fn, zs, applicative), M.term.arg)
      )
    case Abstract():
      return Expression(
          Abstract(M.term.arg, OneStepBetaReduce(M.term.body, zs, applicative))
      )
    case _:
      raise NotImplementedError(f'Unexpected input to OneStepBetaReduce {M}')
  

def BetaReduce(M: Expression):
  # Keep beta-reducing. Will infinite loop for non-halting terms.
  while not M.BetaNormal():
    M = OneStepBetaReduce(M)
  return M


def BetaEquiv(M: Expression, N: Expression):
  return BetaReduce(M) == BetaReduce(N)
