"""
Chapter 5: Types Dependent on Terms
===================================

"""

from typing import Union


class Kind:
  def __str__(self):
    raise NotImplementedError('Do not cast Kind subclass to str')


class AllKinds:
  def __str__(self):
    return '□'

  def __eq__(self, other):
    return isinstance(other, AllKinds)


class Star(Kind):
  def __str__(self):
    return '*:' + str(AllKinds())

  def __eq__(self, other):
    if isinstance(other, KindExpression):
      other = other.kind
    return isinstance(other, Star)


class PiKind(Kind):
  def __init__(self, arg: Union[Var, BindingVar], body: Kind):
    self.arg = arg
    self.body = body
    if isinstance(self.arg, BindingVar):
      self.body.MaybeBindFreeVarsTo(self.arg)

  def __eq__(self, other):
    if isinstance(other, KindExpression):
      other = other.kind
    if not isinstance(other, PiType):
      return False
    return (self.arg, self.body) == (other.arg, other.body)

  def __str__(self):
    if (
        isinstance(self.body, KindExpression)
        and not FreeVars(self.body.Copy()).Contains(self.arg.var)
    ):
      body_str = str(self.body)
      if isinstance(self.body.kind, PiKind) and body_str[0] == '(':
        body_str = body_str[1:-1]
      arg_str = str(self.arg.typ)
      arg_kind = str(self.arg.typ.kind)[:-2]
      if arg_str.endswith(arg_kind):
        arg_str = arg_str[:-len(arg_kind)-1]
      return f'({arg_str} -> {str(body_str)[:-2]}):{AllKinds()}'
    body = self.BodyKind()
    args = str(self.arg)
    if isinstance(body, PiKind):
      while isinstance(body, PiKind):
        args = f'{args},{body.arg}'
        body = body.BodyKind()
    body = str(body)
    return f'Π{args}.{body}'

  def BodyKind(self) -> Kind:
    if isinstance(self.body, KindExpression):
      return self.body.kind
    return self.body


class KindExpression(Kind):
  kind: Kind

  def __init__(self, kind: Kind):
    match kind:
      case KindExpression():
        self.kind = kind.Copy().kind
      case Star():
        self.kind = kind
      case PiKind():
        arg = kind.arg
        if not isinstance(arg, BindingVar):
          arg = BindingVar(arg)
        self.kind = PiKind(arg, KindExpression(kind.body))
      case _:
        raise NotImplementedError(f'Unexpected input to KindExpression {kind}')
  
  def __str__(self):
    return str(self.kind)

  def __eq__(self, other):
    if not isinstance(other, KindExpression):
      return self.kind == other
    return KAlphaEquiv(self, other)

  def __rshift__(self, other):
    if not isinstance(other, KindExpression):
      return False
    return BetaEquiv(self, other)

  def Copy(self) -> 'KindExpression':
    match self.kind:
      case Star():
        return KindExpression(Star())
      case PiKind():
        bv = BindingVar(self.kind.arg)
        bv.typ = TypeExpression(self.kind.arg.typ)
        return KindExpression(PiKind(bv, self.kind.body.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of KindExpression {self.kind}'
        )
  
  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    if isinstance(self.kind, PiKind):
      self.kind.arg.typ.MaybeBindFreeVarsTo(bv)
      self.kind.body.MaybeBindFreeVarsTo(bv)

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0


class Type:
  kind: Kind

  def __str__(self):
    raise NotImplementedError('Do not cast Type subclass to str')

  def Kind(self):
    kind = self.kind
    if isinstance(kind, KindExpression):
      kind = kind.kind
    return kind


class TypeVar(Type):
  def __init__(self, name: str, kind: Kind):
    self.name = name
    self.kind = kind

  def __str__(self):
    kind_str = str(self.kind)[:-2]
    return f'{self.name}:{kind_str}'

  def __hash__(self):
    return hash(str(self))

  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      other = other.typ
    if not isinstance(other, TypeVar):
      return False
    return (self.name, self.kind) == (other.name, other.kind)


class PiType(Type):
  def __init__(self, arg: Union[Var, BindingVar], body: Type):
    self.arg = arg
    self.body = body
    self.kind = Star()
    if isinstance(self.arg, BindingVar):
      self.body.MaybeBindFreeVarsTo(self.arg)

  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      other = other.typ
    if not isinstance(other, PiType):
      return False
    return (self.arg, self.body) == (other.arg, other.body)

  def __str__(self):
    if (
        isinstance(self.body, TypeExpression)
        and not FreeVars(self.body.Copy()).Contains(self.arg.var)
    ):
      body_str = str(self.body)
      if isinstance(self.body.Kind(), PiKind) and body_str[0] == '(':
        body_str = body_str[1:-1]
      arg_str = str(self.arg.typ)
      arg_kind = str(self.arg.typ.kind)[:-2]
      if arg_str.endswith(arg_kind):
        arg_str = arg_str[:-len(arg_kind)-1]
      return f'({arg_str} -> {str(body_str)[:-2]}):{str(self.kind)[:-2]}'
    body = self.BodyType()
    args = str(self.arg)
    if isinstance(body, PiType):
      while isinstance(body, PiType):
        args = f'{args},{body.arg}'
        body = body.BodyType()
    body_kind = str(body.kind)[:-2]
    body = str(body)
    if body.endswith(body_kind):
      body = body[:-len(body_kind)-1]
    kind = str(self.kind)[:-2]
    return f'(Π{args}.{body}):{kind}'

  def BodyType(self) -> Type:
    if isinstance(self.body, TypeExpression):
      return self.body.typ
    return self.body


class TAbstract(Type):
  def __init__(self, arg: Union[Var, BindingVar], body: Type):
    self.arg = arg
    self.body = body
    if isinstance(self.arg, BindingVar):
      self.body.MaybeBindFreeVarsTo(self.arg)
    self.kind = PiKind(arg, body.kind)

  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      other = other.typ
    if not isinstance(other, TAbstract):
      return False
    return (self.arg, self.body) == (other.arg, other.body)

  def __str__(self):
    body = self.BodyType()
    args = str(self.arg)
    if isinstance(body, TAbstract):
      while isinstance(body, TAbstract):
        args = f'{args},{body.arg}'
        body = body.BodyType()
    body_kind = str(body.kind)[:-2]
    body = str(body)
    if body.endswith(body_kind):
      body = body[:-len(body_kind)-1]
    kind = str(self.kind)[:-2]
    return f'(λ{args}.{body}):{kind}'

  def BodyType(self) -> Type:
    if isinstance(self.body, TypeExpression):
      return self.body.typ
    return self.body


class TApply(Type):
  def __init__(self, fn: Type, arg: Term):
    if not isinstance(fn.Kind(), PiKind):
      raise TypeError(f'Unexpected input to TApply {fn}')
    self.fn = fn
    self.arg = arg
    if isinstance(self.fn, TypeExpression):
      self.kind = Substitute(
          self.fn.Kind().body, self.fn.Kind().arg, arg, [], self.fn.Kind().arg
      )
    else:
      self.kind = self.fn.Kind().body

  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      return self == other.typ
    if not isinstance(other, TApply):
      return False
    return (self.fn, self.arg) == (other.fn, other.arg)

  def __str__(self):
    fn = self.FnType()
    fn_kind = str(fn.kind)[:-2]
    fn_str = str(fn)[:-(len(fn_kind) + 1)]
    if isinstance(fn, TApply):
      fn_str = fn_str[1:-1]
    arg = str(self.arg)
    arg_kind = str(self.arg.typ.kind)
    if arg.endswith(arg_kind):
      arg = arg[:-(len(arg_kind) + 1)]
    return f'({fn_str} {arg}):{self.kind}'[:-2]

  def FnType(self):
    if isinstance(self.fn, TypeExpression):
      return self.fn.typ
    return self.fn


class TypeExpression(Type):
  typ: type

  def __init__(self, typ: Type):
    match typ:
      case TypeExpression():
        self.typ = typ.Copy().typ 
      case TypeVar():
        self.typ = typ
      case PiType():
        arg = typ.arg
        if not isinstance(arg, BindingVar):
          arg = BindingVar(arg)
        self.typ = PiType(arg, TypeExpression(typ.body))
      case TAbstract():
        arg = typ.arg
        if not isinstance(arg, BindingVar):
          arg = BindingVar(arg)
        self.typ = TAbstract(arg, TypeExpression(typ.body))
      case TApply():
        self.typ = TApply(TypeExpression(typ.fn), Expression(typ.arg))
      case _:
        raise NotImplementedError(f'Unexpected input to TypeExpression {typ}')
    self.kind = KindExpression(typ.kind)
    self.typ.kind = self.kind

  def __eq__(self, other):
    if not isinstance(other, TypeExpression):
      return self.typ == other
    return TAlphaEquiv(self, other)

  def __str__(self):
    return str(self.typ)

  def __rshift__(self, other):
    if not isinstance(other, TypeExpression):
      return False
    return BetaEquiv(self, other)

  def Copy(self) -> 'TypeExpression':
    match self.typ:
      case TypeVar():
        return TypeExpression(TypeVar(self.typ.name, self.typ.kind))
      case PiType():
        bv = BindingVar(self.typ.arg)
        return TypeExpression(PiType(bv, self.typ.body.Copy()))
      case TAbstract():
        bv = BindingVar(self.typ.arg)
        return TypeExpression(TAbstract(bv, self.typ.body.Copy()))
      case TApply():
        return TypeExpression(TApply(self.typ.fn.Copy(), self.typ.arg.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of TypeExpression {self.typ}'
        )

  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    match self.typ:
      case PiType() | TAbstract():
        self.typ.arg.typ.MaybeBindFreeVarsTo(bv)
        self.typ.body.MaybeBindFreeVarsTo(bv)
      case TApply():
        self.typ.fn.MaybeBindFreeVarsTo(bv)
        self.typ.arg.MaybeBindFreeVarsTo(bv)
    self.kind.MaybeBindFreeVarsTo(bv)

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0

  def ReplaceKind(self, new_k: KindExpression) -> 'TypeExpression':
    assert isinstance(new_k, KindExpression)
    if not (self.kind >> new_k):
      raise TypeError(f'New kind {new_k} must be β-equal to {self.kind}')
    T = self.Copy()
    T.kind = new_k
    T.typ.kind = T.kind
    return T


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Not implemented')

  def Type(self):
    typ = self.typ
    if isinstance(typ, TypeExpression):
      typ = typ.typ
    return typ


class Var(Term):
  def __init__(self, name: str, typ: Type):
    self.name = name
    self.typ = typ

  def __str__(self):
    term = f'{self.name}:{self.typ}'
    k_str = str(self.typ.kind)[:-2]
    if term.endswith(k_str):
      term = term[:-len(k_str) - 1]
    return term

  def __hash__(self):
    return hash(str(self))

  def __eq__(self, other):
    if isinstance(other, Occurrence):
      other = other.var
    assert isinstance(other, Var)
    return self.name == other.name and self.typ == other.typ


class Occurrence:
  def __init__(self, u: Var):
    assert isinstance(u, Var)
    self.var = u
    self.typ = TypeExpression(u.typ)

  def __str__(self):
    return str(self.var)

  def __eq__(self, other):
    if isinstance(other, Occurrence):
      return self.var == other.var
    if isinstance(other, Var):
      return self.var == other
    raise Exception(f'Unexpected RHS {other}')


class FreeVar(Occurrence):
  def Copy(self) -> 'FreeVar':
    return FreeVar(Var(self.var.name, self.typ))


class BindingVar(Occurrence):
  def __init__(self, u: Var):
    if isinstance(u, BindingVar):
      self.var = u.var
      self.typ = u.typ
      return
    assert isinstance(u, Var)
    self.var = u
    self.typ = TypeExpression(u.typ)
    self.var.typ = self.typ
    self.typ.MaybeBindFreeVarsTo(self)

  def __eq__(self, other):
    return id(self) == id(other)

  def __hash__(self):
    return id(self)

  def ShouldBind(self, fv: FreeVar) -> bool:
    return self.var == fv.var


class BoundVar(Occurrence):
  def __init__(self, bv: BindingVar, fv: FreeVar):
    self.bv = bv
    self.var = fv.var
    bv_typ = self.bv.typ
    if TypeExpression(bv_typ) != TypeExpression(self.var.typ):
      raise TypeError(
          f'Cannot bind variable with type {bv_typ} '
          f'to variable with type {self.var.typ}'
      )
    self.typ = TypeExpression(fv.typ)
    self.typ.MaybeBindFreeVarsTo(bv)

  def __str__(self):
    return self.var.name

  def BoundTo(self, bv: BindingVar) -> bool:
    return self.bv == bv

  def Copy(self) -> 'Binding':
    return BoundVar(self.bv, FreeVar(Var(self.var.name, self.typ)))


class Apply(Term):
  def __init__(self, fn: Term, arg: Term):
    self.fn = fn
    self.arg = arg
    if not isinstance(fn.Type(), PiType):
      raise TypeError(f'Left term of Apply must be Π-type {fn.typ}')
    if fn.Type().arg.typ != arg.typ:
      raise TypeError(f'Mismatched types {fn} got {arg}')
    if isinstance(fn, Expression):
      self.typ = Substitute(
          fn.Type().body, fn.Type().arg, arg, [], fn.Type().arg
      )
    else:
      self.typ = fn.Type().body

  def __eq__(self, other):
    if isinstance(other, Expression):
      return self == other.term
    if not isinstance(other, Apply):
      return False
    return (self.fn, self.arg) == (other.fn, other.arg)

  def __str__(self):
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    fn_str = str(self.fn)
    if isinstance(fn, Apply):
      fn_str = '):'.join(fn_str.split('):')[:-1])[1:]
    arg = str(self.arg)
    k_arg = str(self.arg.typ.kind)[:-2]
    if arg.endswith(k_arg):
      arg = arg[:-len(k_arg)-1]
    typ = str(self.typ)
    k_typ = str(self.typ.kind)[:-2]
    if typ.endswith(k_typ):
      typ = typ[:-len(k_typ)-1]
    return f'({fn_str} {arg}):{typ}'

  def Fn(self) -> Union[Var, Apply, Abstract]:
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    if isinstance(fn, Occurrence):
      fn = fn.var
    return fn

  def Arg(self) -> Union[Var, Apply, Abstract]:
    arg = self.arg
    if isinstance(arg, Expression):
      arg = arg.term
    if isinstance(arg, Occurrence):
      arg = arg.var
    return arg


class Abstract(Term):
  def __init__(self, arg: Union[Var, BindingVar], body: Term):
    self.arg = arg
    self.body = body
    if isinstance(arg, BindingVar):
      body.MaybeBindFreeVarsTo(arg)
    self.typ = PiType(self.arg, self.body.typ)

  def __eq__(self, other):
    if isinstance(other, Expression):
      return self == other.term
    if not isinstance(other, Abstract):
      return False
    return (self.arg, self.body) == (other.arg, other.body)

  def __str__(self):
    body = self.BodyTerm()
    args = str(self.arg)
    while isinstance(body, Abstract):
      args = body._AppendMultiArgStr(args, body)
      body = body.BodyTerm()
    typ = str(self.typ)
    kind = str(self.typ.kind)[:-2]
    if typ.endswith(kind):
      typ = typ[:-len(kind)-1]
    return f'(λ{args}.{body}):{typ}'

  def BodyTerm(self) -> Term:
    if isinstance(self.body, Expression):
      return self.body.term
    return self.body

  def _AppendMultiArgStr(self, args_str, body) -> str:
    return args_str + f'.λ{body.arg}'


class Expression(Term):
  def __init__(self, term: Term):
    match term:
      case Expression():
        self.term = term.Copy().term
      case Var():
        self.term = FreeVar(term)
      case FreeVar() | BoundVar():
        self.term = term
      case Apply():
        self.term = Apply(Expression(term.fn), Expression(term.arg))
      case Abstract():
        bv = term.arg
        if not isinstance(bv, BindingVar):
          bv = BindingVar(bv)
        self.term = Abstract(bv, Expression(term.body))
      case _:
        raise NotImplementedError(f'Unexpected input to Expression {term}')
    self.typ = TypeExpression(term.typ)
    self.term.typ = self.typ
    if isinstance(self.term, Occurrence):
      self.term.var.typ = self.typ

  def __str__(self):
    return str(self.term)

  def __eq__(self, other):
    if not isinstance(other, Expression):
      return self.term == other
    return AlphaEquiv(self, other)

  def __rshift__(self, other):
    if not isinstance(other, Expression):
      return False
    return BetaEquiv(self, other)

  def Copy(self):
    match self.term:
      case FreeVar() | BoundVar():
        return Expression(self.term.Copy())
      case Apply():
        return Expression(Apply(self.term.fn, self.term.arg))
      case Abstract():
        return Expression(Abstract(self.term.arg, self.term.body))
      case _:
        raise NotImplementedError(
            f'Unexpected member of Expression {self.term}'
        )

  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    match self.term:
      case FreeVar():
        if bv.ShouldBind(self.term):
          self.term = BoundVar(self.term.var, self.term)
      case Apply():
        self.term.fn.MaybeBindFreeVarsTo(bv)
        self.term.arg.MaybeBindFreeVarsTo(bv)
      case Abstract():
        self.term.arg.typ.MaybeBindFreeVarsTo(bv)
        self.term.body.MaybeBindFreeVarsTo(bv)
    self.typ.MaybeBindFreeVarsTo(bv)

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0

  def ReplaceType(self, new_t: TypeExpression) -> 'Expression':
    assert isinstance(new_t, TypeExpression)
    if not (self.typ >> new_t):
      raise TypeError(f'New type {new_t} must be β-equal to {self.typ}')
    M = self.Copy()
    M.typ = new_t
    M.term.typ = M.typ
    if isinstance(M.term, Occurrence):
      M.term.var = Var(M.term.var.name, new_t)
    return M


class Multiset[T]:
  elems: list[T]

  def Contains(self, x: T) -> bool:
    return x in self.elems

  def __init__(self, xs: Sequence[T]):
    self.elems = list(xs)

  def __str__(self):
    if len(self) == 0:
      return 'Ø'
    elems = ', '.join([str(x) for x in self])
    return f'[{elems}]'

  def __iter__(self):
    for el in self.elems:
      yield el

  def __len__(self):
    return len(self.elems)


class FreeVars(Multiset[Var]):
  def __init__(self, M: Union[KindExpression, TypeExpression, Expression]):
    self.elems = []
    match M:
      case KindExpression():
        self._FindKindFreeVars(M)
      case TypeExpression():
        self._FindTypeFreeVars(M)
      case Expression():
        self._FindTermFreeVars(M)
      case _:
        raise NotImplementedError(f'Unexpected input to FreeVars {M}')
  
  def _FindKindFreeVars(self, K: KindExpression):
    assert isinstance(K, KindExpression)
    if isinstance(K.kind, PiKind):
      self.elems += FreeVars(K.kind.arg.typ).elems + FreeVars(K.kind.body).elems

  def _FindTypeFreeVars(self, T: TypeExpression):
    assert isinstance(T, TypeExpression)
    match T.typ:
      case PiType() | TAbstract():
        self.elems += FreeVars(T.typ.arg.typ).elems + FreeVars(T.typ.body).elems
      case TApply():
        self.elems += FreeVars(T.typ.fn).elems + FreeVars(T.typ.arg).elems
    self.elems += FreeVars(T.typ.kind).elems

  def _FindTermFreeVars(self, M: Expression):
    assert isinstance(M, Expression)
    match M.term:
      case FreeVar():
        self.elems += [M.term.var]
      case Apply():
        self.elems += FreeVars(M.term.fn).elems +  FreeVars(M.term.arg).elems
      case Abstract():
        self._FindTypeFreeVars(M.term.arg.typ)
        self.elems += FreeVars(M.term.body).elems
    self.elems += FreeVars(M.typ)


class DeBrujinIndices(dict[Union[Var], int]):
  def __str__(self):
    return str({str(k): str(v) for k, v in self.items()})

  def copy(self):
    return DeBrujinIndices(super().copy())


def KAlphaEquiv(
    x: KindExpression, y: KindExpression,
    de_brujin: Optional[DeBrujinIndices] = None
) -> bool:
  def _Helper(x: KindExpression, y: KindExpression, de_brujin: DeBrujinIndices) -> bool:
    match x.kind:
      case Star():
        return x.kind == y.kind
      case PiKind():
        if not isinstance(y.kind, PiKind):
          return False
        xu = x.kind.arg
        yu = y.kind.arg
        if not TAlphaEquiv(xu.typ, yu.typ, de_brujin):
          return False
        new_de_brujin = de_brujin.copy()
        new_de_brujin[xu.var] = new_de_brujin[yu.var] = len(de_brujin)
        return _Helper(x.kind.body, y.kind.body, new_de_brujin)
  return _Helper(x, y, de_brujin or DeBrujinIndices())


def TAlphaEquiv(
    x: TypeExpression, y: TypeExpression,
    de_brujin: Optional[DeBrujinIndices] = None
) -> bool:
  def _Helper(
      x: TypeExpression, y: TypeExpression, de_brujin: DeBrujinIndices
  ) -> bool:
    match x.typ:
      case TypeVar():
        return x.typ == y.typ
      case PiType() | TAbstract():
        if not isinstance(y.typ, type(x.typ)):
          return False
        xu = x.typ.arg
        yu = y.typ.arg
        if not TAlphaEquiv(xu.typ, yu.typ, de_brujin):
          return False
        new_de_brujin = de_brujin.copy()
        new_de_brujin[xu.var] = new_de_brujin[yu.var] = len(de_brujin)
        return _Helper(x.typ.body, y.typ.body, new_de_brujin)
      case TApply():
        return (
            isinstance(y.typ, TApply)
            and _Helper(x.typ.fn, y.typ.fn, de_brujin)
            and AlphaEquiv(x.typ.arg, y.typ.arg, de_brujin)
        )
      case _:
        raise NotImplementedError(f'Unexpected input to TAlphaEquiv {x}')
  return _Helper(x, y, de_brujin or DeBrujinIndices())


def AlphaEquiv(
    x: Expression, y: Expression,
    de_brujin: Optional[DeBrujinIndices] = None
) -> bool:
  def _Helper(
      x: TypeExpression, y: TypeExpression, de_brujin: DeBrujinIndices
  ) -> bool:
    match x.term:
      case FreeVar():
        return isinstance(y.term, FreeVar) and x.term == y.term
      case BoundVar():
        if not isinstance(y.term, BoundVar):
          return False
        xu = x.term.var
        yu = y.term.var
        if not TAlphaEquiv(xu.typ, yu.typ, de_brujin):
          return False
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
        if not TAlphaEquiv(xu.typ, yu.typ, de_brujin):
          return False
        new_de_brujin = de_brujin.copy()
        new_de_brujin[xu.var] = new_de_brujin[yu.var] = len(de_brujin)
        return _Helper(x.term.body, y.term.body, new_de_brujin)
      case _:
        raise NotImplementedError(f'Unexpected input to AlphaEquiv {x}')
  return _Helper(x, y, de_brujin or DeBrujinIndices())


class RenameBindingVarError(Exception):
  pass


def Rename(
    M: Union[KindExpression, TypeExpression, Expression],
    x: Union[BindingVar, Var],
    y: Var
) -> Union[TypeExpression, Expression]:
  def _HasBindingVar(M: Union[TypeExpression, Expression], x: Var) -> bool:
    match M:
      case KindExpression():
        match M.kind:
          case Star():
            return False
          case PiKind():
            if M.kind.arg.var == x:
              return True
            return _HasBindingVar(M.kind.body, x)
      case TypeExpression():
        match M.typ:
          case TypeVar():
            return False
          case PiType() | TAbstract():
            if M.typ.arg.var == x:
              return True
            return _HasBindingVar(M.typ.body, x)
          case TApply():
            return _HasBindingVar(M.typ.fn, x) or _HasBindingVar(M.typ.arg, x)
      case Expression():
        match M.term:
          case Occurrence():
            return False
          case Abstract():
            if M.term.arg.var == x:
              return True
            return _HasBindingVar(M.term.body, x)
          case Apply():
            return (
                _HasBindingVar(M.term.fn, x) or _HasBindingVar(M.term.arg, x)
            )
      case _:
        raise NotImplementedError(f'Unexpected input to HasBindingVar {M}')
  
  def _RenameBoundVar(
      M: Union[KindExpression, TypeExpression, Expression],
      x: BindingVar,
      y: BindingVar
  ) -> Union[TypeExpression, Expression]:
    match M:
      case KindExpression():
        match M.kind:
          case Star():
            return M
          case PiKind():
            return KindExpression(
                PiKind(M.kind.arg, _RenameBoundVar(M.kind.body, x, y))
            )
      case TypeExpression():
        match M.typ:
          case TypeVar():
            return M
          case PiType():
            return TypeExpression(PiType(M.typ.arg, _RenameBoundVar(M, x, y)))
          case TAbstract():
            return TypeExpression(
                TAbstract(M.typ.arg, _RenameBoundVar(M, x, y))
            )
          case TApply():
            return TypeExpression(
                TApply(
                    _RenameBoundVar(M.typ.fn, x, y),
                    _RenameBoundVar(M.typ.arg, x, y)
                )
            )
      case Expression():
        match M.term:
          case FreeVar():
            return M
          case BoundVar():
            if M.term.bv == x:
              return BoundVar(y, FreeVar(y.var))
            return M
          case Abstract():
            return Expression(
                Abstract(M.term.arg, _RenameBoundVar(M.term.body, x, y))
            )
          case Apply():
            return Expression(
                Apply(
                    _RenameBoundVar(M.term.fn, x, y),
                    _RenameBoundVar(M.term.arg, x, y)
                )
            )
      case _:
        raise NotImplementedError(f'Unexpected input to RenameBoundVar {M}')

  match M:
    case KindExpression():
      match M.kind:
        case Star():
          return M
        case PiKind():
          if FreeVars(M.kind.body).Contains(y):
            raise RenameFreeVarError(f'{y} in FV({M.kind.body})')
          u = M.kind.arg
          N = M.kind.body
          if u == x:
            v = BindingVar(y)
            N = _RenameBoundVar(N, u, v)
            N.MaybeBindFreeVarsTo(v)
          else:
            v = u
          return KindExpression(PiKind(v, Rename(N, x, y)))
    case TypeExpression():
      match M.typ:
        case TypeVar():
          return M
        case PiType() | TAbstract():
          if FreeVars(M.typ.body).Contains(y):
            raise RenameFreeVarError(f'{y} in FV({M.typ.body})')
          u = M.typ.arg
          N = M.typ.body
          if u == x:
            v = BindingVar(y)
            N = _RenameBoundVar(N, u, v)
            N.MaybeBindFreeVarsTo(v)
          else:
            v = u
          return TypeExpression(type(M.typ)(v, Rename(N, x, y)))
        case TApply():
          return TypeExpression(
              TApply(Rename(M.typ.fn, x, y), Rename(M.typ.arg, x, y))
          )
    case Expression():
      match M.term:
        case FreeVar():
          if M.term.var == x:
            return Expression(y)
          return Expression(M.term.var)
        case BoundVar():
          return M
        case Apply():
          return Expression(
              Apply(Rename(M.term.fn, x, y), Rename(M.term.arg, x, y))
          )
        case Abstract():
          if FreeVars(M.term.body).Contains(y):
            raise RenameFreeVarError(f'{y} in FV({M.term})')
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


def Substitute(
    M: Union[KindExpression, TypeExpression, Expression],
    x: Union[BindingVar, Var],
    N: Expression,
    new_vars: list[Var] = [],
    binding:  Optional[BindingVar] = None,
) -> Union[TypeExpression, Expression]:
  match M:
    case KindExpression():
      match M.kind:
        case Star():
          return M
        case PiKind():
          fv = FreeVars(N)
          if fv.Contains(M.kind.arg.var):
            if not new_vars:
              raise Exception(
                  f'Need variable with type {M.kind.arg.typ} for substitution'
              )
            z = new_vars.pop()
            assert not fv.Contains(z)
            M = Rename(M, M.kind.arg, z)
          return KindExpression(
              PiKind(
                  M.kind.arg, Substitute(M.kind.body, x, N, new_vars, binding)
              )
          )
    case TypeExpression():
      M.kind = M.typ.kind = Substitute(M.kind, x, N, new_vars, binding)
      match M.typ:
        case TypeVar():
          return M
        case PiType() | TAbstract():
          fv = FreeVars(N)
          if fv.Contains(M.typ.arg.var):
            if not new_vars:
              raise Exception(
                  f'Need variable with type {M.typ.arg.typ} for substitution'
              )
            z = new_vars.pop()
            assert not fv.Contains(z)
            M = Rename(M, M.typ.arg, z)
          return TypeExpression(
              type(M.typ)(
                  M.typ.arg, Substitute(M.typ.body, x, N, new_vars, binding)
              )
          )
        case TApply():
          return TypeExpression(
              TApply(
                  Substitute(M.typ.fn, x, N, new_vars, binding),
                  Substitute(M.typ.arg, x, N, new_vars, binding)
              )
          )
    case Expression():
      M.typ = M.term.typ = Substitute(M.typ, x, N, new_vars, binding)
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
                  Substitute(M.term.fn, x, N, new_vars, binding),
                  Substitute(M.term.arg, x, N, new_vars, binding)
              )
          )
        case Abstract():
          fv = FreeVars(N)
          if fv.Contains(M.term.arg.var):
            if not new_vars:
              raise Exception(
                  f'Need variable with type {M.term.arg.typ} for substitution'
              )
            z = new_vars.pop()
            assert not fv.Contains(z)
            M = Rename(M, M.term.arg, z)
          return Expression(
              Abstract(
                  M.term.arg, Substitute(M.term.body, x, N, new_vars, binding)
              )
          )
    case _:
      raise NotImplementedError(f'Unexpected input to Substitute {M}')


def OneStepBetaReduce(
    M: Union[KindExpression, TypeExpression, Expression],
    new_vars: list[Var] = [],
):
  match M:
    case KindExpression():
      match M.kind:
        case Star():
          return M
        case PiKind():
          if not M.kind.arg.typ.BetaNormal():
            new_t = OneStepBetaReduce(M.kind.arg.typ, new_vars)
            new_arg = Var(M.kind.arg.var.name, new_t)
            return KindExpression(PiKind(new_arg, M.kind.body))
          return KindExpression(
              M.kind.arg, OneStepBetaReduce(M.kind.body, new_vars)
          )
    case TypeExpression():
      match M.typ:
        case TypeVar():
          new_k = OneStepBetaReduce(M.typ.kind, new_vars)
          return TypeExpression(TypeVar(M.typ.typ.name, new_k))
        case PiType() | TAbstract():
          if not M.typ.arg.typ.BetaNormal():
            new_t = OneStepBetaReduce(M.typ.arg.typ, new_vars)
            new_arg = Var(M.typ.arg.var.name, new_t)
            return TypeExpression(type(M.typ)(new_arg, M.typ.body))
          return TypeExpression(
              type(M.typ)(M.typ.arg, OneStepBetaReduce(M.typ.body, new_vars))
          )
        case TApply():
          if isinstance(M.typ.FnType(), TAbstract):
            M, N = M.typ.fn, M.typ.arg
            return Substitute(M.typ.body, M.typ.arg, N, new_vars, M.typ.arg)
          if not M.typ.fn.BetaNormal():
            return TypeExpression(
                TApply(OneStepBetaReduce(M.typ.fn, new_vars), M.typ.arg)
            )
          return TypeExpression(
              TApply(M.typ.fn, OneStepBetaReduce(M.typ.arg, new_vars))
          )
    case Expression():
      match M.term:
        case FreeVar() | BoundVar():
          new_t = OneStepBetaReduce(M.term.typ, new_vars)
          return Expression(Var(M.term.var.name, new_t))
        case Abstract():
          if not M.term.arg.typ.BetaNormal():
            new_t = OneStepBetaReduce(M.term.arg.typ, new_vars)
            new_arg = Var(M.term.arg.var.name, new_t)
            return Expression(Abstract(new_arg, M.term.body))
          return  Expression(
              Abstract(M.term.arg, OneStepBetaReduce(M.term.body, new_vars))
          )
        case Apply():
          if isinstance(M.term.Fn(), Abstract):
            M, N = M.term.fn, M.term.arg
            return Substitute(M.term.body, M.term.arg, N, new_vars, M.term.arg)
          if not M.term.fn.BetaNormal():
            return Expression(
                Apply(OneStepBetaReduce(M.term.fn, new_vars), M.term.arg)
            )
          return Expression(
              Apply(M.term.fn, OneStepBetaReduce(M.term.arg, new_vars))
          )
    case _:
      raise NotImplementedError(f'Unexpected input to OneStepBetaReduce {M}')


class Redexes(Multiset[Union[KindExpression, TypeExpression, Expression]]):
  def __init__(self, M: Union[KindExpression, TypeExpression, Expression]):
    match M:
      case KindExpression():
        match M.kind:
          case Star():
            self.elems = []
          case PiKind():
            self.elems = Redexes(M.kind.arg.typ).elems
      case TypeExpression():
        match M.typ:
          case TypeVar():
            self.elems = []
          case PiType() | TAbstract():
            self.elems = (
                Redexes(M.typ.arg.typ).elems + Redexes(M.typ.body).elems
            )
          case TApply():
            self.elems = Redexes(M.typ.fn).elems + Redexes(M.typ.arg).elems
            if isinstance(M.typ.fn.typ, TAbstract):
              self.elems.append(M)
        self.elems += Redexes(M.kind).elems
      case Expression():
        match M.term:
          case FreeVar() | BoundVar():
            self.elems = []
          case Abstract():
            self.elems = (
                Redexes(M.term.arg.typ).elems + Redexes(M.term.body).elems
            )
          case Apply():
            self.elems = Redexes(M.term.fn).elems + Redexes(M.term.arg).elems
            if isinstance(M.term.Fn(), Abstract):
              self.elems.append(M)
        self.elems += Redexes(M.typ).elems
      case _:
        raise NotImplementedError(f'Unexpected input to Redexes {M}')


def BetaReduce(
    M: Union[KindExpression, TypeExpression, Expression],
    new_vars: list[Var] = []
):
  while not M.BetaNormal():
    M = OneStepBetaReduce(M, new_vars)
  return M


def BetaEquiv(
    M: Union[KindExpression, TypeExpression, Expression],
    N: Union[KindExpression, TypeExpression, Expression],
):
  return BetaReduce(M) == BetaReduce(N)


class TypeDeclaration:
  def __init__(self, subj_t: TypeVar):
    if not isinstance(subj_t, TypeVar):
      raise ValueError(f'Cannot create TypeDeclaration with {subj_t}')
    self.subj = TypeExpression(subj_t)

  def Type(self) -> Type:
    return self.subj.typ

  def __str__(self):
    return str(self.subj)


class VarDeclaration:
  def __init__(self, subj: Var):
    if not isinstance(subj, Var):
      raise ValueError(f'Cannot create VarDeclaration with {subj}')
    self.subj = BindingVar(subj)

  def Var(self) -> Var:
    return self.subj.var

  def __str__(self):
    return str(self.subj)


class Domain(Multiset[Union[Var, TypeVar]]):
    def __init__(self, types: list[TypeVar], vars: list[Var]):
      self.vars = Multiset(vars)
      self.types = Multiset(types)
      self.elems = self.types.elems + self.vars.elems

    def ContainsTypeVar(self, u: TypeVar) -> bool:
      assert isinstance(u, TypeVar)
      return self.types.Contains(u)

    def ContainsVar(self, u: Var) -> bool:
      assert isinstance(u, Var)
      return self.vars.Contains(u)


class Domain(Multiset[Union[Var, TypeVar]]):
    def __init__(self, types: list[TypeVar], vars: list[Var]):
      self.vars = Multiset(vars)
      self.types = Multiset(types)
      self.elems = self.types.elems + self.vars.elems

    def ContainsTypeVar(self, u: TypeVar) -> bool:
      assert isinstance(u, TypeVar)
      return self.types.Contains(u)

    def ContainsVar(self, u: Var) -> bool:
      assert isinstance(u, Var)
      return self.vars.Contains(u)


class Context:
  def __init__(self, *args: list[Union[Kind, TypeVar, Var]]):
    self.typ_declarations = []
    self.var_declarations = []
    self.str_declarations = []  # To preserve order for printing only
    for u in args:
      match u:
        case TypeVar():
          for fv in FreeVars(TypeExpression(u).kind):
            if not self.ContainsVar(fv):
              raise ValueError(
                  f'Context {self} does not contain free vars in kind of {u}'
              )
          u = TypeDeclaration(u)
          self.typ_declarations.append(u)
          self.str_declarations.append(u)
        case Var():
          # Check for free variables in the type.
          for fv in FreeVars(Expression(u).typ):
            if not self.ContainsVar(fv):
              raise ValueError(
                  f'Context {self} does not contain free vars in type of {u}'
              )
          u = VarDeclaration(u)
          self.var_declarations.append(u)
          self.str_declarations.append(u)
        case _:
          raise NotImplementedError(f'Unexpected input to Context {u}')
    for u in self.typ_declarations:
      for v in self.var_declarations:
        u.subj.MaybeBindFreeVarsTo(v.subj)
    self.str_declarations = list(map(str, self.str_declarations))
  
  def __str__(self):
    if not self.str_declarations:
      return 'Ø'
    return ', '.join([str(d) for d in self.str_declarations])

  # Overload for subcontext, A < B returns if A is a subcontext of B
  def __lt__(self, other):
    for u in self.typ_declarations:
      if not any(u.subj.typ == v.subj.typ for v in other.typ_declarations):
        return False
    for u in self.var_declarations:
      if not any(u.subj.var == v.subj.var for v in other.var_declarations):
        return False
    return True

  def __eq__(self, other):
    if not isinstance(other, Context):
      return False
    return self < other and other < self

  def ContainsTypeVar(self, u: TypeVar) -> bool:
    assert isinstance(u, TypeVar)
    return self.Dom().ContainsTypeVar(u)

  def ContainsVar(self, u: Var) -> bool:
    assert isinstance(u, Var)
    return self.Dom().ContainsVar(u)

  def Dom(self) -> Domain:
    return Domain(
        [decl.subj.typ for decl in self.typ_declarations],
        [decl.subj.var for decl in self.var_declarations]
    )

  def BindStatementFreeVars(self, sttmt: Statement):
    if isinstance(sttmt.subj, TypeExpression):
      return
    for decl in self.var_declarations:
      sttmt.subj.MaybeBindFreeVarsTo(decl.subj)

  def PushTypeVar(self, u: TypeVar) -> 'Context':
    assert isinstance(u, TypeVar)
    if self.ContainsTypeVar(u):
      raise Exception(f'Context {self} contains {u}')
    return Context(*self.Dom(), u)

  def PushVar(self, u: Var) -> 'Context':
    assert isinstance(u, Var)
    if self.ContainsVar(u):
      raise Exception(f'Context {self} contains {u}')
    if not self.ContainsFreeVars(TypeExpression(u.typ)):
      raise TypeError(
          f'Context {self} does not contain free type variables in {u.typ}'
      )
    return Context(*self.Dom(), u)

  def PullVar(self, u: Var) -> 'Context':
    if not self.ContainsVar(u):
      raise Exception(f'Context {self} does not contain {u}')
    new_ctx = []
    for v in self.Dom():
      if isinstance(v, Var) and u == v:
        continue
      new_ctx.append(v)
    return Context(*new_ctx)

  def ContainsFreeVars(self, rho: TypeExpression):
    assert isinstance(rho, TypeExpression)
    return all(
        self.ContainsVar(u) for u in FreeVars(rho)
    )

  def OverlappingUnion(self, other: 'Context') -> 'Context':
    assert self < other or other < self
    if self < other:
      return other
    return self


class Statement:
  subj: Union[KindExpression, TypeExpression, Expression]
  typ: Union[TypeExpression, Kind, AllKinds]

  def __init__(self, subj: Union[KindExpression, TypeExpression, Expression]):
    self.subj = subj
    match subj:
      case KindExpression():
        self.typ = AllKinds()
      case TypeExpression():
        self.typ = subj.kind
      case Expression():
        self.typ = subj.typ
      case _:
        raise NotImplementedError(f'Unexpected input to Statement {subj}')

  def __str__(self):
    if isinstance(self.subj, Expression) and isinstance(self.subj.term, BoundVar):
      return str(self.subj.term.var)
    return str(self.subj)


class Judgement:
  def __init__(self, ctx: Context, stmt: Statement):
    self.ctx = ctx
    self.stmt = stmt
    self.ctx.BindStatementFreeVars(stmt)

  def __str__(self):
    return f'{self.ctx} |- {self.stmt}'


class DerivationRule:
  ctx: Context
  premisses: list[Judgement]

  def __init__(self, *premisses: Sequence[Judgement]):
    if premisses:
      ctx = premisses[0].ctx
      for pmiss in premisses:
        if not (ctx < pmiss.ctx) and not (pmiss.ctx < ctx):
          raise ValueError(
              'Cannot use different Contexts in premisses of '
              f'the same DerivationRule: {ctx} != {pmiss.ctx}'
          )
    self.premisses = list(premisses)
  
  def Conclusion(self) -> Judgement:
    raise NotImplementedError(
        'Do not call Conclusion with DerivationRule subclass'
    )

  def __str__(self):
    premiss_str = ', '.join([str(p) for p in self.premisses])
    horiz_rule = '-' * len(premiss_str)
    if premiss_str:
      return f'{premiss_str}\n{horiz_rule}\n{self.Conclusion()}'
    return str(self.Conclusion())


class SortRule(DerivationRule):
  def __init__(self, ctx: Context):
    super().__init__()
    self.ctx = ctx

  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(KindExpression(Star())))


class VarRule(DerivationRule):
  def __init__(self, u: Union[TypeVar, Var], premiss: Judgement):
    super().__init__(premiss)
    self.ctx = ctx = premiss.ctx
    match u:
      case TypeVar():
        if self.ctx.ContainsTypeVar(u):
          raise ValueError(
              f'Cannot create VarRule {u} already occurs in Context {ctx}'
          )
        if premiss.stmt.subj != KindExpression(u.kind):
          raise TypeError(
              f'Cannot create VarRule for {u} with mistmatched premiss {premiss}'
          )
      case Var():
        if self.ctx.ContainsVar(u):
          raise ValueError(
              f'Cannot create VarRule {u} already occurs in Context {ctx}'
          )
        if not isinstance(premiss.stmt.subj, TypeExpression):
          raise ValueError(
              f'Cannot create VarRule for {u} with premiss {premiss}'
          )
        if premiss.stmt.subj != TypeExpression(u.typ):
          raise TypeError(
              f'Cannot create VarRule for {u} with mistmatched premiss {premiss}'
          )
      case _:
        raise NotImplementedError(f'Unexpected input to VarRule {u}')
    self.u = u

  def Conclusion(self) -> Judgement:
    match self.u:
      case TypeVar():
        stmt = Statement(TypeExpression(self.u))
        ctx = self.ctx.PushTypeVar(self.u)
      case Var():
        stmt = Statement(Expression(self.u))
        ctx = self.ctx.PushVar(self.u)
    return Judgement(ctx, stmt)


class WeakRule(DerivationRule):
  def __init__(self, u: Union[TypeVar, Var], *premisses: Sequence[Judgement]):
    if len(premisses) != 2:
      raise ValueError('Can only create WeakRule with 2 Judgements')
    super().__init__(*premisses)
    p_ab, p_cs = self.premisses
    ab = p_ab.stmt.subj
    cs = p_cs.stmt.subj
    match u:
      case Var():
        if p_ab.ctx.ContainsVar(u) or p_cs.ctx.ContainsVar(u):
          raise ValueError(f'Cannot redeclare variable {u}')
        if not isinstance(cs, TypeExpression) or cs.typ != u.Type():
          raise TypeError(
              f'Invalid second premiss for WeakRule {p_cs} given {u}'
          )
      case TypeVar():
        if p_ab.ctx.ContainsTypeVar(u) or p_cs.ctx.ContainsTypeVar(u):
          raise ValueError(f'Cannot redeclare type variable {u}')
        if not isinstance(cs, Kind) or cs.kind != u.kind:
          raise TypeError(
              f'Invalid second premiss for WeakRule {p_cs} given {u} '
          )
    self.ctx = p_ab.ctx.OverlappingUnion(p_cs.ctx)
    self.u = u

  def Conclusion(self) -> Judgement:
    p_ab, p_c = self.premisses
    ctx = self.ctx
    match self.u:
      case TypeVar():
        if not self.ctx.ContainsTypeVar(self.u):
          ctx = self.ctx.PushTypeVar(self.u)
        subj = p_ab.stmt.subj.Copy()
      case Var():
        if not self.ctx.ContainsVar(self.u):
          ctx = self.ctx.PushVar(self.u)
        subj = p_ab.stmt.subj.Copy()
    return Judgement(ctx, Statement(subj))


class FormRule(DerivationRule):
  def __init__(self, arg: Var, *premisses: Sequence[Judgement]):
    if len(premisses) != 2:
      raise ValueError('Can only create FormRule with 2 Judgements')
    super().__init__(*premisses)
    p_a, p_b = self.premisses
    self.ctx = p_a.ctx.OverlappingUnion(p_b.ctx.PullVar(arg))
    a = p_a.stmt.subj
    b = p_b.stmt.subj
    if not isinstance(a, TypeExpression):
      raise TypeError(f'Invalid first premiss to FormRule {p_a}')
    if arg.typ != a:
      raise TypeError(
          f'First FormRule premiss not match type of argument {arg}, {p_a}'
      )
    match b:
      case KindExpression():
        self.ab = KindExpression(PiKind(arg, b))
      case TypeExpression():
        self.ab = TypeExpression(PiType(arg, b))
      case _:
        raise NotImplementedError(f'Unexpected input to FormRule {p_b}')

  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(self.ab))


class ApplRule(DerivationRule):
  def __init__(self, *premisses: Sequence[Judgement]):
    if len(premisses) != 2:
      raise ValueError('Can only create ApplRule with 2 Judgements')
    super().__init__(*premisses)
    p_mxab, p_na = self.premisses
    self.ctx = p_mxab.ctx.OverlappingUnion(p_na.ctx)
    mxab, na = p_mxab.stmt.subj, p_na.stmt.subj
    if not isinstance(na, Expression):
      raise TypeError(f'Invalid second premiss to ApplRule {p_na}')
    match mxab:
      case TypeExpression():
        if not isinstance(mxab.Kind(), PiKind):
          raise TypeError(f'Invalid first premiss to ApplRule {p_mxab}')
        if na.typ != mxab.Kind().arg.typ:
          raise TypeError(f'Invalid second premiss to ApplRule {p_na}')
        self.mn = TypeExpression(TApply(mxab, na))
      case Expression():
        if not isinstance(mxab.Type(), PiType):
          raise TypeError(f'Invalid first premiss to ApplRule {p_mxab}')
        if na.typ != mxab.Type().arg.typ:
          raise TypeError(f'Invalid second premiss to ApplRule {p_na}')
        self.mn = Expression(Apply(mxab, na))
      case _:
        raise NotImplementedError(
            f'Unexpected first premiss to ApplRule {p_mxab}'
        )

  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(self.mn))


class AbstRule(DerivationRule):
  def __init__(self, u: Var, *premisses: Sequence[Judgement]):
    if len(premisses) != 2:
      raise ValueError('Can only create AbstRule with 2 Judgements')
    super().__init__(*premisses)
    p_xamb, p_abs = self.premisses
    self.ctx = p_xamb.ctx.OverlappingUnion(p_abs.ctx).PullVar(u)
    xa_mb, ab_s =  p_xamb.stmt.subj, p_abs.stmt.subj
    match xa_mb:
      case TypeExpression():
        if (
            not isinstance(ab_s, KindExpression)
            or not isinstance(ab_s.kind, PiKind)
        ):
          raise TypeError(f'Invalid second premiss to AbstRule {p_abs}')
        if ab_s.kind.arg.typ != u.typ or ab_s.kind.body != xa_mb.kind:
          raise TypeError(f'Mismatched premisses to ApplRule {p_xamb} {p_abs}')
        self.xam_xab = TypeExpression(TAbstract(u, xa_mb))
      case Expression():
        if (
            not isinstance(ab_s, TypeExpression)
            or not isinstance(ab_s.typ, PiType)
        ):
          raise TypeError(f'Invalid second premiss to AbstRule {p_abs}')
        if ab_s.typ.arg.typ != u.typ or ab_s.typ.body != xa_mb.typ:
          raise TypeError(f'Mismatched premisses to ApplRule {p_xamb} {p_abs}')
        self.xam_xab = Expression(Abstract(u, xa_mb))
      case _:
        raise NotImplementedError(
            f'Unexpected first premiss to AbstRule {p_xamb}'
        )
  
  def Conclusion(self):
    return Judgement(self.ctx, Statement(self.xam_xab))


class ConvRule(DerivationRule):
  def __init__(self, *premisses):
    if len(premisses) != 2:
      raise ValueError('Can only create ConvRule with 2 Judgements')
    super().__init__(*premisses)
    p_ab, p_bprime = self.premisses
    self.ctx = p_ab.ctx.OverlappingUnion(p_bprime.ctx)
    ab, b_prime = p_ab.stmt.subj, p_bprime.stmt.subj
    match ab:
      case TypeExpression():
        if not isinstance(b_prime, KindExpression):
          raise TypeError(f'Invalid second premiss to ConvRule {p_bprime}')
        if not (ab.kind >> b_prime):
          raise TypeError(
              f'Kind of first premiss {p_ab} must be β-equal to second '
              f'premiss {p_bprime}'
          )
        self.abprime = ab.ReplaceKind(b_prime)
      case Expression():
        if not isinstance(b_prime, TypeExpression):
          raise TypeError(f'Invalid second premiss to ConvRule {p_bprime}')
        if not (ab.typ >> b_prime):
          raise TypeError(
              f'Kind of first premiss {p_ab} must be β-equal to second '
              f'premiss {p_bprime}'
          )
        self.abprime = ab.ReplaceType(b_prime)
      case _:
        raise NotImplementedError(
            f'Unexpected first premiss to ConvRule {p_ab}'
        )
  
  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(self.abprime))
