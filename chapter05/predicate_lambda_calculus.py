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
    return isinstance(other, Star)


class PiKind(Kind):
  def __init__(self, arg: Union[Var, BindingVar], body: Kind):
    self.arg = arg
    self.body = body
    if isinstance(self.arg, BindingVar):
      self.body.MaybeBindFreeVarsTo(self.arg)

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

  def Copy(self) -> 'KindExpression':
    match self.kind:
      case Star():
        return KindExpression(Star())
      case PiKind():
        bv = self.kind.arg
        return KindExpression(PiKind(bv.var, self.kind.body.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of KindExpression {self.kind}'
        )
  
  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    if isinstance(self.kind, PiKind):
      self.kind.arg.typ.MaybeBindFreeVarsTo(bv)
      self.kind.body.MaybeBindFreeVarsTo(bv)


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
    if isinstance(self.arg, BindingVar):
      self.body.MaybeBindFreeVarsTo(self.arg)
    self.kind = Star()

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
      if isinstance(self.body.kind, PiKind) and body_str[0] == '(':
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
    self.kind = self.fn.Kind().body

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
    # TODO α-equivalence.
    if isinstance(other, TypeExpression):
      other = other.typ
    return self.typ == other

  def __str__(self):
    return str(self.typ)

  def Copy(self) -> 'TypeExpression':
    match self.typ:
      case TypeVar():
        return TypeExpression(self.typ)
      case PiType():
        bv = self.typ.arg
        return TypeExpression(PiType(bv.var, self.typ.body.Copy()))
      case TAbstract():
        bv = self.typ.arg
        return TypeExpression(TAbstract(bv.var, self.typ.body.Copy()))
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
    line = f'{self.name}:{self.typ}'
    k_str = str(self.typ.kind)[:-2]
    if line.endswith(k_str):
      line = line[:-len(k_str) - 1]
    return line

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
  pass


class BindingVar(Occurrence):
  def __init__(self, u: Var):
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
    return self.var == fv


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


class Apply(Term):
  def __init__(self, fn: Term, arg: Term):
    self.fn = fn
    self.arg = arg
    if not isinstance(fn.Type(), PiType):
      raise TypeError(f'Left term of Apply must be Π-type {fn.typ}')
    if fn.Type().arg.Type() != arg.Type():
      raise TypeError(f'Mismatched types {fn} got {arg}')
    self.typ = self.fn.Type()

  def __str__(self):
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    fn_str = str(self.fn)
    if isinstance(fn, Apply):
      fn_str = '):'.join(fn_str.split('):')[:-1])[1:]
    arg = str(self.arg)
    if ':' in arg:
      arg = ':'.join(arg.split(':')[:-1])
    return f'({fn_str} {arg}):{self.typ}'


class Abstract(Term):
  def __init__(self, arg: Union[Var, BindingVar], body: Term):
    self.arg = arg
    self.body = body
    if isinstance(arg, BindingVar):
      body.MaybeBindFreeVarsTo(arg)
    self.typ = PiType(self.arg, self.body.typ)

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
        self.term = Apply(EXpression(term.fn), Expression(term.arg))
      case Abstract():
        bv = term.arg
        if not isinstance(bv, BindingVar):
          bv = BindingVar(bv)
        self.term = Abstract(bv, Expression(term.body))
      case _:
        raise NotImplementedError(f'Unexpected input to Expression {term}')
    self.typ = TypeExpression(term.typ)

  def __str__(self):
    return str(self.term)

  def Copy(self):
    match self.term:
      case FreeVar() | BoundVar():
        return Expression(self.term.var)
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
      self.elems = FreeVars(K.kind.arg.typ).elems + FreeVars(K.kind.body).elems

  def _FindTypeFreeVars(self, T: TypeExpression):
    assert isinstance(T, TypeExpression)
    match T.typ:
      case PiType() | TAbstract():
        self.elems = FreeVars(T.typ.arg.typ).elems + FreeVars(T.typ.body).elems
      case TApply():
        self.elems = FreeVars(T.typ.fn).elems + FreeVars(T.typ.arg).elems
    self.elems += FreeVars(T.typ.kind).elems

  def _FindTermFreeVars(self, M: Expression):
    assert isinstance(M, Expression)
    match M.term:
      case FreeVar():
        self.elems = [M.term.var]
      case Apply():
        self.elems = FreeVars(M.term.fn).elems +  FreeVars(M.term.arg).elems
      case Abstract():
        self._FindTypeFreeVars(M.term.arg.typ)
        self.elems = FreeVars(M.term.body).elems
    self.elems += FreeVars(M.typ)