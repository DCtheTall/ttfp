"""
Chapter 6: The Calculus of Constructions
========================================

"""


class AllKinds:
  def __str__(self):
    return '□'


class Kind:
  def __str__(self):
    raise NotImplementedError('Do not cast Kind subclass to str')


class Star(Kind):
  def __str__(self):
    return '*:' + str(AllKinds())

  def __eq__(self, other):
    if isinstance(other, KindExpression):
      other = other.kind
    return isinstance(other, Star)


class PiKind(Kind):
  def __init__(
      self, arg: Union[TypeVar, BindingTypeVar, Var, BindingVar], body: Kind
  ):
    match arg:
      case BindingTypeVar() | BindingVar():
        pass
      case Var():
        arg = BindingVar(arg)
      case TypeVar():
        arg = BindingTypeVar(arg)
      case _:
        raise NotImplementedError(f'Unexpected argument to PiKind {arg}')
    self.arg = arg
    self.body = body
    if isinstance(body, KindExpression):
      if isinstance(self.arg, Type):
        self.body.MaybeBindFreeTypesTo(self.arg)
      else:
        self.body.MaybeBindFreeVarsTo(self.arg)

  def __eq__(self, other):
    if isinstance(other, KindExpression):
      other = other.kind
    if not isinstance(other, PiKind):
      return False
    return (self.arg, self.body) == (other.arg, other.body)

  def __str__(self):
    if self.IsArrow():
      body_str = str(self.body)
      if isinstance(self.body.kind, PiKind) and self.body.kind.IsArrow():
        body_str = body_str[1:-1]
      if isinstance(self.arg, Type):
        arg_str = str(self.arg.kind)[:-2]
        return f'({arg_str} -> {str(body_str)[:-2]}):{AllKinds()}'
      else:
        arg_str = str(self.arg.typ)
        arg_kind = str(self.arg.typ.kind)[:-2]
        if arg_str.endswith(arg_kind):
          arg_str = arg_str[:-len(arg_kind)-1]
        return f'({arg_str} -> {str(body_str)[:-2]}):{AllKinds()}'
    body = self.BodyKind()
    args = str(self.arg)
    while isinstance(body, PiKind):
      if body.IsArrow():
        break
      args = f'{args},{body.arg}'
      body = body.BodyKind()
    body = str(body)
    return f'Π{args}.{body}'

  def BodyKind(self) -> Kind:
    if isinstance(self.body, KindExpression):
      return self.body.kind
    return self.body

  def IsArrow(self) -> bool:
    if not isinstance(self.body, KindExpression):
      return False
    if isinstance(self.arg, Type):
      return not FreeTypeVars(self.body.Copy()).Contains(self.arg.typ)
    return not FreeVars(self.body.Copy()).Contains(self.arg.var)


class KindExpression(Kind):
  kind: Kind

  def __init__(self, kind: Kind):
     match kind:
      case KindExpression():
        self.kind = kind.Copy().kind
      case Star():
        self.kind = kind
      case PiKind():
        self.kind = PiKind(kind.arg, KindExpression(kind.body))
      case _:
        raise NotImplementedError(f'Unexpected input to KindExpression {kind}')
  
  def __str__(self):
    return str(self.kind)

  def __eq__(self, other):
    # TODO alpha-equivalence
    if isinstance(other, KindExpression):
      return self.kind == other.kind
    if not isinstance(other, Kind):
      return False
    return self.kind == other

  def Copy(self) -> 'KindExpression':
    match self.kind:
      case Star():
        return KindExpression(Star())
      case PiKind():
        return KindExpression(PiKind(self.kind.arg, self.kind.body.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of KindExpression {self.kind}'
        )

  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    if isinstance(self.kind, PiKind):
      if isinstance(self.kind.arg, Type):
        self.kind.arg.kind.MaybeBindFreeTypesTo(btv)
      else:
        self.kind.arg.typ.MaybeBindFreeTypesTo(btv)
      self.kind.body.MaybeBindFreeTypesTo(btv)

  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    if isinstance(self.kind, PiKind):
      if isinstance(self.kind.arg, Type):
        self.kind.arg.kind.MaybeBindFreeVarsTo(bv)
      else:
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

  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      other = other.typ
    if isinstance(other, TOccurrence):
      other = other.typ
    if not isinstance(other, TypeVar):
      return False
    return (self.name, self.kind) == (other.name, other.kind)


class TOccurrence(Type):
  def __init__(self, typ: TypeVar):
    self.typ = typ
    self.kind = KindExpression(typ.kind)
  
  def __eq__(self, other):
    if isinstance(other, TOccurrence):
      return self.typ == other.typ
    return self.typ == other

  def __str__(self):
    tv_str = str(self.typ)
    tv_kind = str(self.typ.kind)[:-2]
    if tv_str.endswith(tv_kind):
      tv_str = tv_str[:-len(tv_kind)-1]
    kind_str = str(self.kind)[:-2]
    return f'{tv_str}:{kind_str}'


class FreeTypeVar(TOccurrence):
  pass


class BindingTypeVar(TOccurrence):
  def __eq__(self, other):
    return id(self) == id(other)

  def __init__(self, typ: TypeVar):
    assert isinstance(typ, TypeVar)
    self.typ = typ
    self.kind = KindExpression(typ.kind)
  
  def ShouldBind(self, ftyp: FreeTypeVar) -> bool:
    return self.typ == ftyp


class BoundTypeVar(TOccurrence):
  def __init__(self, bt: BindingTypeVar, ftyp: FreeTypeVar):
    assert isinstance(bt, BindingTypeVar)
    assert isinstance(ftyp, FreeTypeVar)
    self.bt = bt
    self.typ = ftyp.typ
    self.kind = KindExpression(ftyp.kind)
    self.kind.MaybeBindFreeTypesTo(self.bt)
    if self.bt.typ != self.typ:
      raise TypeError(
          f'Cannot bind variable with type {self.bt} '
          f'to variable with type {self.typ}'
      )

  def __str__(self):
    return self.typ.name

  def BoundTo(self, bt: BindingTypeVar) -> bool:
    return self.bt == bt


class PiType(Type):
  def __init__(
      self, arg: Union[TypeVar, BindingTypeVar, Var, BindingVar], body: Type
  ):
    match arg:
      case BindingTypeVar() | BindingVar():
        pass
      case Var():
        arg = BindingVar(arg)
      case TypeVar():
        arg = BindingTypeVar(arg)
      case _:
        raise NotImplementedError(f'Unexpected argument to PiKind {arg}')
    self.arg = arg
    self.body = body
    if isinstance(body, TypeExpression):
      if isinstance(self.arg, Type):
        self.body.MaybeBindFreeTypesTo(self.arg)
      else:
        self.body.MaybeBindFreeVarsTo(self.arg)
    if isinstance(self.arg, Type):
      self.kind = PiKind(self.arg, self.body.kind)
    else:
      self.kind = Star()

  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      other = other.typ
    if not isinstance(other, PiType):
      return False
    return (self.arg, self.body) == (other.arg, other.body)

  def __str__(self):
    if self.IsArrow():
      body_str = str(self.body)
      body_kind = str(self.BodyType().kind)[:-2]
      if body_str.endswith(body_kind):
        body_str = body_str[:-len(body_kind)-1]
      if isinstance(self.BodyType(), PiType) and self.BodyType().IsArrow():
        body_str = body_str[1:-1]
      arg_str = str(self.arg.typ)
      arg_kind = str(self.arg.typ.kind)[:-2]
      if arg_str.endswith(arg_kind):
        arg_str = arg_str[:-len(arg_kind)-1]
      return f'({arg_str} -> {body_str}):{str(self.kind)[:-2]}'
    body = self.BodyType()
    args = str(self.arg)
    if isinstance(body, PiType):
      while isinstance(body, PiType):
        if body.IsArrow():
          break
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

  def IsArrow(self):
    if not isinstance(self.body, TypeExpression):
      return False
    if isinstance(self.arg, Type):
      return False
    return not FreeVars(self.body.Copy()).Contains(self.arg.var)


class TAbstract(Type):
  def __init__(
      self, arg: Union[TypeVar, BindingTypeVar, Var, BindingVar], body: Type
  ):
    match arg:
      case BindingTypeVar() | BindingVar():
        pass
      case Var():
        arg = BindingVar(arg)
      case TypeVar():
        arg = BindingTypeVar(arg)
      case _:
        raise NotImplementedError(f'Unexpected argument to PiKind {arg}')
    self.arg = arg
    self.body = body
    if isinstance(body, TypeExpression):
      if isinstance(self.arg, Type):
        self.body.MaybeBindFreeTypesTo(self.arg)
      else:
        self.body.MaybeBindFreeVarsTo(self.arg)
    self.kind = PiKind(self.arg, self.body.kind)

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
  def __init__(self, fn: Type, arg: Union[Type, Term]):
    if not isinstance(fn.Kind(), PiKind):
      raise TypeError(f'Unexpected input to TApply {fn}')
    if (
        (
            isinstance(fn.Kind().arg, Type)
            and (not isinstance(arg, Type) or arg.kind != fn.Kind().arg.kind)
        ) or (
            isinstance(fn.Kind().arg, Term)
            and (not isinstance(arg, Term) or arg.typ != fn.Kind().arg.typ)
        )
    ):
      raise TypeError(f'Mismatched inputs to TApply {fn} and {arg}')
    self.fn = fn
    self.arg = arg
    self.kind = fn.Kind().body
    # TODO substitution
    # if isinstance(self.fn, TypeExpression):
    #   pass
  
  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      return self == other.typ
    if not isinstance(other, TApply):
      return False
    return (self.fn, self.arg) == (other.fn, other.arg)

  def __str__(self):
    fn = self.FnType()
    fn_str = str(fn)
    if isinstance(fn, TApply):
      fn_str = fn_str[1:-1]
    if isinstance(self.arg, Type):
      arg = str(self.arg)
      arg_kind = str(self.arg.kind)
      if arg.endswith(arg_kind):
        arg = arg[:-(len(arg_kind) + 1)]
    else:
      arg = str(self.arg)
    return f'({fn_str} {arg}):{self.kind}'[:-2]

  def FnType(self):
    if isinstance(self.fn, TypeExpression):
      return self.fn.typ
    return self.fn


class TypeExpression(Type):
  typ: Type
  kind: Kind

  def __init__(self, typ: Type):
    match typ:
      case TypeExpression():
        self.typ = typ.Copy().typ
      case TypeVar():
        self.typ = FreeTypeVar(typ)
      case PiType() | TAbstract():
        self.typ = type(typ)(typ.arg, TypeExpression(typ.body))
      case TApply():
        if isinstance(typ.arg, Type):
          self.typ = TApply(TypeExpression(typ.fn), TypeExpression(typ.arg))
        else:
          self.typ = TApply(TypeExpression(typ.fn), Expression(typ.arg))
      case _:
        raise NotImplementedError(f'Unexpected input to TypeExpression {typ}')
    self.kind = KindExpression(self.typ.kind)

  def __str__(self):
    return str(self.typ)

  def __eq__(self, other):
    # TODO alpha-equivalence
    if isinstance(other, TypeExpression):
      other = other.typ
    if not isinstance(other, Type):
      return False
    return self.typ == other

  def Type(self) -> Type:
    typ = self.typ
    if isinstance(typ, TOccurrence):
      typ = typ.typ
    return typ

  def Copy(self) -> 'TypeExpression':
    match self.typ:
      case FreeTypeVar() | BoundTypeVar():
        return TypeExpression(self.Type())
      case PiType() | TAbstract():
        return TypeExpression(
            type(self.typ)(self.typ.arg, self.typ.body.Copy())
        )
      case TApply():
        return TApply(self.typ.fn.Copy(), self.typ.arg.Copy())
      case _:
        raise NotImplementedError(
            f'Unexpected member of TypeExpression {self.typ}'
        )

  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    self.kind.MaybeBindFreeTypesTo(btv)
    match self.typ:
      case FreeTypeVar():
        if btv.ShouldBind(self.typ):
          self.typ = BoundTypeVar(btv, self.typ)
      case BoundTypeVar():
        pass
      case PiType() | TAbstract():
        if isinstance(self.typ.arg, Type):
          self.typ.arg.kind.MaybeBindFreeTypesTo(btv)
        else:
          self.typ.arg.typ.MaybeBindFreeTypesTo(btv)
        self.typ.body.MaybeBindFreeTypesTo(btv)
      case TApply():
        self.typ.fn.MaybeBindFreeTypesTo(btv)
        self.typ.arg.MaybeBindFreeTypesTo(btv)

  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    self.kind.MaybeBindFreeVarsTo(bv)
    match self.typ:
      case PiType() | TAbstract():
        if isinstance(self.typ.arg, Type):
          self.typ.arg.kind.MaybeBindFreeVarsTo(bv)
        else:
          self.typ.arg.typ.MaybeBindFreeVarsTo(bv)
        self.typ.body.MaybeBindFreeVarsTo(bv)
      case TApply():
        self.typ.fn.MaybeBindFreeVarsTo(bv)
        self.typ.arg.MaybeBindFreeVarsTo(bv)


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Do not cast Term subclass to str')

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
      term = term[:-len(k_str)-1]
    return term

  def __hash__(self):
    return hash(str(self))

  def __eq__(self, other):
    # if isinstance(other, Occurrence):
    #   other = other.var
    if not isinstance(other, Var):
      return False
    return self.name == other.name and self.typ == other.typ


class Occurrence(Term):
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
    return False


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

  def __str__(self):
    return self.var.name

  def BoundTo(self, bv: BindingVar) -> bool:
    return self.bv == bv


class Apply(Term):
  def __init__(self, fn: Term, arg: Union[Type, Term]):
    if not isinstance(fn.Type(), PiType):
      raise TypeError(f'Unexpected input to TApply {fn}')
    if (
        (
            isinstance(fn.Type().arg, Type)
            and (not isinstance(arg, Type) or arg.kind != fn.Type().arg.kind)
        ) or (
            isinstance(fn.Type().arg, Term)
            and (not isinstance(arg, Term) or arg.typ != fn.Type().arg.typ)
        )
    ):
      raise TypeError(f'Mismatched inputs to TApply {fn} and {arg}')
    self.fn = fn
    self.arg = arg
    self.typ = fn.Type().body
    # TODO substitution
    # if isinstance(self.fn, TypeExpression):
    #   pass

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
    if isinstance(self.arg, Type):
      arg = str(self.arg)
      k_arg = str(self.arg.kind)[:-2]
      if arg.endswith(k_arg):
        arg = arg[:-len(k_arg)-1]
    else:
      arg = str(self.arg)
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

  def Arg(self) -> Union[Type, Term]:
    arg = self.arg
    if isinstance(arg, TypeExpression):
      arg = arg.typ
    if isinstance(arg, Expression):
      arg = arg.term
    if isinstance(arg, Occurrence):
      arg = arg.var
    return arg


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
        if isinstance(term.arg, Type):
          arg = TypeExpression(term.arg)
        else:
          arg = Expression(term.arg)
        self.term = Apply(Expression(term.fn), arg)
      # TODO rest
      case _:
        raise NotImplementedError(f'Unexpected input to Expression {term}')
    self.typ = TypeExpression(self.term.typ)

  def __str__(self):
    return str(self.term)

  def Copy(self):
     match self.term:
      case FreeVar() | BoundVar():
        return Expression(self.term.var)
      case Apply():
        if isinstance(self.term.arg, Type):
          arg = TypeExpression(self.term.arg)
        else:
          arg = Expression(self.term.arg)
        self.term = Apply(Expression(self.term.fn), arg)
      # TODO rest
      case _:
        raise NotImplementedError(
            f'Unexpected member of Expression {self.term}'
        )

  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    self.typ.MaybeBindFreeTypesTo(btv)
    match self.term:
      case FreeVar() | BoundVar():
        self.term.typ.MaybeBindFreeTypesTo(btv)
      case Apply():
        self.term.fn.MaybeBindFreeTypesTo(btv)
        self.term.arg.MaybeBindFreeTypesTo(btv)
      # TODO rest

  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    self.typ.MaybeBindFreeVarsTo(bv)
    match self.term:
      case FreeVar():
        if bv.ShouldBind(self.term):
          self.term = BoundVar(bv, self.term)
      case BoundVar():
        pass
      case Apply():
        self.term.fn.MaybeBindFreeVarsTo(bv)
        self.term.arg.MaybeBindFreeVarsTo(bv)
      # TODO rest


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


class FreeTypeVars(Multiset[TypeVar]):
  def __init__(self, M: Union[KindExpression, TypeExpression, Expression]):
    self.elems = []
    match M:
      case KindExpression():
        self._FindKindFreeTypeVars(M)
      case TypeExpression():
        self._FindTypeFreeTypeVars(M)
      case Expression():
        self._FindTermFreeTypeVars(M)
      case _:
        raise NotImplementedError(f'Unexpected input to FreeTypeVars {M}')
  
  def _FindKindFreeTypeVars(self, K: KindExpression):
    if isinstance(K.kind, PiKind):
      if isinstance(K.kind.arg, Type):
        self.elems += FreeTypeVars(K.kind.arg.kind).elems
      else:
        self.elems += FreeTypeVars(K.kind.arg.typ).elems
      self.elems += FreeTypeVars(K.kind.body).elems

  def _FindTypeFreeTypeVars(self, T: TypeExpression):
    self.elems += FreeTypeVars(T.kind).elems
    match T.typ:
      case FreeTypeVar():
        self.elems.append(T.Type())
      case BoundTypeVar():
        pass
      case PiType() | TAbstract():
        if isinstance(T.typ.arg, Type):
          self.elems += FreeTypeVars(T.typ.arg.kind).elems
        else:
          self.elems += FreeTypeVars(T.typ.arg.typ).elems
        self.elems += FreeTypeVars(T.typ.body).elems
      case TApply():
        self.elems += FreeTypeVars(T.typ.fn).elems
        self.elems += FreeTypeVars(T.typ.arg).elems

  def _FindTermFreeTypeVars(self, M: Expression):
    self.elems += FreeTypeVars(M.typ).elems
    match M.term:
      case Apply():
        self.elems += FreeTypeVars(M.term.fn).elems
        self.elems += FreeTypeVar(M.term.arg).elems
    # TODO rest


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
        raise NotImplementedError(f'Unexpected input to FreeTypeVars {M}')
  
  def _FindKindFreeVars(self, K: KindExpression):
    if isinstance(K.kind, PiKind):
      if isinstance(K.kind.arg, Type):
        self.elems += FreeVars(K.kind.arg.kind).elems
      else:
        self.elems += FreeVars(K.kind.arg.typ).elems
      self.elems += FreeVars(K.kind.body).elems

  def _FindTypeFreeVars(self, T: TypeExpression):
    self.elems += FreeVars(T.kind).elems
    match T.typ:
      case PiType() | TAbstract():
        if isinstance(T.typ.arg, Type):
          self.elems += FreeVars(T.typ.arg.kind)
        else:
          self.elems += FreeVars(T.typ.arg.typ)
        self.elems += FreeVars(T.typ.body).elems
      case TApply():
        self.elems += FreeVars(T.typ.fn).elems
        self.elems += FreeVars(T.typ.arg).elems

  def _FindTermFreeVars(self, M: Expression):
    self.elems += FreeVars(M.typ).elems
    match M.term:
      case FreeVar():
        self.elems.append(M.term.var)
      case Apply():
        self.elems += FreeVars(M.term.fn).elems
        self.elems += FreeVars(M.term.arg).elems
      # TODO rest
