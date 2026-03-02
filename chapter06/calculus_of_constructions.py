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
  def __init__(self, arg: Union[TypeVar, BindingTypeVar, Var], body: Kind):
    match arg:
      case BindingTypeVar():  # TODO BindingVar
        pass
      case Var():
        # TODO
        pass
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
        raise NotImplementedError('TODO')

  def __eq__(self, other):
    # if isinstance(other, KindExpression):
    #   other = other.kind
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
    if isinstance(self.arg, Type):
      return (
          isinstance(self.body, KindExpression)
          and not FreeTypeVars(self.body.Copy()).Contains(self.arg.typ)
      )
    else:
      # TODO
      return False


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
        raise NotImplementedError('TODO')
      self.kind.body.MaybeBindFreeTypesTo(btv)


class Type:
  kind: Kind

  def __str__(self):
    raise NotImplementedError('Do not cast Type subclass to str')

  def Kind(self):
    kind = self.kind
    # if isinstance(kind, KindExpression):
    #   kind = kind.kind
    return kind


class TypeVar(Type):
  def __init__(self, name: str, kind: Kind):
    self.name = name
    self.kind = kind

  def __str__(self):
    kind_str = str(self.kind)[:-2]
    return f'{self.name}:{kind_str}'

  def __eq__(self, other):
    # if isinstance(other, TypeExpression):
    #   other = other.typ
    if not isinstance(other, TypeVar):
      return False
    return (self.name, self.kind) == (other.name, other.kind)


class TOccurrence(Type):
  def __init__(self, typ: TypeVar):
    self.typ = typ
    self.kind = typ.kind
  
  def __eq__(self, other):
    if isinstance(other, TOccurrence):
      return self.typ == other.typ
    return self.typ == other

  def __str__(self):
    return str(self.typ)


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
    self.kind = ftyp.kind
    if self.bt.typ != self.typ:
      raise TypeError(
          f'Cannot bind variable with type {self.bt} '
          f'to variable with type {self.typ}'
      )

  def __str__(self):
    return self.typ.name

  def BoundTo(self, bt: BindingTypeVar) -> bool:
    return self.bt == bt


class TypeExpression(Type):
  typ: Type
  kind: Kind

  def __init__(self, typ: Type):
    match typ:
      case TypeVar():
        self.typ = FreeTypeVar(typ)
      # TODO rest
      case _:
        raise NotImplementedError(f'Unexpected input to TypeExpression {typ}')
    self.kind = KindExpression(self.typ.kind)

  def MaybeBindFreeTypesTo(self):
    match self.typ:
      case FreeTypeVar():
        if btv.ShouldBind(self.typ):
          self.typ = BoundTypeVar(btv, self.typ)
      case BoundTypeVar():
        pass
      # TODO rest

  def Type(self) -> Type:
    typ = self.typ
    if isinstance(typ, TOccurrence):
      typ = typ.typ
    return typ

  def Copy(self) -> 'TypeExpression':
    match self.typ:
      case FreeTypeVar() | BoundTypeVar():
        return TypeExpression(self.Type())
      # TODO rest
      case _:
        raise NotImplementedError(
            f'Unexpected member of TypeExpression {self.typ}'
        )


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
  # TODO Add Expression.
  def __init__(self, M: Union[KindExpression, TypeExpression]):
    self.elems = []
    match M:
      case KindExpression():
        self._FindKindFreeTypeVars(M)
      case TypeExpression():
        self._FindTypeFreeTypeVars(M)
      # TODO Expression
      case _:
        raise NotImplementedError(f'Unexpected input to FreeTypeVars {M}')
  
  def _FindKindFreeTypeVars(self, K: KindExpression):
    if isinstance(K.kind, PiKind):
      if isinstance(K.kind.arg, Type):
        self.elems += FreeTypeVars(K.kind.arg.kind).elems
      else:
        # self.elems += FreeTypeVars(K.kind.arg.typ).elems
        raise NotImplementedError('TODO')

  def _FindTypeFreeTypeVars(self, T: TypeExpression):
    match T.typ:
      case FreeTypeVar():
        self.elems.append(T.Type())
      case BoundTypeVar():
        pass
      # TODO rest


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Do not cast Term subclass to str')

  def Type(self):
    typ = self.typ
    # if isinstance(typ, TypeExpression):
    #   typ = typ.typ
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
    # if isinstance(other, Occurrence):
    #   other = other.var
    if not isinstance(other, Var):
      return False
    return self.name == other.name and self.typ == other.typ