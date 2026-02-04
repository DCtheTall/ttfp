"""
Chapter 4: Types Dependent on Types
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


class KArrow(Kind):
  def __init__(self, arg: Kind, ret: Kind):
    self.arg = arg
    self.ret = ret

  def __str__(self):
    ret_str = str(self.ret)
    if isinstance(self.ret, KArrow):
      ret_str = ret_str[1:-1]
    return f'({str(self.arg)[:-2]} -> {str(ret_str)[:-2]}):{AllKinds()}'

  def __eq__(self, other):
    assert isinstance(other, Kind)
    if not isinstance(other, KArrow):
      return False
    return (self.arg, self.ret) == (other.arg, other.ret)


class Type:
  kind: Kind

  def __str__(self):
    raise NotImplementedError('Do not cast Type subclass to str')

  def Proper(self) -> bool:
    return self.kind == Star()


def Sort(arg: Union[Kind, Type]):
  match arg:
    case Kind():
      return AllKinds()
    case Type():
      return Star()
    case _:
      raise NotImplementedError(f'Unexpected input to Sort {arg}')


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
      other = other.Type()
    if isinstance(other, TOccurrence):
      other = other.typ
    if not isinstance(other, TypeVar):
      return False
    return (self.name, self.kind) == (other.name, other.kind)


class TOccurrence:
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
    self.kind = typ.kind
  
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


class TArrow(Type):
  def __init__(self, arg: Type, ret: Type):
    assert ret.Proper()
    assert arg.Proper()
    self.kind = Star()
    self.arg = arg
    self.ret = ret

  def __str__(self):
    ret_t = self.RetType()
    ret_str = str(ret_t)
    kind_str = str(ret_t.kind)[:-2]
    if ret_str.endswith(kind_str):
      ret_str = ret_str[:-(len(kind_str) + 1)]
    if isinstance(ret_t, TArrow):
      ret_str = ret_str[1:-1]
    arg = str(self.arg)
    kind_str = str(self.arg.kind)[:-2]
    if arg.endswith(kind_str):
      arg = arg[:-(len(kind_str) + 1)]
    return f'({arg} -> {ret_str})'

  def RetType(self) -> Type:
    if isinstance(self.ret, TypeExpression):
      return self.ret.Type()
    return self.ret


class TAbstract(Type):
  def __init__(self, arg: Type, body: Type):
    self.arg = arg
    self.body = body
    self.kind = KArrow(arg.kind, body.kind)
    if isinstance(arg, BindingTypeVar):
      assert isinstance(body, TypeExpression)
      body.MaybeBindFreeTypesTo(arg)

  def __str__(self):
    body = self.BodyType()
    args = str(self.arg)
    while isinstance(body, TAbstract):
      args = body._AppendMultiArgStr(args, body)
      body = body.BodyType()
    body_kind = str(body.kind)[:-2]
    body_str = str(body)
    if body_str.endswith(body_kind):
      body_str = body_str[:-(len(body_kind) + 1)]
    return f'(λ{args}.{body_str}):{self.kind}'[:-2]

  def _AppendMultiArgStr(self, args_str, body) -> str:
    return args_str + f'.λ{body.arg}'

  def BodyType(self) -> Type:
    if isinstance(self.body, TypeExpression):
      return self.body.Type()
    return self.body


class TApply(Type):
  def __init__(self, fn: Type, arg: Type):
    if not isinstance(fn.kind, KArrow):
      raise TypeError(f'TApply must be used with type constructors, {fn}')
    if fn.kind.arg != arg.kind:
      raise TypeError(f'Mismatched kinds {fn} got {arg}')
    self.fn = fn
    self.arg = arg
    self.kind = fn.kind.ret

  def __str__(self):
    fn = self.FnType()
    fn_kind = str(fn.kind)[:-2]
    fn_str = str(fn)[:-(len(fn_kind) + 1)]
    if isinstance(fn, TApply):
      fn_str = fn_str[1:-1]
    arg = str(self.arg)
    arg_kind = str(self.arg.kind)[:-2]
    if arg.endswith(arg_kind):
      arg = arg[:-(len(arg_kind) + 1)]
    return f'({fn_str} {arg}):{self.kind}'[:-2]

  def FnType(self):
    if isinstance(self.fn, TypeExpression):
      return self.fn.Type()
    return self.fn

  def ArgType(self):
    if isinstance(self.arg, TypeExpression):
      return self.arg.Type()
    return self.arg


class TypeExpression(Type):
  typ: Type
  kind: Kind

  def __init__(self, typ: Type):
    match typ:
      case TypeExpression():
        self.typ = typ.Copy().typ
      case TypeVar():
        self.typ = FreeTypeVar(typ)
      case FreeTypeVar():
        self.typ = typ
      case BoundTypeVar():
        self.typ = typ
      case TArrow():
        self.typ = TArrow(TypeExpression(typ.arg), TypeExpression(typ.ret))
      case TApply():
        self.typ = TApply(TypeExpression(typ.fn), TypeExpression(typ.arg))
      case TAbstract():
        arg_t = typ.arg
        if not isinstance(arg_t, BindingTypeVar):
          arg_t = BindingTypeVar(arg_t)
        body_t = TypeExpression(typ.body)
        self.typ = TAbstract(arg_t, body_t)
      case _:
        raise NotImplementedError(
            f'Unexpected input to TypeExpression {type(typ)}'
        )
    self.kind = self.typ.kind
  
  def __str__(self):
    return str(self.typ)

  def __eq__(self, other):
    return TAlphaEquiv(self, other)

  def Type(self) -> Type:
    typ = self.typ
    if isinstance(typ, TOccurrence):
      typ = typ.typ
    return typ

  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    match self.typ:
      case TypeVar():
        raise Exception('Should not store TypeVar in Expression')
      case BindingTypeVar():
        raise Exception('Should not store BindingTypeVar in Expression')
      case FreeTypeVar():
        if btv.ShouldBind(self.typ):
          self.typ = BoundTypeVar(btv, self.typ)
      case BoundTypeVar():
        pass
      case TArrow():
        self.typ.arg.MaybeBindFreeTypesTo(btv)
        self.typ.ret.MaybeBindFreeTypesTo(btv)
      case TApply():
        self.typ.fn.MaybeBindFreeTypesTo(btv)
        self.typ.arg.MaybeBindFreeTypesTo(btv)
      case TAbstract():
        self.typ.body.MaybeBindFreeTypesTo(btv)
      case _:
        raise NotImplementedError(
            f'Unexpected member of TypeExpression {self.typ}'
        )
  
  def Copy(self) -> 'TypeExpression':
    match self.typ:
      case FreeTypeVar() | BoundTypeVar():
        return TypeExpression(self.Type())
      case TArrow():
        return TypeExpression(TArrow(self.typ.arg.Copy(), self.typ.ret.Copy()))
      case TApply():
        return TypeExpression(TApply(self.typ.fn.Copy(), self.typ.arg.Copy()))
      case TAbstract():
        btv = self.typ.arg
        return TypeExpression(TAbstract(btv.typ, self.typ.body.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of TypeExpression {self.typ}'
        )

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0


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
  def __init__(self, T: TypeExpression):
    match T.typ:
      case FreeTypeVar():
        self.elems = [T.typ]
      case TOccurrence():
        self.elems = []
      case TArrow():
        self.elems = (
            FreeTypeVars(T.typ.arg).elems + FreeTypeVars(T.typ.ret).elems
        )
      case TApply():
        self.elems = (
            FreeTypeVars(T.typ.fn).elems + FreeTypeVars(T.typ.arg).elems
        )
      case TAbstract():
        self.elems = FreeTypeVars(T.typ.body).elems
      case _:
        raise NotImplementedError(f'Unexpected input to FreeTypeVars {T.typ}')

  def ContainsBindingVar(self, btv: BindingTypeVar) -> bool:
    return self.Contains(btv.typ)


class Redexes(Multiset[Union[Type, 'Term']]):
  def __init__(self, M: Union[TypeExpression, Expression]):
    match M:
      case Expression():
        match M.term:
          case Occurrence():
            self.elems = []
          case Apply():
            self.elems = []
            if isinstance(M.term.FuncTerm(), Abstract):
              self.elems.append(M.term)
            self.elems.extend(Redexes(M.term.fn).elems)
            self.elems.extend(Redexes(M.term.arg).elems)
          case Abstract():
            self.elems = Redexes(M.term.body).elems
          case _:
            raise NotImplementedError(f'Unexpected input to Redexes {M}')
      case TypeExpression():
        match M.typ:
          case TOccurrence():
            self.elems = []
          case TArrow():
            self.elems = Redexes(M.typ.arg).elems + Redexes(M.typ.ret).elems
          case TApply():
            self.elems = []
            if isinstance(M.typ.fn.Type(), TAbstract):
              self.elems.append(M.typ)
            self.elems.extend(Redexes(M.typ.fn).elems)
            self.elems.extend(Redexes(M.typ.arg).elems)
          case TAbstract():
            self.elems = Redexes(M.typ.body).elems
          case _:
            raise NotImplementedError(f'Unexpected input to Redexes {M}')
      case _:
        raise NotImplementedError(f'Unexpected input to Redexes {M}')


def RenameType(
    T: TypeExpression, x: Union[BindingTypeVar, TypeVar], y: TypeVar
) -> TypeExpression:
  def _HasBindingType(T: TypeExpression, x: TypeVar) -> bool:
    match T.typ:
      case TOccurrence():
        return False
      case TArrow():
        return _HasBindingType(T.typ.arg, x) or _HasBindingType(T.typ.ret, x)
      case TApply():
        return _HasBindingType(T.typ.fn, x) or _HasBindingType(T.typ.arg, x)
      case TAbstract():
        if T.typ.arg.typ == x:
          return True
        return _HasBindingType(T.typ.body, x)
      case _:
        raise NotImplementedError(f'Unexpected input to HasBindingType {T}')

  def _RenameBoundTypes(
      T: TypeExpression, x: BindingTypeVar, y: BindingTypeVar
  ) -> TypeExpression:
    assert isinstance(x, BindingTypeVar) and isinstance(y, BindingTypeVar)
    match T.typ:
      case FreeTypeVar():
        return T
      case BoundTypeVar():
        if T.typ.bt == x:
          return TypeExpression(BoundTypeVar(y, FreeTypeVar(y.typ)))
        return T
      case TArrow():
        return TypeExpression(
            TArrow(
                _RenameBoundTypes(T.typ.arg, x, y),
                _RenameBoundTypes(T.typ.ret, x, y)
            )
        )
      case TApply():
        return TypeExpression(
            TApply(
                _RenameBoundTypes(T.typ.fn, x, y),
                _RenameBoundTypes(T.typ.arg, x, y)
            )
        )
      case TAbstract():
        return TypeExpression(
            TAbstract(T.typ.arg, _RenameBoundTypes(T.typ.body, x, y))
        )
      case _:
        raise NotImplementedError(f'Unexpected input to RenameBoundTypes {T}')

  match T.typ:
    case FreeTypeVar():
      if T.typ.typ == x:
        return TypeExpression(y)
      return TypeExpression(T.typ.typ)
    case BoundTypeVar():
      return T
    case TArrow():
      return TypeExpression(
          TArrow(RenameType(T.typ.arg, x, y), RenameType(T.typ.ret, x, y))
      )
    case TApply():
      return TypeExpression(
          TApply(RenameType(T.typ.fn, x, y), RenameType(T.typ.arg, x, y))
      )
    case TAbstract():
      if FreeTypeVars(T.typ.body).Contains(y):
        raise RenameFreeTypeVarError(f'{y} occurs free in {T.typ}')
      if _HasBindingType(T.typ.body, y):
        raise RenameBindingTypeVarError(f'{y} is a binding type in {T.typ}')
      arg_t = T.typ.arg
      U = T.typ.body
      if arg_t == x:
        new_arg_t = BindingTypeVar(y)
        U = _RenameBoundTypes(U, arg_t, new_arg_t)
      else:
        new_arg_t = arg_t
      return TypeExpression(TAbstract(new_arg_t, RenameType(U, x, y)))
    case _:
      raise NotImplementedError(f'Unexpected input to RenameType {T}')


def SubstituteType(
    T: TypeExpression,
    a: Union[BindingTypeVar, TypeVar],
    B: TypeExpression,
    new_types: list[TypeVar],
    binding: Optional[BindingTypeVar] = None,
) -> TypeExpression:
  match T.typ:
    case FreeTypeVar():
      if T.typ == a:
        return B
      return T
    case BoundTypeVar():
      if binding is not None and T.typ.BoundTo(binding):
        return B
      return T
    case TArrow():
      return TypeExpression(
          TArrow(
              SubstituteType(T.typ.arg, a, B, new_types, binding),
              SubstituteType(T.typ.ret, a, B, new_types, binding)
          )
      )
    case TApply():
      return TypeExpression(
          TApply(
              SubstituteType(T.typ.fn, a, B, new_types, binding),
              SubstituteType(T.typ.arg, a, B, new_types, binding)
          )
      )
    case TAbstract():
      if FreeTypeVars(B).Contains(T.typ.arg.typ):
        if not zs:
          raise Exception('Need more types for substitution')
        new_t = new_types.pop()
        assert not FreeTypeVars(B).Contains(new_t)
        T = RenameType(T, T.typ.arg, new_t)
      return TypeExpression(
          TAbstract(
              T.typ.arg, SubstituteType(T.typ.body, a, B, new_types, binding)
          )
      )
    case _:
      raise NotImplementedError(
          f'Unexpected term in type for SubstituteType {T}'
      )


def OneStepBetaReduceType(
    T: TypeExpression,
    new_types: list[TypeVar] = [],
    applicative=False
) -> TypeExpression:
  match T.typ:
    case TOccurrence():
      return T
    case TArrow():
      if not T.typ.fn.BetaNormal():
        return TypeExpression(
            TArrow(
                OneStepBetaReduceType(T.typ.fn, new_types, applicative),
                T.typ.ret
            )
        )
      return TypeExpression(
          TArrow(
              T.typ.fn,
              OneStepBetaReduceType(T.typ.ret, new_types, applicative)
          )
      )
    case TApply():
      # Applicative order: evaluate innermost-leftmost redex first.
      if applicative:
        if not T.typ.fn.BetaNormal():
          return TypeExpression(
              TApply(
                  OneStepBetaReduceType(T.typ.fn, new_types, applicative),
                  T.typ.arg
              )
          )
        if not T.typ.arg.BetaNormal():
          return TypeExpression(
              TApply(
                  T.typ.fn,
                  OneStepBetaReduceType(T.typ.arg, new_types, applicative)
              )
          )
        if isinstance(T.typ.fn.Type(), TAbstract):
          T, U = T.typ.fn, T.typ.arg
          return SubstituteType(T.typ.body, T.typ.arg, U, new_types, T.typ.arg)
        return T
      # Normal order: evaluate outermost-leftmost redex first.
      if isinstance(T.typ.fn.Type(), TAbstract):
        T, U = T.typ.fn, T.typ.arg
        return SubstituteType(T.typ.body, T.typ.arg, U, new_types, T.typ.arg)
      if T.typ.fn.BetaNormal():
        return TypeExpression(
            TApply(
                T.typ.fn,
                OneStepBetaReduceType(T.typ.arg, new_types, applicative)
            )
        )
      return TypeExpression(
          TApply(
              OneStepBetaReduceType(T.typ.fn, new_types, applicative),
              T.typ.arg
          )
      )
    case TAbstract():
      return TypeExpression(
          TAbstract(
              T.typ.arg,
              OneStepBetaReduceType(T.typ.body, new_types, applicative)
          )
      )
    case _:
      raise NotImplementedError(f'Unexpected input to OneStepBetaReduce {T}')


def BetaReduceType(
    T: TypeExpression,
    new_types: list[TypeVar] = [],
):
  # In λ2 all types are guaranteed to normalize.
  while not T.BetaNormal():
    T  = OneStepBetaReduceType(T, new_types)
  return T


def TBetaEquiv(a: TypeExpression, b: TypeExpression) -> bool:
  return BetaReduceType(a) == BetaReduceType(b)



class DeBrujinIndices(dict[Union[TypeVar, 'Var'], int]):
  def __str__(self):
    return str({str(k): str(v) for k, v in self.items()})

  def copy(self):
    return DeBrujinIndices(super().copy())


def TAlphaEquiv(
    x: TypeExpression, y: TypeExpression,
    de_brujin: Optional[DeBrujinIndices] = None
) -> bool:
  def _Helper(
      x: TypeExpression, y: TypeExpression, de_brujin: DeBrujinIndices
  ) -> bool:
    match x.typ:
      case FreeTypeVar():
        return isinstance(y.typ, FreeTypeVar) and x.typ == y.typ
      case BoundTypeVar():
        if not isinstance(y.typ, BoundTypeVar):
          return False
        xt = x.Type()
        yt = y.Type()
        if xt in de_brujin and yt in de_brujin:
          return de_brujin[xt] == de_brujin[yt]
        if xt not in de_brujin and yt not in de_brujin:
          return xt == yt
        return False
      case TArrow():
        return (
            isinstance(y.typ, TArrow)
            and _Helper(x.typ.arg, y.typ.arg, de_brujin)
            and _Helper(x.typ.ret, y.typ.ret, de_brujin)
        )
      case TApply():
        return (
            isinstance(y.typ, TApply)
            and _Helper(x.typ.fn, y.typ.fn, de_brujin)
            and _Helper(x.typ.arg, y.typ.arg, de_brujin)
        )
      case TAbstract():
        if not isinstance(y.typ, TAbstract):
          return False
        xt = x.typ.arg
        yt = y.typ.arg
        new_de_brujin = de_brujin.copy()
        new_de_brujin[xt.typ] = new_de_brujin[yt.typ] = len(de_brujin)
        return _Helper(x.typ.body, y.typ.body, new_de_brujin)
      case _:
        raise NotImplementedError(f'Unexpected input to AlphaEquiv {x}')
  return _Helper(x, y, de_brujin or DeBrujinIndices())


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Not implemented')

  def Type(self) -> Type:
    typ = self.typ
    if isinstance(typ, TypeExpression):
      typ = typ.typ
    if isinstance(typ, TOccurrence):
      typ = typ.typ
    assert (
        isinstance(typ, TypeVar)
        or isinstance(typ, TArrow)
        or isinstance(typ, TApply)
    )
    return typ


class Var(Term):
  def __init__(self, name: str, typ: Type):
    self.name = name
    self.typ = typ
    if not self.typ.Proper():
      raise TypeError(f'Can only create terms with proper type got {typ}')

  def __str__(self):
    line = f'{self.name}:{self.typ}'
    if line.endswith(':*'):
      line = line[:-2]
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
  def __eq__(self, other):
    return id(self) == id(other)

  def __init__(self, u: Var):
    assert isinstance(u, Var)
    self.var = u
    self.typ = TypeExpression(u.typ)
    self.var.typ = self.typ

  def __hash__(self):
    return id(self)

  def ShouldBind(self, fv: FreeVar) -> bool:
    return self.var == fv

  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    self.typ.MaybeBindFreeTypesTo(btv)


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


class FreeVars(Multiset[Var]):
  def __init__(self, e: Expression):
    match e.term:
      case FreeVar():
        self.elems = [e.term.var]
      case BoundVar():
        self.elems = []
      case Apply():
        self.elems = FreeVars(e.term.fn).elems + FreeVars(e.term.arg).elems
      case Abstract():
        self.elems = FreeVars(e.term.body).elems
      case _:
        raise NotImplementedError(f'Unexpected member of Expression {e.term}')

  def ContainsBindingVar(self, bv: BindingVar) -> bool:
    return self.Contains(bv.var)


class Apply(Term):
  def __init__(self, fn: Term, arg: Term):
    self.fn = fn
    self.arg = arg
    if not isinstance(fn.Type(), TArrow):
      raise TypeError(f'Left term of Apply must be Arrow type {fn.typ}')
    if fn.Type().arg.Type() != arg.Type():
      raise TypeError(f'Mismatched types {fn} got {arg}')
    self.typ = self.fn.Type().ret
    assert self.typ.Proper()

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
    self.typ = TArrow(self.arg.typ, self.body.typ)
    assert self.typ.Proper()

  def __str__(self):
    body = self.BodyTerm()
    args = str(self.arg)
    while isinstance(body, Abstract):
      args = body._AppendMultiArgStr(args, body)
      body = body.BodyTerm()
    typ = str(self.typ)
    return f'(λ{args}.{body}):{self.typ}'

  def BodyTerm(self) -> Term:
    if isinstance(self.body, Expression):
      return self.body.term
    return self.body

  def _AppendMultiArgStr(self, args_str, body) -> str:
    return args_str + f'.λ{body.arg}'


class Expression(Term):
  term: Term
  typ: TypeExpression

  def __init__(self, u: Term):
    match u:
      case Expression():
        self.term = u.Copy().term
      case Var():
        self.term = FreeVar(u)
      case FreeVar():
        self.term = u
      case BoundVar():
        self.term = u
      case Apply():
        self.term = Apply(Expression(u.fn), Expression(u.arg))
      case Abstract():
        v = u.arg
        if not isinstance(v, BindingVar):
          v = BindingVar(v)
        self.term = Abstract(v, Expression(u.body))
      case _:
        raise NotImplementedError(f'Unexpected input to Expression {type(u)}')
    self.SetType(TypeExpression(u.typ))

  def __str__(self):
    return str(self.term)

  def __eq__(self, other):
    return AlphaEquiv(self, other)

  def Closed(self) -> bool:
    return len(FreeVars(self)) == 0

  def SetType(self, typ: TypeExpression):
    self.typ = typ
    self.term.typ = typ
    if isinstance(self.term, Occurrence):
      self.term.var.typ = typ

  def MaybeBindFreeVarsTo(self, bv: BindingVar):
    match self.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case FreeVar():
        if bv.ShouldBind(self.term):
          self.term = BoundVar(bv, self.term)
      case BoundVar():
        pass
      case Apply():
        self.term.fn.MaybeBindFreeVarsTo(bv)
        self.term.arg.MaybeBindFreeVarsTo(bv)
      case Abstract():
        self.term.body.MaybeBindFreeVarsTo(bv)
      case _:
        raise NotImplementedError(
            f'Unexpected member of Expression {self.term}'
        )
  
  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    match self.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case Occurrence():
        pass
      case Apply():
        self.term.fn.MaybeBindFreeTypesTo(btv)
        self.term.arg.MaybeBindFreeTypesTo(btv)
      case Abstract():
        self.term.arg.typ.MaybeBindFreeTypesTo(btv)
        self.term.body.MaybeBindFreeTypesTo(btv)
      case _:
        raise NotImplementedError(f'Unexpected member of Expression {self.term}')
    self.typ.MaybeBindFreeTypesTo(btv)

  def Copy(self) -> 'Expression':
    match self.term:
      case FreeVar() | BoundVar():
        return Expression(self.term.var)
      case Apply():
        return Expression(Apply(self.term.fn.Copy(), self.term.arg.Copy()))
      case Abstract():
        bv = self.term.arg
        return Expression(Abstract(bv.var, self.term.body.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of Expression {self.term}'
        )
  
  def ReplaceType(
      self, old_t: TypeExpression, new_t: TypeExpression,
      binder_map: Optional[dict[BindingVar, BindingVar]] = None
  ) -> 'Expression':
    if binder_map is None:
      binder_map = {}
    match self.term:
      case FreeVar() | BoundVar():
        if TypeExpression(self.typ) != old_t:
          return self
        u = self.term.var
        u = Var(u.name, new_t)
        if isinstance(self.term, FreeVar) or self.term.bv not in binder_map:
          return Expression(FreeVar(u))
        return Expression(BoundVar(binder_map[self.term.bv], FreeVar(u)))
      case Apply():
        return Expression(
            Apply(
                self.term.fn.ReplaceType(old_t, new_t, binder_map),
                self.term.arg.ReplaceType(old_t, new_t, binder_map)
            )
        )
      case Abstract():
        u = self.term.arg.var
        if self.term.arg.typ == old_t:
          u = Var(u.name, new_t)
          u = binder_map[self.term.arg] = BindingVar(u)
        M = Expression(
            Abstract(u, self.term.body.ReplaceType(old_t, new_t, binder_map))
        )
        if M.typ == old_t:
          M.SetType(new_t)
        return M
    return self


class Statement:
  subj: Union[Kind, TypeExpression, Expression]
  typ: Union[TypeExpression, Kind, AllKinds]

  def __init__(self, subj: Union[Kind, TypeExpression, Expression]):
    self.subj = subj
    match subj:
      case Kind():
        self.typ = AllKinds()
      case TypeExpression():
        self.typ = subj.kind
      case Expression():
        self.typ = subj.typ
      case _:
        raise NotImplementedError(f'Unexpected input to Statement {subj}')

  def __str__(self):
    return str(self.subj)


class TypeDeclaration:
  def __init__(self, subj_t: TypeVar):
    if not isinstance(subj_t, TypeVar):
      raise ValueError(f'Cannot create TypeDeclaration with {subj_t}')
    self.subj = BindingTypeVar(subj_t)

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


class Context:
  def __init__(self, *args: list[Union[Kind, TypeVar, Var]]):
    self.typ_declarations = []
    self.var_declarations = []
    self.str_declarations = []  # To preserve order for printing only
    for u in args:
      match u:
        case TypeVar():
          u = TypeDeclaration(u)
          self.typ_declarations.append(u)
          self.str_declarations.append(u)
        case Var():
          for tv in FreeTypeVars(TypeExpression(u.typ)):
            if not self.ContainsTypeVar(tv.typ):
              raise ValueError(f'Context {self} does not contain free types in {u}')
          u = VarDeclaration(u)
          self.var_declarations.append(u)
          self.str_declarations.append(u)
        case _:
          raise NotImplementedError(f'Unexpected input to Context {u}')
    for u in self.var_declarations:
      for v in self.typ_declarations:
        u.subj.MaybeBindFreeTypesTo(v.subj)
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

  def BindStatementFreeVars(self, sttmt: Statement):
    if isinstance(sttmt.subj, Kind):
      return
    for decl in self.typ_declarations:
      sttmt.subj.MaybeBindFreeTypesTo(decl.subj)
    if isinstance(sttmt.subj, TypeExpression):
      return
    for decl in self.var_declarations:
      sttmt.subj.MaybeBindFreeVarsTo(decl.subj)

  def ContainsTypeVar(self, typ: TypeVar) -> bool:
    return self.Dom().ContainsTypeVar(typ)

  def ContainsVar(self, u: Var) -> bool:
    return self.Dom().ContainsVar(u)

  def Dom(self) -> Domain:
    return Domain(
        [decl.subj.typ for decl in self.typ_declarations],
        [decl.subj.var for decl in self.var_declarations]
    )

  def PushKind(self, kind: Kind) -> 'Context':
    return Context(*self.Dom(), kind)

  def PushTypeVar(self, u: TypeVar) -> 'Context':
    assert isinstance(u, TypeVar)
    if self.ContainsTypeVar(u):
      raise Exception(f'Context {self} contains {u}')
    return Context(*self.Dom(), u)

  def PushVar(self, u: Var):
    assert isinstance(u, Var)
    if self.ContainsVar(u):
      raise Exception(f'Context {self} contains {u}')
    if not self.ContainsFreeTypes(TypeExpression(u.typ)):
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

  def PullTypeVar(self, u: TypeVar) -> 'Context':
    if not self.ContainsTypeVar(u):
      raise Exception(f'Context {self} does not contain {u}')
    new_ctx = []
    for v in self.Dom():
      if isinstance(v, TypeVar) and u == v:
        continue
      new_ctx.append(v)
    return Context(*new_ctx)

  def ContainsFreeTypes(self, rho: TypeExpression):
    assert isinstance(rho, TypeExpression)
    return all(
        self.ContainsTypeVar(alpha.typ) for alpha in FreeTypeVars(rho)
    )

  def OverlappingUnion(self, other: 'Context') -> 'Context':
    assert self < other or other < self
    if self < other:
      return other
    return self


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
    return Judgement(self.ctx, Statement(Star()))


class VarRule(DerivationRule):
  def __init__(self, premiss: Judgement, u: Union[TypeVar, Var]):
    super().__init__(premiss)
    self.ctx = ctx = premiss.ctx
    match u:
      case TypeVar():
        if self.ctx.ContainsTypeVar(u):
          raise ValueError(
              f'Cannot create VarRule {u} already occurs in Context {ctx}'
          )
        if u.kind != Star() and premiss.stmt.subj != u.kind:
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
        if TypeExpression(premiss.stmt.subj) != TypeExpression(u.typ):
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
    assert p_ab.ctx == p_cs.ctx
    ab = p_ab.stmt.subj
    match ab:
      case Expression():
        if not isinstance(ab.term, BoundVar):
          raise TypeError(f'Invalid first premiss for WeakRule {p_ab}')
      case TypeExpression():
        assert isinstance(ab.typ, BoundTypeVar)
      case Kind():
        assert isinstance(ab, Kind)
      case _:
        raise NotImplementedError(
            f'Unexpected premiss for WeakRule {p_ab}'
        )
    cs = p_cs.stmt.subj
    match u:
      case Var():
        if p_ab.ctx.ContainsVar(u) or p_cs.ctx.ContainsVar(u):
          raise ValueError(f'Cannot redeclare variable {u}')
        if not isinstance(cs, TypeExpression) and cs.Type() != u.Type():
          raise TypeError(
              f'Invalid second premiss for WeakRule {p_cs} given {u}'
          )
      case TypeVar():
        if p_ab.ctx.ContainsTypeVar(u) or p_cs.ctx.ContainsTypeVar(u):
          raise ValueError(f'Cannot redeclare type variable {u}')
        if not isinstance(cs, Kind) and cs.kind != u.kind:
          raise TypeError(
              f'Invalid second premiss for WeakRule {p_cs} given {u} '
          )
    self.u = u
    self.ctx = p_ab.ctx

  def Conclusion(self) -> Judgement:
    p_ab, p_c = self.premisses
    ctx = self.ctx
    match self.u:
      case TypeVar():
        if not self.ctx.ContainsTypeVar(self.u):
          ctx = self.ctx.PushTypeVar(self.u)
        if isinstance(p_ab.stmt.subj, Kind):
          subj = p_ab.stmt.subj
        else:
          subj = p_ab.stmt.subj.Copy()
      case Var():
        if not self.ctx.ContainsVar(self.u):
          ctx = self.ctx.PushVar(self.u)
        subj = p_ab.stmt.subj.Copy()
    return Judgement(ctx, Statement(subj))


class FormRule(DerivationRule):
  def __init__(self, *premisses: Sequence[Judgement]):
    if len(premisses) != 2:
      raise ValueError('Can only create WeakRule with 2 Judgements')
    super().__init__(*premisses)
    p_a, p_b = self.premisses
    self.ctx = p_a.ctx.OverlappingUnion(p_b.ctx)
    a = p_a.stmt.subj
    b = p_b.stmt.subj
    match a:
      case Kind():
        if not isinstance(b, Kind):
          raise TypeError(f'FormRule premiss mismatch: {p_a} vs. {p_b}')
        self.ab = KArrow(a, b)
      case Type():
        if not isinstance(b, Type):
          raise TypeError(f'FormRule premiss mismatch:{p_a} vs. {p_b}')
        if not a.Proper() or not b.Proper():
          raise TypeError(f'FormRule premisses must be proper types: {p_a} and {p_b}')
        self.ab = TypeExpression(TArrow(a, b))
      case _:
        raise NotImplementedError(f'Unexpected input to FormRule {p_a}')

  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(self.ab))


class ApplRule(DerivationRule):
  def __init__(self, *premisses: Sequence[Judgement]):
    super().__init__(*premisses)
    if len(premisses) != 2:
      raise ValueError('Can only create ApplRule with 2 Judgements')
    p_mab, p_na = self.premisses
    self.ctx = p_mab.ctx.OverlappingUnion(p_na.ctx)
    match p_mab.stmt.subj:
      case TypeExpression():
        k_mab = p_mab.stmt.subj.kind
        if not isinstance(k_mab, KArrow):
          raise TypeError(f'Unexpected first premiss to ApplRule {p_mab}')
        if not isinstance(p_na.stmt.subj, TypeExpression):
          raise TypeError(f'Unexpected second premiss to ApplRule {p_na}')
        if k_mab.arg != p_na.stmt.subj.kind:
          raise TypeError(f'Unexpected second premiss to ApplRule {p_na}')
      case Expression():
        t_mab = p_mab.stmt.subj.Type()
        if not isinstance(t_mab, TArrow):
          raise TypeError(f'Unexpected first premiss to ApplRule {p_mab}')
        if not isinstance(p_na.stmt.subj, Expression):
          raise TypeError(f'Unexpected second premiss to ApplRule {p_na}')
        if t_mab.arg.Type() != p_na.stmt.subj.Type():
          raise TypeError(f'Unexpected second premiss to ApplRule {p_na}')
      case _:
        raise NotImplementedError(
            f'Unexpected first premiss to ApplRule {p_mab}'
        )
  
  def Conclusion(self):
    p_fn, p_arg = self.premisses
    fn = p_fn.stmt.subj
    arg = p_arg.stmt.subj
    match fn:
      case TypeExpression():
        subj = TypeExpression(TApply(fn, arg))
      case Expression():
        subj = Expression(Apply(fn, arg))
    return Judgement(self.ctx, Statement(subj))


class AbstRule(DerivationRule):
  def __init__(self, arg: Union[TypeVar, Var], *premisses: Sequence[Judgement]):
    super().__init__(*premisses)
    if len(premisses) != 2:
      raise ValueError('Can only create AbstRule with 2 Judgements')
    p_xamb, p_abs = self.premisses
    self.ctx = p_xamb.ctx.OverlappingUnion(p_abs.ctx)
    match arg:
      case TypeVar():
        if not isinstance(p_xamb.stmt.subj, TypeExpression):
          raise TypeError(f'Unexpected first premiss of AbstRule {p_xamb}')
        k_abst = KArrow(arg.kind, p_xamb.stmt.subj.kind)
        if not isinstance(p_abs.stmt.subj, Kind):
          raise TypeError(f'Unexpected second premiss of AbstRule {p_abs}')
        if k_abst != p_abs.stmt.subj:
          raise TypeError(f'Mismatched second premiss of AbstRule {p_abs}')
      case Var():
        if not isinstance(p_xamb.stmt.subj, Expression):
          raise TypeError(f'Unexpected first premiss of AbstRule {p_xamb}')
        t_abst = TArrow(arg.typ, p_xamb.stmt.subj.Type())
        if not isinstance(p_abs.stmt.subj, TypeExpression):
          raise TypeError(f'Unexpected second premiss of AbstRule {p_abs}')
        if not t_abst != p_abs.stmt.subj.Type():
          raise TypeError(f'Mismatched second premiss of AbstRule {p_abs}')
      case _:
        raise NotImplementedError(f'Unexpected input to AbstRule {arg}')
    self.arg = arg
  
  def Conclusion(self) -> Judgement:
    p = self.premisses[0]
    a = self.arg
    body = p.stmt.subj
    match body:
      case TypeExpression():
        subj = TypeExpression(TAbstract(a, body))
        ctx = self.ctx.PullTypeVar(a)
      case Expression():
        subj = Expression(Abstract(a, body))
        ctx = self.ctx.PullVar(a)
    return Judgement(ctx, Statement(subj))


class ConvRule(DerivationRule):
  def __init__(self, *premisses: Sequence[Judgement]):
    super().__init__(*premisses)
    if len(premisses) != 2:
      raise ValueError('Can only create ConvRule with 2 Judgements')
    p_ab, p_bs = self.premisses
    self.ctx = p_ab.ctx.OverlappingUnion(p_bs.ctx)
    if not isinstance(p_ab.stmt.subj, Expression):
      raise TypeError(f'Unexpected first premiss for ConvRule {p_ab}')
    if not isinstance(p_bs.stmt.subj, TypeExpression):
      raise TypeError(f'Unexpected second premiss for ConvRule {p_bs}')
    if not p_bs.stmt.subj.Type().Proper():
      raise TypeError(
          f'Second premiss for ConvRule should be proper type {p_bs}'
      )
    p_ab_t = p_ab.stmt.subj.typ
    if p_ab_t.kind != p_ab.stmt.subj.typ.kind:
      raise TypeError(f'Mismatched kind in ConvRule {p_ab} {p_bs}')
    if not TBetaEquiv(TypeExpression(p_ab_t), TypeExpression(p_bs.stmt.subj)):
      raise TypeError(
          f'Premisses must be β-equivalent {p_ab_t} {p_bs}'
      )

  def Conclusion(self) -> Judgement:
    p_ab, p_bs = self.premisses
    subj = p_ab.stmt.subj.ReplaceType(
        TypeExpression(p_ab.stmt.subj.typ), TypeExpression(p_bs.stmt.subj)
    )
    return Judgement(self.ctx, Statement(subj))


class Derivation:
  def __init__(self, ctx: Context):
    # All derivations in this system start with (sort).
    self.ctx = ctx
    self.rules: list[DerivationRule] = []
    self.conclusions: list[Judgement] = []
    self.SortRule()

  def SortRulePremiss(self) -> Judgement:
    return self.conclusions[0]

  def _AddRule(self, rule: DerivationRule) -> Judgement:
    self.rules.append(rule)
    self.rules[-1].ctx = self.ctx
    concl = rule.Conclusion()
    self.ctx = concl.ctx
    self.conclusions.append(concl)
    return concl

  def PremissForType(self, typ: Type):
    for concl in self.conclusions:
      if not isinstance(concl.stmt.subj, TypeExpression):
        continue
      if TypeExpression(typ) == TypeExpression(concl.stmt.subj):
        return concl
    return None

  def SortRule(self) -> Judgement:
    sort_rule = SortRule(self.ctx)
    self.rules.append(sort_rule)
    concl = sort_rule.Conclusion()
    self.conclusions.append(concl)
    return concl

  def VarRule(self, u: Union[TypeVar, Var]) -> Judgement:
    premiss = None
    for i, rule in enumerate(self.rules):
      if isinstance(rule, FormRule) and premiss is None:
        if isinstance(u, TypeVar):
          if isinstance(rule.ab, Kind) and rule.ab == u.kind:
            premiss = self.conclusions[i]
        else:
          assert isinstance(u, Var)
          if (
              isinstance(rule.ab, TypeExpression)
              and rule.ab == TypeExpression(u.Type())
          ):
            premiss = self.conclusions[i]
      if isinstance(rule, VarRule):
        match (u, rule.u):
          case (TypeVar(), TypeVar()):
            if rule.u == u and self.ctx.ContainsTypeVar(u):
              return self.conclusions[i]
          case (Var(), Var()):
            if rule.u == u and self.ctx.ContainsVar(u):
              return self.conclusions[i]
    if isinstance(u, Var):
      assert u.Type().Proper()
      premiss = self.PremissForType(u.Type())
      assert premiss is not None
    if premiss is None:
      assert isinstance(u, TypeVar), type(u)
      assert u.Proper(), u
      if not isinstance(self.rules[-1], SortRule):
        self.SortRule()
      premiss = self.conclusions[-1]
    return self._AddRule(VarRule(premiss, u))

  def WeakRule(
      self, u: Union[TypeVar, Var], p_ab: Judgement, p_cs: Judgement
  ) -> Judgement:
    assert p_ab in self.conclusions
    assert p_cs in self.conclusions
    assert p_ab.ctx < self.ctx and p_cs.ctx < self.ctx
    return self._AddRule(WeakRule(u, p_ab, p_cs))

  def FormRule(self, p_a: Judgement, p_b: Judgement) -> Judgement:
    assert p_a in self.conclusions
    assert p_b in self.conclusions
    return self._AddRule(FormRule(p_a, p_b))

  def ApplRule(self, p_mab: Judgement, p_na: Judgement) -> Judgement:
    assert p_mab in self.conclusions
    assert p_na in self.conclusions
    return self._AddRule(ApplRule(p_mab, p_na))

  def AbstRule(
      self, arg: Union[TypeVar, Var], p_xamb: Judgement, p_abs: Judgement
  ) -> Judgement:
    assert p_xamb in self.conclusions
    assert p_abs in self.conclusions
    return self._AddRule(AbstRule(arg, p_xamb, p_abs))

  def ConvRule(self, p_ab: Judgement, p_bs: Judgement) -> Judgement:
    assert p_ab in self.conclusions
    assert p_bs in self.conclusions
    return self._AddRule(ConvRule(p_ab, p_bs))

  def ContainsKind(self, kind) -> bool:
    for concl in self.conclusions:
      if isinstance(concl.stmt.subj, Kind) and concl.stmt.subj == kind:
        return True
    return False
  
  def _Justification(
      self, rule: DerivationRule, keys: dict[Judgement, str]
  ) -> str:
    match rule:
      case SortRule():
        return '(sort)'
      case VarRule():
        typ_key = keys[rule.premisses[0]]
        return f'(var) on ({typ_key})'
      case WeakRule():
        ab_key = keys[rule.premisses[0]]
        cs_key = keys[rule.premisses[1]]
        return f'(weak) on ({ab_key}) and ({cs_key})'
      case FormRule():
        as_key = keys[rule.premisses[0]]
        bs_key = keys[rule.premisses[1]]
        return f'(form) on ({as_key}) and ({bs_key})'
      case ApplRule():
        mab_key = keys[rule.premisses[0]]
        na_key = keys[rule.premisses[1]]
        return f'(appl) on ({mab_key}) and ({na_key})'
      case AbstRule():
        xamb_key = keys[rule.premisses[0]]
        abs_key = keys[rule.premisses[1]]
        return f'(abst) on ({xamb_key}) and ({abs_key})'
      case ConvRule():
        ab_key = keys[rule.premisses[0]]
        bs_key = keys[rule.premisses[1]]
        return f'(conv) on ({ab_key}) and ({bs_key})'
      case _:
        raise ValueError(f'Unexpected input to Justification {rule}')

  def LinearFormat(self) -> str:
    result = []
    keys: dict[Judgement, str] = {}
    for rule, concl in zip(self.rules, self.conclusions):
      key = chr(ord('a') + len(keys))
      keys[concl] = key
      justif = self._Justification(rule, keys)
      line = f'({key}) {concl}    {justif}'
      result.append(line)
      result.append('-' * len(line))
    return '\n'.join(result)

  def FlagFormat(self) -> str:
    result = []
    indent_count = 0
    keys: dict[Judgement, str] = {}
    for rule, concl in zip(self.rules, self.conclusions):
      indent = '| ' * indent_count
      key = chr(ord('a') + len(keys))
      keys[concl] = key
      justif = self._Justification(rule, keys)
      match rule:
        case SortRule():
          line = f'({key}) {indent}{concl.stmt}    {justif}'
        case VarRule():
          if isinstance(concl.stmt.subj, TypeExpression):
            decl = concl.stmt.subj.Type()
          else:
            assert isinstance(concl.stmt.subj, Expression)
            decl = concl.stmt.subj.term.var
          seperator = (
              ' ' * len(f'({key}) ')
              + '| ' * indent_count
              + '|'
              + '-' * (len(str(decl)) + 3)
          )
          line = f'{' ' * (len(key) + 2)} {indent}| {decl} |'
          result.extend([seperator, line, seperator])
          indent_count += 1
          indent = '| ' * indent_count
          line = f'({key}) {indent}{concl.stmt}    {justif}'
        case AbstRule():
          indent_count -= 1
          indent = '| ' * indent_count
          line = f'({key}) {indent}{concl.stmt}    {justif}'
        case DerivationRule():
          line = f'({key}) {indent}{concl.stmt}    {justif}'
      result.append(line)
      result.append(f'    {indent[:-1]}' + '-' * (len(line) - len(indent) - 3))
    return '\n'.join(result)

  def _PremissForVarIdx(self, u: Union[TypeVar, Var]):
    for i, rule in enumerate(self.rules):
      if not isinstance(rule, VarRule):
        continue
      match (u, rule.u):
        case (TypeVar(), TypeVar()):
          if u == rule.u:
            return i
        case (Var(), Var()):
          if u == rule.u:
            return i
    raise ValueError(f'{u} not declared')

  def AppendRules(self, other: 'Derivation'):
    premiss_map: dict[str, int] = {}
    def _LookupPremiss(premiss: Judgement):
      return self.conclusions[premiss_map[str(premiss)]]
    for rule in other.rules:
      match rule:
        case SortRule():
          premiss_map[str(rule.Conclusion())] = 0
          continue
        case VarRule():
          p = rule.premisses[0]
          p = _LookupPremiss(p)
          if isinstance(rule.u, TypeVar):
            if self.ctx.ContainsTypeVar(rule.u):
              premiss_map[str(rule.Conclusion())] = self._PremissForVarIdx(
                  rule.u
              )
              continue
          else:
            assert isinstance(rule.u, Var)
            if self.ctx.ContainsVar(rule.u):
              premiss_map[str(rule.Conclusion())] = self._PremissForVarIdx(
                  rule.u
              )
              continue
          self._AddRule(VarRule(p, rule.u))
        case WeakRule():
          p1, p2 = rule.premisses
          p1, p2 = _LookupPremiss(p1), _LookupPremiss(p2)
          self._AddRule(WeakRule(rule.u, p1, p2))
        case FormRule():
          p1, p2 = rule.premisses
          p1, p2 = _LookupPremiss(p1), _LookupPremiss(p2)
          self._AddRule(FormRule(p1, p2))
        case ApplRule():
          p1, p2 = rule.premisses
          p1, p2 = _LookupPremiss(p1), _LookupPremiss(p2)
          self._AddRule(ApplRule(p1, p2))
        case AbstRule():
          p1, p2 = rule.premisses
          p1, p2 = _LookupPremiss(p1), _LookupPremiss(p2)
          self._AddRule(AbstRule(rule.arg, p1, p2))
        case ConvRule():
          p1, p2 = rule.premisses
          p1, p2 = _LookupPremiss(p1), _LookupPremiss(p2)
          self._AddRule(ConvRule(p1, p2))
      premiss_map[str(rule.Conclusion())] = len(self.rules) - 1


def DeriveKind(jdgmnt: Judgement) -> Derivation:
  if not isinstance(jdgmnt.stmt.subj, Kind):
    raise TypeError(f'Unexpected subject in judgement {jdgmnt}')
  d = Derivation(jdgmnt.ctx)
  def _Helper(kind: Kind):
    match kind:
      case Star():
        if isinstance(d.rules[-1], SortRule):
          return d.conclusions[-1]
        return d.SortRule()
      case KArrow():
        return d.FormRule(_Helper(kind.arg), _Helper(kind.ret))
      case _:
        raise NotImplementedError(f'Unexpected subject in judgement {jdgmnt}')
  _Helper(jdgmnt.stmt.subj)
  assert d.ctx == jdgmnt.ctx
  return d


def DeriveType(jdgmnt: Judgement) -> Derivation:
  if not isinstance(jdgmnt.stmt.subj, TypeExpression):
    raise TypeError(f'Unexpected subject in judgement {jdgmnt}')
  d = Derivation(Context())
  def _Helper(T: TypeExpression):
    match T.typ:
      case FreeTypeVar():
        if not d.ContainsKind(T.kind):
          d.AppendRules(
              DeriveKind(Judgement(Context(), Statement(T.typ.kind)))
          )
        return d.VarRule(T.Type())
      case BoundTypeVar():
        raise ValueError(f'Should not need rule for bound type {T.typ}')
      case TArrow():
        return d.FormRule(_Helper(T.typ.arg), _Helper(T.typ.ret))
      case TApply():
        return d.ApplRule(_Helper(T.typ.fn), _Helper(T.typ.arg))
      case TAbstract():
        if not d.ctx.ContainsTypeVar(T.typ.arg.typ):
          if not d.ContainsKind(T.typ.arg.typ.kind):
            d.AppendRules(
                DeriveKind(Judgement(Context(), Statement(T.typ.arg.typ.kind)))
            )
          d.VarRule(T.typ.arg.typ)
        if T.Proper():
          d.SortRule()
        else:
          d.AppendRules(DeriveKind(Judgement(Context(), Statement(T.kind))))
        p_t = d.conclusions[-1]
        return d.AbstRule(T.typ.arg.typ, _Helper(TypeExpression(T.typ.body)), p_t)
  _Helper(TypeExpression(jdgmnt.stmt.subj))
  assert d.ctx == jdgmnt.ctx
  return d


def DeriveTerm(jdgmnt: Judgement) -> Derivation:
  if not isinstance(jdgmnt.stmt.subj, Expression):
    raise TypeError(f'Unexpected subject in judgement {jdgmnt}')
  d = Derivation(Context())
  def _Helper(M: Expression):
    # Currently assumes β-normal form is in context.
    # Does not support when the context has the unreduced form.
    if not M.term.typ.BetaNormal():
      t = BetaReduceType(TypeExpression(M.typ))
      N = M.Copy()
      N.SetType(t)
      _Helper(N)
      p1 = d.conclusions[-1]
      ctx_types = [t.typ for t in FreeTypeVars(M.typ)]
      d.AppendRules(
          DeriveType(Judgement(Context(*ctx_types), Statement(M.term.typ)))
      )
      p2 = d.conclusions[-1]
      return d.ConvRule(p1, p2)
    match M.term:
      case FreeVar():
        if d.PremissForType(TypeExpression(M.typ)) is None:
          ctx_types = [t.typ for t in FreeTypeVars(M.typ)]
          d.AppendRules(
              DeriveType(Judgement(Context(*ctx_types), Statement(M.typ)))
          )
        return d.VarRule(M.term.var)
      case BoundVar():
        raise ValueError(f'Should not need rule for bound var {M.term}')
      case Apply():
        return d.ApplRule(_Helper(M.term.fn), _Helper(M.term.arg))
      case Abstract():
        p_body = _Helper(Expression(M.term.body))
        if not d.ctx.ContainsVar(M.term.arg.var):
          if d.PremissForType(TypeExpression(M.term.arg.typ)) is None:
            ctx_types = [t.typ for t in FreeTypeVars(M.typ)]
            d.AppendRules(
                DeriveType(Judgement(Context(*ctx_types), Statement(M.typ)))
            )
          d.VarRule(M.term.arg.var)
        p_t = d.PremissForType(TypeExpression(M.Type()))
        if p_t is None:
          ctx_types = [t.typ for t in FreeTypeVars(M.typ)]
          d.AppendRules(
              DeriveType(Judgement(Context(*ctx_types), Statement(M.typ)))
          )
          p_t = d.conclusions[-1]
        return d.AbstRule(M.term.arg.var, p_body, p_t)
  _Helper(Expression(jdgmnt.stmt.subj))
  assert d.ctx == jdgmnt.ctx
  return d
