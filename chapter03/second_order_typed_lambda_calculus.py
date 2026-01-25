"""
Chapter 3: Second Order Typed Lambda Calculus
=============================================

"""


from typing import Optional, Union


class Type:
  def __str__(self):
    raise NotImplementedError('Do not cast Type subclass to str')


class TypeVar(Type):
  def __init__(self, name: str):
    self.name = name

  def __str__(self):
    return self.name


class TOccurrence:
  def __init__(self, typ: TypeVar):
    self.typ = typ
  
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

  def __str__(self):
    return str(self.typ) + ':*'
  
  def ShouldBind(self, ftyp: FreeTypeVar) -> bool:
    return self.typ == ftyp


class BoundTypeVar(TOccurrence):
  def __init__(self, bt: BindingTypeVar, ftyp: FreeTypeVar):
    assert isinstance(bt, BindingTypeVar)
    assert isinstance(ftyp, FreeTypeVar)
    self.bt = bt
    self.typ = ftyp.typ
    if self.bt.typ != self.typ:
      raise TypeError(
          f'Cannot bind variable with type {self.bt} '
          f'to variable with type {self.typ}'
      )

  def BoundTo(self, bt: BindingTypeVar) -> bool:
    return self.bt == bt


class Arrow(Type):
  def __init__(self, arg: Type, ret: Type):
    self.arg = arg
    self.ret = ret

  def __str__(self):
    # Right associative, Apply is left associative.
    ret = self.Ret()
    ret_str = str(ret)
    if isinstance(ret, Arrow):
      ret_str = ret_str[1:-1]
    return f'({self.arg} -> {ret_str})'

  def Arg(self):
    if isinstance(self.arg, ExpressionType):
      return self.arg.Type()
    return self.arg

  def Ret(self):
    if isinstance(self.ret, ExpressionType):
      return self.ret.Type()
    return self.ret

  def __eq__(self, other):
    assert isinstance(other, Type)
    if not isinstance(other, Arrow):
      return False
    return (self.Arg(), self.Ret()) == (other.Arg(), other.Ret())


class PiType(Type):
  def __init__(self, arg: Union[TypeVar, BindingTypeVar], body: Type):
    self.arg = arg
    self.body = body

  def __str__(self):
    body = self.BodyType()
    args = str(self.arg)
    if isinstance(body, PiType):
      while isinstance(body, PiType):
        args = f'{args[:-2]},{body.arg}'
        body = body.BodyType()
    return f'Π{args}.{body}'

  def __eq__(self, other):
    return TAlphaEquiv(ExpressionType(self), ExpressionType(other))
  
  def BodyType(self):
    if isinstance(self.body, ExpressionType):
      return self.body.typ
    return self.body


class ExpressionType(Type):
  typ: Type

  def __init__(self, typ: Type):
    match typ:
      case ExpressionType():
        self.typ = typ.Copy().typ
      case TypeVar():
        self.typ = FreeTypeVar(typ)
      case FreeTypeVar():
        self.typ = typ
      case BoundTypeVar():
        self.typ = typ
      case Arrow():
        self.typ = Arrow(ExpressionType(typ.arg), ExpressionType(typ.ret))
      case PiType():
        arg_t = typ.arg
        if not isinstance(arg_t, BindingTypeVar):
          arg_t = BindingTypeVar(arg_t)
        body_t = ExpressionType(typ.body)
        body_t.MaybeBindFreeTypesTo(arg_t)
        self.typ = PiType(arg_t, body_t)
      case _:
        raise NotImplementedError(
            f'Unexpected input to TypeExpression {type(typ)}'
        )
  
  def __str__(self):
    return str(self.typ)

  def __eq__(self, other):
    if isinstance(other, ExpressionType):
      return TAlphaEquiv(self, other)
    assert isinstance(other, Type)
    return self.typ == other
  
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
      case Arrow():
        self.typ.arg.MaybeBindFreeTypesTo(btv)
        self.typ.ret.MaybeBindFreeTypesTo(btv)
      case PiType():
        self.typ.body.MaybeBindFreeTypesTo(btv)
      case _:
        raise NotImplementedError(f'Unexpected member of ExpressionType {self.typ}')
  
  def Copy(self) -> 'ExpressionType':
    match self.typ:
      case FreeTypeVar() | BoundTypeVar():
        return ExpressionType(self.typ.typ)
      case Arrow():
        return ExpressionType(Arrow(self.typ.arg.Copy(), self.typ.ret.Copy()))
      case PiType():
        btv = self.typ.arg
        return ExpressionType(PiType(btv.typ, self.typ.body.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of ExpressionType {self.typ}'
        )


class RenameFreeTypeVarError(Exception):
  pass


class RenameBindingTypeVarError(Exception):
  pass


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
  def __init__(self, T: ExpressionType):
    match T.typ:
      case FreeTypeVar():
        self.elems = [T.typ]
      case TOccurrence():
        self.elems = []
      case Arrow():
        self.elems = FreeTypeVars(T.typ.arg).elems + FreeTypeVars(T.typ.ret).elems
      case PiType():
        self.elems = FreeTypeVars(T.typ.body).elems
      case _:
        raise NotImplementedError(f'Unexpected input to OccursFree {T}')

  def ContainsBindingVar(self, bv: BindingVar):
    return self.Contains(bv.var)


def RenameType(
    T: ExpressionType, x: Union[BindingTypeVar, TypeVar], y: TypeVar
) -> ExpressionType:
  def _HasBindingType(T: ExpressionType, x: TypeVar) -> bool:
    match T.typ:
      case TOccurrence():
        return False
      case Arrow():
        return _HasBindingType(T.typ.arg, x) or _HasBindingType(T.typ.ret, x)
      case PiType():
        if T.typ.arg.typ == x:
          return True
        return _HasBindingType(T.typ.body, x)
      case _:
        raise NotImplementedError(f'Unexpected input to HasBindingType {T}')

  def _RenameBoundTypes(
      T: ExpressionType, x: BindingTypeVar, y: BindingTypeVar
  ) -> ExpressionType:
    assert isinstance(x, BindingTypeVar) and isinstance(y, BindingTypeVar)
    if isinstance(T.typ, FreeTypeVar):
      return T
    if isinstance(T.typ, BoundTypeVar):
      if T.typ.bt == x:
        return ExpressionType(BoundTypeVar(y, FreeTypeVar(y.typ)))
      return T
    if isinstance(T.typ, Arrow):
      return ExpressionType(
          Arrow(
              _RenameBoundTypes(T.typ.arg, x, y),
              _RenameBoundTypes(T.typ.ret, x, y)
          )
      )
    if isinstance(T.typ, PiType):
      return ExpressionType(
          PiType(T.typ.arg, _RenameBoundTypes(T.typ.body, x, y))
      )
    else:
      raise NotImplementedError(f'Unexpected input to RenameBoundTypes {T}')

  if isinstance(T.typ, FreeTypeVar):
    if T.typ.typ == x:
      return ExpressionType(y)
    return ExpressionType(T.typ.typ)
  if isinstance(T.typ, BoundTypeVar):
    return T
  if isinstance(T.typ, Arrow):
    return ExpressionType(
        Arrow(RenameType(T.typ.arg, x, y), RenameType(T.typ.ret, x, y))
    )
  if isinstance(T.typ, PiType):
    if FreeTypeVars(T.typ.body).Contains(y):
      raise RenameFreeTypeVarError(f'{y} occurs free in {T.typ}')
    if _HasBindingType(T.typ.body, y):
      raise RenameBindingTypeVarError(f'{y} is a binding type in {T.typ}')
    arg_t = T.typ.arg
    U = T.typ.body
    if arg_t == x:
      new_arg_t = BindingTypeVar(y)
      U = _RenameBoundTypes(U, arg_t, new_arg_t)
      U.MaybeBindFreeTypesTo(new_arg_t)
    else:
      new_arg_t = arg_t
    return ExpressionType(PiType(new_arg_t, RenameType(U, x, y)))


class DeBrujinIndices(dict[Union[TypeVar, 'Var'], int]):
  def __str__(self):
    return str({str(k): str(v) for k, v in self.items()})

  def copy(self):
    return DeBrujinIndices(super().copy())


def TAlphaEquiv(
    x: ExpressionType, y: ExpressionType,
    de_brujin: Optional[DeBrujinIndices] = None
) -> bool:
  def _Helper(
      x: ExpressionType, y: ExpressionType, de_brujin: DeBrujinIndices
  ) -> bool:
    if isinstance(x.typ, FreeTypeVar):
      return isinstance(y.typ, FreeTypeVar) and x.typ == y.typ
    if isinstance(x.typ, BoundTypeVar):
      if not isinstance(y.typ, BoundTypeVar):
        return False
      xt = x.Type()
      yt = y.Type()
      if xt in de_brujin and yt in de_brujin:
        return de_brujin[xt] == de_brujin[yt]
      if xt not in de_brujin and yt not in de_brujin:
        return xt == yt
      return False
    if isinstance(x.typ, Arrow):
      return (
          isinstance(y.typ, Arrow)
          and _Helper(x.typ.arg, y.typ.arg, de_brujin)
          and _Helper(x.typ.ret, y.typ.ret, de_brujin)
      )
    if isinstance(x.typ, PiType):
      if not isinstance(y.typ, PiType):
        return False
      xt = x.typ.arg
      yt = y.typ.arg
      new_de_brujin = de_brujin.copy()
      new_de_brujin[xt.typ] = new_de_brujin[yt.typ] = len(de_brujin)
      return _Helper(x.typ.body, y.typ.body, new_de_brujin)
    raise NotImplementedError(f'Unexpected input to AlphaEquiv {x}')
  return _Helper(x, y, de_brujin or DeBrujinIndices())


def SubstituteType(
    T: ExpressionType,
    a: Union[BindingTypeVar, TypeVar],
    B: ExpressionType,
    new_types: list[TypeVar],
    binding: Optional[BindingTypeVar] = None,
) -> ExpressionType:
  match T.typ:
    case FreeTypeVar():
      if T.typ == a:
        return B
      return T
    case BoundTypeVar():
      if binding is not None and T.typ.BoundTo(binding):
        return B
      return T
    case Arrow():
      return ExpressionType(
          Arrow(
              SubstituteType(T.typ.arg, a, B, new_types, binding),
              SubstituteType(T.typ.ret, a, B, new_types, binding)
          )
      )
    case PiType():
      if FreeTypeVars(B).Contains(T.typ.arg.typ):
        if not zs:
          raise Exception('Need more types for substitution')
        new_t = new_types.pop()
        assert not TypeOccuresFree(B, new_t)
        T = RenameTerm(T, T.typ.arg, new_t)
      return ExpressionType(
          PiType(T.typ.arg, SubstituteType(T.typ.body, a, B, new_types, binding))
      )
    case _:
      raise NotImplementedError(f'Unexpected term in type for SubstituteType {T}')


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Not implemented')

  def Type(self):
    typ = self.typ
    if isinstance(typ, ExpressionType):
      typ = typ.typ
    if isinstance(typ, TOccurrence):
      typ = typ.typ
    assert (
      isinstance(typ, TypeVar)
      or isinstance(typ, Arrow)
      or isinstance(typ, PiType)
    )
    return typ


class Var(Term):
  def __init__(self, name: str, typ: Type):
    self.name = name
    self.typ = typ

  def __str__(self):
    return f'{self.name}:{self.typ}'

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
    self.typ = u.typ

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
    self.typ = ExpressionType(u.typ)

  def __hash__(self):
    return id(self)

  def ShouldBind(self, fv: FreeVar) -> bool:
    return self.var == fv


class BoundVar(Occurrence):
  def __init__(self, bv: BindingVar, fv: FreeVar):
    self.bv = bv
    self.var = fv.var
    bv_typ = self.bv.typ
    if isinstance(bv_typ, ExpressionType):
      bv_typ = bv_typ.Type()
    if bv_typ != self.var.Type():
      raise TypeError(
          f'Cannot bind variable with type {bv_typ} '
          f'to variable with type {self.var.typ}'
      )
    self.typ = fv.typ

  def __str__(self):
    # Bound variables omit types.
    return str(self.var).split(':')[0]

  def BoundTo(self, bv: BindingVar) -> bool:
    return self.bv == bv


class Apply(Term):
  def __init__(self, fn: Term, arg: Term):
    self.fn = fn
    self.arg = arg
    if not isinstance(fn.Type(), Arrow):
      raise TypeError(f'Left term of Apply must be Arrow type {fn.typ}')
    if fn.Type().arg != arg.typ:
      raise TypeError(f'Expected type {fn.Type().arg} got {arg.typ}')
    self.typ = self.fn.Type().ret

  def __str__(self):
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    fn_str = str(fn)
    if isinstance(fn, Apply):
      fn_str = '):'.join(fn_str.split('):')[:-1])[1:]
    arg = str(self.arg)
    if ':' in arg and not isinstance(self.arg.term, FreeVar):
      arg = ':'.join(arg.split(':')[:-1])
    return f'({fn_str} {arg}):{self.typ}'

  def FuncTerm(self) -> Term:
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    return fn


class TApply(Apply):
  def __init__(
      self, fn: Term, arg: Type,
      # In case `arg` is a binding type variable in `fn`'s Π-type.
      new_types: list[TypeVar] = []
  ):
    fn_type = fn.Type()
    if not isinstance(fn_type, PiType):
      raise TypeError(f'TApply must be used on Π-types, got {fn_type}')
    self.fn = fn
    assert not isinstance(arg, PiType)
    self.arg = arg
    self.new_types = new_types
    bound_var = fn_type.arg
    body_type = fn_type.body
    self.typ = SubstituteType(
        ExpressionType(body_type),
        bound_var,
        ExpressionType(arg),
        new_types,
        bound_var if isinstance(bound_var, BindingTypeVar) else None
    )


class Abstract(Term):
  def __init__(self, arg: Union[Var, BindingVar], body: Term):
    self.arg = arg
    self.body = body
    self.typ = Arrow(self.arg.typ, self.body.typ)

  def __str__(self):
    body = self.BodyTerm()
    args = str(self.arg)
    while isinstance(body, Abstract):
      args = body._AppendMultiArgStr(args, body)
      body = body.BodyTerm()
    body_str = str(body)
    if ':' in body_str and isinstance(body, Apply):
      body_str = ':'.join(body_str.split(':')[:-1])
    if isinstance(body, TAbstract):
      body_str = 'Π'.join(body_str.split('Π')[:-1])
    return f'(λ{args}.{body_str}):{self.typ}'

  def BodyTerm(self) -> Term:
    if isinstance(self.body, Expression):
      return self.body.term
    return self.body

  def _AppendMultiArgStr(self, args_str, body):
    return args_str + f'.λ{body.arg}'


class TAbstract(Abstract):
  def __init__(self, arg: Union[TypeVar, BindingTypeVar], body: Term):
    self.arg = arg
    self.body = body
    self.typ = PiType(arg, body.typ)

  def _AppendMultiArgStr(self, args_str, body):
    if isinstance(body, TAbstract) and args_str[-2:] == ':*':
      args_str = args_str[:-2]
      return args_str + f',{body.arg}'
    return args_str + f'.λ{body.arg}'


class Expression(Term):
  term: Term
  typ: ExpressionType

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
      case TApply():
        self.term = TApply(
            Expression(u.fn), ExpressionType(u.arg), u.new_types,
        )
      case Apply():
        self.term = Apply(Expression(u.fn), Expression(u.arg))
      case TAbstract():
        arg_t = u.arg
        if not isinstance(arg_t, BindingTypeVar):
          arg_t = BindingTypeVar(arg_t)
        body = Expression(u.body)
        body.MaybeBindFreeTypesTo(arg_t)
        self.term = TAbstract(arg_t, body)
      case Abstract():
        v = u.arg
        if not isinstance(v, BindingVar):
          v = BindingVar(v)
        body = Expression(u.body)
        body.MaybeBindFreeVarsTo(v)
        self.term = Abstract(v, body)
      case _:
        raise NotImplementedError(f'Unexpected input to Expression {type(u)}')
    self.SetType(ExpressionType(u.typ))

  def __str__(self):
    return str(self.term)

  def __eq__(self, other):
    return AlphaEquiv(self, other)

  def Closed(self) -> bool:
    return len(FreeVars(self)) == 0

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0

  def SetType(self, typ: ExpressionType):
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
      case TApply():
        self.term.fn.MaybeBindFreeVarsTo(bv)
      case Apply():
        self.term.fn.MaybeBindFreeVarsTo(bv)
        self.term.arg.MaybeBindFreeVarsTo(bv)
      case Abstract():
        self.term.body.MaybeBindFreeVarsTo(bv)
      case _:
        raise NotImplementedError(f'Unexpected member of Expression {self.term}')
  
  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    match self.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case Occurrence():
        if btv.ShouldBind(self.term.typ.typ):
          self.typ.MaybeBindFreeTypesTo(btv)
          self.SetType(self.typ)
      case Apply():
        self.term.fn.MaybeBindFreeTypesTo(btv)
        self.term.arg.MaybeBindFreeTypesTo(btv)
      case TAbstract():
        self.term.body.MaybeBindFreeTypesTo(btv)
      case Abstract():
        self.term.arg.typ.MaybeBindFreeTypesTo(btv)
        self.term.body.MaybeBindFreeTypesTo(btv)
      case _:
        raise NotImplementedError(f'Unexpected member of Expression {self.term}')
    self.typ.MaybeBindFreeTypesTo(btv)

  def Copy(self):
    match self.term:
      case FreeVar() | BoundVar():
        return Expression(self.term.var)
      case TApply():
        return Expression(TApply(self.term.fn.Copy(), self.term.arg.typ))
      case Apply():
        return Expression(Apply(self.term.fn.Copy(), self.term.arg.Copy()))
      case TAbstract():
        bt = self.term.arg
        return Expression(TAbstract(bt.typ, self.term.body.Copy()))
      case Abstract():
        bv = self.term.arg
        return Expression(Abstract(bv.var, self.term.body.Copy()))
      case _:
        raise NotImplementedError(f'Unexpected member of Expression {self.term}')

  def ReplaceType(
      self, btv: BindingTypeVar, T: Type, new_types: list[TypeVar],
      binder_map: Optional[dict[BindingVar, BindingVar]] = None
  ):
    if binder_map is None:
      binder_map = {}
    match self.term:
      case FreeVar() | BoundVar():
        u = self.term.var
        typ = SubstituteType(
            ExpressionType(u.typ), btv, ExpressionType(T), new_types, btv
        )
        u.typ = typ.Type()
        if isinstance(self.term, FreeVar):
          return Expression(FreeVar(u))
        return Expression(BoundVar(binder_map[self.term.bv], FreeVar(u)))
      case TApply():
        return Expression(
            TApply(
                self.term.fn.ReplaceType(btv, T, new_types, binder_map),
                SubstituteType(
                    self.term.arg, btv, ExpressionType(T), new_types, btv
                )
            )
        )
      case Apply():
        return Expression(
            Apply(
                self.term.fn.ReplaceType(btv, T, new_types, binder_map),
                self.term.arg.ReplaceType(btv, T, new_types, binder_map)
            )
        )
      case TAbstract():
        return Expression(
            TAbstract(
                self.term.arg.typ,
                self.term.body.ReplaceType(btv, T, new_types, binder_map)
            )
        )
      case Abstract():
        u = self.term.arg.var
        typ = SubstituteType(
            ExpressionType(u.typ), btv, ExpressionType(T), new_types, btv
        )
        u.typ = typ.Type()
        binder_map[self.term.arg] = BindingVar(u)
        M = Expression(
            Abstract(
                binder_map[self.term.arg],
                self.term.body.ReplaceType(btv, T, new_types, binder_map)
            )
        )
        return M


class FreeVars(Multiset[Var]):
  def __init__(self, e: Expression):
    match e.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case FreeVar():
        self.elems = [e.term.var]
      case BoundVar():
        self.elems = []
      case TApply():
        self.elems = FreeVars(e.term.fn).elems
      case Apply():
        self.elems = FreeVars(e.term.fn).elems + FreeVars(e.term.arg).elems
      case Abstract():
        self.elems = FreeVars(e.term.body).elems
      case _:
        raise NotImplementedError(f'Unexpected member of Expression {e.term}')

  def ContainsBindingVar(self, bv: BindingVar):
    return self.Contains(bv.var)


def AlphaEquiv(x: Expression, y: Expression) -> bool:
  def _Helper(
      x: Expression, y: Expression, de_brujin: DeBrujinIndices
  ) -> bool:
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
      case TApply():
        if not isinstance(y.term, TApply):
          return False
        if not _Helper(x.term.fn, y.term.fn, de_brujin):
          return False
        return TAlphaEquiv(x.term.arg, y.term.arg, de_brujin)
      case Apply():
        return (
            isinstance(y.term, Apply)
            and _Helper(x.term.fn, y.term.fn, de_brujin)
            and _Helper(x.term.arg, y.term.arg, de_brujin)
        )
      case TAbstract():
        if not isinstance(y.term, TAbstract):
          return False
        xt = x.Type().arg
        yt = y.Type().arg
        new_de_brujin = de_brujin.copy()
        new_de_brujin[xt.typ] = new_de_brujin[yt.typ] = len(de_brujin)
        return _Helper(x.term.body, y.term.body, new_de_brujin)
      case Abstract():
        if not isinstance(y.term, Abstract):
          return False
        xu = x.term.arg
        yu = y.term.arg
        if not TAlphaEquiv(
            xu.typ, yu.typ, de_brujin
        ):
          return False
        new_de_brujin = de_brujin.copy()
        new_de_brujin[xu.var] = new_de_brujin[yu.var] = len(de_brujin)
        return _Helper(x.term.body, y.term.body, new_de_brujin)
  return _Helper(x, y, de_brujin=DeBrujinIndices())


def RenameTerm(M: Expression, x: Var, y: Var) -> Expression:
  def _HasBindingVar(M: Expression, y: Var) -> bool:
    match M.term:
      case Var():
        raise Exception('Should not store Var in Expression')
      case BindingVar():
        raise Exception('Should not store BindingVar in Expression')
      case FreeVar() | BoundVar():
        return False
      case TApply():
        return _HasBindingVar(M.term.fn, y)
      case Apply():
        return _HasBindingVar(M.term.fn, y) or _HasBindingVar(M.term.arg, y)
      case TAbstract():
        return _HasBindingVar(M.term.body, y)
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
          return BoundVar(y, FreeVar(y.var))
        return M
      case TApply():
        return Expression(
            TApply(_RenameBoundVars(M.term.fn, x, y), M.term.arg)
        )
      case Apply():
        return Expression(
            Apply(
                _RenameBoundVars(M.term.fn, x, y),
                _RenameBoundVars(M.term.arg, x, y)
            )
        )
      case TAbstract():
        return Expression(
            TAbstract(M.term.arg, _RenameBoundVars(M.term.body, x, y))
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
    case TApply():
      return Expression(TApply(RenameTerm(M.term.fn, x, y), M.term.arg))
    case Apply():
      return Expression(
          Apply(RenameTerm(M.term.fn, x, y), RenameTerm(M.term.arg, x, y))
      )
    case TAbstract():
      return Expression(TAbstract(M.term.arg, RenameTerm(M.term.body, x, y)))
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
      return Expression(Abstract(v, RenameTerm(N, x, y)))
    case _:
      raise NotImplementedError(f'Unexpected input to Rename {M}')


def SubstituteTerm(
    M: Expression, x: Var, N: Expression, zs: list[Var],
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
    case TApply():
      return Expression(
          Apply(SubstituteTerm(M.term.fn, x, N, zs, binding), M.term.arg)
      )
    case Apply():
      return Expression(
          Apply(
              SubstituteTerm(M.term.fn, x, N, zs, binding),
              SubstituteTerm(M.term.arg, x, N, zs, binding)
          )
      )
    case TAbstract():
      return Expression(
          TAbstract(M.term.arg, SubstituteTerm(M.term.body, x, N, zs, binding))
      )
    case Abstract():
      if FreeVars(N).ContainsBindingVar(M.term.arg):
        if not zs:
          raise Exception(
              f'Need more variables for substitution for type {M.term.arg.typ}'
          )
        z = zs.pop()
        assert not FreeVars(N).Contains(z)
        M = RenameTerm(M, M.term.arg, z)
      return Expression(
          Abstract(M.term.arg, SubstituteTerm(M.term.body, x, N, zs, binding))
      )
    case _:
      raise NotImplementedError(f'Unexpected term in input for Substitute {M}')


class Redexes(Multiset[Term]):
  def __init__(self, M: Expression):
    match M.term:
      case Occurrence():
        self.elems = []
      case TApply():
        self.elems = []
        if isinstance(M.term.FuncTerm(), TAbstract):
          self.elems.append(M.term)
        self.elems.extend(Redexes(M.term.fn).elems)
      case Apply():
        self.elems = []
        if isinstance(M.term.FuncTerm(), Abstract):
          self.elems.append(M.term)
        self.elems.extend(Redexes(M.term.fn).elems)
        self.elems.extend(Redexes(M.term.arg).elems)
      case TAbstract():
        self.elems = Redexes(M.term.body).elems
      case Abstract():
        self.elems = Redexes(M.term.body).elems
      case _:
        raise NotImplementedError(f'Unexpected input to Redexes {M}')


def OneStepBetaReduce(M: Expression, new_vars: list[Var] = [], new_types: list[TypeVar] = [], applicative=False):
  match M.term:
    case Occurrence():
      return M
    case TApply():
      fn, arg_t = M.term.fn, M.term.arg
      if isinstance(fn.term, TAbstract):
        return fn.term.body.ReplaceType(fn.term.arg, arg_t, new_types)
      if not fn.BetaNormal():
        return Expression(
            TApply(
                OneStepBetaReduce(fn, new_vars, new_types, applicative),
                arg_t,
                M.term.new_types
            )
        )
      return M
    case Apply():
      # Applicative order: evaluate innermost-leftmost redex first.
      if applicative:
        if not M.term.fn.BetaNormal():
          return Expression(
              Apply(
                  OneStepBetaReduce(
                      M.term.fn, new_vars, new_types, applicative
                  ),
                  M.term.arg
              )
          )
        if not M.term.arg.BetaNormal():
          return Expression(
              Apply(
                  M.term.fn,
                  OneStepBetaReduce(
                      M.term.arg, new_vars, new_types, applicative
                  )
              )
          )
        if isinstance(M.term.FuncTerm(), Abstract):
          M, N = M.term.fn, M.term.arg
          return SubstituteTerm(
              M.term.body, M.term.arg.var, N, new_vars, M.term.arg
          )
        return M
      # Normal order: evaluate outermost-leftmost redex first.
      if isinstance(M.term.FuncTerm(), Abstract) and not isinstance(M.term.FuncTerm(), TAbstract):
        M, N = M.term.fn, M.term.arg
        return SubstituteTerm(M.term.body, M.term.arg.var, N, new_vars, M.term.arg)
      if M.term.fn.BetaNormal():
        return Expression(
            Apply(
                M.term.fn,
                OneStepBetaReduce(M.term.arg, new_vars, new_types, applicative)
            )
        )
      return Expression(
          Apply(OneStepBetaReduce(M.term.fn, new_vars, new_types, applicative), M.term.arg)
      )
    case TAbstract():
      return Expression(
          TAbstract(M.term.arg, OneStepBetaReduce(M.term.body, zs, applicative))
      )
    case Abstract():
      return Expression(
          Abstract(M.term.arg, OneStepBetaReduce(M.term.body, zs, applicative))
      )
    case _:
      raise NotImplementedError(f'Unexpected input to OneStepBetaReduce {M}')


class Statement:
  def __init__(self, subject: Union[Expression, ExpressionType], typ: Type):
    if typ != subject.Type():
      raise TypeError(
          f'Cannot create Statement with expression with type {subject.typ} '
          f'and type {typ}'
      )
    self.subj = subject
    self.typ = typ

  def __str__(self):
    return str(self.subj)


class TypeDeclaration:
  def __init__(self, subj_t: TypeVar):
    if not isinstance(subj_t, TypeVar):
      raise ValueError(f'Cannot create declaration with {subj_t}')
    self.subj = BindingTypeVar(subj_t)

  def Type(self):
    return self.subj.typ

  def __str__(self):
    return str(self.subj)


class Declaration:
  def __init__(self, subject: Var):
    if not isinstance(subject, Var):
      raise ValueError(f'Cannot create declaration with {subject}')
    self.subj = BindingVar(subject)

  def Var(self):
    return self.subj.var

  def __str__(self):
    return str(self.subj)


class Domain(Multiset[Union[Var, TypeVar]]):
    def __init__(self, types: list[TypeVar], vars: list[Var]):
      self.vars = Multiset(vars)
      self.types = Multiset(types)
      self.elems = self.types.elems + self.vars.elems

    def ContainsType(self, u: TypeVar):
      assert isinstance(u, TypeVar)
      return self.types.Contains(u)

    def ContainsVar(self, u: Var):
      assert isinstance(u, Var)
      return self.vars.Contains(u)


class Context:
  def __init__(self, *vars: Sequence[Union[Var, TypeVar]]):
    self.var_declarations = []
    self.typ_declarations = []
    self.declarations = []  # To preserve order for printing only
    for u in vars:
      match u:
        case Var():
          for tv in FreeTypeVars(ExpressionType(u.typ)):
            if not self.ContainsVar(tv.typ):
              raise ValueError(f'Context {self} does not contain free types in {u}')
          self.var_declarations.append(Declaration(u))
          self.declarations.append(self.var_declarations[-1])
        case TypeVar():
          self.typ_declarations.append(TypeDeclaration(u))
          self.declarations.append(self.typ_declarations[-1])
        case _:
          raise NotImplementedError(f'Unexpected input to Context {u}')

  def __str__(self):
    if not self.declarations:
      return 'Ø'
    return ', '.join([str(d) for d in self.declarations])
  
  # Overload for subcontext, A < B returns if A is a subcontext of B
  def __lt__(self, other):
    for u in self.typ_declarations:
      for v in other.typ_declarations:
        if u.subj.typ == v.subj.typ:
          break
      else:
        return False
    for u in self.var_declarations:
      for v in other.var_declarations:
        if u.subj.var == v.subj.var:
          break
      else:
        return False
    return True

  # Overload for permutation, A == B returns if A is a permutation of B
  def __eq__(self, other):
    return (self < other) and (other < self)

  # Overload for projection, A | B
  def __or__(self, other: Sequence[Var]):
    return Context(*(set(self.Dom()) & set(other)))

  def BindStatementFreeVars(self, sttmt: Statement):
    for decl in self.typ_declarations:
      sttmt.subj.MaybeBindFreeTypesTo(decl.subj)
    if isinstance(sttmt.subj, ExpressionType):
      return
    for decl in self.var_declarations:
      sttmt.subj.MaybeBindFreeVarsTo(decl.subj)
  
  def ContainsVar(self, u: Union[Var, TypeVar]):
    match u:
      case Var():
        return self.Dom().ContainsVar(u)
      case TypeVar():
        return self.Dom().ContainsType(u)
      case _:
        raise NotImplementedError(f'Unexpected input to ContainsVar {u}')

  def PullVar(self, u: Union[Var, TypeVar]):
    args = []
    for v in self.Dom():
      match (u, v):
        case (Var(), Var()):
          if u != v:
            args.append(v)
        case (_, Var()):
          args.append(v)
        case (TypeVar(), TypeVar()):
          if u != v:
            args.append(v)
        case (_, TypeVar()):
          args.append(v)
        case (_, _):
          raise NotImplementedError(f'Unexpected input to PullVar {u}')
    return Context(*args)

  def PushTypeVar(self, u: TypeVar):
    assert isinstance(u, TypeVar)
    if self.ContainsVar(u):
      raise Exception(f'Context {self} contains {u}')
    return Context(*self.Dom(), u)

  def PushVar(self, u: Var):
    assert isinstance(u, Var)
    if self.ContainsVar(u):
      raise Exception(f'Context {self} contains {u}')
    if not self.ContainsFreeTypes(ExpressionType(u.typ)):
      raise TypeError(
          f'Context {self} does not contain free type variables in {u.typ}'
      )
    return Context(*self.Dom(), u)

  def PushVars(self, *us: list[Union[Var, TypeVar]]):
    return Context(*self.Dom(), *us)

  def Dom(self) -> Domain:
    return Domain(
        [decl.subj.typ for decl in self.typ_declarations],
        [decl.subj.var for decl in self.var_declarations]
    )

  def ContainsFreeTypes(self, rho: ExpressionType):
    assert isinstance(rho, ExpressionType)
    for alpha in FreeTypeVars(rho):
      if not self.ContainsVar(alpha.typ):
        return False
    return True

  def Insersect(self, other):
    if self < other:
      return self
    assert other < self
    return other


class Judgement:
  def __init__(self, ctx: Context, stmt: Statement):
    self.ctx = ctx
    self.stmt = stmt
    self.ctx.BindStatementFreeVars(stmt)

  def __str__(self):
    return f'{self.ctx} |- {self.stmt}'


class DerivationRule:
  def __init__(self, *premisses: Sequence[Judgement]):
    if premisses:
      ctx = premisses[0].ctx
      for pmiss in premisses:
        if not (ctx < pmiss.ctx) and not (pmiss.ctx < ctx):
          raise ValueError(
              'Cannot use different Contexts in premisses of '
              f'the same DerivationRule: {ctx} != {pmiss.ctx}'
          )
    self.premisses = premisses
  
  def Conclusion(self) -> Judgement:
    raise NotImplementedError(
        'Do not call Conclusion with Derivation subclass'
    )

  def __str__(self):
    premiss_str = ', '.join([str(p) for p in self.premisses])
    horiz_rule = '-' * len(premiss_str)
    if premiss_str:
      return f'{premiss_str}\n{horiz_rule}\n{self.Conclusion()}'
    return str(self.Conclusion())


class VarRule(DerivationRule):
  def __init__(self, ctx: Context, u: Var):
    if not ctx.ContainsVar(u):
      raise ValueError(f'Cannot create VarRule for {u} with Context {ctx}')
    super().__init__()
    self.ctx = ctx
    self.u = u

  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(Expression(self.u), self.u.typ))


class ApplRule(DerivationRule):
  def __init__(self, *premisses: Sequence[Judgement]):
    if len(premisses) != 2:
      raise ValueError('Can only create ApplRule with 2 Judgements')
    super().__init__(*premisses)

  def Conclusion(self) -> Judgement:
    p_fn, p_arg = self.premisses
    fn = p_fn.stmt.subj
    arg = p_arg.stmt.subj
    expr = Expression(Apply(fn, arg))
    return Judgement(p_fn.ctx.Insersect(p_arg.ctx), Statement(expr, expr.typ))


class AbstRule(DerivationRule):
  def __init__(self, arg: Var, premiss: Judgement):
    super().__init__(premiss)
    p = self.premisses[0]
    if not p.ctx.ContainsVar(arg):
      raise ValueError(f'Cannot call Abst rule with var {arg} and Context {p.ctx}')
    self.arg = arg
  
  def Conclusion(self) -> Judgement:
    p = self.premisses[0]
    a = self.arg
    body = p.stmt.subj
    expr = Expression(Abstract(a, body))
    return Judgement(p.ctx.PullVar(a), Statement(expr, expr.Type()))


class FormRule(DerivationRule):
  def __init__(self, ctx: Context, u: Type):
    super().__init__()
    self.ctx = ctx
    if not self.ctx.ContainsFreeTypes(ExpressionType(u)):
      raise TypeError(f'Context {ctx} does not contain free types in {u}')
    self.u = ExpressionType(u)

  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(self.u, self.u.Type()))


class Appl2Rule(DerivationRule):
  def __init__(self, *premisses: Sequence[Judgement]):
    if len(premisses) != 2:
      raise ValueError('Can only create Appl2Rule with 2 Judgements')
    super().__init__(*premisses)
  
  def Conclusion(self) -> Judgement:
    p_fn, p_arg = self.premisses
    fn = p_fn.stmt.subj
    arg = p_arg.stmt.subj
    expr = Expression(TApply(fn, arg))
    return Judgement(p_fn.ctx, Statement(expr, expr.Type()))


class Abst2Rule(DerivationRule):
  def __init__(self, arg: TypeVar, premiss: Judgement):
    super().__init__(premiss)
    p = self.premisses[0]
    if not p.ctx.ContainsVar(arg):
      raise ValueError(f'Cannot call Abst rule with var {arg} and Context {p.ctx}')
    self.arg = arg

  def Conclusion(self) -> Judgement:
    p = self.premisses[0]
    a = self.arg
    body = p.stmt.subj
    if isinstance(body, Expression):
      expr = Expression(TAbstract(a, body))
    else:
      assert isinstance(body, ExpressionType)
      expr = ExpressionType(PiType(a, body))
    return Judgement(p.ctx.PullVar(a), Statement(expr, expr.Type()))


class Derivation:
  def __init__(self, ctx: Context):
    self.ctx = ctx
    self.rules: list[DerivationRule] = []
    self.conclusions: list[Judgement] = []

  def _AddRule(self, rule: DerivationRule) -> Judgement:
    self.rules.append(rule)
    concl = rule.Conclusion()
    self.conclusions.append(concl)
    return concl

  def VarRule(self, u: Var) -> Judgement:
    return self._AddRule(VarRule(self.ctx, u))

  def ApplRule(self, fn: Judgement, arg: Judgement) -> Judgement:
    assert fn in self.conclusions
    assert arg in self.conclusions
    return self._AddRule(ApplRule(fn, arg))

  def AbstRule(self, arg: Var, body: Judgement) -> Judgement:
    assert body in self.conclusions
    concl = self._AddRule(AbstRule(arg, body))
    self.ctx = concl.ctx
    return concl

  def FormRule(self, t: Type) -> Judgement:
    return self._AddRule(FormRule(self.ctx, t))

  def Appl2Rule(self, fn: Judgement, arg: Judgement) -> Judgement:
    assert fn in self.conclusions
    # assert arg in self.conclusions
    return self._AddRule(Appl2Rule(fn, arg))

  def Abst2Rule(self, arg: TypeVar, body: Judgement) -> Judgement:
    assert body in self.conclusions
    concl = self._AddRule(Abst2Rule(arg, body))
    self.ctx = concl.ctx
    return concl

  def _Justification(self, rule: DerivationRule, keys: dict[Judgement, str]) -> str:
    match rule:
      case VarRule():
        return '(var)'
      case ApplRule():
        fn_key = keys[rule.premisses[0]]
        arg_key = keys[rule.premisses[1]]
        return f'(appl) on ({fn_key}) and ({arg_key})'
      case AbstRule():
        body_key = keys[rule.premisses[0]]
        return f'(abst) on ({body_key})'
      case FormRule():
        return '(form)'
      case Appl2Rule():
        fn_key = keys[rule.premisses[0]]
        arg_key = keys[rule.premisses[1]]
        return f'(appl2) on ({fn_key}) and ({arg_key})'
      case Abst2Rule():
        body_key = keys[rule.premisses[0]]
        return f'(abst2) on ({body_key})'
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
    var_abst_order: list[Optional[Var]] = []
    typ_abst_order: list[Optional[TypeVar]] = []
    for rule in self.rules:
      if isinstance(rule, Abst2Rule):
        typ_abst_order.append(rule.arg)
        var_abst_order.append(Var('', TypeVar('')))
      if isinstance(rule, AbstRule):
        var_abst_order.append(rule.arg)
        typ_abst_order.append(TypeVar(''))
    reverse = lambda lst: list(reversed(lst))
    var_abst_order = reverse(var_abst_order)
    typ_abst_order = reverse(typ_abst_order)
    def _SortKey(
        decl: Union[Declaration, TypeDeclaration],
        var_abst_order: list[Var],
        typ_abst_order: list[TypeVar]
    ):
      try:
        match decl:
          case Declaration():
            return var_abst_order.index(decl.subj.var)
          case TypeDeclaration():
            return typ_abst_order.index(decl.subj.typ)
          case _:
            raise NotImplementedError(f'Unexpected input to SortKey {decl}')
      except ValueError:
        return -1
    declarations = sorted(
        self.conclusions[0].ctx.declarations,
        key=lambda d: _SortKey(d, var_abst_order, typ_abst_order)
    )
    for decl in declarations:
      key = chr(ord('a') + len(keys))
      if isinstance(decl, TypeDeclaration):
        keys[decl.subj.typ] = key
      else:
        assert isinstance(decl, Declaration)
        keys[decl.subj.var] = key
      indent = '| ' * indent_count
      seperator = (
          ' ' * len(f'({key}) ')
          + '| ' * indent_count
          + '|'
          + '-' * (len(str(decl)) + 3)
      )
      line = f'({key}) {indent}| {decl} |'
      result.extend([seperator, line, seperator])
      indent_count += 1
    for rule, concl in zip(self.rules, self.conclusions):
      indent = '| ' * indent_count
      if isinstance(rule, VarRule):
        key = chr(ord('a') + len(keys))
        keys[concl] = key
        var_key = keys[concl.stmt.subj.term.var]
        justif = f'(var) on ({var_key})'
      else:
        if isinstance(rule, AbstRule) or isinstance(rule, Abst2Rule):
          indent_count -= 1
          indent = '| ' * indent_count
        key = chr(ord('a') + len(keys))
        keys[concl] = key
        justif = self._Justification(rule, keys)
      line = f'({key}) {indent}{concl.stmt}    {justif}'
      result.append(line)
      result.append(f'    {indent[:-1]}' + '-' * (len(line) - len(indent) - 3))
    return '\n'.join(result)


def DeriveTerm(jdgmnt: Judgement) -> Derivation:
  term_vars: list[Union[Var, TypeVar]] = []
  def _FindVars(M: Expression):
    match M.term:
      case FreeVar():
        assert jdgmnt.ctx.ContainsVar(M.term.var)
      case BoundVar():
        pass
      case TAbstract():
        term_vars.append(M.term.arg.typ)
        _FindVars(M.term.body)
      case Abstract():
        term_vars.append(M.term.arg.var)
        _FindVars(M.term.body)
      case TApply():
        term_vars.append(M.term.arg.Type())
        _FindVars(M.term.fn)
      case Apply():
        _FindVars(M.term.fn)
        _FindVars(M.term.arg)
      case _:
        raise ValueError(f'Unexpected term {M.term}')
  _FindVars(Expression(jdgmnt.stmt.subj))
  term_vars = [
      u for u in term_vars
      if (
          (isinstance(u, Var) or isinstance(u, TypeVar))
          and not jdgmnt.ctx.ContainsVar(u)
      )
  ]
  ctx = jdgmnt.ctx.PushVars(*term_vars)
  d = Derivation(ctx)
  def _Helper(M: Expression) -> DerivationRule:
    match M.term:
      case FreeVar():
        return d.VarRule(M.term.var)
      case BoundVar():
        raise ValueError(f'Should not need rule for bound variable {M.term}')
      case TApply():
        arg_premiss = d.FormRule(M.term.arg)
        return d.Appl2Rule(_Helper(M.term.fn), arg_premiss)
      case Apply():
        return d.ApplRule(_Helper(M.term.fn), _Helper(M.term.arg))
      case TAbstract():
        return d.Abst2Rule(M.term.arg.typ, _Helper(Expression(M.term.body)))
      case Abstract():
        return d.AbstRule(M.term.arg.var, _Helper(Expression(M.term.body)))
      case _:
        raise NotImplementedError(f'Unexpected subject in judgement {M}')
  _Helper(Expression(jdgmnt.stmt.subj))
  return d


def DeriveType(jdgmnt: Judgement) -> Derivation:
  term_vars: list[Union[Var, TypeVar]] = []
  def _FindTypeVars(T: ExpressionType):
    match T.typ:
      case FreeTypeVar():
        assert jdgmnt.ctx.ContainsVar(T.Type())
      case BoundTypeVar():
        pass
      case PiType():
        term_vars.append(T.typ.arg.typ)
        _FindTypeVars(T.typ.body)
      case Arrow():
        _FindTypeVars(T.typ.arg)
        _FindTypeVars(T.typ.ret)
      case _:
        raise ValueError(f'Unexpected term {M.term}')
  _FindTypeVars(ExpressionType(jdgmnt.stmt.subj))
  ctx = jdgmnt.ctx.PushVars(*term_vars)
  d = Derivation(ctx)
  def _Helper(T: ExpressionType) -> DerivationRule:
    match T.typ:
      case FreeTypeVar():
        return d.FormRule(T.typ.typ)
      case BoundTypeVar():
        raise ValueError(f'Should not need rule for bound type {T.typ}')
      case PiType():
        return d.Abst2Rule(T.typ.arg.typ, _Helper(ExpressionType(T.typ.body)))
      case Arrow():
        _Helper(T.typ.arg)
        _Helper(T.typ.ret)
        return d.FormRule(T.typ)
  _Helper(ExpressionType(jdgmnt.stmt.subj))
  return d


def PrenexNormalForm(T: Type, top_level: bool = True) -> bool:
  # Prenex normal form: Only top-level abstractions can be Π-types.
  if isinstance(T, ExpressionType):
    T = T.Type()
  match T:
    case TypeVar():
      return True
    case PiType():
      return top_level and PrenexNormalForm(T.body, top_level)
    case Arrow():
      return (
          PrenexNormalForm(T.Arg(), False) and PrenexNormalForm(T.Ret(), False)
      )
    case _:
      raise NotImplementedError(f'Unexpected input to PrenexNormalForm {T}')


class TermNotFoundError(Exception):
  pass


class MissingTermForTypeError(Exception):
  pass


def FindTerm(
    ctx: Context, typ: ExpressionType, new_vars: list[Var]
) -> tuple[Expression, Derivation]:
  if not PrenexNormalForm(typ):
    raise TypeError(f'{typ} is not a Rank-1 polymorphism')

  def _Unify(
      candidate: Type, target: Type, type_params: list[BindingTypeVar],
      subsitution_map: dict[TypeVar, Type]
  ) -> bool:
    for tv in type_params:
      if candidate == target: 
        if tv in substitution_map:
          return substitution_map[tv] == target
        substitution_map[tv] = target
        return True
    if isinstance(candidate, Arrow) and isinstance(target, Arrow):
      return (
          _Unify(candidate.arg, target.arg, type_params, substituion_map)
          and _Unify(candidate.ret, target.ret, type_params, substituion_map)
      )
    return candidate == target
  
  def _ApplySubst(t: Type, substitution_map: dict[TypeVar, Type]) -> Type:
    if isinstance(t, Arrow):
      return Arrow(_ApplySubst(t.arg), _ApplySubst(t.ret))
    for tv, replacement in substitution_map.items():
      if t == tv:
        return replacement
    return t

  def _Helper(
      ctx: Context, typ: ExpressionType, visited: set[str], new_vars: list[Var]
  ):
    if str(typ) in visited:
      raise TermNotFoundError(f'Cycle detected in {typ}')
    new_visited = visited | {str(typ)}
    match typ.Type():
      case PiType():
        ctx, body_term = _Helper(
            ctx.PushTypeVar(typ.Type().arg.typ),
            ExpressionType(typ.Type().body),
            new_visited,
            new_vars
        )
        return ctx, Expression(TAbstract(typ.Type().arg, body_term))
      case Arrow():
        for u in new_vars:
          if typ.Type().arg == u.typ:
            new_vars.remove(u)
            break
        else:
          raise MissingTermForTypeError(
              f'Need fresh variable with type {typ.Type().arg}'
          )
        ctx, body = _Helper(
            ctx.PushVar(u), ExpressionType(typ.Type().ret), new_visited, new_vars
        )
        return ctx, Expression(Abstract(u, body))
    for decl in ctx.declarations:
      if isinstance(decl, TypeDeclaration):
        continue
      candidate_term = Expression(decl.subj.var)
      candidate_typ = decl.subj.typ.Type()
      type_params = []
      while isinstance(candidate_typ, PiType):
        type_params.append(candidate_typ.arg)
        candidate_typ = candidate_typ.body.Type()
      arg_types = []
      while isinstance(candidate_typ, Arrow):
        arg_types.append(candidate_typ.arg)
        candidate_typ = candidate_typ.Ret()
      subst_map = {}
      if _Unify(candidate_typ, typ.Type(), type_params, subst_map):
        try:
          cur_term = candidate_term
          real_arg_types = []
          for arg_t in arg_types:
            real_arg_types.append(_ApplySubst(arg_t, subst_map))
          for tv in type_params:
            if tv not in substitution_map:
              raise TermNotFoundError('Ambiguous type parameter')
            replacement = subst_map[tv]
            cur_term = Expression(TApply(cur_term, replacement))
          for need_arg_type in real_arg_types:
            ctx, arg_term = _Helper(ctx, need_arg_type, new_visited, new_vars)
            cur_term = Expression(Apply(cur_term, arg_term))
          return ctx, cur_term
        except TermNotFoundError:
          continue
    raise TermNotFoundError(f'Could not find term for {typ}')
  ctx, term = _Helper(ctx, typ, set(), new_vars)
  return term, DeriveTerm(Judgement(ctx, Statement(term, typ)))
