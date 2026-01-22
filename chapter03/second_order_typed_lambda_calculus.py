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
  def __init__(self, arg: TypeVar, ret: TypeVar):
    self.arg = arg
    self.ret = ret

  def __str__(self):
    # Right associative, Apply is left associative.
    ret = self.ret
    ret_str = str(ret)
    if isinstance(ret, Arrow):
      ret_str = ret_str[1:-1]
    return f'({self.arg} -> {ret_str})'

  def __eq__(self, other):
    assert isinstance(other, Type)
    if not isinstance(other, Arrow):
      return False
    return (self.arg, self.ret) == (other.arg, other.ret)


class PiType(Type):
  def __init__(self, arg: Union[TypeVar, BindingTypeVar], body: Type):
    self.arg = arg
    self.body = body

  def __str__(self):
    body = self.BodyType()
    args = str(self.arg)[:-2]
    if isinstance(body, PiType):
      while isinstance(body, PiType):
        args += f',{str(body.arg)[:-2]}'
        body = body.BodyType()
    return f'Π{args}:*.{body}'
  
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
        return []
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
        T = Rename(T, T.typ.arg, new_t)
      return ExpressionType(
          PiType(T.typ.arg, SubstituteType(T.typ.body, a, B, new_types, binding))
      )
    case _:
      raise NotImplementedError(f'Unexpected term in type for SubstituteType {T}')


def OneStepBetaReduceType(
    fn: 'Expression', arg: Type, new_types: list[TypeVar] = []
) -> ExpressionType:
  if isinstance(fn, Expression):
    fn = fn.term
  assert isinstance(fn, TAbstract)
  assert isinstance(fn.Type(), PiType)
  # Cannot use Π-types on righthand side in λ2.
  assert not isinstance(arg, PiType)
  return SubstituteType(fn.body.typ, fn.arg.typ, arg, new_types, fn.arg)


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

  def ShouldBind(self, fv: FreeVar) -> bool:
    return self.var == fv


class BoundVar(Occurrence):
  def __init__(self, bv: BindingVar, fv: FreeVar):
    assert isinstance(bv, BindingVar)
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
      raise TypeError(f'Expected type {fn.typ.arg} got {arg.typ}')
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
    if not isinstance(fn.Type(), PiType):
      raise TypeError(f'TApply must be used on Π-types, got {fn}')
    self.fn = fn
    assert not isinstance(arg, PiType)
    self.arg = arg
    self.new_types = new_types
    self.typ = OneStepBetaReduceType(
        Expression(self.fn), self.arg, self.new_types
    )


class Abstract(Term):
  def __init__(self, arg: Union[Var, BindingVar], body: Term):
    self.arg = arg
    self.body = body
    self.typ = Arrow(self.arg.typ, self.body.typ)

  def __str__(self):
    body = self.BodyTerm()
    args = str(self.arg)
    if isinstance(body, Abstract):
      while isinstance(body, Abstract):
        args += f'.λ{body.arg}'
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


class TAbstract(Abstract):
  def __init__(self, arg: Union[TypeVar, BindingTypeVar], body: Term):
    self.arg = arg
    self.body = body
    self.typ = PiType(arg, body.typ)


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
        self.term.fn.MaybeBindFreeTypesTo(bv)
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


class Statement:
  def __init__(self, subject: Expression, typ: Type):
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
    for u in vars:
      match u:
        case Var():
          self.var_declarations.append(Declaration(u))
        case TypeVar():
          self.typ_declarations.append(TypeDeclaration(u))
        case _:
          raise NotImplementedError(f'Unexpected input to Context {u}')
    self.declarations = list(self.typ_declarations) + list(self.var_declarations)

  def __str__(self):
    if not self.declarations:
      return 'Ø'
    return ', '.join([str(d) for d in self.declarations])
  
  # Overload for subcontext, A < B returns if A is a subcontext of B
  def __lt__(self, other):
    for u in self.typ_declarations:
      for v in other.typ_declarations:
        if u.subj.var == v.subj.var:
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
  # def __or__(self, other: Sequence[Var]):
  #   return Context(*(set(self.Dom()) & set(other)))

  # def BindStatementFreeVars(self, sttmt: Statement):
  #   for decl in self.declarations:
  #     sttmt.subj.MaybeBindFreeVarsTo(decl.subj)
  
  def ContainsVar(self, u: Union[Var, TypeVar]):
    match u:
      case Var():
        return self.Dom().ContainsVar(u)
      case TypeVar():
        return self.Dom().ContainsType(u)
      case _:
        raise NotImplementedError(f'Unexpected input to ContainsVar {u}')

  # def PullVar(self, u: Var):
  #   return Context(*[v for v in self.Dom() if v != u])

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

  # def PushVars(self, *us: list[Var]):
  #   return Context(*us, *self.Dom())

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
