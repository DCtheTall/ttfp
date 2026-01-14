"""
Chapter 3: Second Order Typed Lambda Calculus
=============================================

"""


from typing import Union


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
  
  def ShouldBind(self, ftyp: FreeTypeVar) -> bool:
    return self.typ == ftyp


class BoundTypeVar(TOccurrence):
  def __init__(self, bt: BindingTypeVar, ftyp: FreeTypeVar):
    assert isinstance(bt, BindingTypeVar)
    self.bt = bt
    self.typ = ftyp
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
    args = str(self.arg)
    if isinstance(body, PiType):
      while isinstance(body, PiType):
        args += f',{body.arg}'
        body = body.BodyType()
    return f'Π{args}:*.{body}'
  
  def BodyType(self):
    if isinstance(self.body, ExpressionType):
      return self.body.typ
    return self.body


class ExpressionType(Type):
  typ: Type

  def __init__(self, typ: Type):
    if isinstance(typ, ExpressionType):
      self.typ = typ.Copy().typ
    elif isinstance(typ, TypeVar):
      self.typ = FreeTypeVar(typ)
    elif isinstance(typ, FreeTypeVar):
      self.typ = typ
    elif isinstance(typ, BoundTypeVar):
      self.typ = typ
    elif isinstance(typ, Arrow):
      self.typ = Arrow(ExpressionType(typ.arg), ExpressionType(typ.ret))
    elif isinstance(typ, PiType):
      arg_t = typ.arg
      if not isinstance(arg_t, BindingTypeVar):
        arg_t = BindingTypeVar(arg_t)
      body_t = ExpressionType(typ.body)
      body_t.MaybeBindFreeTypesTo(arg_t)
      self.typ = PiType(arg_t, body_t)
    else:
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

  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    if isinstance(self.typ, TypeVar):
      raise Exception('Should not store TypeVar in Expression')
    elif isinstance(self.typ, BindingTypeVar):
      raise Exception('Should not store BindingTypeVar in Expression')
    elif isinstance(self.typ, FreeTypeVar):
      if btv.ShouldBind(self.typ):
        self.typ = BoundTypeVar(btv, self.typ.typ)
    elif isinstance(self.typ, BoundTypeVar):
      pass
    elif isinstance(self.typ, Arrow):
      self.typ.arg.MaybeBindFreeTypesTo(btv)
      self.typ.ret.MaybeBindFreeTypesTo(btv)
    elif isinstance(self.typ, PiType):
      self.typ.body.MaybeBindFreeTypesTo(btv)
    else:
      raise NotImplementedError(f'Unexpected member of ExpressionType {self.typ}')
  
  def Copy(self):
    if isinstance(self.typ, FreeTypeVar) or isinstance(self.typ, BoundTypeVar):
      return ExpressionType(self.typ.typ)
    if isinstance(self.typ, Arrow):
      return ExpressionType(Arrow(self.typ.arg.Copy(), self.typ.ret.Copy()))
    if isinstance(self.typ, PiType):
      btv = self.typ.arg
      return ExpressionType(PiType(btv.typ, self.typ.body.Copy()))
    raise NotImplementedError(f'Unexpected member of Expression {self.term}')


def TAlphaEquiv(x: ExpressionType, y: ExpressionType):
  def _Helper(x: ExpressionType, y: ExpressionType, de_brujin: dict[TypeVar, int]):
    if isinstance(x.typ, FreeTypeVar):
      return isinstance(y.typ, FreeTypeVar) and x.typ == y.typ
    if isinstance(x.typ, BoundTypeVar):
      if not isinstance(y.typ, BoundTypeVar):
        return False
      xt = x.typ.typ
      yt = y.typ.typ
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
  return _Helper(x, y, de_brujin={})


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Not implemented')


class Var(Term):
  def __init__(self, name: str, typ: Type):
    self.name = name
    self.typ = typ

  def __str__(self):
    return f'{self.name}:{self.typ}'

  def __hash__(self):
    return hash(str(self))


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
    self.typ = u.typ

  def ShouldBind(self, fv: FreeVar) -> bool:
    return self.var == fv


class BoundVar(Occurrence):
  def __init__(self, bv: BindingVar, fv: FreeVar):
    assert isinstance(bv, BindingVar)
    self.bv = bv
    self.var = fv.var
    if self.bv.typ != self.var.typ:
      raise TypeError(
          f'Cannot bind variable with type {self.bv.typ} '
          f'to variable with type {self.fv.typ}'
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
    if not isinstance(fn.typ, Arrow):
      raise TypeError(f'Left term of Apply must be Arrow type {fn.typ}')
    if fn.typ.arg != arg.typ:
      raise TypeError(f'Expected type {fn.typ.arg} got {arg.typ}')
    self.typ = self.fn.typ.ret

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
    return f'(λ{args}.{body_str}):{self.typ}'

  def BodyTerm(self) -> Term:
    # if isinstance(self.body, Expression):
    #   return self.body.term
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
      if isinstance(u, TAbstract):
        arg_t = u.arg
        if not isinstance(arg_t, BindingTypeVar):
          arg_t = BindingTypeVar(arg_t)
        body = Expression(u.body)
        body.MaybeBindFreeTypesTo(arg_t)
        self.term = TAbstract(arg_t, body)
      else:
        v = u.arg
        if not isinstance(v, BindingVar):
          v = BindingVar(v)
        body = Expression(u.body)
        body.MaybeBindFreeVarsTo(v)
        self.term = Abstract(v, body)
    else:
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
    if isinstance(self.term, Var):
      raise Exception('Should not store Var in Expression')
    elif isinstance(self.term, BindingVar):
      raise Exception('Should not store BindingVar in Expression')
    elif isinstance(self.term, FreeVar):
      if bv.ShouldBind(self.term):
        self.term = BoundVar(bv, self.term)
    elif isinstance(self.term, BoundVar):
      pass
    elif isinstance(self.term, Apply):
      self.term.fn.MaybeBindFreeVarsTo(bv)
      self.term.arg.MaybeBindFreeVarsTo(bv)
    elif isinstance(self.term, Abstract):
      self.term.body.MaybeBindFreeVarsTo(bv)
    else:
      raise NotImplementedError(f'Unexpected member of Expression {self.term}')
  
  def MaybeBindFreeTypesTo(self, btv: BindingTypeVar):
    if isinstance(self.term, Var):
      raise Exception('Should not store Var in Expression')
    elif isinstance(self.term, BindingVar):
      raise Exception('Should not store BindingVar in Expression')
    elif isinstance(self.term, Occurrence):
      if btv.ShouldBind(self.term.typ.typ):
        self.typ.MaybeBindFreeTypesTo(btv)
        self.SetType(self.typ)
    elif isinstance(self.term, Apply):
      self.term.fn.MaybeBindFreeTypesTo(btv)
      self.term.arg.MaybeBindFreeTypesTo(btv)
    elif isinstance(self.term, Abstract):
      self.term.body.MaybeBindFreeTypesTo(btv)
    else:
      raise NotImplementedError(f'Unexpected member of Expression {self.term}')
    self.typ.MaybeBindFreeTypesTo(btv)


def AlphaEquiv(x: Expression, y: Expression):
  # assert TAlphaEquiv(x.typ, y.typ)
  pass
