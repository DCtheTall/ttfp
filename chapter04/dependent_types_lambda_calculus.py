"""
Chapter 4: Types Dependent on Types
===================================

"""

from typing import Union


class Kind:
  def __str__(self):
    raise NotImplementedError('Do not cast Kind subclass to str')


class Star(Kind):
  def __str__(self):
    return '*'

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
    return f'({self.arg} -> {ret_str})'

  def __eq__(self, other):
    assert isinstance(other, Kind)
    if not isinstance(other, KArrow):
      return False
    return (self.arg, self.ret) == (other.arg, other.ret)


class AllKinds:
  def __str__(self):
    return '□'

  def __eq__(self, other):
    return isinstance(other, AllKinds)


class Type:
  kind: Kind

  def __str__(self):
    raise NotImplementedError('Do not cast Type subclass to str')

  def Proper(self):
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
    return f'{self.name}:{self.kind}'

  def __eq__(self, other):
    if isinstance(other, TOccurrence):
      other = other.typ
    assert isinstance(other, TypeVar)
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
    name, *others = str(self.typ).split(':')
    assert len(others) == 1
    return name

  def BoundTo(self, bt: BindingTypeVar) -> bool:
    return self.bt == bt


class TArrow(Type):
  def __init__(self, arg: Type, ret: Type):
    assert arg.Proper()
    assert ret.Proper()
    self.arg = arg
    self.ret = ret
    self.kind = Star()


class TAbstract(Type):
  def __init__(self, arg: Type, body: Type):
    self.arg = arg
    self.body = body
    self.kind = KArrow(arg.kind, body.kind)
    if isinstance(arg, BindingTypeVar):
      assert isinstance(body, TypeExpression)
      body.MaybeBindFreeTypesTo(arg)

  def __str__(self):
    body = self.body
    args = str(self.arg)
    while isinstance(body, TAbstract):
      args = body._AppendMultiArgStr(args, body)
      body = body.body_key
    return f'(λ{args}.{body}):{self.kind}'

  def _AppendMultiArgStr(self, args_str, body):
    return args_str + f'.λ{body.arg}'


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
    fn = self.fn
    fn_str = str(self.fn)
    if isinstance(fn, TApply):
      fn_str = '):'.join(fn_str.split('):')[:-1])[1:]
    arg = str(self.arg)
    return f'({fn_str} {arg}):{self.kind}'


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
        raise NotImplementedError(f'Unexpected member of TypeExpression {self.typ}')
  
  def Copy(self) -> 'TypeExpression':
    match self.typ:
      case FreeTypeVar() | BoundTypeVar():
        return TypeExpression(self.typ.typ)
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

