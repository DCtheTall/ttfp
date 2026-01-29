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
    return f'{self.name}:{self.kind}'[:-2]

  def __eq__(self, other):
    if isinstance(other, TypeExpression):
      other = other.Type()
    if isinstance(other, TOccurrence):
      other = other.typ
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

  def __str__(self):
    ret_str = str(self.ret)
    if isinstance(self.ret, TArrow):
      ret_str = ret_str[1:-1]
    return f'({self.arg} -> {ret_str}):{str(self.kind)[:-2]}'


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
    return f'(λ{args}.{body}):{self.kind}'[:-2]

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
    return f'({fn_str} {arg}):{self.kind}'[:-2]


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
        raise NotImplementedError(
            f'Unexpected member of TypeExpression {self.typ}'
        )
  
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
      case Arrow():
        self.elems = FreeTypeVars(T.typ.arg).elems + FreeTypeVars(T.typ.ret).elems
      case TApply():
        self.elems = FreeTypeVars(T.typ.body).elems
      case _:
        raise NotImplementedError(f'Unexpected input to OccursFree {T}')

  def ContainsBindingVar(self, btv: BindingTypeVar):
    return self.Contains(btv.typ)


class Term:
  typ: Type

  def __str__(self):
    raise NotImplementedError('Not implemented')

  def Type(self):
    typ = self.typ
    if isinstance(typ, TypeExpression):
      typ = typ.typ
    if isinstance(typ, TOccurrence):
      typ = typ.typ
    assert (
      isinstance(typ, TypeVar)
      or isinstance(typ, TArrow)
    )
    return typ


class Var(Term):
  def __init__(self, name: str, typ: Type):
    self.name = name
    self.typ = typ

  def __str__(self):
    line = f'{self.name}:{self.typ}'
    kind_str = str(self.typ.kind)
    return line[:len(kind_str)]

  def __hash__(self):
    return hash(str(self))

  def __eq__(self, other):
    if isinstance(other, Occurrence):
      other = other.var
    assert isinstance(other, Var)
    return self.name == other.name and self.Type() == other.Type()


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
    self.typ = TypeExpression(u.typ)

  def __hash__(self):
    return id(self)

  def ShouldBind(self, fv: FreeVar) -> bool:
    return self.var == fv


class BoundVar(Occurrence):
  def __init__(self, bv: BindingVar, fv: FreeVar):
    self.bv = bv
    self.var = fv.var
    bv_typ = self.bv.typ
    if isinstance(bv_typ, TypeExpression):
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

  def ContainsBindingVar(self, bv: BindingVar):
    return self.Contains(bv.var)


class Apply(Term):
  def __init__(self, fn: Term, arg: Term):
    self.fn = fn
    self.arg = arg
    if not isinstance(fn.Type(), Arrow):
      raise TypeError(f'Left term of Apply must be Arrow type {fn.typ}')
    if fn.Type().arg != arg.Type():
      raise TypeError(f'Mismatched types {fn} got {arg}')
    self.typ = self.fn.Type().ret

  def __str__(self):
    fn = self.fn
    if isinstance(fn, Expression):
      fn = fn.term
    fn_str = str(self.fn)
    if isinstance(fn, Apply):
      fn_str = '):'.join(fn_str.split('):')[:-1])[1:]
    arg = str(self.arg)
    if ':' in arg and not self._ShouldDisplayArgType():
      arg = ':'.join(arg.split(':')[:-1])
    return f'({fn_str} {arg}):{self.typ}'


class Abstract(Term):
  def __init__(self, arg: Union[Var, BindingVar], body: Term):
    self.arg = arg
    self.body = body
    if isinstance(arg, BindingVar):
      body.MaybeBindFreeVarsTo(arg)
    self.typ = Arrow(self.arg.typ, self.body.typ)

  def __str__(self):
    body = self.BodyTerm()
    args = str(self.arg)
    while isinstance(body, Abstract):
      args = body._AppendMultiArgStr(args, body)
      body = body.BodyTerm()
    return f'(λ{args}.{body}):{self.typ}'

  def BodyTerm(self) -> Term:
    if isinstance(self.body, Expression):
      return self.body.term
    return self.body

  def _AppendMultiArgStr(self, args_str, body):
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

  # def BetaNormal(self) -> bool:
  #   return len(Redexes(self)) == 0

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
      case Apply():
        return Expression(Apply(self.term.fn.Copy(), self.term.arg.Copy()))
      case Abstract():
        bv = self.term.arg
        return Expression(Abstract(bv.var, self.term.body.Copy()))
      case _:
        raise NotImplementedError(
            f'Unexpected member of Expression {self.term}'
        )


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


class KindDeclaration:
  def __init__(self, subj_k: Kind):
    if not isinstance(subj_k, Kind):
      raise ValueError(f'Cannot create KindDeclaration with {subj_k}')
    self.subj = subj_k

  def __str__(self):
    return str(self.subj)


class TypeDeclaration:
  def __init__(self, subj_t: TypeVar):
    if not isinstance(subj_t, TypeVar):
      raise ValueError(f'Cannot create TypeDeclaration with {subj_t}')
    self.subj = BindingTypeVar(subj_t)

  def Type(self):
    return self.subj.typ

  def __str__(self):
    return str(self.subj)


class VarDeclaration:
  def __init__(self, subj: Var):
    if not isinstance(subj, Var):
      raise ValueError(f'Cannot create VarDeclaration with {subj}')
    self.subj = BindingVar(subj)

  def Var(self):
    return self.subj.var

  def __str__(self):
    return str(self.subj)


class Domain(Multiset[Union[Var, TypeVar]]):
    def __init__(self, kinds: list[Kind], types: list[TypeVar], vars: list[Var]):
      self.kinds = Multiset(kinds)
      self.vars = Multiset(vars)
      self.types = Multiset(types)
      self.elems = self.kinds.elems + self.types.elems + self.vars.elems

    def ContainsKind(self, u: Kind):
      assert isinstance(u, Kind)
      return self.kinds.Contains(u)

    def ContainsTypeVar(self, u: TypeVar):
      assert isinstance(u, TypeVar)
      return self.types.Contains(u)

    def ContainsVar(self, u: Var):
      assert isinstance(u, Var)
      return self.vars.Contains(u)


class Context:
  def __init__(self, *args: list[Union[Kind, TypeVar, Var]]):
    self.kind_declarations = []
    self.typ_declarations = []
    self.var_declarations = []
    self.str_declarations = []  # To preserve order for printing only
    for u in args:
      u_str = str(u)
      if u_str != str(Star()):
        self.str_declarations.append(u_str)
      match u:
        case Kind():
          self.kind_declarations.append(KindDeclaration(u))
        case TypeVar():
          if u.kind != Star() and not self.ContainsKind(u.kind):
            raise ValueError(f'Context {self} does not contain kinds in {u}')
          self.typ_declarations.append(TypeDeclaration(u))
        case Var():
          for tv in FreeTypeVars(TypeExpression(u.typ)):
            if not self.ContainsTypeVar(tv.typ):
              raise ValueError(f'Context {self} does not contain free types in {u}')
          self.var_declarations.append(VarDeclaration(u))
        case _:
          raise NotImplementedError(f'Unexpected input to Context {u}')
  
  def __str__(self):
    if not self.str_declarations:
      return 'Ø'
    return ', '.join([d for d in self.str_declarations])

  # Overload for subcontext, A < B returns if A is a subcontext of B
  def __lt__(self, other):
    for u in self.kind_declarations:
      if not any(u.subj == v.subj for v in other.kind_declarations):
        return False
    for u in self.typ_declarations:
      if not any(u.subj.typ == v.subj.typ for v in other.typ_declarations):
        return False
    for u in self.var_declarations:
      if not any(u.subj.var == v.subj.var for v in other.var_declarations):
        return False
    return True

  def BindStatementFreeVars(self, sttmt: Statement):
    if isinstance(sttmt.subj, Kind):
      return
    for decl in self.typ_declarations:
      sttmt.subj.MaybeBindFreeTypesTo(decl.subj)
    if isinstance(sttmt.subj, TypeExpression):
      return
    for decl in self.var_declarations:
      sttmt.subj.MaybeBindFreeVarsTo(decl.subj)

  def ContainsKind(self, kind: Kind):
    return self.Dom().ContainsKind(kind)

  def ContainsTypeVar(self, typ: TypeVar):
    return self.Dom().ContainsTypeVar(typ)

  def ContainsVar(self, u: Var):
    return self.Dom().ContainsVar(u)

  def Dom(self) -> Domain:
    return Domain(
        [decl.subj for decl in self.kind_declarations],
        [decl.subj.typ for decl in self.typ_declarations],
        [decl.subj.var for decl in self.var_declarations]
    )

  def PushKind(self, kind: Kind):
    return Context(*self.Dom(), kind)

  def PushTypeVar(self, u: TypeVar):
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

  def ContainsFreeTypes(self, rho: TypeExpression):
    assert isinstance(rho, TypeExpression)
    return all(
        self.ContainsTypeVar(alpha.typ) for alpha in FreeTypeVars(rho)
    )


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
    self.ctx = premiss.ctx
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
        if premiss.stmt.subj.typ != u.typ:
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
  def __init__(self, u: Union[TypeVar, Var], *premisses):
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
  def __init__(self, *premisses):
    if len(premisses) != 2:
      raise ValueError('Can only create WeakRule with 2 Judgements')
    super().__init__(*premisses)
    p_a, p_b = self.premisses
    assert p_a.ctx < p_b.ctx or p_b.ctx < p_a.ctx
    if p_a.ctx < p_b.ctx:
      self.ctx = p_b.ctx
    else:
      self.ctx = p_a.ctx
    a = p_a.stmt.subj
    b = p_b.stmt.subj
    if Sort(a) != Sort(b):
      raise TypeError(
          f'Both premisses in FormRule must be same sort {p_a} {p_b}'
      )
    match a:
      case Kind():
        self.ab = KArrow(a, b)
      case Type():
        self.ab = TypeExpression(TArrow(a, b))
      case _:
        raise NotImplementedError(f'Unexpected input to FormRule {p_a}')

  def Conclusion(self) -> Judgement:
    return Judgement(self.ctx, Statement(self.ab))


class Derivation:
  def __init__(self, ctx: Context):
    # All derivations in this system start with (sort).
    self.ctx = ctx
    sort_rule = SortRule(ctx)
    self.rules: list[DerivationRule] = [sort_rule]
    self.conclusions: list[Judgement] = [sort_rule.Conclusion()]

  def SortRulePremiss(self) -> Judgement:
    return self.conclusions[0]

  def _AddRule(self, rule: DerivationRule) -> Judgement:
    self.rules.append(rule)
    for p in rule.premisses:
      assert p.ctx < self.ctx
    self.rules[-1].ctx = self.ctx
    concl = rule.Conclusion()
    self.ctx = concl.ctx
    self.conclusions.append(concl)
    return concl

  def _PremissForType(self, typ: TypeVar):
    for i, rule in enumerate(self.rules):
      if (
          isinstance(rule, VarRule)
          and isinstance(rule.u, TypeVar)
          and rule.u == typ
      ):
        return self.conclusions[i]
    raise TypeError(f'{typ} is not declared')

  def VarRule(self, u: Union[TypeVar, Var]) -> Judgement:
    premiss = None
    for i, rule in enumerate(self.rules):
      if not isinstance(rule, VarRule):
        continue
      match (u, rule.u):
        case (TypeVar(), TypeVar()):
          if rule.u == u:
            return self.conclusions[i]
          assert u.kind == Star()  # TODO other kinds
          premiss = self.conclusions[-1]
        case (TypeVar(), _):
          premiss = self.SortRulePremiss()
        case (Var(), Var()):
          if rule.u == u:
            return self.conclusions[i]
          premiss = self._PremissForType(u.Type())
        case (Var(), _):
          premiss = self._PremissForType(u.Type())
        case (_, _):
          raise NotImplementedError(f'Unexpected input to VarRule {u}')
    if premiss is None:
      assert isinstance(u, TypeVar), type(u)
      assert u.kind == Star()
      premiss = self.conclusions[-1]
    concl = self._AddRule(VarRule(premiss, u))
    return concl

  def WeakRule(self, u: Union[TypeVar, Var], p_ab: Judgement, p_cs: Judgement):
    assert p_ab in self.conclusions
    assert p_cs in self.conclusions
    assert p_ab.ctx < self.ctx and p_cs.ctx < self.ctx
    return self._AddRule(WeakRule(u, p_ab, p_cs))

  def FormRule(self, p_a: Judgement, p_b: Judgement):
    assert p_a in self.conclusions
    assert p_b in self.conclusions
    return self._AddRule(FormRule(p_a, p_b))
  
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
        a_key = keys[rule.premisses[0]]
        b_key = keys[rule.premisses[1]]
        return f'(form) on ({a_key}) and ({b_key})'
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
