"""
Chapter 2: Simply Typed Lambda Calculus
=======================================

"""


from typing import Optional, Sequence, Union

import untyped as ut


class Type:
  def __str__(self):
    raise NotImplementedError('Do not cast Type subclass to str')

  def __hash__(self):
    return id(self)


class TypeVar(Type):
  def __init__(self, name: str):
    self.name = name

  def __str__(self):
    return self.name


class Arrow(Type):
  def __init__(self, arg: Type, ret: Type):
    self.arg = arg
    self.ret = ret

  def __hash__(self):
    return hash(hash(self.arg) + hash(self.ret))
  
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
    if isinstance(self.body, Expression):
      return self.body.term
    return self.body


class Expression(Term):
  term: Term
  typ: Type

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
      v = u.arg
      if not isinstance(v, BindingVar):
        v = BindingVar(v)
      body = Expression(u.body)
      body.MaybeBindFreeVarsTo(v)
      self.term = Abstract(v, body)
    else:
      raise NotImplementedError(f'Unexpected input to Expression {type(u)}')
    self.typ = self.term.typ

  def __str__(self):
    return str(self.term)

  def __eq__(self, other):
    return AlphaEquiv(self, other)

  def __rshift__(self, other):
    return BetaEquiv(self, other)

  def MaybeBindFreeVarsTo(self, v: BindingVar):
    if isinstance(self.term, Var):
      raise Exception('Should not store Var in Expression')
    elif isinstance(self.term, BindingVar):
      raise Exception('Should not store BindingVar in Expression')
    elif isinstance(self.term, FreeVar):
      if v.ShouldBind(self.term):
        self.term = BoundVar(v, self.term)
    elif isinstance(self.term, BoundVar):
      pass
    elif isinstance(self.term, Apply):
      self.term.fn.MaybeBindFreeVarsTo(v)
      self.term.arg.MaybeBindFreeVarsTo(v)
    elif isinstance(self.term, Abstract):
      self.term.body.MaybeBindFreeVarsTo(v)
    else:
      raise NotImplementedError(f'Unexpected member of Expression {self.term}')
  
  def Copy(self):
    if isinstance(self.term, FreeVar) or isinstance(self.term, BoundVar):
      return Expression(self.term.var)
    if isinstance(self.term, Apply):
      return Expression(Apply(self.term.fn.Copy(), self.term.arg.Copy()))
    if isinstance(self.term, Abstract):
      bv = self.term.arg
      return Expression(Abstract(bv.var, self.term.body.Copy()))
    raise NotImplementedError(f'Unexpected member of Expression {self.term}')

  def Closed(self) -> bool:
    return len(FreeVars(self)) == 0

  def BetaNormal(self) -> bool:
    return len(Redexes(self)) == 0


class Multiset:
  terms: list[Term]

  def Contains(self, x: Term) -> bool:
    return x in self.terms

  def __str__(self):
    if len(self) == 0:
      return 'Ø'
    terms = ', '.join([str(x) for x in self])
    return f'[{terms}]'

  def __iter__(self):
    for term in self.terms:
      yield term

  def __len__(self):
    return len(self.terms)


class FreeVars(Multiset):
  def __init__(self, e: Expression):
    if isinstance(e.term, Var):
      raise Exception('Should not store Var in Expression')
    elif isinstance(e.term, BindingVar):
      raise Exception('Should not store BindingVar in Expression')
    elif isinstance(e.term, FreeVar):
      self.terms = [e.term.var]
    elif isinstance(e.term, BoundVar):
      self.terms = []
    elif isinstance(e.term, Apply):
      self.terms = FreeVars(e.term.fn).terms + FreeVars(e.term.arg).terms
    elif isinstance(e.term, Abstract):
      self.terms = FreeVars(e.term.body).terms
    else:
      raise NotImplementedError(f'Unexpected member of Expression {e.term}')

  def ContainsBindingVar(self, bv: BindingVar):
    return self.Contains(bv.var)


class Statement:
  def __init__(self, subject: Expression, typ: Type):
    if subject.typ != typ:
      raise TypeError(
          f'Cannot create Statement with expression with type {subject.typ} '
          f'and type {typ}'
      )
    self.subj = subject
    self.typ = typ

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


class Domain(Multiset):
    def __init__(self, vars: list[Var]):
      self.terms = vars


class Context:
  def __init__(self, *vars: Sequence[Var]):
    self.declarations = [Declaration(u) for u in vars]
    uniq_vars = set(d.Var().name for d in self.declarations)
    if len(self.declarations) != len(uniq_vars):
      raise ValueError('All declarations must be diferent')

  def __str__(self):
    if not self.declarations:
      return 'Ø'
    return ', '.join([str(d) for d in self.declarations])

  # Overload for subcontext, A < B returns if A is a subcontext of B
  def __lt__(self, other):
    for u in self.declarations:
      for v in other.declarations:
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
    for decl in self.declarations:
      sttmt.subj.MaybeBindFreeVarsTo(decl.subj)
  
  def ContainsVar(self, u: Var):
    return self.Dom().Contains(u)

  def PullVar(self, u: Var):
    return Context(*[v for v in self.Dom() if v != u])

  def PushVar(self, u: Var):
    return Context(u, *self.Dom())

  def PushVars(self, *us: list[Var]):
    return Context(*us, *self.Dom())

  def Dom(self) -> Domain:
    return Domain([decl.subj.var for decl in self.declarations])


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
    return Judgement(p_fn.ctx, Statement(expr, expr.typ))


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
    return Judgement(p.ctx.PullVar(a), Statement(expr, expr.typ))


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
    concl = self._AddRule(ApplRule(fn, arg))
    return concl

  def AbstRule(self, arg: Var, body: Judgement) -> Judgement:
    assert body in self.conclusions
    concl = self._AddRule(AbstRule(arg, body))
    self.ctx = concl.ctx
    return concl

  def _Justification(self, rule: DerivationRule, keys: dict[Judgement, str]) -> str:
    if isinstance(rule, VarRule):
      return '(var)'
    if isinstance(rule, ApplRule):
      fn_key = keys[rule.premisses[0]]
      arg_key = keys[rule.premisses[1]]
      return f'(appl) on ({fn_key}) and ({arg_key})'
    if isinstance(rule, AbstRule):
      body_key = keys[rule.premisses[0]]
      return f'(abst) on ({body_key})'
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
    abst_order: list[Var] = []
    for rule in self.rules:
      if isinstance(rule, AbstRule):
        abst_order.append(rule.arg)
    abst_order = list(reversed(abst_order))
    def _SortKey(decl: Declaration, abst_order: list[Var]):
      try:
        return abst_order.index(decl.subj.var)
      except ValueError:
        return -1
    declarations = sorted(
        self.conclusions[0].ctx.declarations,
        key=lambda d: _SortKey(d, abst_order)
    )
    for decl in declarations:
      key = chr(ord('a') + len(keys))
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
        if isinstance(rule, AbstRule):
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
  term_vars: list[Var] = []
  def _FindVars(M: Expression):
    if isinstance(M.term, FreeVar):
      assert jdgmnt.ctx.ContainsVar(M.term.var)
    elif isinstance(M.term, BoundVar):
      pass
    elif isinstance(M.term, Abstract):
      term_vars.append(M.term.arg.var)
      _FindVars(M.term.body)
    elif isinstance(M.term, Apply):
      _FindVars(M.term.fn)
      _FindVars(M.term.arg)
    else:
      raise ValueError(f'Unexpected term {M.term}')
  _FindVars(Expression(jdgmnt.stmt.subj))
  ctx = jdgmnt.ctx.PushVars(*term_vars)
  d = Derivation(ctx)
  def _Helper(M: Expression) -> DerivationRule:
    if isinstance(M.term, FreeVar):
      return d.VarRule(M.term.var)
    if isinstance(M.term, BoundVar):
      raise ValueError(f'Should not need rule for bound variable {M.term}')
    if isinstance(M.term, Apply):
      return d.ApplRule(_Helper(M.term.fn), _Helper(M.term.arg))
    if isinstance(M.term, Abstract):
      return d.AbstRule(M.term.arg.var, _Helper(Expression(M.term.body)))
  _Helper(Expression(jdgmnt.stmt.subj))
  return d


class ContextMissingTypeError(Exception):
  pass


class MissingReturnTypeError(Exception):
  pass


def FindTerm(
    ctx: Context, typ: Type, new_vars: list[Var]
) -> tuple[Expression, Derivation]:
  def _Helper(ctx: Context, typ: Type, new_vars: list[Var]):
    for decl in ctx.declarations:
      if decl.subj.typ == typ:
        return ctx, Expression(decl.subj.var)
    if isinstance(typ, Arrow):
      for u in new_vars:
        if u.typ == typ.arg:
          new_vars.remove(u)
          ctx, body = _Helper(ctx.PushVar(u), typ.ret, new_vars)
          return ctx, Expression(Abstract(u, body))
      else:
        raise ContextMissingTypeError(
            f'Need variable with type {typ.arg} to add to Context'
        )
    for decl in ctx.declarations:
      target_t = decl.subj.typ
      arg_goals = []
      while isinstance(target_t, Arrow) and target_t != typ:
        arg_goals.append(target_t.arg)
        target_t = target_t.ret
      if target_t == typ:
        term = Expression(decl.subj.var)
        try:
          for arg_goal in arg_goals:
            _, arg = _Helper(ctx, arg_goal, new_vars)
            term = Expression(Apply(term, arg))
          return ctx, term
        except MissingReturnTypeError:
          continue
    else:
      raise MissingReturnTypeError(f'No variable has or returns {typ}')
  _, term = _Helper(ctx, typ, new_vars)
  return term, DeriveTerm(Judgement(ctx, Statement(term, typ)))


class TypePlaceholder(Type):
  typ: Optional[Type]

  def __init__(self):
    self.typ = None

  def Prune(self):
    typ = self
    while isinstance(typ, TypePlaceholder) and typ.typ is not None:
      typ = typ.typ
    return typ

  def OccursIn(self, typ):
    if isinstance(typ, Arrow):
      return self.OccursIn(typ.arg) or self.OccursIn(typ.ret)
    if self.Prune() == typ.Prune():
      return True
    if typ.typ is not None:
      return self.OccursIn(typ.typ)
    return False


def InferTypes(
    M: ut.Expression, free_types: list[Type]
) -> list[tuple[ut.Expression, Type]]:
  def _Prune(typ: Type):
    if isinstance(typ, TypePlaceholder):
      return typ.Prune()
    return typ

  def _Unify(t1: Type, t2: Type):
    t1 = _Prune(t1)
    t2 = _Prune(t2)
    if t1 == t2:
      return
    if isinstance(t1, TypePlaceholder):
      if t1.OccursIn(t2):
        raise TypeError('Term is not typeable due to cycle')
      t1.typ = t2
      return
    if isinstance(t2, TypePlaceholder):
      if t2.OccursIn(t1):
        raise TypeError('Term is not typeable due to cycle')
      t2.typ = t1
      return
    if isinstance(t1, Arrow) and isinstance(t2, Arrow):
      _Unify(t1.arg, t2.arg)
      _Unify(t1.ret, t2.ret)
      return
    raise TypeError('Type mismatch unifying types')

  def _Infer(M: ut.Expression, env: dict[ut.Var, TypePlaceholder]):
    if isinstance(M.term, ut.FreeVar):
      if M.term.var in env:
        return [(M, env[M.term.var])]
      typ_p = TypePlaceholder()
      env[M.term.var] = typ_p
      return [(M, typ_p)]
    if isinstance(M.term, ut.BoundVar):
      assert M.term.var in env
      return [(M, env[M.term.var])]
    if isinstance(M.term, ut.Apply):
      fn_types = _Infer(M.term.fn, env)
      arg_types = _Infer(M.term.arg, env)
      ret_p = TypePlaceholder()
      _Unify(fn_types[0][1], Arrow(arg_types[0][1], ret_p))
      return [(M, ret_p)] + fn_types + arg_types
    if isinstance(M.term, ut.Abstract):
      arg_p = TypePlaceholder()
      new_env = env.copy()
      new_env[M.term.arg.var] = arg_p
      body_types = _Infer(M.term.body, new_env)
      return (
          [(M, Arrow(arg_p, body_types[0][1]))]
          + [(M.term.arg, arg_p)]
          + body_types
      )
    raise Exception(f'Unexpected input to InferType {M}')
  types = _Infer(M, {})
  
  def _Assign(typ: Type, typemap: dict[TypePlaceholder, TypeVar]):
    typ = _Prune(typ)
    if isinstance(typ, Arrow):
      typemap[typ] = Arrow(_Assign(typ.arg, typemap), _Assign(typ.ret, typemap))
      return typemap[typ]
    if typ in typemap:
      return typemap[typ]
    if not free_types:
      raise TypeError('Need more free types')
    typemap[typ] = free_types.pop()
    return typemap[typ]
  typemap = {}
  for _, typ in types:
    _Assign(typ, typemap)
  return [(N, typemap[_Prune(typ_p)]) for N, typ_p in types]


def InferType(M: ut.Expression, free_types: list[TypeVar]):
  return InferTypes(M, free_types)[0][1]


def Rename(M: Expression, x: Var, y: Var) -> Expression:
  def _HasBindingVar(M: Expression, y: Var) -> bool:
    if isinstance(M.term, Var):
      raise Exception('Should not store Var in Expression')
    if isinstance(M.term, BindingVar):
      raise Exception('Should not store BindingVar in Expression')
    if (
        isinstance(M.term, BoundVar)
        or isinstance(M.term, FreeVar)
    ):
      return False
    if isinstance(M.term, Apply):
      return _HasBindingVar(M.term.fn, y) or _HasBindingVar(M.term.arg, y)
    if isinstance(M.term, Abstract):
      bv = M.term.arg
      if bv.var == y:
        return True
      return _HasBindingVar(M.term.body, y)
    raise NotImplementedError(f'Unexpected input to HasBindingVar {M}')

  def _RenameBoundVars(
      M: Expression, x: BindingVar, y: BindingVar
  ) -> Expression:
    assert isinstance(x, BindingVar) and isinstance(y, BindingVar)
    if isinstance(M.term, FreeVar):
      return M
    if isinstance(M.term, BoundVar):
      if M.term.bv == x:
        return BoundVar(y, FreeVar(y.var))
      return M
    if isinstance(M.term, Apply):
      return Expression(
          Apply(
              _RenameBoundVars(M.term.fn, x, y),
              _RenameBoundVars(M.term.arg, x, y)
          )
      )
    if isinstance(M.term, Abstract):
      return Expression(
          Abstract(M.term.arg, _RenameBoundVars(M.term.body, x, y))
      )
    raise NotImplementedError(f'Unexpected input to RenameBoundVars {M}')

  if isinstance(M.term, FreeVar):
    if M.term.var == x:
      return Expression(y)
    return Expression(M.term.var)
  if isinstance(M.term, BoundVar):
    return M
  if isinstance(M.term, Apply):
    return Expression(Apply(Rename(M.term.fn, x, y), Rename(M.term.arg, x, y)))
  if isinstance(M.term, Abstract):
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
    return Expression(Abstract(v, Rename(N, x, y)))
  raise NotImplementedError(f'Unexpected input to Rename {M}')


def AlphaEquiv(x: Expression, y: Expression) -> bool:
  def _Helper(x: Expression, y: Expression, de_brujin: dict[Var, int]):
    if isinstance(x.term, FreeVar):
      return isinstance(y.term, FreeVar) and x.term == y.term
    if isinstance(x.term, BoundVar):
      if not isinstance(y.term, BoundVar):
        return False
      xu = x.term.var
      yu = y.term.var
      if xu in de_brujin and yu in de_brujin:
        return de_brujin[xu] == de_brujin[yu]
      if xu not in de_brujin and yu not in de_brujin:
        return xu == yu
      return False
    if isinstance(x.term, Apply):
      return (
          isinstance(y.term, Apply)
          and _Helper(x.term.fn, y.term.fn, de_brujin)
          and _Helper(x.term.arg, y.term.arg, de_brujin)
      )
    if isinstance(x.term, Abstract):
      if not isinstance(y.term, Abstract):
        return False
      xu = x.term.arg
      yu = y.term.arg
      new_de_brujin = de_brujin.copy()
      new_de_brujin[xu.var] = new_de_brujin[yu.var] = len(de_brujin)
      return _Helper(x.term.body, y.term.body, new_de_brujin)
    raise NotImplementedError(f'Unexpected input to AlphaEquiv {x}')
  return _Helper(x, y, de_brujin={})


def Substitute(
    M: Expression, x: Var, N: Expression, zs: list[Var],
    binding: Optional[BindingVar] = None,
) -> Expression:
  if isinstance(M.term, FreeVar):
    if M.term == x:
      return N
    return M
  if isinstance(M.term, BoundVar):
    if binding is not None and M.term.BoundTo(binding):
      return N
    return M
  if isinstance(M.term, Apply):
    return Expression(
        Apply(
            Substitute(M.term.fn, x, N, zs, binding),
            Substitute(M.term.arg, x, N, zs, binding)
        )
    )
  if isinstance(M.term, Abstract):
    if FreeVars(N).ContainsBindingVar(M.term.arg):
      if not zs:
        raise Exception('Need more variables for substitution')
      z = zs.pop()
      assert not FreeVars(N).Contains(z)
      M = Rename(M, M.term.arg, z)
    return Expression(
        Abstract(M.term.arg, Substitute(M.term.body, x, N, zs, binding))
    )
  raise NotImplementedError(f'Unexpected term in input for Substitute {M}')


class Redexes(Multiset):
  def __init__(self, M: Expression):
    if isinstance(M.term, Occurrence):
      self.terms = []
    elif isinstance(M.term, Apply):
      self.terms = []
      if isinstance(M.term.FuncTerm(), Abstract):
        self.terms.append(M.term)
      self.terms.extend(Redexes(M.term.fn).terms)
      self.terms.extend(Redexes(M.term.arg).terms)
    elif isinstance(M.term, Abstract):
      self.terms = Redexes(M.term.body).terms
    else:
      raise NotImplementedError(f'Unexpected input to Redexes {M}')


def OneStepBetaReduce(M: Expression, zs: list[Var] = [], applicative=False):
  if isinstance(M.term, Occurrence):
    return M
  if isinstance(M.term, Apply):
    # Applicative order: evaluate innermost-leftmost redex first.
    if applicative:
      if not M.term.fn.BetaNormal():
        return Expression(
            Apply(OneStepBetaReduce(M.term.fn, zs, applicative), M.term.arg)
        )
      if not M.term.arg.BetaNormal():
        return Expression(
            Apply(M.term.fn, OneStepBetaReduce(M.term.arg, zs, applicative))
        )
      if isinstance(M.term.FuncTerm(), Abstract):
        M, N = M.term.fn, M.term.arg
        return Substitute(M.term.body, M.term.arg.var, N, zs, M.term.arg)
      return M
    # Normal order: evaluate outermost-leftmost redex first.
    if isinstance(M.term.FuncTerm(), Abstract):
      M, N = M.term.fn, M.term.arg
      return Substitute(M.term.body, M.term.arg.var, N, zs, M.term.arg)
    if M.term.fn.BetaNormal():
      return Expression(
          Apply(M.term.fn, OneStepBetaReduce(M.term.arg, zs, applicative))
      )
    return Expression(
        Apply(OneStepBetaReduce(M.term.fn, zs, applicative), M.term.arg)
    )
  if isinstance(M.term, Abstract):
    return Expression(
        Abstract(M.term.arg, OneStepBetaReduce(M.term.body, zs, applicative))
    )
  raise NotImplementedError(f'Unexpected input to OneStepBetaReduce {M}')


def BetaReduce(M: Expression):
  # In λ-> all terms are guaranteed to normalize.
  while not M.BetaNormal():
    M = OneStepBetaReduce(M)
  return M


def BetaEquiv(M: Expression, N: Expression):
  return BetaReduce(M) == BetaReduce(N)
