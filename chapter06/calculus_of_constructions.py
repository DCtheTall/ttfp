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