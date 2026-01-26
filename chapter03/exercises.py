"""
Chapter 3 Exercises
===================

"""

import itertools

from second_order_typed_lambda_calculus import *



def RunExercises():
  # Declate type variables.
  alpha = TypeVar('α')
  beta = TypeVar('β')
  gamma = TypeVar('γ')
  delta = TypeVar('δ')
  sigma = TypeVar('σ')
  nat = TypeVar('nat')
  boolT = TypeVar('bool')
  contradict = PiType(alpha, alpha)


  print('Exercise 3.1')
  f = Var('f', Arrow(alpha, beta))
  x = Var('x', alpha)
  valid_contexts = []
  for p in itertools.permutations([alpha, beta, f, x]):
    try:
      valid_contexts.append(Context(*p))
    except ValueError:
      pass
  for i, ctx in enumerate(valid_contexts):
    print(f'{i + 1}:', ctx)
  

  print('\nExericse 3.2')
  f = Var('f', Arrow(alpha, beta))
  g = Var('g', Arrow(beta, gamma))
  x = Var('x', alpha)
  M = Expression(
      TAbstract(
          alpha,
          TAbstract(
              beta,
              TAbstract(
                  gamma,
                  Abstract(f, Abstract(g, Abstract(x, Apply(g, Apply(f, x)))))
              )
          )
      )
  )
  print('Derive:')
  print(M)
  deriv = DeriveTerm(Judgement(Context(), Statement(M, M.Type())))
  print(deriv.FlagFormat())


  print('\nExercise 3.3a')
  print('M:', M)
  suc = Var('suc', Arrow(nat, nat))
  even = Var('even', Arrow(nat, boolT))
  print('(M nat nat bool suc even):')
  print('Apply nat:')
  M = Expression(TApply(M, nat))
  print(M)
  print('Apply nat:')
  M = Expression(TApply(M, nat))
  print(M)
  print('Apply bool:')
  M = Expression(TApply(M, boolT))
  print(M)
  print('Apply suc:')
  M = Expression(Apply(M, suc))
  print(M)
  print('Apply even:')
  M = Expression(Apply(M, even))
  print(M)

  print('\nExercise 3.3b')
  print(M)
  M = OneStepBetaReduce(M)
  print('    ->', M)
  M = OneStepBetaReduce(M)
  print('    ->', M)
  M = OneStepBetaReduce(M)
  print('    ->', M)
  M = OneStepBetaReduce(M)
  print('    ->', M)
  M = OneStepBetaReduce(M)
  print('    ->', M)

  
  print('\nExercise 3.4')
  f = Var('f', Arrow(alpha, alpha))
  g = Var('g', Arrow(alpha, beta))
  x = Var('x', alpha)
  M = Expression(
      TAbstract(
          alpha,
          TAbstract(
              beta,
              Abstract(
                  f,
                  Abstract(g, Abstract(x, Apply(g, Apply(f, Apply(f, x)))))
              )
          )
      )
  )
  M = Expression(TApply(TApply(M, nat), boolT))
  print('Derive:')
  print(M)
  deriv = DeriveTerm(Judgement(Context(), Statement(M, M.Type())))
  print(deriv.FlagFormat())


  print('\nExercise 3.5')
  print('⊥:', contradict)
  x = Var('x', contradict)
  ctx = Context(beta, x)
  print('Γ:', ctx)

  print('Exercise 3.5a')
  T = ExpressionType(contradict)
  deriv = DeriveType(
      Judgement(Context(), Statement(ExpressionType(contradict), contradict))
  )
  print(deriv.FlagFormat())

  print('Exercise 3.5b')
  M = Expression(TApply(x, beta))
  deriv = DeriveTerm(Judgement(ctx, Statement(M, beta)))
  print(deriv.FlagFormat())

  print('Exercise 3.5c')
  u = Var('u', beta)
  M = Expression(Abstract(u, TApply(x, beta)))
  print(M)
  deriv = DeriveTerm(Judgement(ctx, Statement(M, Arrow(beta, beta))))
  print(deriv.FlagFormat())
  M = Expression(TApply(x, Arrow(beta, beta)))
  print(M)
  deriv = DeriveTerm(Judgement(ctx, Statement(M, Arrow(beta, beta))))
  print(deriv.FlagFormat())
  M = Expression(
      Apply(TApply(x, Arrow(beta, Arrow(beta, beta))), TApply(x, beta))
  )
  print(M)
  deriv = DeriveTerm(Judgement(ctx, Statement(M, Arrow(beta, beta))))
  print(deriv.FlagFormat())

  print('Exercise 3.5d')
  f = Var('f', Arrow(beta, Arrow(beta, beta)))
  M = Expression(
      Abstract(f, Apply(Apply(f, TApply(x, beta)), TApply(x, beta)))
  )
  print(M)
  t1 = M.Type()
  print('type1:', t1)
  N = Expression(TApply(x, Arrow(Arrow(beta, Arrow(beta, beta)), beta)))
  print(N)
  t2 = N.Type()
  print('type2:', t2)
  print('type1 =α type2:', t1 == t2)


  print('\nExercise 3.6a')
  T = ExpressionType(
      PiType(
          alpha,
          PiType(
              beta,
              Arrow(
                  Arrow(nat, alpha),
                  Arrow(Arrow(alpha, Arrow(nat, beta)), Arrow(nat, beta))
              )
          )
      )
  )
  ctx = Context(nat)
  x = Var('x', Arrow(nat, alpha))
  y = Var('y', Arrow(alpha, Arrow(nat, beta)))
  z = Var('z', nat)
  print(T)
  print('Γ:', ctx)
  _, deriv = FindTerm(ctx, T, [x, y, z])
  print(deriv.FlagFormat())

  print('Exercise 3.6b')
  T = ExpressionType(
      PiType(
          delta,
          Arrow(
              Arrow(Arrow(alpha, gamma), delta),
              Arrow(Arrow(alpha, beta), Arrow(Arrow(beta, gamma), delta))
          )
      )
  )
  print(T)
  ctx = Context(alpha, beta, gamma)
  print('Γ:', ctx)
  x = Var('x', Arrow(Arrow(alpha, gamma), delta))
  y = Var('y', Arrow(alpha, beta))
  z = Var('z', Arrow(beta, gamma))
  u = Var('u', alpha)
  _, deriv = FindTerm(ctx, T, [x, y, z, u])
  print(deriv.FlagFormat())

  print('Exercise 3.6c')
  T = ExpressionType(
      PiType(
          alpha,
          PiType(
              beta,
              PiType(
                  gamma,
                  Arrow(
                      Arrow(alpha, Arrow(Arrow(beta, alpha), gamma)),
                      Arrow(alpha, gamma)
                  )
              )
          )
      )
  )
  print(T)
  ctx = Context()
  print('Γ:', ctx)
  x = Var('x', Arrow(alpha, Arrow(Arrow(beta, alpha), gamma)))
  y = Var('y', alpha)
  z = Var('z', beta)
  _, deriv = FindTerm(ctx, T, [x, y, z])
  print(deriv.FlagFormat())


  print('\nExercise 3.7')
  print('⊥:', contradict)
  x = Var('x', Arrow(alpha, contradict))
  f = Var('f', Arrow(Arrow(alpha, alpha), alpha))
  ctx = Context(alpha, beta, x, f)
  print('Γ:', ctx)
  print(f'Term with type {alpha}:')
  u = Var('u', alpha)
  M = Expression(Apply(f, Abstract(u, u)))
  print(M)
  deriv = DeriveTerm(Judgement(ctx, Statement(M, alpha)))
  print(deriv.FlagFormat())
  print(f'Term with type {beta}:')
  N = Expression(TApply(Apply(x, M), beta))
  print(N)
  deriv = DeriveTerm(Judgement(ctx, Statement(N, beta)))
  print(deriv.FlagFormat())


  print('\nExercise 3.8')
  T1 = ExpressionType(
      PiType(alpha, PiType(beta, Arrow(alpha, Arrow(beta, alpha))))
  )
  print('T1:', T1)
  x = Var('x', alpha)
  y = Var('y', beta)
  term, deriv = FindTerm(Context(), T1, [x, y])
  print(term)
  print(deriv.FlagFormat())
  T2 = ExpressionType(
      PiType(alpha, Arrow(alpha, PiType(beta, Arrow(beta, alpha))))
  )
  print('T2:', T2)
  M = Expression(
      TAbstract(alpha, Abstract(x, TAbstract(beta, Abstract(y, x))))
  )
  print(M)
  deriv = DeriveTerm(Judgement(Context(), Statement(M, T2.Type())))
  print(deriv.FlagFormat())


  print('\nExercise 3.9')
  x = Var('x', Arrow(alpha, Arrow(beta, gamma)))
  y = Var('y', Arrow(alpha, beta))
  z = Var('z', alpha)
  S = Expression(
      TAbstract(
          alpha,
          TAbstract(
              beta,
              TAbstract(
                  gamma,
                  Abstract(
                      x,
                      Abstract(y, Abstract(z, Apply(Apply(x, z), Apply(y, z))))
                  )
              )
          )
      )
  )
  print(S)


  print('\nExercise 3.10a')
  x = Var('x', PiType(alpha, Arrow(alpha, alpha)))
  M = Expression(
      Abstract(x, Apply(TApply(x, Arrow(sigma, sigma)), TApply(x, sigma)))
  )
  print('M:', M)
  deriv = DeriveTerm(Judgement(Context(sigma), Statement(M, M.Type())))
  print(deriv.FlagFormat())

  print('Exercise 3.10b')
  y = Var('y', alpha)
  N = Expression(TAbstract(alpha, Abstract(y, y)))
  print('N:', N)
  applied = Expression(Apply(M, N))
  print('(M N):', applied)
  deriv = DeriveTerm(
      Judgement(Context(sigma), Statement(applied, applied.Type()))
  )
  print(deriv.FlagFormat())


  print('\nExercise 3.11')
  print('⊥:', contradict)
  x = Var('x', contradict)
  M = Expression(
      Abstract(
          x,
          Apply(
            Apply(
                TApply(x, Arrow(contradict, Arrow(contradict, contradict))),
                Apply(TApply(x, Arrow(contradict, contradict)), x)
            ),
            Apply(
                Apply(
                    TApply(
                        x, Arrow(contradict, Arrow(contradict, contradict))
                    ),
                    x
                ),
                x
            ),
          )
      )
  )
  print(M)
  deriv = DeriveTerm(Judgement(Context(), Statement(M, M.Type())))
  print(deriv.FlagFormat())
  print('type:', M.Type())


  print('\nExercise 3.12')
  Nat = ExpressionType(
      PiType(alpha, Arrow(Arrow(alpha, alpha), Arrow(alpha, alpha)))
  )
  print('Nat:', Nat)
  f = Var('f', Arrow(alpha, alpha))
  x = Var('x', alpha)
  Zero = Expression(TAbstract(alpha, Abstract(f, Abstract(x, x))))
  print('Zero:', Zero)
  One = Expression(TAbstract(alpha, Abstract(f, Abstract(x, Apply(f, x)))))
  print('One:', One)
  Two = Expression(
      TAbstract(alpha, Abstract(f, Abstract(x, Apply(f, Apply(f, x)))))
  )
  print('Two:', Two)
  n = Var('n', Nat)
  fb = Var('f', Arrow(beta, beta))
  xb = Var('x', beta)
  Suc = Expression(
      Abstract(
          n,
          TAbstract(
              beta,
              Abstract(
                  fb,
                  Abstract(
                      xb, Apply(fb, Apply(Apply(TApply(n, beta), fb), xb))
                  )
              )
          )
      )
  )
  print('Suc:', Suc)
  SZero = Expression(Apply(Suc, Zero))
  print('(Suc Zero):', SZero)
  SZero = BetaReduce(SZero)
  print('    ->>', SZero)
  print('    =α One:', SZero == One)
  SOne = Expression(Apply(Suc, One))
  print('(Suc One):', SOne)
  SOne = BetaReduce(SOne)
  print('    ->>', SOne)
  print('    =α Two:', SOne == Two)


  print('\nExercise 3.13a')
  m = Var('m', Nat)
  Add = Expression(
      Abstract(
          m,
          Abstract(
              n,
              TAbstract(
                  alpha,
                  Abstract(
                      f,
                      Abstract(
                          x,
                          Apply(
                              Apply(TApply(m, alpha), f),
                              Apply(Apply(TApply(n, alpha), f), x)
                          )
                      )
                  )
              )
          )
      )
  )
  # One = Expression(TAbstract(alpha, Abstract(f, Abstract(x, Apply(f, x)))))
  print('Add:', Add)
  Added = Expression(Apply(Apply(Add, One), One))
  print('(Add One One):', Added)
  Added = BetaReduce(Added)
  print('    ->>', Added)
  print('    =α Two:', Added == Two)

  print('Exercise 3.13b')
  Mult = Expression(
      Abstract(
          m,
          Abstract(
              n,
              TAbstract(
                  alpha,
                  Abstract(
                      f,
                      Abstract(
                          x,
                          Apply(
                              Apply(
                                  TApply(m, alpha), Apply(TApply(n, alpha), f)
                              ),
                              x
                          )
                      )
                  )
              )
          )
      )
  )
  print('Mult:', Mult)
  MOneZero = Expression(Apply(Apply(Mult, One), Zero))
  print('(Mult One Zero):', MOneZero)
  MOneZero = BetaReduce(MOneZero)
  print('    ->>', MOneZero)
  print('    =α Zero:', MOneZero == Zero)
  MTwoZero = Expression(Apply(Apply(Mult, Two), Zero))
  print('(Mult Two Zero):', MTwoZero)
  MTwoZero = BetaReduce(MTwoZero)
  print('    ->>', MTwoZero)
  print('    =α Zero:', MTwoZero == Zero)
  MZeroTwo = Expression(Apply(Apply(Mult, Zero), Two))
  print('(Mult Zero Two):', MZeroTwo)
  MZeroTwo = BetaReduce(MZeroTwo)
  print('    ->>', MZeroTwo)
  print('    =α Zero:', MZeroTwo == Zero)
  MOneOne = Expression(Apply(Apply(Mult, One), One))
  print('(Mult One One):', MOneOne)
  MOneOne = BetaReduce(MOneOne)
  print('    ->>', MOneOne)
  print('    =α One:', MOneOne == One)
  MOneTwo = Expression(Apply(Apply(Mult, One), Two))
  print('(Mult One Two):', MOneTwo)
  MOneTwo = BetaReduce(MOneTwo)
  print('    ->>', MOneTwo)
  print('    =α Two:', MOneTwo == Two)


  print('\nExercise 3.14')
  Bool = ExpressionType(PiType(alpha, Arrow(alpha, Arrow(alpha, alpha))))
  print('Bool:', Bool)
  x = Var('x', alpha)
  y = Var('y', alpha)
  Tru = Expression(TAbstract(alpha, Abstract(x, Abstract(y, x))))
  print('True:', Tru)
  Fls = Expression(TAbstract(alpha, Abstract(x, Abstract(y, y))))
  print('False:', Fls)
  u = Var('u', Bool)
  p = Var('p', beta)
  q = Var('q', beta)
  Neg = Expression(
      Abstract(
          u,
          TAbstract(
              beta,
              Abstract(p, Abstract(q, Apply(Apply(TApply(u, beta), q), p)))
          )
      )
  )
  print('Neg:', Neg)
  NTrue = Expression(Apply(Neg, Tru))
  print('(Neg True):', NTrue)
  NTrue = BetaReduce(NTrue)
  print('    ->>', NTrue)
  print('    =α False:', NTrue == Fls)
  NFalse = Expression(Apply(Neg, Fls))
  print('(Neg False):', NFalse)
  NFalse = BetaReduce(NFalse)
  print('    ->>', NFalse)
  print('    =α True:', NFalse == Tru)


  print('\nExercise 3.15')
  v = Var('v', Bool)
  M = Expression(
      Abstract(
          u,
          Abstract(
              v,
              TAbstract(
                  beta,
                  Abstract(
                      p,
                      Abstract(
                          q,
                          Apply(
                              Apply(
                                  TApply(u, beta),
                                  Apply(Apply(TApply(v, beta), p), q)
                              ),
                              Apply(Apply(TApply(v, beta), q), q)
                          )
                      )
                  )
              )
          )
      )
  )
  print('M:', M)
  print('Exercise 3.15a')
  MTrueTrue = Expression(Apply(Apply(M, Tru), Tru))
  print('(M True True):', MTrueTrue)
  MTrueTrue = BetaReduce(MTrueTrue)
  print('    ->>', MTrueTrue)
  print('    =α True:', MTrueTrue == Tru)
  MTrueFalse = Expression(Apply(Apply(M, Tru), Fls))
  print('(M True False):', MTrueFalse)
  MTrueFalse = BetaReduce(MTrueFalse)
  print('    ->>', MTrueFalse)
  print('    =α False:', MTrueFalse == Fls)
  MFalseTrue = Expression(Apply(Apply(M, Fls), Tru))
  print('(M False True):', MFalseTrue)
  MFalseTrue = BetaReduce(MFalseTrue)
  print('    ->>', MFalseTrue)
  print('    =α False:', MFalseTrue == Fls)
  MFalseFalse = Expression(Apply(Apply(M, Fls), Fls))
  print('(M False False):', MFalseFalse)
  MFalseFalse = BetaReduce(MFalseFalse)
  print('    ->>', MFalseFalse)
  print('Exercise 3.15b')
  print('M is logical And')


  print('\nExercise 3.16')
  Or = Expression(
      Abstract(
          u,
          Abstract(
              v,
              TAbstract(
                  beta,
                  Abstract(
                      p,
                      Abstract(
                          q,
                          Apply(
                              Apply(
                                  TApply(u, beta),
                                  Apply(Apply(TApply(v, beta), p), p)
                              ),
                              Apply(Apply(TApply(v, beta), p), q)
                          )
                      )
                  )
              )
          )
      )
  )
  print('Or:', Or)
  OrTrueTrue = Expression(Apply(Apply(Or, Tru), Tru))
  print('(Or True True):', OrTrueTrue)
  OrTrueTrue = BetaReduce(OrTrueTrue)
  print('    ->>', OrTrueTrue)
  print('    =α True:', OrTrueTrue == Tru)
  OrTrueFalse = Expression(Apply(Apply(Or, Tru), Fls))
  print('(Or True False):', OrTrueFalse)
  OrTrueFalse = BetaReduce(OrTrueFalse)
  print('    ->>', OrTrueFalse)
  print('    =α True:', OrTrueFalse == Tru)
  OrFalseTrue = Expression(Apply(Apply(Or, Fls), Tru))
  print('(Or False True):', OrFalseTrue)
  OrFalseTrue = BetaReduce(OrFalseTrue)
  print('    ->>', OrFalseTrue)
  print('    =α True:', OrFalseTrue == Tru)
  OrFalseFalse = Expression(Apply(Apply(Or, Fls), Fls))
  print('(Or False False):', OrFalseFalse)
  OrFalseFalse = BetaReduce(OrFalseFalse)
  print('    ->>', OrFalseFalse)
  print('    =α False:', OrFalseFalse == Fls)
  Xor = Expression(
      Abstract(
          u,
          Abstract(
              v,
              TAbstract(
                  beta,
                  Abstract(
                      p,
                      Abstract(
                          q,
                          Apply(
                              Apply(
                                  TApply(u, beta),
                                  Apply(Apply(TApply(v, beta), q), p)
                              ),
                              Apply(Apply(TApply(v, beta), p), q)
                          )
                      )
                  )
              )
          )
      )
  )
  print('Xor:', Xor)
  XorTrueTrue = Expression(Apply(Apply(Xor, Tru), Tru))
  print('(Or True True):', XorTrueTrue)
  XorTrueTrue = BetaReduce(XorTrueTrue)
  print('    ->>', XorTrueTrue)
  print('    =α False:', XorTrueTrue == Fls)
  XorTrueFalse = Expression(Apply(Apply(Xor, Tru), Fls))
  print('(Or True False):', XorTrueFalse)
  XorTrueFalse = BetaReduce(XorTrueFalse)
  print('    ->>', XorTrueFalse)
  print('    =α True:', XorTrueFalse == Tru)
  XorFalseTrue = Expression(Apply(Apply(Xor, Fls), Tru))
  print('(Or False True):', XorFalseTrue)
  XorFalseTrue = BetaReduce(XorFalseTrue)
  print('    ->>', XorFalseTrue)
  print('    =α True:', XorFalseTrue == Tru)
  XorFalseFalse = Expression(Apply(Apply(Xor, Fls), Fls))
  print('(Or False False):', XorFalseFalse)
  XorFalseFalse = BetaReduce(XorFalseFalse)
  print('    ->>', XorFalseFalse)
  print('    =α False:', XorFalseFalse == Fls)
  Implies = Expression(
      Abstract(
          u,
          Abstract(
              v,
              TAbstract(
                  beta,
                  Abstract(
                      p,
                      Abstract(
                          q,
                          Apply(
                              Apply(
                                  TApply(u, beta),
                                  Apply(Apply(TApply(v, beta), p), q)
                              ),
                              Apply(Apply(TApply(v, beta), p), p)
                          )
                      )
                  )
              )
          )
      )
  )
  print('Implies:', Implies)
  ImpliesTrueTrue = Expression(Apply(Apply(Implies, Tru), Tru))
  print('(Implies True True):', ImpliesTrueTrue)
  ImpliesTrueTrue = BetaReduce(ImpliesTrueTrue)
  print('    ->>', ImpliesTrueTrue)
  print('    =α True:', ImpliesTrueTrue == Tru)
  ImpliesTrueFalse = Expression(Apply(Apply(Implies, Tru), Fls))
  print('(Implies True False):', ImpliesTrueFalse)
  ImpliesTrueFalse = BetaReduce(ImpliesTrueFalse)
  print('    ->>', ImpliesTrueFalse)
  print('    =α False:', ImpliesTrueFalse == Fls)
  ImpliesFalseTrue = Expression(Apply(Apply(Implies, Fls), Tru))
  print('(Implies False True):', ImpliesFalseTrue)
  ImpliesFalseTrue = BetaReduce(ImpliesFalseTrue)
  print('    ->>', ImpliesFalseTrue)
  print('    =α True:', ImpliesFalseTrue == Tru)
  ImpliesFalseFalse = Expression(Apply(Apply(Implies, Fls), Fls))
  print('(Implies False False):', ImpliesFalseFalse)
  ImpliesFalseFalse = BetaReduce(ImpliesFalseFalse)
  print('    ->>', ImpliesFalseFalse)
  print('    =α True:', ImpliesFalseFalse == Tru)


  print('\nExercise 3.17')
  Nat = ExpressionType(
      PiType(alpha, Arrow(Arrow(alpha, alpha), Arrow(alpha, alpha)))
  )
  Bool = ExpressionType(PiType(beta, Arrow(beta, Arrow(beta, beta))))
  n = Var('n', Nat)
  u = Var('u', gamma)
  v = Var('v', gamma)
  w = Var('w', gamma)
  IsZero = Expression(
      Abstract(
          n,
          TAbstract(
              gamma,
              Abstract(
                  u,
                  Abstract(
                      v, Apply(Apply(TApply(n, gamma), Abstract(w, v)), u)
                  )
              )
          )
      )
  )
  print('IsZero:', IsZero)
  IsZZero = Expression(Apply(IsZero, Zero))
  print('(IsZero Zero):', IsZZero)
  IsZZero = BetaReduce(IsZZero)
  print('    ->>', IsZZero)
  print('    =α True:', IsZZero == Tru)
  IsZOne = Expression(Apply(IsZero, One))
  print('(IsZero One):', IsZOne)
  IsZOne = BetaReduce(IsZOne)
  print('    ->>', IsZOne)
  print('    =α False:', IsZOne == Fls)
  IsZTwo = Expression(Apply(IsZero, Two))
  print('(IsZero Two):', IsZTwo)
  IsZTwo = BetaReduce(IsZTwo)
  print('    ->>', IsZTwo)
  print('    =α False:', IsZTwo == Fls)


  print('\nExercise 3.18')
  Bool = ExpressionType(PiType(beta, Arrow(beta, Arrow(beta, beta))))
  Tree = ExpressionType(
      PiType(
          alpha,
          Arrow(
              Arrow(Bool, alpha),
              Arrow(Arrow(Bool, Arrow(alpha, Arrow(alpha, alpha))), alpha)
          )
      )
  )
  print('Tree:', Tree)

  print('Exercise 3.18a')
  u = Var('u', Arrow(Bool, alpha))
  v = Var('v', Arrow(Bool, Arrow(alpha, Arrow(alpha, alpha))))
  def BuildTree(M: Expression):
    assert M.Type() == alpha
    return Expression(TAbstract(alpha, Abstract(u, Abstract(v, M))))
  print('M = (u False):')
  print(BuildTree(Expression(Apply(u, Fls))))
  print('M = (v True (u False) (u True)):')
  print(
      BuildTree(
          Expression(Apply(Apply(Apply(v, Tru), Apply(u, Fls)), Apply(u, Tru)))
      )
  )
  print('M = (v True (u True) (v False (u True) (u False))):')
  print(
      BuildTree(
          Expression(
              Apply(
                  Apply(Apply(v, Tru), Apply(u, Tru)),
                  Apply(Apply(Apply(v, Fls), Apply(u, Tru)), Apply(u, Fls))
              )
          )
      )
  )

  print('Exercise 3.18b')
  p = Var('p', Bool)
  s = Var('s', Tree)
  t = Var('t', Tree)
  ug = Var('u', Arrow(Bool, gamma))
  vg = Var('v', Arrow(Bool, Arrow(gamma, Arrow(gamma, gamma))))
  M = Expression(
      Abstract(
          p,
          TAbstract(
              gamma,
              Abstract(
                  ug,
                  Abstract(
                      vg,
                      Apply(
                          Apply(
                              Apply(vg, p),
                              Apply(Apply(TApply(s, gamma), ug), vg)
                          ),
                          Apply(Apply(TApply(t, gamma), ug), vg)
                      )
                  )
              )
          )
      )
  )
  print(M)


if __name__ == '__main__':
  RunExercises()