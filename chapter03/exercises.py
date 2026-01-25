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
  M = OneStepBetaReduce(M, [], [])
  print('    ->', M)
  M = OneStepBetaReduce(M, [], [])
  print('    ->', M)
  M = OneStepBetaReduce(M, [], [])
  print('    ->', M)
  M = OneStepBetaReduce(M, [], [])
  print('    ->', M)
  M = OneStepBetaReduce(M, [], [])
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
  SZero = BetaReduce(SZero, [], [])
  print('    ->>', SZero)
  print('    =α One:', SZero == One)
  SOne = Expression(Apply(Suc, One))
  print('(Suc One):', SOne)
  SOne = BetaReduce(SOne, [], [])
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
  Added = BetaReduce(Added, [], [])
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
  MOneZero = BetaReduce(MOneZero, [], [])
  print('    ->>', MOneZero)
  print('    =α Zero:', MOneZero == Zero)
  MTwoZero = Expression(Apply(Apply(Mult, Two), Zero))
  print('(Mult Two Zero):', MTwoZero)
  MTwoZero = BetaReduce(MTwoZero, [], [])
  print('    ->>', MTwoZero)
  print('    =α Zero:', MTwoZero == Zero)
  MZeroTwo = Expression(Apply(Apply(Mult, Zero), Two))
  print('(Mult Zero Two):', MZeroTwo)
  MZeroTwo = BetaReduce(MZeroTwo, [], [])
  print('    ->>', MZeroTwo)
  print('    =α Zero:', MZeroTwo == Zero)
  MOneOne = Expression(Apply(Apply(Mult, One), One))
  print('(Mult One One):', MOneOne)
  MOneOne = BetaReduce(MOneOne, [], [])
  print('    ->>', MOneOne)
  print('    =α One:', MOneOne == One)
  MOneTwo = Expression(Apply(Apply(Mult, One), Two))
  print('(Mult One Two):', MOneTwo)
  MOneTwo = BetaReduce(MOneTwo, [], [])
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
  z = Var('z', Bool)
  u = Var('u', alpha)
  v = Var('v', alpha)
  Neg = Expression(
      Abstract(
          z,
          TAbstract(
              alpha,
              Abstract(u, Abstract(v, Apply(Apply(TApply(z, alpha), v), u)))
          )
      )
  )
  print('Neg:', Neg)
  NTrue = Expression(Apply(Neg, Tru))
  print('(Neg True):', NTrue)
  NTrue = BetaReduce(NTrue, [], [])
  print('    ->>', NTrue)
  print('    =α False:', NTrue == Fls)
  NFalse = Expression(Apply(Neg, Fls))
  print('(Neg False):', NFalse)
  NFalse = BetaReduce(NFalse, [], [])
  print('    ->>', NFalse)
  print('    =α True:', NFalse == Tru)


if __name__ == '__main__':
  RunExercises()