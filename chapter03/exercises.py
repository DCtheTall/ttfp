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

if __name__ == '__main__':
  RunExercises()