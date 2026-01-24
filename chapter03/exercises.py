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
              Abstract(f, Abstract(g, Abstract(x, Apply(g, Apply(f, Apply(f, x))))))
          )
      )
  )
  M = Expression(TApply(TApply(M, nat), boolT))
  print('Derive:')
  print(M)
  deriv = DeriveTerm(Judgement(Context(), Statement(M, M.Type())))
  print(deriv.FlagFormat())

if __name__ == '__main__':
  RunExercises()