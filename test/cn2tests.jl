using Test

using SoleBase: CLabel
using SoleRules
using DataFrames
using SoleModels: ClassificationRule, apply
using MLJ


X...,y = MLJ.load_iris()

X = DataFrame(X)
y = Vector{CLabel}(y)


X_pl = PropositionalLogiset( @view X_df[:,:] )


@time decision_list = CN2(X_df, y) 
outcome_on_training = apply(decision_list, X_pl)


@test decision_list isa DecisionList
@test all(outcome_on_training .== y)



 

