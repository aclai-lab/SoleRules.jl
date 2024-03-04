using Test

using SoleBase: CLabel
using SoleRules
using DataFrames
using SoleModels: ClassificationRule, apply
using MLJ


X...,y = MLJ.load_iris()

X = DataFrame(X)
y = Vector{CLabel}(y)

X_pl_view = PropositionalLogiset(@view X[:,:])


# Test on training data
@btime decision_list = CN2(X, y)
@btime sole_decision_list = sole_cn2(X_pl_view, y)

@test_broken outcome_on_training = apply(decision_list, X_pl_view)

outcome_on_training = apply(decision_list, X_pl)


@test decision_list isa DecisionList
@test all(outcome_on_training .== y)


