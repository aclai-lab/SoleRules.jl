using Test

using SoleBase: CLabel
using SoleRules
using DataFrames
using SoleModels: ClassificationRule, apply, DecisionList
using SoleData
using MLJ
using StatsBase


include("../src/algorithms/base-cn2.jl")
include("../src/algorithms/sole-cn2.jl")

# Input
X...,y = MLJ.load_iris()

X_df = DataFrame(X)
X_pl = PropositionalLogiset(X_df)

n_instances = ninstances(X_pl)

y = Vector{CLabel}(y)
############################################################################################

# Test
base_decisionlist  = base_cn2(X_df, y)
sole_decisionlist  = sole_cn2(X_pl, y)

@test base_decisionlist isa DecisionList
@test sole_decisionlist isa DecisionList

base_outcome_on_training = apply(base_decisionlist, X_pl)
sole_outcome_on_training = apply(sole_decisionlist, X_pl)

@test all(base_outcome_on_training .== y)
@test all(sole_outcome_on_training .== y)

############################################################################################

# Accuracy test
ntrain = 2 * round(Int, n_instances/3)

ind_train = sample(1:n_instances, ntrain, replace=false)
ind_test = setdiff(collect(1:n_instances), train_indxs)

X_pl_train = SoleData.instances(X_pl, ind_train, Val(false))
X_pl_test  = SoleData.instances(X_pl, ind_test, Val(false))

dl_partialdataset = sole_cn2(X_pl_train, y[ind_train])
oc_partialdataset = apply(dl_partialdataset, X_pl_test)          # outcomes









# Time
# @btime base_cn2(X, y)
# @btime sole_cn2(X_pl_view, y)

# @test_broken outcome_on_training = apply(decision_list, X_pl_view)
