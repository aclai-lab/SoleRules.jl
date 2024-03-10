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
X = PropositionalLogiset(X_df)

n_instances = ninstances(X)

y = Vector{CLabel}(y)
############################################################################################

# Test
base_decisionlist  = base_cn2(X_df, y)
sole_decisionlist  = sole_cn2(X, y)

@test base_decisionlist isa DecisionList
@test sole_decisionlist isa DecisionList

base_outcome_on_training = apply(base_decisionlist, X)
sole_outcome_on_training = apply(sole_decisionlist, X)

@test all(base_outcome_on_training .== y)
@test all(sole_outcome_on_training .== y)

############################################################################################

# Accuracy
rng = Random.MersenneTwister(1)
permutation = randperm(rng, n_instances)

ntrain = round(Int, n_instances/3)*2

train_slice = permutation[1:ntrain]
test_slice = permutation[(ntrain+1):end]

X_train = SoleData.instances(X, train_slice, Val(false))
X_test = SoleData.instances(X, test_slice, Val(false))

decisonlist = sole_cn2(X_train, y[train_slice])
outcomes = apply(decisonlist, X_test)

############################################################################################

# Time
@btime base_cn2(X_df, y)
@btime sole_cn2(X, y)

# @test_broken outcome_on_training = apply(decision_list, X_pl_view)
