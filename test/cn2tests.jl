using Test

using SoleBase: CLabel
using SoleRules
using DataFrames
using SoleModels: ClassificationRule, apply, DecisionList
using SoleData
using MLJ
using StatsBase
using Random

module BaseCN2
include("../src/algorithms/base-cn2.jl")
end

module SoleCN2
include("../src/algorithms/sole-cn2.jl")
end

# Input
X...,y = MLJ.load_iris()
X_df = DataFrame(X)
X = PropositionalLogiset(X_df)
n_instances = ninstances(X)
y = Vector{CLabel}(y)
############################################################################################


# Test
base_decisionlist = BaseCN2.base_cn2(X_df, y)
sole_decisionlist = SoleCN2.sole_cn2(X, y)

@test base_decisionlist isa DecisionList
@test sole_decisionlist isa DecisionList

base_outcome_on_training = apply(base_decisionlist, X)
sole_outcome_on_training = apply(sole_decisionlist, X)

# @test all(base_outcome_on_training .== y)
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

# ================================
decisionlist = SoleCN2.sole_cn2(X_train, y[train_slice])
outcomes = apply(decisionlist, X_test)

decisionlist2 = BaseCN2.base_cn2(SoleData.gettable(X_train), y[train_slice])
outcomes2 = apply(decisionlist2, X_test)

@test all(outcomes .== outcomes2)
# ================================




# @test_nowarn listrules(decisionlist)
# @test_nowarn listrules(decisionlist2)

# @test length(listrules(decisionlist)) == length(listrules(decisionlist2))

# @test SoleModels.antecedent.(listrules(decisionlist)) == SoleModels.antecedent.(listrules(decisionlist2))
# @test SoleModels.consequent.(listrules(decisionlist)) == SoleModels.consequent.(listrules(decisionlist2))

# # @test (listrules(decisionlist)) == (listrules(decisionlist2))

# @test MLJ.accuracy(outcomes, y[test_slice]) > 0.8
# @test MLJ.accuracy(outcomes2, y[test_slice]) > 0.8

# ############################################################################################

# using BenchmarkTools
# # Time
# @btime BaseCN2.base_cn2(X_df, y)
# @btime SoleCN2.sole_cn2(X, y)

# @test_broken outcome_on_training = apply(decision_list, X_pl_view)
