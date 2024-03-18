import SoleBase: CLabel
using SoleLogics
import SoleLogics: children
import SoleRules: RuleAntecedent

using SoleData
import SoleData: ScalarCondition, PropositionalLogiset, BoundedScalarConditions
import SoleData: alphabet, instances
using SoleModels: DecisionList, Rule, ConstantModel
using DataFrames
using StatsBase: mode, countmap

global beam_width = 3


istop(lmlf::LeftmostLinearForm) = children(lmlf) == [⊤]




# def get_dist(Y, W, domain):
#     """
#     Determine the class distribution for a given array of
#     classifications. Identify the number of classes from the data
#     domain.

#     Parameters
#     ----------
#     Y : ndarray, int
#         Array of classifications.
#     W : ndarray, float
#         Weights.
#     domain : Orange.data.domain.Domain
#         Data domain.

#     Returns
#     -------
#     dist : ndarray
#         Class distribution.

#     """
#     return np.bincount(Y, weights=W, minlength=len(domain.class_var.values))

function get_dist(
    y::Vector{CLabel};
    W::Vector{<:Real}
)



end

function soleentropy(
    y::AbstractVector{<:CLabel};
)::Float32

    distribution = values(countmap(y))
    isempty(distribution) &&
        return Inf
    length(distribution) == 1 &&
        return 0.0

    prob = distribution ./ sum(distribution)
    return -sum(prob .* log2.(prob))
end

# Check condition equivalence
function checkconditionsequivalence(
    φ1::RuleAntecedent,
    φ2::RuleAntecedent,
)::Bool
    return  length(φ1) == length(φ2) &&
            !any(iszero, map( x-> x ∈ atoms(φ1), atoms(φ2)))
end


# function feature(
#     φ::RuleAntecedent
# )::AbstractVector{UnivariateSymbolValue}
#     conditions = value.(atoms(φ))
#     return feature.(conditions)
# end
# function conjunctibleconds(
#     bsc::BoundedScalarConditions,
#     φ::Formula
# )::Union{Bool,BoundedScalarConditions}

#     φ_features = feature(φ)
#     conds = [(meta_cond, vals) for (meta_cond, vals) ∈ bsc.grouped_featconditions
#                 if feature(meta_cond) ∉ φ_features]
#     return conds == [] ? false : BoundedScalarConditions{ScalarCondition}(conds)
# end


function sortantecedents(
    star::AbstractVector{RuleAntecedent},
    X::PropositionalLogiset,
    y::AbstractVector{CLabel},
    beam_width::Int64,
    quality_evaluator::Function
)
    isempty(star) && return [], Inf

    antsquality = map(antd->begin
            satinds = interpret(antd, X) |> findall
            quality_evaluator(y[satinds])
    end, star)

    i_newstar = partialsortperm(antsquality, 1:min(beam_width, length(antsquality)))
    bestantecedent_quality = antsquality[i_newstar[1]]
    return (i_newstar, bestantecedent_quality)
end


function newconditions(
    X::PropositionalLogiset,
    antecedent::RuleAntecedent
)::Vector{Atom{ScalarCondition}}

    satindexes = interpret(antecedent, X) |> findall

    coveredX = SoleData.instances(X, satindexes, Val(true))
    conditions = Atom{ScalarCondition}.(atoms(alphabet(coveredX)))

    return [a for a in conditions if a ∉ atoms(antecedent)]
end

function specializeantecedents(
    star::AbstractVector{RuleAntecedent},
    X::PropositionalLogiset,
)::Vector{RuleAntecedent}

    if isempty(star)
        conditions =  map(sc->Atom{ScalarCondition}(sc), alphabet(X))
        return  map(a->RuleAntecedent([a]), conditions)
    else
        newstar = RuleAntecedent[]
        for i_ant ∈ star
            i_possibleconditions = newconditions(X, i_ant)
            isempty(i_possibleconditions) && continue

            for j_atom ∈ i_possibleconditions
                newantecedent = deepcopy(i_ant)
                push!(newantecedent.children, j_atom)
                push!(newstar, newantecedent)
            end
        end
    end
    return newstar
end

function beamsearch(
    X::PropositionalLogiset,
    y::AbstractVector{CLabel},
    quality_evaluator::Function = soleentropy
)::LeftmostConjunctiveForm

    bestantecedent = LeftmostConjunctiveForm([⊤])
    bestantecedent_entropy = soleentropy(y)

    newstar = RuleAntecedent[]
    while true
        (star, newstar) = newstar, RuleAntecedent[]
        newstar = specializeantecedents(star, X)
        isempty(newstar) && break

        (perm_, candidateantecedent_entropy) = sortantecedents(newstar,X,y,beam_width, quality_evaluator)
        newstar = newstar[perm_]
        if candidateantecedent_entropy < bestantecedent_entropy
            bestantecedent = newstar[1]
            bestantecedent_entropy = candidateantecedent_entropy
        end
    end
    return bestantecedent
end

function sequentialcovering(
    X::PropositionalLogiset,
    y::AbstractVector{CLabel};
)::DecisionList

    length(y) != nrow(X) && error("size of X and y mismatch")
    uncoveredslice = collect(1:ninstances(X))

    uncoveredX = SoleData.instances(X, uncoveredslice, Val(true))
    uncoveredy = y[uncoveredslice]

    rulelist = Rule[]
    while true

        bestantecedent = beamsearch(uncoveredX, uncoveredy)
        istop(bestantecedent) && break

        antecedentcoverage  = interpret(bestantecedent, uncoveredX) |> findall
        consequent = uncoveredy[antecedentcoverage] |> mode
        info_cm = (;
            supporting_labels = nothing
        )
        consequent_cm = ConstantModel(consequent, info_cm)

        push!(rulelist, Rule(bestantecedent, consequent_cm))

        setdiff!(uncoveredslice, uncoveredslice[antecedentcoverage])
        uncoveredX = SoleData.instances(X, uncoveredslice, Val(true))
        uncoveredy = y[uncoveredslice]
    end
    if !allunique(uncoveredy)
        error("Default class can't be created")
    end
    defaultconsequent = uncoveredy[begin]
    return DecisionList(rulelist, defaultconsequent)
end

sole_cn2 = sequentialcovering

#= Int.(values(currentrule_distribution)) =#
# currentrule_distribution = Dict(unique(y) .=> 0)

# for c in coveredy
#     currentrule_distribution[c] += 1
# end
