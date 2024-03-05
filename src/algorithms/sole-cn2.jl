#= Sole =#
using SoleLogics
using SoleRules
using SoleData
using Debugger
using SoleBase
dbg = Debugger
#= Others =#
using BenchmarkTools
using DataFrames
using StatsBase: countmap
#= Import  =#
import SoleData: PropositionalLogiset, ScalarCondition, BoundedScalarConditions
import SoleData: alphabet, feature
import SoleLogics: children
import SoleBase: CLabel
import Base: ==, ∈

# variabile temporaneamente globale

global user_defined_max = 3
global SPEC_VERSION = :new



# Check condition equivalence
function checkconditionsequivalence(
    φ1::LeftmostLinearForm,
    φ2::LeftmostLinearForm,
)::Bool
    return  typeof(φ1) == typeof(φ2) &&
            length(φ1) == length(φ2) &&
            !any(iszero, map( x-> x ∈ atoms(φ1), atoms(φ2)))
end

function checkconditionsequivalence(
    φ1::LeftmostLinearForm,
    φs::Vector{LeftmostLinearForm},
)::Bool
    return any(φ_i->checkconditionsequivalence(φ_i, φ1), φ_i ∈ φs)
end


function feature(
    φ::LeftmostConjunctiveForm{Atom{ScalarCondition}}
)::AbstractVector{UnivariateSymbolValue}
    conditions = value.(atoms(φ))
    return feature.(conditions)
end

function composeformulas!(
    φ::LeftmostConjunctiveForm,
    a::Atom
)
    feature(value(a)) ∉ feature(φ) && push!(φ.children, a)
end

# return only conditions that make sense to be conjuncted with φ
# If no conditions are founded -> return false

function conjunctibleconds(
    bsc::BoundedScalarConditions,
    φ::Formula
)::Union{Bool,BoundedScalarConditions}

    φ_features = feature(φ)
    conds = [(meta_cond, vals) for (meta_cond, vals) ∈ bsc.grouped_featconditions
                if feature(meta_cond) ∉ φ_features]
    return conds == [] ? false : BoundedScalarConditions{ScalarCondition}(conds)
end

function specializestar(
    star::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}},
    conditions::BoundedScalarConditions;
    kwargs...
)
    if length(star) == 0

        newstar = map(a->LeftmostConjunctiveForm{Atom{ScalarCondition}}([a]), atoms(conditions))

    else
        newstar = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
        for antecedent ∈ star
            (reducedconditions = conjunctibleconds(conditions, antecedent)) == false && continue
            for atom ∈ atoms(reducedconditions)

                antecedentcopy = deepcopy(antecedent)
                composeformulas!(antecedentcopy, atom)

                checkconditionsequivalence(antecedentcopy, antecedent) &&
                checkconditionsequivalence(antecedentcopy, newstar ) &&
                push!(newstar, antecedentcopy)
            end
        end
    end
    return newstar
end

function entropy(
    y::AbstractVector{<:CLabel};
)::Float32

    length(y) == 0 && return Inf

    count = values(countmap(y))
    length(count) == 1 && return 0.0

    logbase = length(count)
    prob = count ./ sum(count)
    return -sum(prob .* log.(logbase, prob))
end

# Ordina gli antecedenti ( formule del tipo LeftmostCF ) in base all' entropia
function sorted_antecedents(
    star::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}},
    X::PropositionalLogiset,
    y::Vector{<:CLabel}
)
    antsentropy = map(ind->(ind=>entropy(y[interpret(star[ind], X)])), 1:length(star))
    sort!(antsentropy, by=e->e.second)
    i_bests = first.(length(antsentropy) > user_defined_max ?
                antsentropy[1:user_defined_max] : antsentropy)

    bestentropy = antsentropy[1].second
    return (i_bests, bestentropy)
end

function bestantecedent(
    boundedconditions::BoundedScalarConditions,
    X::PropositionalLogiset,
    y::AbstractVector{CLabel}
)
    star = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
    best_antecedent = LeftmostConjunctiveForm([⊤])
    bestentropy = Inf

    while true

        newstar = specializestar(star, boundedconditions)

        isempty(newstar) && break
        orderedantecedents_indexs, newbestentropy = sorted_antecedents(newstar, X, y)

        if newbestentropy < bestentropy
            best_antecedent = newstar[orderedantecedents_indexs[1]]
            bestentropy = newbestentropy
        end
        star = newstar[orderedantecedents_indexs]
    end
    return best_antecedent
end

function sole_cn2(
    X::PropositionalLogiset,
    y::AbstractVector{CLabel};
    kwargs...
)
    length(y) != nrow(X) && error("size of X and y mismatch")

    boundedconditions = SoleData.alphabet(X, [≤, ≥])
    slice_tocover = collect(1:length(y))

    current_X = X[slice_tocover, :]
    current_y = y[slice_tocover]

    rulelist = Vector{SoleModels.ClassificationRule}([])
    while length(slice_tocover) > 0

        best_antecedent = bestantecedent(boundedconditions, current_X, current_y)
        covered_offsets = findall(z->z==1, interpret(best_antecedent, current_X))
        antecedentclass = findmax(countmap(current_y[covered_offsets]))[2]

        push!(rulelist, Rule(best_antecedent, antecedentclass))
        setdiff!(slice_tocover, slice_tocover[covered_offsets])

        current_X = X[slice_tocover, :]
        current_y = y[slice_tocover]
    end
    return DecisionList(rulelist, ⊤)

end
