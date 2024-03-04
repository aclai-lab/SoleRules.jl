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




_getmostcommon(classlist) = findmin(countmap(classlist))[2]


function Base.:(==)(
    φ1::LeftmostLinearForm,
    φ2::LeftmostLinearForm,
)::Bool
    return typeof(φ1) == typeof(φ2) && 
            length(φ1) == length(φ2) && 
                !any(iszero, map( x-> x ∈ atoms(φ1), atoms(φ2)))
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

function conjunctible_conditions(
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
        newstar = [LeftmostConjunctiveForm{Atom{ScalarCondition}}([atom]) for atom ∈ atoms(conditions)]
    else
        newstar = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
        for antecedent ∈ star

            (reducedconditions = conjunctible_conditions(conditions, antecedent)) != false && continue
            for atom ∈ atoms(reducedconditions)

                antecedentcopy = deepcopy(antecedent)
                composeformulas!(antecedentcopy, atom)

                antecedentcopy ∉ newstar && 
                antecedentcopy ∉ star && 
                push!(newstar, antecedentcopy) 
            end      
        end
    end
    return newstar
end


function old_specializestar(
    star::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}, 
    conditions::BoundedScalarConditions;
    kwargs...
)
    if length(star) == 0
        newstar = [LeftmostConjunctiveForm{Atom{ScalarCondition}}([atom]) for atom ∈ atoms(conditions)]
    else
        newstar = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
        for antecedent ∈ star, atom ∈ atoms(conditions)
                antecedentcopy = deepcopy(antecedent)
                composeformulas!(antecedentcopy, atom)

                antecedentcopy ∉ newstar && 
                antecedentcopy ∉ star && push!(newstar, antecedentcopy) 
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


#= ================================================================================================================ =#

function coveredindexes(
    φ::LeftmostConjunctiveForm, 
    X::PropositionalLogiset
)
    return findall(z->z==1, interpret(φ, X))
end

 
# Ordina gli antecedenti ( formule del tipo LeftmostCF ) in base all' entropia
function sorted_antecedents(
    star::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}},
    X::PropositionalLogiset,
    y::Vector{<:CLabel}
)
    entropyes = map(ind->(ind=>entropy(y[interpret(star[ind], X)])), 
                1:length(star))
                
    sort!(entropyes, by=e->e.second)
    i_bests = first.(length(entropyes) > user_defined_max ? 
                            entropyes[1:user_defined_max] : entropyes)

    bestentropy = entropyes[1].second
    return (i_bests, bestentropy)
end



function find_best_antecedent(
    boundedconditions::BoundedScalarConditions,
    X::PropositionalLogiset,
    y::AbstractVector{CLabel}
)
    star = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
    bestantecedent = LeftmostConjunctiveForm([⊤])
    bestentropy = Inf
    
    while true

        newstar = SPEC_VERSION == :old ? 
            old_specializestar(star, boundedconditions) : specializestar(star, boundedconditions)

        isempty(newstar) && break   
        orderedantecedents_indexs, newbestentropy = sorted_antecedents(newstar, X, y)
        
        if newbestentropy < bestentropy
            bestantecedent = newstar[orderedantecedents_indexs[1]] 
            bestentropy = newbestentropy
        end
        star = newstar[orderedantecedents_indexs]


        # Attenzione qui
        # bestentropy ≤ 0.0 ? break : continue

    end
    return bestantecedent
end

function sole_cn2(
    X::PropositionalLogiset,
    y::AbstractVector{CLabel};
    kwargs...
)
    length(y) != nrow(X) && error("size of X and y mismatch")

    println("SPEC_VERSION = $(SPEC_VERSION)")

    boundedconditions = alphabet(X, [≤, ≥])    
    slice_tocover = collect(1:length(y))
    
    current_X = X[slice_tocover, :]
    current_y = y[slice_tocover]

    rulelist = Vector{SoleModels.ClassificationRule}([])
    while length(slice_tocover) > 0
        
        # print("$(length(slice_tocover)) ")
        
        best_antecedent = find_best_antecedent(boundedconditions, current_X, current_y)
        covered_offsets = coveredindexes(best_antecedent, current_X)
        antecedentclass = _getmostcommon(current_y[covered_offsets])

        push!(rulelist, Rule(best_antecedent, antecedentclass))
                
        setdiff!(slice_tocover, slice_tocover[covered_offsets])        
        current_X = X[slice_tocover, :]
        current_y = y[slice_tocover]
    end        
    return DecisionList(rulelist, ⊤)

end

