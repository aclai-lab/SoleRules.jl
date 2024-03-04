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


_getmostcommon( classlist ) = findmin(countmap(classlist))[2]


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

# TODO oppure composeformulas(φ, LeftmostConjunctiveForm(a)) ????
function composeformulas!(
    φ::LeftmostConjunctiveForm, 
    a::Atom
)
    feature(value(a)) ∉ feature(φ) && push!(φ.children, a)
end



function smart_conditions(
    bsc::BoundedScalarConditions,
    φ::Formula

)::Union{Bool,BoundedScalarConditions}

    φ_features = feature(φ)
    println("smart")

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

            (reducedconditions = smart_conditions(conditions, antecedent)) != false && continue
            for atom ∈ atoms(reducedconditions)

                antecedentcopy = deepcopy(antecedent)
                composeformulas!(antecedentcopy, atom)

                antecedentcopy ∉ newstar && 
                antecedentcopy ∉ star && push!(newstar, antecedentcopy) 
            end      
        end
    end
    return newstar
end


function new_specializestar(
    star::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}, 
    conditions::BoundedScalarConditions;
    kwargs...
)
    if length(star) == 0
        newstar = [LeftmostConjunctiveForm{Atom{ScalarCondition}}([atom]) for atom ∈ atoms(conditions)]
    else
        newstar = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
        for antecedent ∈ star
            
            reducedconditions = smart_conditions(conditions, antecedent)
            reducedconditions == false && continue 

            for atom ∈ atoms(smart_conditions(conditions, antecedent))

                antecedentcopy = deepcopy(antecedent)
                composeformulas!(antecedentcopy, atom)

                antecedentcopy ∉ newstar && 
                antecedentcopy ∉ star && push!(newstar, antecedentcopy) 
            end      
        end
    end
    return newstar
end




# dummy function for entropy
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

# return the indexes of the covered instances
function coveredindexes(
    φ::LeftmostConjunctiveForm, 
    X::PropositionalLogiset
)
    return findall(z->z==1, interpret(φ, X))
end


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
        newstar = specializestar(star, boundedconditions)

        isempty(newstar) && break   
        orderedantecedents_indexs, newbestentropy = sorted_antecedents(newstar, X, y)
        
        if newbestentropy < bestentropy
            bestantecedent = newstar[orderedantecedents_indexs[1]] 
            bestentropy = newbestentropy
        end
        star = newstar[orderedantecedents_indexs]


        # Non si può fare meglio di così
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
    

    print("computing alphabet...")
    boundedconditions = alphabet(X, [≤, ≥])
    println(" end")
    
    slice_tocover = collect(1:length(y))

    current_X, current_y = X[slice_tocover, :], y[slice_tocover]
 

    rulelist = Vector{SoleModels.ClassificationRule}([])

    while length(slice_tocover) > 0
        
        print("$(length(slice_tocover)) ")
        
        best_antecedent = find_best_antecedent(boundedconditions, current_X, current_y)
        i_covered_relative = coveredindexes(best_antecedent, current_X)
        most_common_class = _getmostcommon(current_y[i_covered_relative])

        # Virtually remove the instances
        setdiff!(slice_tocover, slice_tocover[i_covered_relative])

        current_X, current_y = X[slice_tocover, :], y[slice_tocover]

        push!(rulelist, Rule(best_antecedent, most_common_class))
    end        
    return DecisionList(rulelist, ⊤)

end


#= 
    iris_df = DataFrame(load_iris())
    X_df = iris_df[:, 1:(end-1)]
    y = Vector{CLabel}(iris_df[:, end])
    X_pl = PropositionalLogiset(X_df)
=#



