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
global const user_defined_max = 2


Base.in(φ::LeftmostLinearForm, a::Atom) = a ∈ φ.children
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
function Base.push!(
    φ::LeftmostConjunctiveForm, 
    a::Atom
)
    feature(value(a)) ∉ feature(φ) && push!(φ.children, a)
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
        for antecedent ∈ star, atom ∈ atoms(conditions)
            antecedentcopy = deepcopy(antecedent)
            push!(antecedentcopy, atom)
            antecedentcopy ∉ newstar && push!(newstar, antecedentcopy)       
        end
    end
    return newstar
end


# dummy function for entropy
function entropy(
    y::AbstractVector{<:CLabel};
)::Float32
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


# TODO parlarne con Giò
function sorted_antecedents(
    star::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}},
    X::PropositionalLogiset,
    y::Vector{<:CLabel}
)
    # entropyes = Vector(Pairs(antecedent_index, antecedent_entropy))
    entropyes = map(ind -> (ind=>entropy(y[interpret(star[ind], X)])), 
                                1:length(star))

    sort!(entropyes, by=e->e.second)
    # reduce the number of antecedents to user_defined_max
    i_bests = first.(length(entropyes) > user_defined_max ? 
                            entropyes[1:user_defined_max] : entropyes) 
    bestentropy = second(entropyes[1])
    
    return (i_bests, bestentropy)
end



function find_best_antecedent(
    boundedconditions::BoundedScalarConditions,
    X::PropositionalLogiset,
    y::AbstractVector{CLabel}
)
    star = Vector{LeftmostConjunctiveForm}([])
    bestentropy = Inf
    while true

        newstar = specializestar(star, boundedconditions)
        isempty(newstar) && break                                                                           # Exit condition
        # If Cᵢ is statistically significant and better than
        # BEST_CPX by user-defined criteria when tested on E,
        # Then replace the current value of BEST.CPX by Cᵢ.

        # TODO include test for significance
        i_orderedantecedents, newbestentropy = sorted_antecedents(newstar, X, y)
        
        if newbestentropy < bestentropy
            bestantecedent = newstar[i_orderedantecedents[1]] 
            bestruleentropy = newbestentropy
        end

        star = newstar[i_orderedantecedents]
    end
    return entropyes
end


function exec()

    df = DataFrame([1 2 3 ; 5 6 7; 8 9 10], :auto)
    X = PropositionalLogiset(df)
    boundedconditions = alphabet(X, [≤, ≥])

    y = ["+","+","-"]
        
    star0 = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
    star1 = specializestar(star0, boundedconditions)
    @show findbestantecedents(star1[1:4], PropositionalLogiset(df), y)
end


#= 

---- TODO ----


Ho redirezionato molti comportamenti di PropositionalLogiset al suo table interno. 
A proposito rinomina il dataset dentro in qualcosa che faccia capire che è una tabella. Tipo tabledataset, ad esempio.
Ho aggiunto test così si capisce che cosa funziona e cosa non funziona. Aggiungici anche il codice che hai usato te per 
testarlo, così i test diventano più robusti. https://docs.julialang.org/en/v1/stdlib/Test/

=#