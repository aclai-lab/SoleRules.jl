#= Sole =#
using SoleLogics
using SoleRules
using SoleData
using Debugger
dbg = Debugger
#= Others =#
using BenchmarkTools
using DataFrames
#= Import  =#
import SoleData: PropositionalLogiset, BoundedScalarConditions
import SoleData: propositionalalphabet, feature
import SoleLogics: children
import Base: ==


Base.in(φ::LeftmostConjunctiveForm, a::Atom) = a ∈ φ.children

# Due LeftmostConjunctiveForm sono uguali se hanno:
#    - lo stesso numero di atomi
#    - ogni atomo di φ₁ è anche on φ₂
function ==(
    φ1::LeftmostConjunctiveForm,
    φ2::LeftmostConjunctiveForm,
)::Bool
    return length(φ1) == length(φ2) && 
        !any(iszero, map( x-> x ∈ atoms(φ1), atoms(φ2)))
end

function feature(
    φ::LeftmostConjunctiveForm
)::AbstractVector{UnivariateSymbolFeature}
    conditions =  value.(atoms(φ))
    return feature.(conditions)
end

function Base.push!(
    φ::LeftmostConjunctiveForm, 
    a::Atom
)
    feature(value(a)) ∉ feature(φ) && push!(φ.children, a)
end


function specializestar(
    star::Vector{LeftmostConjunctiveForm{Atom}}, 
    conditions::BoundedScalarConditions;
    kwargs...
)
    if length(star) == 0
        newstar = [LeftmostConjunctiveForm{Atom}([atom]) for atom ∈ atoms(conditions)]
    else
        newstar = []
        for antecedent ∈ star, atom ∈ atoms(conditions)
            antecedentcopy = deepcopy(antecedent)
            push!(antecedentcopy, atom)
            antecedentcopy ∉ newstar && push!(newstar, antecedentcopy)       
        end
    end
    return newstar
end


function mmm()
    df = DataFrame([1 2; 4 5], :auto)
    boundedconditions = propositionalalphabet(PropositionalLogiset(df))
        
    #= function findBestAntecedent =#
    star0 = Vector{LeftmostConjunctiveForm{Atom}}([])
    #= function SpecializeStar =#
    star1 = specializestar(star0, boundedconditions)
    star2 = specializestar(star1, boundedconditions)

    return star2
end



#===========================================================================

AbstractSyntaxStructure
    LeftmostLinearForm
    Literal
    MultiFormula
    SyntaxTree
        SyntaxBranch
        SyntaxLeaf
            Atom
            Truth
                BooleanTruth
                HeytingTruth

=============================================================================#


#= ERROR in SPECIALIZESTAR             
    convert(#unused#::Type{Atom
                            ScalarCondition
                                Int64, 
                                UnivariateSymbolFeature, 
                                ScalarMetaCondition{UnivariateSymbolFeature, 🔋typeof(<=)}}}}, 
                                
                    p::Atom{
                            ScalarCondition{
                                Int64, 
                                UnivariateSymbolFeature, 
                                ScalarMetaCondition{UnivariateSymbolFeature, 🔋typeof(>=)}}})
=#
