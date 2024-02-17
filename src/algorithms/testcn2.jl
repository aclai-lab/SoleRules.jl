using DataFrames
using SoleLogics
using SoleRules
using SoleData
import SoleData: PropositionalLogiset, BoundedScalarConditions
import SoleData: propositionalalphabet, feature

using Debugger
db = Debugger


Base.in(φ::LeftmostConjunctiveForm, a::Atom) = a ∈ φ.children
antecedent(v::AbstractVector{LeftmostConjunctiveForm}) = length(v)





function feature(
    φ::LeftmostConjunctiveForm
)::AbstractVector{UnivariateSymbolFeature}
    conditions =  value.(φ.children)
    return feature.(conditions)
end

function Base.push!(
    φ::LeftmostConjunctiveForm, 
    atom::Atom
)
    feature(value(atom)) ∉ feature(φ) && push!(φ.children, atom)
    # features = feature(φ) 
    # if feature(value(atom)) ∉ features 
    #     push!(φ.children, a)
    # end
end



function specializestar(
    star::AbstractVector{LeftmostConjunctiveForm}, 
    conditions::BoundedScalarConditions;
    kwargs...
)
    if nantecedent(star) == 0
        newstar = [LeftmostConjunctiveForm([atom]) for atom ∈ atoms(conditions)]
    else
        newstar = []#= Vector{LeftmostConjunctiveForm{Atom{ScalarCondition{Int64, UnivariateSymbolFeature, ScalarMetaCondition{UnivariateSymbolFeature, Function}}}}}([]) =#
        for antecedent ∈ star
            for atom ∈ atoms(conditions)
                antecedentcopy = deepcopy(antecedent)
                push!(antecedentcopy, atom)

                antecedentcopy ∉ newstar && push!(newstar, antecedentcopy)       
            end
        end
    end
    return newstar
end
#=             convert(#unused#::Type{Atom
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


function mmm()
    df = DataFrame([1 2 3; 4 5 6], :auto)
    boundedconditions = propositionalalphabet(PropositionalLogiset(df))
        
    #= function findBestAntecedent =#
    star0 = Vector{LeftmostConjunctiveForm}([])
    @bp
    #= function SpecializeStar =#
    star1 = specializestar(star0, boundedconditions)
    star2 = specializestar(star1, boundedconditions)
    ret = features(star1[1])
    println(ret)

end