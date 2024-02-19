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
import SoleData: propositionalalphabet, feature
import SoleLogics: children
import SoleBase: CLabel
import Base: ==, ∈


function feature(
    φ::LeftmostConjunctiveForm{Atom{ScalarCondition}}
)::AbstractVector{UnivariateSymbolFeature}
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

function entropy(
    φ::Formula,
    P::PropositionalLogiset,
    y::AbstractVector{CLabel};
    kwargs...
    )::Float32


    interpretations = interpret(φ, P)

    # getindex.....


    count = values(countmap(interpretations))
    length(count) == 1 && return 0.0     

    logbase = length(val)
    prob = count ./ sum(count)

    return -sum(prob .* log.(logbase, prob))
end

#= ================================================================================================================ =#
function findbestantecedent(
    boundedconditions::BoundedScalarConditions,
    examples::AbstractDataFrame,
    y::AbstractVector{CLabel};
    kwargs...
)
    star = Vector{LeftmostConjunctiveForm}([])
    # bestantecedent = LeftmostConjunctiveForm([TOP])               
    pl = PropositionalLogiset(examples)

    while true
        newstar = specializestar(star, boundedconditions)
        isempty(newstar) && break # Exit condition
        
        entropyes = map(ind -> (ind=>entropy(
                                    newstar[ind], 
                                    pl,
                                    y
                                    )), 1:length(newstar))

        # ordinamento!(entropyes, "ordina secondo entropia")
        # newbestruleentropy = entropydf[1, :E]

        # if (newbestruleentropy < bestruleentropy)
        #     bestantecedent, bestruleentropy = entropydf[1, :]
        # end
        # # Reduce de number of rules to the user defined max

        # userdefinedmax = 3
        # if nrow(entropydf) > userdefinedmax
        #     entropydf = entropydf[1:userdefinedmax, :]
        # end
        # newstarrules = entropydf[:, :R] 
        # star = rules2star( newstarrules )
    end
    return bestrule
end


function exec()
    df = DataFrame([1 2; 4 5], :auto)
    boundedconditions = propositionalalphabet(PropositionalLogiset(df))
        
    star0 = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])

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

