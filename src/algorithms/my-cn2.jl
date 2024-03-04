using SoleData
using SoleLogics
using SoleBase
using SoleModels
using DataFrames
using Random
using StatsBase: countmap
# using Debugger
# using CSV
# db = Debugger
import SoleLogics: LogicalInstance, Formula, LeftmostLinearForm
import SoleModels: Rule, AbstractModel, ConstantModel
import SoleBase: CLabel
import SoleData: PropositionalLogiset, BoundedScalarConditions
import SoleData: features, UnivariateSymbolValue

global bestruleentropy = 2.0
global test_ops = [≥, ≤]
global user_defined_max = 3


struct Selector    
    att::Symbol # simil Feature
    val
    test_operator
end

# >>>

    Base.show(io::IO, s::Selector) = print(io, "($(s.att) $(s.test_operator) $(s.val))")
    test_operator(sel::Selector) = sel.test_operator
    varname(sel::Selector) = sel.att
    treshold(sel::Selector) = sel.val # che poi non è una treshold :)

    function computeselectors(df)

        selectorlist = []
        attributes = names(df)
        for attribute ∈ attributes, test_op ∈ test_ops
            map( x -> push!( selectorlist, Selector(Symbol(attribute), x, test_op)), 
                        unique(df[:, attribute]) 
                )
        end
        return selectorlist
    end

    function selector2soleatom(sel::Selector)::Atom
        feature = UnivariateSymbolValue(varname(sel))
        tresh = treshold(sel)
        test_op = test_operator(sel)
        return Atom(ScalarCondition(feature, test_op, tresh))
    end
    function selector2soleatom(sel::Set{Selector})::Tuple{Atom}
        return Tuple(selector2soleatom.(sel))
    end
#######################################################################################################  

struct RuleBody
    selectors::Set{Selector}
end

# >>>

    function Base.:(==)(r1::RuleBody, r2::RuleBody)
        if ( length(r1.selectors) != length(r2.selectors) )
                return false
        end
        for r1sel in r1.selectors
            if r1sel ∉ r2.selectors
                return false
            end
        end
            return true
    end
        
    function Base.show(io::IO, r::RuleBody)
        nselector = length(getselectors(r))
        count = 1
        for sel in r.selectors
            print(io, "$sel")
            if count < nselector
                print(io, " ∧ ")
            end
            count = count + 1
        end
    end
    
    getselectors(rb::RuleBody) = rb.selectors
    pushselector!(rule::RuleBody, selector::Selector) = push!(rule.selectors, selector)
    getattributes(r::RuleBody) = [varname(sel) for sel ∈ getselectors(r)]

    function appendselector(rule::RuleBody, s::Selector)
        newrule = deepcopy(rule)
        if s.att ∉ getattributes(rule)
            pushselector!(newrule, s)
        end
        return newrule
    end
    
#######################################################################################################  

struct MyRule
    body::RuleBody
    head
end

# >>>

    function Base.show(io::IO, rule::MyRule)
        println(io, " $(rule.body) ⟶ ($(rule.head))" )
    end

    head(r::MyRule) = r.head 
    getselectors(mr::MyRule) = getselectors(mr.body)
    _AND(atoms) = length(atoms) > 1 ? LeftmostConjunctiveForm(∧(atoms)) : atoms[1]
    
    function myrule2solerule(myrule::MyRule)
        selectors = getselectors(myrule)
        atoms = selector2soleatom(selectors)
        
        _antecedent = _AND(atoms)
        _consequent = ConstantModel(head(myrule))
        return Rule(_antecedent, _consequent)
    end

#######################################################################################################  

struct Star 
    rules::Array{RuleBody}
end

# >>>

    starsize(star::Star) = length(star.rules)
    pushrule!(star, rule) = push!(star.rules, rule)
    rules2star(ruleslist::Array{RuleBody}) = Star(ruleslist)
    rules(star::Star) = star.rules
    

    function specializestar(star, selectors)
        if isempty(star)
            newstar = Star([RuleBody(Set([sel])) for sel ∈ selectors])
        else
            newstar = Star([])
            for rule ∈ rules(star)
                for selector ∈ selectors
                    newrule = appendselector(rule, selector)
                    if (newrule ∉ rules(newstar)) && (newrule != rule)
                        pushrule!(newstar, newrule)
                    end 
                end
            end
        end
        return newstar
    end

    Base.isempty(star::Star) = (length(star.rules) == 0)

    function Base.show(io::IO, s::Star)
        println("Star:")
        for r in rules(s)
            print(" • ")
            println(io,r)
        end
    end
    function Base.show(io::IO, dict::Dict{RuleBody, Float32})
        for key ∈ keys(dict)
            println(io,"$key    $(dict[key])")
        end
    end

#######################################################################################################  

struct RuleList
    list::Vector{MyRule}
end

# >>>

    function Base.show(io::IO, rl::RuleList)
        println("Rules: ( ordered )")
        for rule ∈ rl.list
            print(io, " * ")
            print(rule)
        end
    end
    
    function Base.getindex(rl::RuleList, index::Int)
        return rl.list[index]
    end
########################################################################################################
# End structures definition

_getmostcommon( classlist ) = findmin(countmap(classlist))[2]
symbolnames(X_df::AbstractDataFrame) = Symbol.(names(X_df))

function entropy(x)

    if length(x) == 0 return Inf end
    val = values(countmap(x))
    if length(val) == 1 return 0.0 end    
    logbase = length(val)
    prob = val ./ sum(val)
    return -sum( prob .* log.(logbase, prob) )
end

function complexcoverage(rulebody::RuleBody, examples)::Vector{Bool}

    compcov = ones(Bool, nrow(examples))

    for selector ∈ getselectors(rulebody)
        test_op = test_operator(selector)
        compcov = test_op.(examples[!, varname(selector)], 
                                        treshold(selector)
                                        ) .& compcov
    end

    return compcov
end 

function entropy(rule, examples)
    coveredindexes = findall(x->x==1, complexcoverage(rule, examples) )
    coveredclasses = examples[coveredindexes, end]
    return entropy(coveredclasses)
end

function findBestComplex(selectors, X, y)

    star = Star([])
    bestrule = RuleBody(Set([]))
    bestruleentropy = 2
    while true

        newstar = specializestar(star, selectors)
    
        if isempty(newstar)
            break
        end
        entropydf = DataFrame(R=RuleBody[], E=Float32[])
        for rule ∈ newstar.rules
                    
            coverage = complexcoverage(rule, X)
            coveredindexes = findall(x->x==1, coverage)
            push!(entropydf, ( 
                        rule, 
                        entropy(y[coveredindexes]),

                    ))
        end
        sort!(entropydf, [:E])
        newbestruleentropy = entropydf[1, :E]
        if newbestruleentropy < bestruleentropy
            bestrule, bestruleentropy = entropydf[1, :]
        end
        if nrow(entropydf) > user_defined_max
            entropydf = entropydf[1:user_defined_max, :]
        end
        star = rules2star(entropydf[:, :R])
    end
return bestrule
end

function _getmostcommon( classlist )
    occurrence = countmap(classlist)
    return findmin(occurrence)[2]
end



function CN2(
    X::AbstractDataFrame,
    y::AbstractVector{CLabel};
    kwargs...
)
    length(y) != nrow(X) && error("size of X and y mismatch")
    
    current_X = @view X[:,:]
    current_y = @view y[:]
    
    slice_tocover = collect(1:length(y))
    print("computing selectors...")
    selectors = computeselectors(X)
    println(" end")
    rulelist = Vector{SoleModels.ClassificationRule}([])
    

    while length(slice_tocover) > 0
        bestcomplex = findBestComplex(selectors, current_X, current_y)
        coverage = complexcoverage(bestcomplex, current_X)
        coveredindexes = findall(x->x==1, coverage)
        mostcommonclass = _getmostcommon(current_y[coveredindexes])
        push!(rulelist, myrule2solerule(MyRule(bestcomplex, mostcommonclass)))
        
        # Virtually remove the instances
        setdiff!(slice_tocover, slice_tocover[coveredindexes])
        current_X = @view X[slice_tocover, :]
        current_y = @view y[slice_tocover]
    end        
    return DecisionList(rulelist, ⊤)
end

# function execmy()

#     datasets_dir = "/home/edoardo/Scrivania/TesiTitocinio/example-dataset/"
#     input = datasets_dir * "iris.csv"
    
#     Xy_df = DataFrame(CSV.File(input))

#     X_df = Xy_df[:, 1:(end-1)]

#     y = Vector{SoleBase.CLabel}(String.(Xy_df[:, end]))

#     CN2(X_df, y) 
# end



