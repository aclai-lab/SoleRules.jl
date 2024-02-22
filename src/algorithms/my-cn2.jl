using SoleData
using SoleLogics
using SoleBase
using SoleModels
using DataFrames
using Random
using StatsBase: countmap
using Debugger
db = Debugger
import SoleLogics: LogicalInstance, Formula, LeftmostLinearForm
import SoleModels: Rule, AbstractModel, ConstantModel
import SoleBase: CLabel
import SoleData: PropositionalLogiset, BoundedScalarConditions
import SoleData: features, alphabet, UnivariateSymbolValue
const global bestruleentropy = 2.0


struct Selector    
    att::Symbol # simil Feature
    val
end

# >>>

    Base.show(io::IO, s::Selector) = print(io, "($(s.att) = $(s.val))")

    varname(sel::Selector) = sel.att
    treshold(sel::Selector) = sel.val # che poi non è una treshold :)

    function computeselectors(df)
        selectorlist = []
        attributes = names(df)
        # do per scontato che l' attributo target sia l' ultimo 
        for attribute in attributes[1:end-1]
            map( x -> push!( selectorlist, Selector(Symbol(attribute), x)), unique(df[:, attribute]) )
        end
    
        return selectorlist
    end

    function selector2soleatom(sel::Selector)::Atom
        feature = UnivariateSymbolValue(varname(sel))
        tresh = treshold(sel)
        return Atom(ScalarCondition(feature, ≤, tresh)) # (≤) sarebbe (=), sostitusione solo a scopo dimostrativo.  
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

    gethead(r::MyRule) = r.head 
    getselectors(mr::MyRule) = getselectors(mr.body)
    _AND(atoms) = length(atoms) > 1 ? LeftmostConjunctiveForm(∧(atoms)) : atoms[1]
    
    function myrule2solerule(myrule::MyRule)
        selectors = getselectors(myrule)
        atoms = selector2soleatom(selectors)
        
        _antecedent = _AND(atoms)
        _consequent = ConstantModel(gethead(myrule))
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

getmostcommon( classlist ) = findmin(countmap(classlist))[2]
symbolnames(X_df::AbstractDataFrame) = Symbol.(names(X_df))

function entropy(x)
    if length(x) == 0 return 2.0 end
    val = values(countmap(x))
    if length(val) == 1 return 0.0 end    
    logbase = length(val)
    pi = val ./ sum(val)
    return -sum( pi .* log.(logbase, pi) )
end

function complexcoverage(rulebody::RuleBody, examples)::Vector{Bool}

    complexcoverage = ones(Bool, nrow(examples))
    for selector ∈ getselectors(rulebody)
        selcoverage = (examples[!, selector.att] .== selector.val) 
        complexcoverage = Bool.(selcoverage) .& complexcoverage
    end
    return complexcoverage
end 

function entropy(rule, examples)
    coveredindexes = findall(x->x==1, complexcoverage(rule, examples) )
    coveredclasses = examples[coveredindexes, end]
    return entropy(coveredclasses)
end

function findBestComplex(selectors, examples)

    star = Star([])
    bestrule = RuleBody(Set([]))
    bestruleentropy = 2
    
    while true
        
        newstar = specializestar(star, selectors)
         #= Exit condition =#
         if isempty(newstar)
            break
        end
        #= Dataframe definition =#
        entropydf = DataFrame(R=RuleBody[], E=Float32[])

        for rule ∈  newstar.rules

            coverage = complexcoverage(rule, examples)
            # Indici delle istanze coperte
            coveredindexes = findall(x->x==1, coverage)
            # Array cotenente gli attributi target di ogni istanza coperta
            coveredclasses = examples[ coveredindexes, end]
            enrpy = entropy(coveredclasses)
            # Aggiungo la regola e la sua valutazione al dizionario
            push!(entropydf, (rule, enrpy))
            
        end
       
        sort!(entropydf, [:E])
        # Tende a mantenere le regole più generali a parità di entropia 
        newbestruleentropy = entropydf[1, :E]
        if ( newbestruleentropy < bestruleentropy)
            bestrule = entropydf[1, :R]
            bestruleentropy = entropydf[1, :E]
        end
        # Reduce de number of rules to the user defined max
        userdefinedmax = 3
        if nrow(entropydf) > userdefinedmax
            entropydf = entropydf[1:userdefinedmax, :]
        end
        newstarrules = entropydf[:, :R] 
        star = rules2star( newstarrules )
     end
return bestrule
end

function getmostcommon( classlist )
    occurrence = countmap(classlist)
    return findmin(occurrence)[2]
end



function CN2(
    X_df::AbstractDataFrame,
    y::AbstractVector{CLabel};
    kwargs...
)
    selectorlist = computeselectors(X_df)
    currentX_df = @view X_df[:,:]
    indexes = collect(1:length(y))
    rulelist = []


    while length(indexes) > 0
            
        bestcomplex = findBestComplex(selectorlist, currentX_df)
        coverage = complexcoverage(bestcomplex, currentX_df)
         
        coveredindexes = findall(x->x==1, coverage)
        mostcommonclass = getmostcommon(y[coveredindexes])
        push!(rulelist, MyRule(bestcomplex, mostcommonclass))
        
        # Virtually remove the instances
        setdiff!(indexes, indexes[coveredindexes])
        currentX_df = @view X_df[indexes, :]
    end
        
    return RuleList(rulelist)
end


function execmy()

    df = DataFrame([1 2 3 4; 5 6 7 8], :auto)
    y = Vector{SoleBase.CLabel}(["+", "-"])
    CN2(df, y)

end