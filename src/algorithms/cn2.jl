using SoleData
using SoleLogics
using SoleBase
using DataFrames
using Random
import SoleLogics: LogicalInstance, Formula, LeftmostLinearForm
import SoleModels: Rule, AbstractModel, ConstantModel
import SoleData: PropositionalLogiset, getconditionset, getfeatures, alphabetlogiset, ScalarCondition, UnivariateSymbolFeature
import SoleBase: CLable


struct Selector    
    att::Symbol # simil Feature
    val
end

# >>>

    Base.show(io::IO, s::Selector) = print(io, "($(s.att) = $(s.val))")
    UnivariateSymbolFeature

    varname(sel::Selector) = sel.att
    treshold(sel::Selector) = sel.val # che poi non è una treshold :)

    function selector2soleatom(sel::Selector)::Atom
        feature = UnivariateSymbolFeature(varname(sel))
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
    head::Int64
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

function entropy(x)

    if length(x) == 0
        return 2.0    
    end
    val = values(countmap(x))
    if length(val) == 1
        return 0.0
    end    

    logbase = length(val)
    pi = val ./ sum(val)
    return -sum( pi .* log.(logbase, pi) )
end

function computeselectors(df)
    selectorlist = []
    attributes = names(df)
    # do per scontato che l' attributo target sia l' ultimo 
    for attribute ∈ attributes[1:end-1]
        map( x -> push!( selectorlist, Selector(Symbol(attribute), x)), unique(df[:, attribute]) )
    end
    return selectorlist
end

function getrulecoverage(rulebody::RuleBody, examples)
    rulecoverage = ones(Bool, nrow(examples))
    for selector ∈ getselectors(rulebody)
        selcoverage = (examples[!, selector.att] .== selector.val) 
        rulecoverage = Bool.(selcoverage) .& rulecoverage
    end
    return rulecoverage
end 

function entropy(rule, examples)
    coveredindexes = findall(x->x==1, getrulecoverage(rule, examples) )
    coveredclasses = examples[coveredindexes, end]
    return entropy(coveredclasses)
end

function findBestComplex(selectors, examples)

        star = Star([])
        bestrule = RuleBody(Set([]))
        bestruleentropy = 2.0
        
        while true
            
            newstar = specializestar(star, selectors)
            if isempty(newstar) #= Exit condition =#  
                break 
            end
            entropydf = DataFrame(R=RuleBody[], E=Float32[])
            for rule ∈ rules(newstar)
                # Aggiungo la regola e la sua valutazione al dizionario
                enrpy = entropy(rule, examples)
                push!(entropydf, (rule, enrpy))
            end
           
            sort!(entropydf, [:E])
            newbestruleentropy = entropydf[1, :E]
            if (newbestruleentropy < bestruleentropy)
                bestrule, bestruleentropy = entropydf[1, :]
            end
            # Reduce de number of rules to the user defined max
            @bp
            userdefinedmax = 3
            if nrow(entropydf) > userdefinedmax
                entropydf = entropydf[1:userdefinedmax, :]
            end
            newstarrules = entropydf[:, :R] 
            star = rules2star( newstarrules )
         end
    return bestrule
end

# includere caso ≤. ≥

function CN2(
    examples::AbstractDataFrame,
    #=, y::AsbtracVector{CLable}  =#;
)
    # vettore di atomi 
    selectorlist = computeselectors(examples)
    rulelist = []
    # ricordati bit-mask + subdataframe (@view)
    while nrow(examples) > 0
        
        #currentexamples = @view examples[slicing]
        # FBC restituisce Formula !
        bestrule = findBestComplex(selectorlist, examples)
        
        rulecoverage = getrulecoverage(bestrule, examples)
        coveredindexes = findall(x->x==1, rulecoverage)
        examplesclass = examples[coveredindexes, end]
        mostcommonclass = getmostcommon(examplesclass)

        push!(rulelist, MyRule(bestrule, mostcommonclass) ) 
        deleteat!(examples, coveredindexes)
    end
    
    return RuleList(rulelist)
end

dbg.@run CN2(df)
println(myrule2solerule(rlist[1])) 
println(myrule2solerule(rlist[2])) 
