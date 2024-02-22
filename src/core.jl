import SoleLogics: alphabet

############################################################################################
#### Fundamental definitions ###############################################################
############################################################################################
"""
    const Item = SoleLogics.Formula

Fundamental type in the context of association rule mining.
An [`Item`](@ref) is a logical formula, which can be [`SoleLogics.check`](@ref)ed on models.

See also [`SoleLogics.check`](@ref), [`SoleLogics.Formula`].
"""
const Item = SoleLogics.Formula

"""
    const Itemset = Vector{Item}
    function Itemset(item::Item)
    function Itemset(itemsets::Vector{Itemset})

Collection of *unique* [`Item`](@ref)s.
In the context of association rule mining, we want to work with interesting
[`Itemset`](@ref)s: how much interesting is an [`Itemset`](@ref) is established through
specific meaningfulness measures such as [`lsupport`](@ref) and [`gsupport`](@ref).
"""
const Itemset = Vector{<:Item}
Itemset(item::Item) = Itemset([item])
Itemset(itemsets::Vector{Itemset}) = Itemset.([union(itemsets...)...])

function Base.convert(::Type{Item}, itemset::Itemset)::Item
    @assert length(itemset) == 1 "Cannot convert $(itemset) of length $(length(itemset)) " *
        "to Item: itemset must contain exactly one item"
    return first(itemset)
end

function Base.show(io::IO, itemset::Itemset)
    print(io, "[" * join([syntaxstring(item) for item in itemset], ", ") * "]")
end

"""
    toformula(itemset::Itemset)

Conjunctive normal form of the [`Item`](@ref)s contained in `itemset`.

See also [`SoleLogics.LeftmostConjunctiveForm`](@ref)
"""
toformula(itemset::Itemset) = LeftmostConjunctiveForm(itemset)

# See meaningfulness measures section.
# A ConstrainedMeasure is a tuple shaped as (global measure, local threshold, global threshold)
"""
    const Threshold = Float64

Threshold value for meaningfulness measures.
"""
const Threshold = Float64

"""
    const WorldsMask = Vector{Int64}

See also [`Contributors`](@ref).
"""
const WorldsMask = Vector{Int64}

"""
    const EnhancedItemset = Tuple{Item,WorldsMask}

"Enhanced" representation of a vector of [`Itemset`](@ref), in which each [`Item`](@ref) is
associated to a counter and a specific [`WorldsMask`](@ref).

See also [`Item`](@ref), [`Itemset`](@ref), [`WorldsMask`](@ref).
"""
const EnhancedItemset = Vector{<:Tuple{<:Item,Integer,WorldsMask}}

"""
    const ConditionalPatternBase = Vector{Vector{EnhancedItemset}}

This is needed to implement [`fpgrowth`](@ref) algorithm
[as described here](https://www.cs.sfu.ca/~jpei/publications/sigmod00.pdf).

See also [`fpgrowth`](@ref).
"""
const ConditionalPatternBase = Vector{EnhancedItemset}

"""
    const ARule = Tuple{Itemset,Itemset}

An association rule represents a strong and meaningful co-occurrence relationship between
two [`Itemset`](@ref)s whose intersection is empty.

The meaningfulness of an [`ARule`](@ref) can be established through specific meaningfulness
measures.
For example, local confidence ([`lconfidence`](@ref)) when testing the rule on
a specific logical instance of a dataset, or global confidence ([`gconfidence`](@ref))
when testing the rule on an entire dataset.

See also [`gconfidence`](@ref), [`lconfidence`](@ref), [`Itemset`](@ref).
"""
const ARule = Tuple{Itemset,Itemset} # NOTE: see SoleLogics.Rule
antecedent(rule::ARule) = first(rule)
consequent(rule::ARule) = last(rule)

"""
    const ConstrainedMeasure = Tuple{Function, Threshold, Threshold}

In the context of modal logic, where the instances of a dataset are relational objects,
every meaningfulness measure must capture two aspects: how much an [`Itemset`](@ref) or an
[`ARule`](@ref) is meaningful *inside an instance*, and how much the same object is
meaningful *across the instances*.

For this reason, we can think of a meaningfulness measure as a matryoshka composed of
an external global measure and an internal local measure.
The global measure tests for how many instances a local measure overpass a local threshold.
At the end of the process, a global threshold can be used to establish if the global measure
is actually meaningful or not.
(Note that this generalizes the propositional logic case scenario, where it is enough to
just apply a measure across instances.)

Therefore, a [`ConstrainedMeasure`](@ref) is a tuple composed of a global meaningfulness
measure, a local threshold and a global threshold.

See also [`gconfidence`](@ref), [`gsupport`](@ref).
"""
const ConstrainedMeasure = Tuple{Function, Threshold, Threshold}

doc_islocalof = doc_isglobalof = """
    islocalof(::Function, ::Function)::Bool
    isglobalof(::Function, ::Function)::Bool

Trait to indicate that a local meaningfulness measure is used as subroutine in a global
measure, or, vice versa, a global measure contains a local measure.

For example, `islocalof(lsupport, gsupport)` is `true`, and `isglobalof(gsupport, lsupport)`
is `false`.

!!! warning
    When implementing a custom meaningfulness measure, make sure to implement both
    traits if necessary. This is fundamental to guarantee the correct behavior of some
    methods, such as [`getlocalthreshold`](@ref).

See also [`getlocalthreshold`](@ref), [`gsupport`](@ref), [`lsupport`](@ref).
"""

"""$(doc_islocalof)"""
islocalof(::Function, ::Function)::Bool = false
"""$(doc_isglobalof)"""
isglobalof(::Function, ::Function)::Bool = false

"""
    ARMSubject = Union{Itemset,ARule}

[Memoizable](https://en.wikipedia.org/wiki/Memoization) types for association rule mining
(ARM).

See also [`GmeasMemo`](@ref), [`LmeasMemo`](@ref).
"""
const ARMSubject = Union{Itemset,ARule} # memoizable association-rule-mining types

"""
    const LmeasMemoKey = Tuple{Symbol,ARMSubject,Int64}

Key of a [`LmeasMemo`](@ref) dictionary.
Represents a local meaningfulness measure name (as a `Symbol`), a [`ARMSubject`](@ref),
and the number of a dataset instance where the measure is applied.

See also [`LmeasMemo`](@ref), [`ARMSubject`](@ref).
"""
const LmeasMemoKey = Tuple{Symbol,ARMSubject,Int64}

"""
    const LmeasMemo = Dict{LmeasMemoKey,Float64}

Association between a local measure of a [`ARMSubject`](@ref) on a specific dataset instance,
and its value.

See also [`LmeasMemoKey`](@ref), [`ARMSubject`](@ref).
"""
const LmeasMemo = Dict{LmeasMemoKey,Float64}

"""
Structure for storing association between a local measure, applied on a certain
[`ARMSubject`](@ref) on a certain [`LogicalInstance`](@ref), and a vector of integers
representing the worlds for which the measure is greater than a certain threshold.

This type is intended to be used inside an [`ARuleMiner`](@ref) `info` named tuple, to
support the execution of, for example, [`fpgrowth`](@ref) algorthm.

See also [`LmeasMemoKey`](@ref), [`WorldMask`](@ref)
"""
const Contributors = Dict{LmeasMemoKey, WorldsMask}

"""
    const GmeasMemoKey = Tuple{Symbol,ARMSubject}

Key of a [`GmeasMemo`](@ref) dictionary.
Represents a global meaningfulness measure name (as a `Symbol`) and a [`ARMSubject`](@ref).

See also [`GmeasMemo`](@ref), [`ARMSubject`](@ref).
"""
const GmeasMemoKey = Tuple{Symbol,ARMSubject}

"""
    const GmeasMemo = Dict{GmeasMemoKey,Float64}

Association between a global measure of a [`ARMSubject`](@ref) on a dataset, and its value.

The reference to the dataset is not explicited here, since [`GmeasMemo`](@ref) is intended
to be used as a [memoization](https://en.wikipedia.org/wiki/Memoization) structure inside
[`ARuleMiner`](@ref) objects, and the latter already knows the dataset they are working with.

See also [`GmeasMemoKey`](@ref), [`ARMSubject`](@ref).
"""
const GmeasMemo = Dict{GmeasMemoKey,Float64} # global measure of an itemset/arule => value

############################################################################################
#### Association rule miner machines #######################################################
############################################################################################

"""
    struct ARuleMiner
        X::AbstractDataset              # target dataset
        algo::MiningAlgo                # algorithm used to perform extraction

        alphabet::Vector{Item}

        # global meaningfulness measures and their thresholds (both local and global)
        item_constrained_measures::Vector{<:ConstrainedMeasure}
        rule_constrained_measures::Vector{<:ConstrainedMeasure}

        nonfreqitems::Vector{Itemset}   # non-frequent itemsets dump
        freqitems::Vector{Itemset}      # collected frequent itemsets
        arules::Vector{ARule}           # collected association rules

        lmemo::LmeasMemo                # local memoization structure
        gmemo::GmeasMemo                # global memoization structure
        info::NamedTuple                # general informations
    end

Machine learning model interface to perform association rules extraction.

# Examples
```julia-repl
julia> using SoleRules
julia> using SoleData

# Load NATOPS DataFrame
julia> X_df, y = load_arff_dataset("NATOPS");

# Convert NATOPS DataFrame to a Logiset
julia> X = scalarlogiset(X_df)

# Prepare some propositional atoms
julia> p = Atom(ScalarCondition(UnivariateMin(1), >, -0.5))
julia> q = Atom(ScalarCondition(UnivariateMin(2), <=, -2.2))
julia> r = Atom(ScalarCondition(UnivariateMin(3), >, -3.6))

# Prepare some modal atoms using later relationship - see [`SoleLogics.IntervalRelation`](@ref))
julia> lp = box(IA_L)(p)
julia> lq = diamond(IA_L)(q)
julia> lr = boxlater(r)

# Compose a vector of items, regrouping the atoms defined before
julia> manual_alphabet = Vector{Item}([p, q, r, lp, lq, lr])

# Create an association rule miner wrapping `apriori` algorithm - see [`apriori`](@ref);
# note that meaningfulness measures are not explicited and, thus, are defaulted as in the
# call below.
julia> miner = ARuleMiner(X, apriori(), manual_alphabet)

# Create an association rule miner, expliciting global meaningfulness measures with their
# local and global thresholds, both for [`Itemset`](@ref)s and [`ARule`](@ref).
julia> miner = ARuleMiner(X, apriori(), manual_alphabet,
    [(gsupport, 0.1, 0.1)], [(gconfidence, 0.2, 0.2)])

# Consider the dataset and the learning algorithm wrapped by `miner` (respectively `X` and `apriori`)
# Mine the frequent itemsets, that is to say the itemsets for which `item_constrained_measures` are large enough.
# Then iterate the generator returned by [`mine`](@ref) to enumerate the meaningful association rules.
julia> for arule in SoleRules.mine(miner)
    println(miner)
end
```

See also  [`ARule`](@ref), [`apriori`](@ref), [`ConstrainedMeasure`](@ref), [`Itemset`](@ref),
[`GmeasMemo`](@ref), [`LmeasMemo`](@ref), [`MiningAlgo`](@ref).
"""
struct ARuleMiner
    # target dataset
    X::AbstractDataset
    # algorithm used to perform extraction
    algo::FunctionWrapper{Nothing,Tuple{ARuleMiner,AbstractDataset}}
    alphabet::Vector{Item}

    # meaningfulness measures
    item_constrained_measures::Vector{<:ConstrainedMeasure}
    rule_constrained_measures::Vector{<:ConstrainedMeasure}

    nonfreqitems::Vector{Itemset}   # non-frequent itemsets dump
    freqitems::Vector{Itemset}      # collected frequent itemsets
    arules::Vector{ARule}           # collected association rules

    lmemo::LmeasMemo                # local memoization structure
    gmemo::GmeasMemo                # global memoization structure
    info::NamedTuple                # general informations

    function ARuleMiner(
        X::AbstractDataset,
        algo::Function,
        alphabet::Vector{<:Item},
        item_constrained_measures::Vector{<:ConstrainedMeasure},
        rule_constrained_measures::Vector{<:ConstrainedMeasure};
        info::NamedTuple = (;)
    )
        new(X, MiningAlgo(algo), alphabet,
            item_constrained_measures,
            rule_constrained_measures,
            Vector{Itemset}([]), Vector{Itemset}([]), Vector{ARule}([]),
            LmeasMemo(), GmeasMemo(), info
        )
    end

    function ARuleMiner(
        X::AbstractDataset,
        algo::Function,
        alphabet::Vector{<:Item}
    )
        ARuleMiner(X, MiningAlgo(algo), alphabet,
            [(gsupport, 0.1, 0.1)], [(gconfidence, 0.2, 0.2)]
        )
    end
end

"""
    const MiningAlgo = FunctionWrapper{Nothing,Tuple{ARuleMiner,AbstractDataset}}

[Function wrapper](https://github.com/yuyichao/FunctionWrappers.jl) representing a function
which performs mining of frequent [`Itemset`](@ref)s in a [`ARuleMiner`](@ref).

See also [`SoleLogics.AbstractDataset`](@ref), [`ARuleMiner`](@ref).
"""
const MiningAlgo = FunctionWrapper{Nothing,Tuple{ARuleMiner,AbstractDataset}}

doc_aruleminer_getters = """
    dataset(miner::ARuleMiner)::AbstractDataset
    algorithm(miner::ARuleMiner)::MiningAlgo
    alphabet(miner::ARuleMiner)::Vector{Item}

    item_meas(miner::ARuleMiner)::Vector{<:ConstrainedMeasure}
    rule_meas(miner::ARuleMiner)::Vector{<:ConstrainedMeasure}

    getlocalthreshold(miner::ARuleMiner, meas::Function)::Float64
    getglobalthreshold(miner::ARuleMiner, meas::Function)::Float64

    freqitems(miner::ARuleMiner)::Vector{Itemset}
    nonfreqitems(miner::ARuleMiner)::Vector{Itemset}
    arules(miner::ARuleMiner)::Vector{ARule}

    getlocalmemo(miner::ARuleMiner)::LmeasMemo
    getlocalmemo(miner::ARuleMiner, key::LmeasMemoKey)::Float64

    getglobalmemo(miner::ARuleMiner)::GmeasMemo
    getglobalmemo(miner::ARuleMiner, key::GmeasMemoKey)::Float64

    info(miner::ARuleMiner)::NamedTuple
    info(miner::ARuleMiner, key::Symbol)

[`ARuleMiner`](@ref) getters.
"""

doc_aruleminer_setters = """
    setlocalthreshold(miner::ARuleMiner, meas::Function, threshold::Threshold)
    setglobalthreshold(miner::ARuleMiner, meas::Function, threshold::Threshold)

    setlocalmemo(miner::ARuleMiner, key::LmeasMemoKey, val::Float64)
    setglobalmemo(miner::ARuleMiner, key::GmeasMemoKey, val::Float64)

Setters for [`ARuleMiner`](@ref) fields.
"""

"""$(doc_aruleminer_getters)"""
dataset(miner::ARuleMiner)::AbstractDataset = miner.X

"""$(doc_aruleminer_getters)"""
algorithm(miner::ARuleMiner)::MiningAlgo = miner.algo
"""$(doc_aruleminer_getters)"""
alphabet(miner::ARuleMiner) = miner.alphabet

"""$(doc_aruleminer_getters)"""
item_meas(miner::ARuleMiner)::Vector{<:ConstrainedMeasure} = miner.item_constrained_measures
"""$(doc_aruleminer_getters)"""
rule_meas(miner::ARuleMiner)::Vector{<:ConstrainedMeasure} = miner.rule_constrained_measures

"""$(doc_aruleminer_getters)"""
getlocalthreshold(miner::ARuleMiner, meas::Function) = begin
    for (gmeas, _, lthreshold) in item_meas(miner)
        if gmeas == meas || islocalof(meas, gmeas)
            return lthreshold
        end
    end

    error("The provided miner has no local threshold for $meas. Maybe the miner is not " *
        "initialized properly, and $meas is omitted. Please use item_meas/rule_meas " *
        "to check which measures are available, and setlocalthreshold to add a new " *
        "local measure, together with its local threshold.")
end
"""$(doc_aruleminer_setters)"""
setlocalthreshold(miner::ARuleMiner, meas::Function, threshold::Threshold) = begin
    error("TODO: This method is not implemented yet.")
end

"""$(doc_aruleminer_getters)"""
getglobalthreshold(miner::ARuleMiner, meas::Function)::Float64 = begin
    for (gmeas, gthreshold, _) in item_meas(miner)
        if gmeas == meas
            return gthreshold
        end
    end

    error("The provided miner has no global threshold for $meas. Maybe the miner is not " *
    "initialized properly, and $meas is omitted. Please use item_meas/rule_meas " *
    "to check which measures are available, and setglobalthreshold to add a new " *
    "global measure, together with local and global thresholds.")
end
"""$(doc_aruleminer_setters)"""
setglobalthreshold(miner::ARuleMiner, meas::Function, threshold::Threshold) = begin
    error("TODO: This method is not implemented yet.")
end

"""$(doc_aruleminer_getters)"""
freqitems(miner::ARuleMiner) = miner.freqitems
"""$(doc_aruleminer_getters)"""
nonfreqitems(miner::ARuleMiner) = miner.nonfreqitems
"""$(doc_aruleminer_getters)"""
arules(miner::ARuleMiner) = miner.arules

"""$(doc_aruleminer_getters)"""
getlocalmemo(miner::ARuleMiner)::LmeasMemo = miner.lmemo
"""$(doc_aruleminer_getters)"""
getlocalmemo(miner::ARuleMiner, key::LmeasMemoKey) = get(miner.lmemo, key, nothing)
"""$(doc_aruleminer_setters)"""
setlocalmemo(miner::ARuleMiner, key::LmeasMemoKey, val::Float64) = miner.lmemo[key] = val

"""$(doc_aruleminer_getters)"""
getglobalmemo(miner::ARuleMiner)::GmeasMemo = miner.gmemo
"""$(doc_aruleminer_getters)"""
getglobalmemo(miner::ARuleMiner, key::GmeasMemoKey) = get(miner.gmemo, key, nothing)
"""$(doc_aruleminer_setters)"""
setglobalmemo(miner::ARuleMiner, key::GmeasMemoKey, val::Float64) = miner.gmemo[key] = val

"""$(doc_aruleminer_getters)"""
info(miner::ARuleMiner)::NamedTuple = miner.info
"""$(doc_aruleminer_getters)"""
info(miner::ARuleMiner, key::Symbol) = getfield(miner.info, key)

"""
    function mine(miner::ARuleMiner)

Synonym for `SoleRules.apply(miner, dataset(miner))`.

See also [`ARule`](@ref), [`Itemset`](@ref), [`SoleRules.apply`](@ref).
"""
function mine(miner::ARuleMiner)
    return apply(miner, dataset(miner))
end

"""
    function apply(miner::ARuleMiner, X::AbstractDataset)

Extract association rules in the dataset referenced by `miner`, saving the interesting
[`Itemset`](@ref)s inside `miner`.
Then, return a generator of [`ARules`](@ref)s.

See also [`ARule`](@ref), [`Itemset`](@ref).
"""
function apply(miner::ARuleMiner, X::AbstractDataset)
    # extract frequent itemsets
    miner.algo(miner, X)
    return arules_generator(freqitems(miner), miner)
end

function Base.show(io::IO, miner::ARuleMiner)
    println(io, "$(dataset(miner))")

    println(io, "Alphabet: $(alphabet(miner))\n")
    println(io, "Items measures: $(item_meas(miner))")
    println(io, "Rules measures: $(rule_meas(miner))\n")

    println(io, "# of frequent patterns mined: $(length(freqitems(miner)))")
    println(io, "# of association rules mined: $(length(arules(miner)))\n")

    println(io, "Local measures memoization structure entries: " *
        "$(length(miner.lmemo |> keys))")
    println(io, "Global measures memoization structure entries: " *
        "$(length(miner.gmemo |> keys))\n")

    print(io, "Additional infos: $(info(miner) |> keys)")
end
