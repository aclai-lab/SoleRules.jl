############################################################################################
#### Data structures #######################################################################
############################################################################################

"""
Fundamental data structure used in FP-Growth algorithm.
Essentialy, an [`FPTree`](@ref) is a prefix tree where a root-leaf path represent an [`Itemset`](@ref).

Consider the [`Itemset`](@ref)s sorted by [`gsupport`](@ref) of their items.
An [`FPTree`](@ref) is such that the common [`Item`](@ref)s-prefix shared by different
[`Itemset`](@ref)s is not stored multiple times.

This implementation generalizes the propositional logic case scenario to modal logic;
given two [`Itemset`](@ref)s sharing a [`Item`](@ref) prefix, they share the same path only
if the worlds in which the they are true is the same.
"""
struct FPTree
    content::Union{Nothing,Item}    # the Item contained in this node (nothing if root)

    parent::Union{Nothing,FPTree}   # parent node
    children::Vector{FPTree}        # children nodes

    count::Integer                  # number of equal Items this node represents

    contributors::UInt64            # hash representing the worlds contributing to this node
    linkage::Union{Nothing,FPTree}  # link to another FPTree root

    # empty constructor
    function FPTree()
        new(nothing, nothing, FPTree[], 0, UInt64(0), nothing)
    end

    # choose root or new subtree constructor
    function FPTree(itemset::Itemset, miner::ARuleMiner; isroot=true)
        FPTree(itemset, miner, Val(isroot)) # singleton design pattern
    end

    # root constructor
    function FPTree(itemset::Itemset, miner::ARuleMiner, ::Val{true})
        fptree = FPTree()

        push!(children(fptree), FPTree(itemset, miner; isroot=false))
        for child in children(fptree)
            parent(child) = fptree
        end

        return fptree
    end

    # internal tree constructor
    function FPTree(itemset::Itemset, miner::ARuleMiner, ::Val{false})
        firstitem = itemset[1]
        contribhash = getcontributors(firstitem, miner)

        fptree = length(itemset) == 1 ?
            new(firstitem, nothing, FPTree[], 1, contribhash, nothing) :
            FPTree(firstitem, nothing, FPTree[FPTree(itemset[2:end], miner; isroot=false)],
                1, contribhash, nothing)

        for child in children(fptree)
            parent(child) = fptree
        end

        return fptree
    end
end

doc_fptree_getters = """
    content(fptree::FPTree)::Union{Nothing,Item}
    children(fptree::FPTree)::Vector{FPTree}
    contributors(fptree::FPTree)::UInt64
    count(fptree::FPTree)::Integer
    linkage(fptree::FPTree)::Union{Nothing,FPTree}

[`FPTree`](@ref) getters.
"""

doc_fptree_setters = """
[`FPTree`](@ref) setters.
"""

"""$(doc_fptree_getters)"""
content(fptree::FPTree)::Union{Nothing,Item} = fptree.content
"""$(doc_fptree_getters)"""
children(fptree::FPTree)::Vector{FPTree} = fptree.children
"""$(doc_fptree_getters)"""
contributors(fptree::FPTree)::UInt64 = fptree.contributors
"""$(doc_fptree_getters)"""
count(fptree::FPTree)::Integer = fptree.count
"""$(doc_fptree_getters)"""
linkage(fptree::FPTree)::Union{Nothing,FPTree} = fptree.linkage

"""
    function follow(fptree::FPTree)::Union{Nothing,FPTree}

Follow `fptree` linkage to (an internal node of) another [`FPTree`](@ref).
"""
function follow(fptree::FPTree)::Union{Nothing,FPTree}
    arrival = linkage(fptree)
    return arrival === nothing ? item : follow(arrival)
end

"""
    struct HeaderTable
        items::Vector{Item}
        linkage::Dict{Item,Union{Nothing,FPTree}}
    end

Utility data structure used to fastly access [`FPTree`](@ref) internal nodes.
"""
struct HeaderTable
    items::Vector{Item} # vector of Items, sorted decreasingly by global support
    linkage::Dict{Item,Union{Nothing,FPTree}} # Item -> FPTree internal node association

    function HeaderTable(items::Vector{Item})
        new(items, Dict{Item,FPTree}([item => nothing for item in items]))
    end
end

doc_htable_getters = """
    items(htable::HeaderTable)
    linkage(htable::HeaderTable, item::Item)

[`HeaderTable`](@ref) getters.
"""

"""$(doc_htable_getters)"""
items(htable::HeaderTable) = htable.items

"""$(doc_htable_getters)"""
linkage(htable::HeaderTable, item::Item) = htable.linkage[item]

"""
    function follow(htable::HeaderTable, item::Item)::Union{Nothing,FPTree}

Follow `htable` linkage to (an internal node of) a [`FPTree`](@ref).
"""
function follow(htable::HeaderTable, item::Item)::Union{Nothing,FPTree}
    arrival = linkage(htable, item)
    return arrival === nothing ? item : follow(arrival, item)
end

############################################################################################
#### Main FP-Growth logic ##################################################################
############################################################################################

"""
    fpgrowth(; fulldump::Bool=true, verbose::Bool=true)::Function

Wrapper function for the FP-Growth algorithm over a modal dataset.
Returns a `function f(miner::ARuleMiner, X::AbstractDataset)::Nothing` that runs the main
FP-Growth algorithm logic, [as described here](https://www.cs.sfu.ca/~jpei/publications/sigmod00.pdf).
"""
function fpgrowth(;
    fulldump::Bool=true,   # mostly for testing purposes, also keeps track of non-frequent patterns
    verbose::Bool=true,
)::Function

    function _fpgrowth(miner::ARuleMiner, X::AbstractDataset)::Nothing
        @assert SoleRules.gsupport in reduce(vcat, item_meas(miner)) "FP-Growth requires "*
            "global support (SoleRules.gsupport) as meaningfulness measure in order to " *
            "work. Please, add a tuple (SoleRules.gsupport, local support threshold, " *
            "global support threshold) to miner.item_constrained_measures field."

        # retrieve local support threshold, as this is necessary later to filter which
        # frequent items are meaningful on each instance.
        lsupport_threshold = getlocalthreshold(miner, SoleRules.gsupport)

        # get the frequent itemsets from the first candidates set;
        # note that meaningfulness measure should leverage memoization when miner is given!
        frequents = [candidate
            for (gmeas_algo, lthreshold, gthreshold) in item_meas(miner)
            for candidate in Itemset.(alphabet(miner))
            if gmeas_algo(item, X, lthreshold, miner=miner) >= gthreshold
        ]

        # associate each instance in the dataset with its frequent itemsets
        _ninstances = ninstances(X)
        ninstance_toitemsets_sorted = fill(Vector{Itemset}, _ninstances)

        # for each instance, sort its frequent itemsets by global support
        for i in 1:_ninstances
            ninstance_toitemsets_sorted[i] = sort([
                itemset
                for itemset in frequents
                if getlocalmemo(miner, (:lsupport, itemset, i)) > lsupport_threshold
            ], by=t -> getglobalmemo(miner, (:gsupport, t)), rev=true)
        end


    end

    return _fpgrowth
end
