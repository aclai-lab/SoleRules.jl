############################################################################################
#### Data structures #######################################################################
############################################################################################

"""
Fundamental data structure used in FP-Growth algorithm.
Essentialy, an [`FPTree`](@ref) is a prefix tree where a root-leaf path represent an
[`Itemset`](@ref).

Consider the [`Itemset`](@ref)s sorted by [`gsupport`](@ref) of their items.
An [`FPTree`](@ref) is such that the common [`Item`](@ref)s-prefix shared by different
[`Itemset`](@ref)s is not stored multiple times.

This implementation generalizes the propositional logic case scenario to modal logic;
given two [`Itemset`](@ref)s sharing a [`Item`](@ref) prefix, the worlds in which they are
true is accumulated.
"""
mutable struct FPTree
    content::Union{Nothing,Item}        # Item contained in this node (nothing if root)

    parent::Union{Nothing,FPTree}       # parent node
    const children::Vector{FPTree}      # children nodes

    count::Int64                        # number of equal Items this node represents

    const contributors::WorldsMask      # worlds contributing to this node
    linkage::Union{Nothing,FPTree}      # link to another FPTree root

    # empty constructor
    function FPTree()
        new(nothing, nothing, FPTree[], 0, Int64[], nothing)
    end

    # choose root or new subtree constructor;
    # ninstance is needed to start defining `contributors` for each node,
    # as this is not a standard, propositional FPTree but a more general modal one.
    function FPTree(itemset::Itemset, ninstance::Int64, miner::ARuleMiner; isroot=true)
        FPTree(itemset, ninstance, miner, Val(isroot)) # singleton design pattern
    end

    # root constructor
    function FPTree(itemset::Itemset, ninstance::Int64, miner::ARuleMiner, ::Val{true})
        # make FPTree empty root
        fptree = FPTree()

        # start growing a path
        children!(fptree, FPTree(itemset, miner; isroot=false))

        return fptree
    end

    # internal tree constructor
    function FPTree(itemset::Itemset, ninstance::Int64, miner::ARuleMiner, ::Val{false})
        firstitem = itemset[1]
        _contributors = SoleRules.contributors(:lsupport, firstitem, ninstance, miner)

        fptree = length(itemset) == 1 ?
            new(firstitem, nothing, FPTree[], 1, _contributors, nothing) :
            new(firstitem, nothing,
                FPTree[FPTree(itemset[2:end], ninstance, miner; isroot=false)],
                1, _contributors, nothing)

        map(child -> parent!(child, fptree), children(fptree))

        return fptree
    end

    function FPTree(pbase::ConditionalPatternBase, miner::ARuleMiner)
        fptree = FPTree()

        for enhanceditemset in pbase
            continue
        end
    end
end

doc_fptree_getters = """
    content(fptree::FPTree)::Union{Nothing,Item}
    parent(fptree::FPTree)::Union{Nothing,FPTree}
    children(fptree::FPTree)::Vector{FPTree}
    count(fptree::FPTree)::Int64
    contributors(fptree::FPTree)::WorldsMask
    linkage(fptree::FPTree)::Union{Nothing,FPTree}

[`FPTree`](@ref) getters.
"""

doc_fptree_setters = """
    content!(fptree::FPTree)::Union{Nothing,Item}
    parent!(fptree::FPTree)::Union{Nothing,FPTree}
    children!(fptree::FPTree)::Vector{FPTree}
    count!(fptree::FPTree)::Int64
    addcount!(fptree::FPTree, deltacount::Int64)
    contributors!(fptree::FPTree, contribution::WorldsMask)
    addcontributors!(fptree::FPTree)::WorldsMask
    linkage!(fptree::FPTree)::Union{Nothing,FPTree}

[`FPTree`](@ref) setters.
"""

"""$(doc_fptree_getters)"""
content(fptree::FPTree)::Union{Nothing,Item} = fptree.content
"""$(doc_fptree_getters)"""
parent(fptree::FPTree)::Union{Nothing,FPTree} = fptree.parent
"""$(doc_fptree_getters)"""
children(fptree::FPTree)::Vector{FPTree} = fptree.children

"""$(doc_fptree_getters)"""
count(fptree::FPTree)::Int64 = fptree.count
"""$(doc_fptree_getters)"""
contributors(fptree::FPTree)::WorldsMask = fptree.contributors

"""$(doc_fptree_getters)"""
linkage(fptree::FPTree)::Union{Nothing,FPTree} = fptree.linkage

"""$(doc_fptree_setters)"""
content!(fptree::FPTree, item::Union{Nothing,Item}) = fptree.content = item
"""$(doc_fptree_setters)"""
parent!(fptree::FPTree, parentfpt::Union{Nothing,FPTree}) = fptree.parent = parentfpt
"""$(doc_fptree_setters)"""
children!(fptree::FPTree, child::FPTree) = begin
    push!(children(fptree), child)
    parent!(child, fptree)
end

"""$(doc_fptree_setters)"""
count!(fptree::FPTree, newcount::Int64) = fptree.count = newcount
"""$(doc_fptree_setters)"""
addcount!(fptree::FPTree, deltacount::Int64) = fptree.count = fptree.count + deltacount
"""$(doc_fptree_setters)"""
contributors!(fptree::FPTree, contribution::WorldsMask) = fptree.contributors = contribution
"""$(doc_fptree_setters)"""
addcontributors!(fptree::FPTree, contribution::WorldsMask) =
    fptree.contributors .+= contribution

"""
    islist(fptree::FPTree)::Bool

Return true if every subtree in `fptree` has exactly 0 or 1 children.

See also [`FPTree`](@ref)
"""
function islist(fptree::FPTree)::Bool
    arity = fptree |> children |> length

    if arity == 1
        return islist(fptree |> children |> first)
    elseif arity > 1
        return false
    else
        # arity is 0
        return true
    end
end

"""
    function retrieveall(fptree::FPTree)::Itemset

Return all the [`Item`](@ref) contained in `fptree`.

See also [`FPTree`](@ref), [`Item`](@ref), [`Itemset`](@ref).
"""
function retrieveall(fptree::FPTree)::Itemset

    function _retrieve(fptree::FPTree)
        retrieved = Itemset([_retrieve(child) for child in children(fptree)])

        _content = content(fptree)
        if !isnothing(_content)
            push!(retrieved, Itemset(_content))
        end

        return retrieved
    end

    return reduce(vcat, _retrieve(fptree)) |> unique
end

"""
    function follow(fptree::FPTree)::Union{Nothing,FPTree}

Follow `fptree` linkage to (an internal node of) another [`FPTree`](@ref).

See also [`FPTree`](@ref), [`HeaderTable`](@ref).
"""
function follow(fptree::FPTree)::Union{Nothing,FPTree}
    arrival = linkage(fptree)
    return isnothing(arrival) ? item : follow(arrival)
end

"""
    function link!(from::FPTree, to::FPTree)

Establish a linkage between two [`FPTree`](@ref)s.
If the starting tree is already linked with something, the already existing linkages are
followed until a new "empty-linked" [`FPTree`](@ref) is found.

See also [`follow`](@ref), [`FPTree`](@ref), [`HeaderTable`](@ref).
"""
function link!(from::FPTree, to::FPTree)
    # find the last FPTree by iteratively following the internal link
    if !isnothing(linkage(from))
        from = follow(from)
    end

    from.linkage = to
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

    function HeaderTable(items::Vector{<:Item}, fptseed::FPTree)
        # make an empty htable, whose entries are `Item` objects, in `items`
        htable = new(items, Dict{Item,Union{Nothing,FPTree}}([
            item => nothing for item in items]))

        # iteratively fill htable
        child = children(fptseed)
        while !isempty(child)
            link!(htable, fptseed)
            child = children(child)
        end

        return htable
    end

    function HeaderTable(itemsets::Vector{<:Itemset}, fptseed::FPTree)
        return HeaderTable(convert.(Item, itemsets), fptseed)
    end
end

doc_htable_getters = """
    items(htable::HeaderTable)
    linkage(htable::HeaderTable, item::Item)

[`HeaderTable`](@ref) getters.
"""

doc_htable_setters = """
    linkage!(htable::HeaderTable, item::Item, fptree::FPTree)

[`HeaderTable`](@ref) setters.
"""

"""$(doc_htable_getters)"""
items(htable::HeaderTable) = htable.items

"""$(doc_htable_getters)"""
linkage(htable::HeaderTable, item::Item) = htable.linkage[item]

"""$(doc_htable_setters)"""
linkage!(htable::HeaderTable, item::Item, fptree::FPTree) = htable.linkage[item] = fptree

"""
    function follow(htable::HeaderTable, item::Item)::Union{Nothing,FPTree}

Follow `htable` linkage to (an internal node of) a [`FPTree`](@ref).
"""
function follow(htable::HeaderTable, item::Item)::Union{Nothing,FPTree}
    arrival = linkage(htable, item)
    return isnothing(arrival) ? arrival : follow(arrival, item)
end

"""
    function link!(htable::HeaderTable, fptree::FPTree)

Establish a linkage between the entry in `htable` corresponding to the [`content`](@ref)
of `fptree`.

See also [`content`](@ref), [`FPTree`](@ref), [`HeaderTable`](@ref).
"""
function link!(htable::HeaderTable, fptree::FPTree)
    _content = content(fptree)
    arrival = follow(htable, _content)

    # the content of `fptree` was never seen before by this `htable`
    if linkage(htable, _content) |> isnothing
        linkage!(htable, _content, fptree)
    # the arrival FPTree is linked to the new `fptree`
    elseif arrival isa FPTree
        link!(arrival, fptree)
    # invalid option
    else
        error("Error trying to establish a linkage between HeaderTable and an object " *
            "of type $(typeof(arrival)).")
    end
end

doc_fptree_push = """
    function Base.push!(
        fptree::FPTree,
        itemset::Itemset,
        ninstance::Int64,
        miner::ARuleMiner;
        htable::Union{Nothing,HeaderTable}=nothing
    )

    function Base.push!(
        fptree::FPTree,
        itemset::EnhancedItemset,
        ninstance::Int64,
        miner::ARuleMiner;
        htable::Union{Nothing,HeaderTable}=nothing
    )

    function Base.push!(fptree::FPTree, itemsets::Vector{T}, miner::ARuleMiner) where
        {T <: Union{Itemset, EnhancedItemset}}

Push one or more [`Itemset`](@ref)s/[`EnhancedItemset`](@ref) to an [`FPTree`](@ref).
If an [`HeaderTable`](@ref) is provided, it is leveraged to develop internal links.

!!! warning
    To optimally leverage the compression capabilities of [`FPTree`](@ref)s, the
    [`Itemset`](@ref)s provided should be sorted decreasingly by [`gsupport`](@ref).
    By default, to improve performances, this check is not performed inside this method.

See also [`EnhancedItemset`](@ref), [`FPTree`](@ref), [`gsupport`](@ref),
[`HeaderTable`](@ref), [`Itemset`](@ref).
"""

"""$(doc_fptree_push)"""
function Base.push!(
    fptree::FPTree,
    itemset::Itemset,
    ninstance::Int64,
    miner::ARuleMiner;
    htable::Union{Nothing,HeaderTable}=nothing,
)
    # end of push case
    if length(itemset) == 0
        return
    end

    item = convert(Item, itemset)
    _contributors = contributors(:lsupport, item, ninstance, miner)

    # check if a subtree whose content is the first item in `itemset` already exists
    for child in children(fptree)
        if content(child) == item
            # update the current fptree count and contributors array
            addcount!(child, 1)

            # update contributors (if `fptree` is not the main empty root)
            addcontributors!(child, _contributors)

            # recursively create a subtree, then end
            push!(child, itemset[2:end], ninstance, miner; htable=htable)
            return
        end
    end

    # if no subtree exists, create a new one
    subfptree = FPTree(itemset, ninstance, miner; isroot=false)
    children!(fptree, subfptree)
    addcount!(subfptree, 1)
    addcontributors!(subfptree, _contributors)

    # and stretch the link coming out from `item` in `htable`, to consider the new child
    link!(htable, subfptree)
end

"""$(doc_fptree_push)"""
function Base.push!(
    fptree::FPTree,
    itemset::EnhancedItemset,
    ninstance::Int64,
    miner::ARuleMiner;
    htable::Union{Nothing,HeaderTable}=nothing,
)
    # end of push case
    if length(itemset) == 0
        return
    end
    # TODO: rewrite this for Enhanced itemsets case
    item = convert(Item, itemset)
    _contributors = contributors(:lsupport, item, ninstance, miner)

    # check if a subtree whose content is the first item in `itemset` already exists
    for child in children(fptree)
        if content(child) == item
            # update the current fptree count and contributors array
            addcount!(child, 1)

            # update contributors (if `fptree` is not the main empty root)
            addcontributors!(child, _contributors)

            # recursively create a subtree, then end
            push!(child, itemset[2:end], ninstance, miner; htable=htable)
            return
        end
    end

    # if no subtree exists, create a new one
    subfptree = FPTree(itemset, ninstance, miner; isroot=false)
    children!(fptree, subfptree)
    addcount!(subfptree, 1)
    addcontributors!(subfptree, _contributors)

    # and stretch the link coming out from `item` in `htable`, to consider the new child
    link!(htable, subfptree)
end

"""$(doc_fptree_push)"""
Base.push!(
    fptree::FPTree,
    itemsets::Vector{T},
    ninstance::Int64,
    miner::ARuleMiner;
    htable::Union{Nothing,HeaderTable}=nothing
) where {T <: Union{Itemset, EnhancedItemset}} = [push!(
    fptree, itemset, ninstance, miner; htable=htable) for itemset in itemsets]

Base.reverse(htable::HeaderTable) = reverse(items(htable))

"""
    patternbase(item::Item, htable::HeaderTable)::ConditionalPatternBase

Retrieve the conditional pattern base of `fptree` based on `item`.

The conditional pattern based on a [`FPTree`](@ref) is the set of all the paths from the
tree root to nodes containing `item` (not included).

Thinking about the modal generalization of [`fpgrowth`](@ref), you can see each collected
path to be an "enhanced [`Itemset`](@ref)", where each [`Item`](@ref) is associated with
a [`WorldsMask`](@ref), given by the minimum of its [`contributors`](@ref) and the ones of
`item`.

See also [`contributors`](@ref), [`fpgrowth`](@ref), [`FPTree`](@ref), [`Item`](@ref),
[`Itemset`](@ref), [`WorldsMask`](@ref).
"""
function patternbase(item::Item, htable::HeaderTable)
    # think a pattern base as a vector of vector of itemsets (a vector of vector of items);
    # the reason why the type is explicited differently here, is that every item must be
    # associated with a specific WorldsMask to guarantee correctness.
    _patternbase = ConditionalPatternBase([])

    # follow horizontal references starting from `htable`;
    # for each reference, collect all the ancestors keeping a WorldsMask which, at each
    # position, is the minimum between the value in reference's mask and the new node one.
    fptree = linkage(htable, item)
    fptcontributors = contributors(fptree)

    while !isnothing(fptree)
        enchanceditemset = EnhancedItemset([])

        ancestorfpt = parent(fptree)
        while !isnothing(content(ancestorfpt))
            # prepend! instead of push! because we must keep the top-down order of items
            # in a path, but we are visiting a branch from bottom upwards.
            prepend!(enchanceditemset, (content(fptree),
                merge(minimum, fptcontributors, contributors(ancestorfpt))))
            ancestorfpt = parent(ancestorfpt)
        end

        # before following the linkage, push the collected "enhanced Itemset"
        push!(_patternbase, enchanceditemset)
        fptree = linkage(fptree)
    end

    return _patternbase
end

############################################################################################
#### Main FP-Growth logic ##################################################################
############################################################################################

"""
    fpgrowth(; fulldump::Bool=true, verbose::Bool=true)::Function

Wrapper function for the FP-Growth algorithm over a modal dataset.
Returns a `function f(miner::ARuleMiner, X::AbstractDataset)::Nothing` that runs the main
FP-Growth algorithm logic,
[as described here](https://www.cs.sfu.ca/~jpei/publications/sigmod00.pdf).
"""
function fpgrowth(;
    fulldump::Bool=true,   # mostly for testing purposes
    verbose::Bool=true,
)::Function

    # utility function to build a modal FP-Tree by eager-loading `ninstance` `itemsets`;
    # for each internal node, a contributor-worlds array is kept.
    function _allinstancespush!(
        fptree::FPTree,
        ninstance_to_itemsets::Vector{Vector{Itemset}},
        ninstances::Int64,
        miner::ARuleMiner,
        htable::HeaderTable
    )
        # simply call the single itemset case multiple times,
        # assuming i-th itemsets refers to i-th instance
        [push!(fptree, ninstance_to_itemsets[i], i, miner; htable=htable)
            for i in 1:ninstances]
    end

    function _fpgrowth_preamble(miner::ARuleMiner, X::AbstractDataset) # ::Nothing
        @assert SoleRules.gsupport in reduce(vcat, item_meas(miner)) "FP-Growth requires " *
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
            if gmeas_algo(candidate, X, lthreshold, miner=miner) >= gthreshold
        ] |> unique

        # associate each instance in the dataset with its frequent itemsets
        _ninstances = ninstances(X)
        ninstance_toitemsets_sorted = [Vector{Itemset}([]) for _ in 1:_ninstances]

        # for each instance, sort its frequent itemsets by global support
        for i in 1:_ninstances
            ninstance_toitemsets_sorted[i] = sort([
                    itemset
                    for itemset in frequents
                    if getlocalmemo(miner, (:lsupport, itemset, i)) > lsupport_threshold
                ], by=t -> getglobalmemo(miner, (:gsupport, t)), rev=true)
        end

        # create an initial fptree
        fptree = FPTree()
        # create and fill an header table, necessary to traverse FPTrees horizontally
        htable = HeaderTable(frequents, fptree)

        _allinstancespush!(fptree, ninstance_toitemsets_sorted, _ninstances, miner, htable)

        return fptree, htable

        # call main logic
        # _fpgrowth_kernel(fptree, htable, miner, Itemset())
    end

    function _fpgrowth_kernel(
        fptree::FPTree,
        htable::HeaderTable,
        miner::ARuleMiner,
        leftout_items::Itemset
    )
        # if `fptree` contains only one path (hence, it can be considered a linked list),
        # then combine all the Itemset collected from previous step with the remained ones.
        if islist(fptree)
            survivor_items = retrieveall(fptree)
            push!(freqitems(miner), (combine(leftout_items, survivor_items)|>collect)...)
        else
            for item in reverse(htable)
                # conditional pattern base is a vector of "enhanced" itemsets, that is,
                # itemsets whose items are paired with a contributors vector.
                conditional_patternbase = patternbase(item, htable)

            end
        end
    end

    return _fpgrowth_preamble
end

############################################################################################
#### Specific utilities ####################################################################
############################################################################################


"""
    macro fpoptimize(ex)

Enable [`ARuleMiner`](@ref) contructor to handle [`fpgrowth`](@ref) efficiently by
leveraging a [`Contributors`](@ref) structure.

# Usage
julia> miner = @fpoptimize ARuleMiner(X, apriori(), manual_alphabet, _item_meas, _rule_meas)

See also [`ARuleMiner`](@ref), [`Contributors`](@ref), [`fpgrowth`](@ref).
"""
macro fpoptimize(ex)
    # Extracting function name and arguments
    func, args = ex.args[1], ex.args[2:end]

    # Constructing the modified expression with kwargs
    return esc(:($(func)($(args...); info=(; contributors=Contributors([])))))

    return new_ex
end
