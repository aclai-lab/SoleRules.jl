############################################################################################
#### Itemsets ##############################################################################
############################################################################################

"""
    combine(itemsets::Vector{<:Itemset}, newlength::Integer)

Return a generator which combines [`Itemset`](@ref)s from `itemsets` into new itemsets of
length `newlength` by taking all combinations of two itemsets and joining them.

See also [`Itemset`](@ref).
"""
function combine(itemsets::Vector{<:Itemset}, newlength::Integer)
    return Iterators.filter(
        combo -> length(combo) == newlength,
        Iterators.map(
            combo -> union(combo[1], combo[2]),
            combinations(itemsets, 2)
        )
    )
end

"""
    combine(variable::Vector{<:Item}, fixed::Vector{<:Item})

Return a generator of [`Itemset`](@ref), which iterates the combinations of [`Item`](@ref)s
in `variable` and prepend them to `fixed` vector.

See also [`Item`](@ref), [`Itemset`](@ref).
"""
function combine(variable::Vector{<:Item}, fixed::Vector{<:Item})
    return (Itemset(vcat(combo, fixed)) for combo in combinations(variable))
end

"""
    grow_prune(candidates::Vector{Itemset}, frequents::Vector{Itemset}, k::Integer)

Return a generator, which yields only the `candidates` for which every (k-1)-length subset
is in `frequents`.

See also [`Itemset`](@ref).
"""
function grow_prune(candidates::Vector{Itemset}, frequents::Vector{Itemset}, k::Integer)
    # if the frequents set does not contain the subset of a certain candidate,
    # that candidate is pruned out.
    return Iterators.filter(
        # the iterator yields only itemsets for which every combo is in frequents
        itemset -> all(combo ->
            combo in frequents, combinations(itemset, k-1)),
        combine(candidates, k)
    )
end

"""
    coalesce_contributors(
        itemset::Itemset,
        miner::ARuleMiner;
        lthreshold::Union{Nothing,Threshold}=nothing
    )

Consider all the [`contributors`](@ref) of an [`ARMSubject`](@ref) on all the instances.
Return their sum and a boolean value, indicating whether the resulting contributors
overpasses the local support threshold enough times.

See also [`ARMSubject`](@ref), [`contributors`](@ref), [`Threshold`](@ref).
"""
function coalesce_contributors(
    itemset::Itemset,
    miner::ARuleMiner;
    lmeas::Function=lsupport
)
    if isnothing(lmeas)
        lmeas = lsupport
    end

    _ninstances = ninstances(dataset(miner))
    _contributors = sum([contributors(:lsupport, itemset, i, miner) for i in 1:_ninstances])

    lsupp_integer_threshold = convert(Int64, floor(
        getlocalthreshold(miner, lmeas) * length(_contributors)
    ))

    return _contributors, Base.count(
        x -> x > 0, _contributors) >= lsupp_integer_threshold
end

############################################################################################
#### Association rules #####################################################################
############################################################################################

"""
    arules_generator(itemsets::Vector{Itemset}, miner::ARuleMiner)

Generates association rules from the given collection of `itemsets` and `miner`.
Iterates through the powerset of each itemset to generate meaningful [`ARule`](@ref).

To establish the meaningfulness of each association rule, check if it meets the global
constraints specified in `rule_meas(miner)`, and yields the rule if so.

See also [`ARule`](@ref), [`ARuleMiner`](@ref), [`Itemset`](@ref), [`rule_meas`](@ref).
"""
@resumable function arules_generator(
    itemsets::Vector{Itemset},
    miner::ARuleMiner
)
    for itemset in itemsets
        subsets = powerset(itemset)
        for subset in subsets
            _antecedent = subset
            _consequent = symdiff(itemset, subset)

            if length(_antecedent) == 0 || length(_consequent) == 0
                continue
            end

            interesting = true
            currentrule = ARule((_antecedent, _consequent))

            for meas in rule_meas(miner)
                (gmeas_algo, lthreshold, gthreshold) = meas
                gmeas_result = gmeas_algo(
                    currentrule, dataset(miner), lthreshold, miner=miner)

                if gmeas_result < gthreshold
                    interesting = false
                    break
                end
            end

            if interesting
                push!(arules(miner), currentrule)
                @yield currentrule
            end
        end
    end
end
