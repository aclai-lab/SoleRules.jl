"""
    function apriori(
        fulldump::Bool = true
    )::Function

Wrapper of Apriori algorithm over a (modal) dataset.
This returns a void function whose arg
"""
function apriori(;
    fulldump::Bool = true   # mostly for testing purposes
)::Function

    # look at the (k-1)-subsets of each candidate itemset:
    # if a subset was not frequent, then prune it.
    function _prune(
        candidates::Vector{Itemset},
        frequents::Vector{Itemset},
        k::Integer
    )
        survivors = Vector{Itemset{<:ItemsetContent}}([])

        # if the frequents set does not contain the subset of a certain candidate,
        # that candidate is pruned out.
        for itemset in candidates
            for combo in reduce(vcat, combinations([itemset], k) |> collect)
                if value(combo) in frequents
                    push!(survivors, itemset)
                    break
                end
            end
        end

        return survivors
    end

    # modal apriori main logic, as in https://ceur-ws.org/Vol-3284/492.pdf
    function _apriori(miner::ARuleMiner, X::AbstractDataset)::Nothing
        # candidates of length 1 - all the letters in our alphabet
        candidates = Itemset.(alphabet(miner))

        frequents = Vector{Itemset}([])     # frequent itemsets collection
        nonfrequents = Vector{Itemset}([])  # non-frequent itemsets collection (testing)

        while !isempty(candidates)
           # for each candidate, establish if it is interesting or not
            for item in candidates
                interesting = true

                for meas in item_meas(miner)
                    (gmeas_algo, lthreshold, gthreshold) = meas
                    if gmeas_algo(item, X, lthreshold) < gthreshold
                        interesting = false
                        break
                    end
                end

                if interesting
                    # dump the just computed frequent itemsets inside the miner
                    push!(frequents, item)
                elseif fulldump
                    # dump the non-frequent itemsets (maybe because of testing purposes)
                    push!(nonfrequents, item)
                end
            end

            # save frequent and nonfrequent itemsets inside miner structure
            push!(freqitems(miner), frequents...)
            push!(nonfreqitems(miner), nonfrequents...)

            # generate new candidates
            k = (candidates |> first |> length) + 1
            candidates = combine(candidates, k)
            candidates = _prune(candidates, frequents, k-1)

            # empty support structures
            empty!(frequents)
            empty!(nonfrequents)
        end
    end

    return _apriori
end
