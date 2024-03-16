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
import SoleData: alphabet, feature, instances
import SoleLogics: children
import SoleBase: CLabel
import Base: ==, ∈
using MLJ: load_iris

# variabile temporaneamente globale

global beam_width = 3
global SPEC_VERSION = :new

function istop(
    lmlf::LeftmostLinearForm
)
    return children(lmlf ) == [⊤]
end


function entropy(
    y::AbstractVector{<:CLabel};
)::Float32

    length(y) == 0 && return Inf

    count = values(countmap(y))
    length(count) == 1 && return 0.0

    logbase = length(count)
    prob = count ./ sum(count)
    return -sum(prob .* log.(logbase, prob))
end

# Check condition equivalence
function checkconditionsequivalence(
    φ1::LeftmostConjunctiveForm{Atom{ScalarCondition}},
    φ2::LeftmostConjunctiveForm{Atom{ScalarCondition}},
)::Bool
    return  length(φ1) == length(φ2) &&
            !any(iszero, map( x-> x ∈ atoms(φ1), atoms(φ2)))
end

function checkconditionsequivalence(
    φ1::LeftmostConjunctiveForm{Atom{ScalarCondition}},
    φs::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}},
)::Bool
    return any(φ_i->checkconditionsequivalence(φ_i, φ1), φs)
end


function feature(
    φ::LeftmostConjunctiveForm{Atom{ScalarCondition}}
)::AbstractVector{UnivariateSymbolValue}
    conditions = value.(atoms(φ))
    return feature.(conditions)
end

function composeformulas!(
    φ::LeftmostConjunctiveForm,
    a::Atom
)
    if feature(value(a)) ∉ feature(φ)
        push!(φ.children, a)
    else return false end
end

function conjunctibleconds(
    bsc::BoundedScalarConditions,
    φ::Formula
)::Union{Bool,BoundedScalarConditions}

    φ_features = feature(φ)
    conds = [(meta_cond, vals) for (meta_cond, vals) ∈ bsc.grouped_featconditions
                if feature(meta_cond) ∉ φ_features]
    return conds == [] ? false : BoundedScalarConditions{ScalarCondition}(conds)
end


function sortantecedents(
    star::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}},
    X::PropositionalLogiset,
    y::Vector{<:CLabel},
    beam_width::Int64
)
    length(star) == 0 && return [], Inf

    antd_entropies = map(antd->begin
            sat_idxs = interpret(antd, X)
            entropy(y[sat_idxs])
        end, star)
    i_bests = partialsortperm(antd_entropies, 1:min(beam_width, length(antd_entropies)))
    bestentropy = antd_entropies[i_bests[1]]

    return (i_bests, bestentropy)
end

function find_new_conditions(
    X::PropositionalLogiset,
    candidate_antecedent::LeftmostConjunctiveForm
)::Vector{Atom{ScalarCondition}}

    sat_idexs = interpret(candidate_antecedent, X)
    X_covered = SoleData.instances(X, sat_idexs, Val(false))
    @show SoleData.gettable(X_covered)
    # TODO correct cast?
    _atoms = Vector{Atom{ScalarCondition}}(atoms(alphabet(X_covered)))
    possible_atoms = [a for a in _atoms if a ∉ atoms(candidate_antecedent) ]
    return possible_atoms
end

function refine_antecedents(
    candidate_antecedents::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}},
    X::PropositionalLogiset,
)::Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}

    if length(candidate_antecedents) == 0

        possible_conditions =  map(sc->Atom{ScalarCondition}(sc), alphabet(X))
        # qui ci va la condizione di uscita ?
        #  printstyled("atoms(ant) | EMPTY\n", bold=true, color=:red)
        # @showlc possible_conditions :blue

        return  map(a->LeftmostConjunctiveForm{Atom{ScalarCondition}}([a]), possible_conditions)
    else
        refined_antecedents = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
        for ant ∈ candidate_antecedents

            possible_conditions = find_new_conditions(X, ant)
            isempty(possible_conditions) &&
                return Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])

            @showlc atoms(ant) :red
            # @showlc possible_conditions :blue

            for atom ∈ possible_conditions
                new_antecedent = deepcopy(ant)
                push!(new_antecedent.children, atom)
                push!(refined_antecedents, new_antecedent)
            end
        end
    end
    return refined_antecedents
end

function beamsearch(
    X::PropositionalLogiset,
    y::AbstractVector{CLabel},
)
    best_antecedent = LeftmostConjunctiveForm([⊤])
    bestentropy = entropy(y)

    newstar = Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
    while true

        (star, newstar) = newstar, Vector{LeftmostConjunctiveForm{Atom{ScalarCondition}}}([])
        # @showlc star :green
        # @show best_antecedent
        newstar = refine_antecedents(star, X)
        isempty(newstar) && break

        _sortperm, newbestentropy = sortantecedents(newstar,X,y,beam_width)
        newstar = newstar[_sortperm]
        if newbestentropy < bestentropy
            best_antecedent = newstar[begin]
            bestentropy = newbestentropy
            # println("Aggiornato best_antecedent:")
            # @show best_antecedent
        end

        # readline()
        # print("\033c") #clear the terminal
    end
    return best_antecedent
end

function displaylist(decisionlist)
    for rule in rulebase(decisionlist)
        print("$(SoleModels.info(rule.consequent)[1]) $(rule)")
    end
end

function sole_cn2(
    X::PropositionalLogiset,
    y::AbstractVector{CLabel};
)
    length(y) != nrow(X) && error("size of X and y mismatch")
    slice_tocover = collect(1:length(y))


    current_X = SoleData.instances(X, slice_tocover, Val(false))
    current_y = y[slice_tocover]

    rulelist = Rule[]
    while true
        currentrule_distribution = Dict(unique(y) .=> 0)

        best_antecedent = beamsearch(current_X, current_y)
        @show best_antecedent
        # Exit condition
        istop(best_antecedent) && break
        covered_offsets = findall(z->z==1,
                            interpret(best_antecedent, current_X))
        @show current_X
        @show covered_offsets
        covered_y = current_y[covered_offsets]
        for c in covered_y
            currentrule_distribution[c] += 1
        end
        antecedentclass = findmax(countmap(covered_y))[2]
        info_cm = (;
            supporting_labels = Int.(values(currentrule_distribution))
        )
        consequent_cm = SoleModels.ConstantModel(antecedentclass, info_cm)

        push!(rulelist, Rule(best_antecedent, consequent_cm))

        setdiff!(slice_tocover, slice_tocover[covered_offsets])
        current_X = SoleData.instances(X, slice_tocover, Val(false))
        current_y = y[slice_tocover]
    end

    defaultrule_consequent = current_y[begin]
    defaultrule = Rule(⊤, defaultrule_consequent)
    return DecisionList(rulelist, defaultrule)


end

X...,y = load_iris()
X_df = DataFrame(X)
X = PropositionalLogiset(X_df)
n_instances = ninstances(X)
y = Vector{CLabel}(y)
