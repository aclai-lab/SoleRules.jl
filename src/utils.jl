# shared logic amongs methods that performs binning; see equicut and quantilecut.
# Explanation:
# consider the variable targetted by feature (feature.i_variable);
# return a sorted list of its separation values.
function _cut(X_df::DataFrame, feature::Function, var::Integer, cutpolitic::Function)
    vals = map(x -> feature(x), X_df[:,var])
    return cutpolitic(vcat(vals))
end

"""
Bin [`DataFrame`](@ref) values into discrete, equispaced intervals.
Return the sorted separation values vector for each variable.
"""
function equicut(
    X_df::DataFrame,
    feature::Function,
    var::Integer;
    distance::Integer = 3,
    keepleftbound = true
)

    function _equicut(vals::Vector{Float64})
        unique!(vals)

        if !issorted(vals)
           sort!(vals)
        end

        valslen = length(vals)
        @assert distance < valslen "Distance $(distance) is higher than unique values to " *
        "bin, which is $(valslen). Please lower the distance."

        ranges = collect(Iterators.partition(1:valslen, distance))
        bounds = [vals[last(r)] for r in ranges]

        if keepleftbound
            append!(bounds, vals[1])
        end

        return bounds |> unique |> sort
    end

    # return the thresholds associated with each feature
    return _cut(X_df, feature, var, _equicut)
end

"""
Bin [`DataFrame`](@ref) values in equal-sized bins.
Return the sorted separation values vector for each variable.
"""
function quantilecut(
    X_df::DataFrame,
    feature::Function,
    var::Integer;
    nbins::Integer = 3
)

    function _quantilecut(vals::Vector{Float64})
        h = fit(Histogram, vals, nbins=nbins)
        return collect(h.edges...)
    end

    return _cut(X_df, feature, var, _quantilecut)
end

"""
Return the atoms wrapping all the possible conditions shaped as
    condition(feature(nvariable) testop threshold)
such as
    `ScalarCondition(UnivariateMin(1), >, -0.5)`
whose [`syntaxstring`](@ref) is
    `min[V3] > 1.1`

See also [`syntaxstring`](@ref), [`SoleModels.TestOperator`](@ref),
[`SoleLogics.UnivariateFeature`](@ref).
"""
function make_conditions(
    thresholds::Vector{Float64},
    nvariables::Vector{Int64},
    features::Vector{DataType}, # NOTE: this should be Vector{<:AbstractFeature}
    testops::Vector{SoleModels.TestOperator};
    condition = ScalarCondition
)
    return [
        Atom(condition(feature(nvariable), testop, threshold))
        for (threshold, nvariable, feature, testop)
            in IterTools.product(thresholds, nvariables, features, testops)
    ]
end