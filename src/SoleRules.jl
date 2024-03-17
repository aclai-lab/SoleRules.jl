module SoleRules
# Currently, the only topic covered by SoleRules is Association Rules.

import Base.show
using Combinatorics
using FunctionWrappers: FunctionWrapper
using IterTools
using Parameters
using Random
using ResumableFunctions

using Reexport
@reexport using SoleBase
@reexport using SoleLogics
@reexport using MultiData
@reexport using SoleModels
@reexport using SoleData

using SoleLogics: AbstractInterpretation, getinstance, LogicalInstance, nworlds
using SoleData: SupportedLogiset, UnivariateSymbolValue

using StatsBase

include("core.jl")

export Item
export Itemset, toformula

export Threshold
export WorldsMask, EnhancedItemset, ConditionalPatternBase

export ARule
export antecedent, consequent

export ConstrainedMeasure, islocalof, isglobalof
export ARMSubject
export LmeasMemoKey, LmeasMemo, Contributors
export GmeasMemoKey, GmeasMemo
export Contributors

export ARuleMiner
export dataset, algorithm
export item_meas, rule_meas
export freqitems, nonfreqitems, arules
export getlocalthreshold, setlocalthreshold
export getglobalthreshold, setglobalthreshold
export getlocalmemo, setlocalmemo
export getglobalmemo, setglobalmemo
export info

export mine, apply

# export RuleAntecedent, Star

include("meaningfulness-measures.jl")

export lsupport, gsupport
export lconfidence, gconfidence

include("manipulations.jl")

export Zcombine, prune
export getcontributors
export arules_generator

include("algorithms/apriori.jl")

export apriori

include("algorithms/fpgrowth.jl")

export FPTree
export content, parent, children, count, contributors
export content!, parent!, children!, count!, addcount!, contributors!, addcontributors!
export islist, retrieveall

export HeaderTable, items
export linkage, linkage!, follow, link! # dispatches for both FPTree and HeaderTable
export patternbase
export fpgrowth, @fpoptimize


include("algorithms/base-cn2.jl")

export CN2

include("utils.jl") # IDEA: move this in SoleData

export equicut, quantilecut
export make_conditions

end
