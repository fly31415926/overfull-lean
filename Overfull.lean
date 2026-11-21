import Overfull.Arithmetic
import Overfull.Basic
import Overfull.ColorClasses
import Overfull.CliqueColors
import Overfull.CutCounting
import Overfull.Relabeling
import Overfull.SharpnessArithmetic
import Overfull.Sharpness.Petersen
import Overfull.Sharpness.Encoding
import Overfull.Sharpness.WeightedPetersen
import Overfull.Sharpness.Family
import Overfull.Sharpness.DeletedPetersen
import Overfull.Sharpness.UpperColoring
import Overfull.Sharpness.ColoringObstruction
import Overfull.Sharpness.WholeCliques
import Overfull.Sharpness.OddSets
import Overfull.Specifications
import Overfull.Sharpness.Theorems
import Overfull.MainReduction
import Overfull.RobustExpansion
import Overfull.BipartiteMatching
import Overfull.RobustStability
import Overfull.External.PerfectBMatching
import Overfull.FractionalMatching
import Overfull.Dense.CycleAbsorber
import Overfull.MatchingProbability
import Overfull.Vizing.Theorem
import Overfull.OverfullSubgraphs

import Overfull.Multigraph
import Overfull.MatchingPolytope
import Overfull.HallDefect
import Overfull.BipartiteAugment
import Overfull.BipartiteRange
import Overfull.SmallCuts
import Overfull.External.FiniteCirculation
import Overfull.Dense.SignedFlow
import Overfull.Dense.UnequalFlow
import Overfull.MultigraphMatchingProbability

import Overfull.Konig
import Overfull.Dense.GeometricCorrection
import Overfull.MultigraphColoring
import Overfull.Dense.TripartiteGraph
import Overfull.Dense.LinkFlows
import Overfull.Dense.FractionalTriangles
import Overfull.TutteBerge
import Overfull.BalancedColoring
import Overfull.MultigraphGreedy
import Overfull.SparseColoring
import Overfull.RandomReserve
import Overfull.RandomReserveDegrees
import Overfull.MatchingExtension
import Overfull.BipartitePackingDeficiency
import Overfull.BipartitePackingStep
import Overfull.BipartitePacking
import Overfull.BipartitePackingCorollaries
import Overfull.Probability.Hypergeometric
import Overfull.Dense.Encoding
import Overfull.Dense.Reserve
import Overfull.Dense.FiniteAbsorberRemainders
import Overfull.Dense.FiniteAbsorber
import Overfull.Dense.FiniteAbsorberSubgraph
import Overfull.MultigraphFanApplications
import Overfull.OrdinaryRandomReserveDegrees
import Overfull.OrdinaryRobustStability
import Overfull.OrdinaryPackingWorking
import Overfull.PairedCut.Labels
import Overfull.PairedCut.Full
import Overfull.RobustRealization
import Overfull.AuxiliaryCompletion
import Overfull.AuxiliaryCompletion.BalancedIncidenceGraph
import Overfull.MatchingPairing
import Overfull.OrdinaryPackingBounds
import Overfull.OrdinaryPackingInitial
import Overfull.OrdinaryMatchingCompletion
import Overfull.OrdinaryPackingStrategy
import Overfull.BalancedCore
import Overfull.MatchingRepairAccounting
import Overfull.OrdinaryPacking
import Overfull.MatchingRepairLoad
import Overfull.MatchingRepairStep
import Overfull.Dense.BalanceRepairBounds
import Overfull.Dense.BalanceRepair.Graph
import Overfull.Dense.BalanceRepair.Routing
import Overfull.MatchingRepair
import Overfull.Dense.BalanceRepair
import Overfull.Replacement
import Overfull.PrescribedMatching
/-!
# Partial formalization of the overfull manuscript

Every included mathematical module is imported here. In addition to the
sharpness results, the development proves structural preliminaries and
records the final critical-graph reduction with its missing inputs explicit.
The specification `Overfull.MainTheorem` remains unproved.
See README.md and docs/coverage.json for the precise scope of the checked work.
-/
