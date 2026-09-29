import Proof.Foundations.WireScaleTransfer

/-!
# Common physical hard cores and their padded target facts

The recovery dichotomy must freeze one truth table before the two circuit modes
split.  `PhysicalCommonCore` records that table with separate natural wire
budgets for the two physical families; the only target-length loss is the
factor-27 coefficient shrink from `WireScaleTransfer`.
-/

namespace NearCubicWires.PhysicalHardness

open NearCubicWires
open NearCubicWires.AppendixC
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryPipeline
open NearCubicWires.WireScaleTransfer

end NearCubicWires.PhysicalHardness
