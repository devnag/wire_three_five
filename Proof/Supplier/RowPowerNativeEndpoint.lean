import Proof.Supplier.RowPowerNativeReusable

/-! Exact reusable endpoint and binary meaning of the executed native-field
appender. Its output is ready for the next call on the same physical bank. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReusable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open Streaming SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def block (w : ℕ) (z : ℤ) (negative : Bool) :=
  RowPowerBlock.digits negative (decide (z<0))
    (ClockNormalize.resize w (binary (natBitLength z.natAbs) z.natAbs))

theorem raw_output_live (source : List Bool) (pos w : ℕ) (z : ℤ)
    (positive negative : List Bool) (i : Fin 12) (hi : i=0 ∨ i=9 ∨ i=10 ∨ i=11) :
    (RowPowerNative.output source pos w (binary (natBitLength z.natAbs) z.natAbs)
      (decide (z<0)) positive negative).tapes i=
    (![source,[],[],[],[],[],[],[],[],List.replicate w true,
      positive++marks (block w z false)++[false],
      negative++marks (block w z true)++[false]] : Fin 12 → List Bool) i := by
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp [RowPowerNative.output,RecoveryFocus.config,RowPowerNative.pick,
    RowPowerNative.parsed,TapeEmbedding.config,RowPowerNative.extraTapes,
    DecompositionNativeMagnitude.fieldOutput,MatrixDimensionField.output,
    RowPowerBlock.final,Composition.rightConfig,Fin.addCases,block]

end NearCubicWires.RepairOrdinary.RowPowerNativeReusable
