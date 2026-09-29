import Proof.Rows.RowsInitMasterFan

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSectionVars false

namespace RowsInit.SymLoopFan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open RowsConstruction RowsConstruction.BaseLayout
noncomputable section

/-- The 17 request-level source words (`T = |input|`, `native`, `mask` the request's own fields, `N c` the SYM
drivers `driverLen r c`). -/
def symSrc (q T : Nat) (native mask : List Bool) (N : Fin 4 → Nat) : Fin 17 → List Bool :=
  ![List.replicate (T+1) true, frame (SignedSortKey.binary (T+1) 0),
    List.replicate (P1Closure.HardwireBudget.C (T+1)) true, CompareMachine.word q, CompareMachine.word 0,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.R T q (T+1)) true,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.U T q (T+1)) true, mask,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.H T q (T+1)) true, native,
    frame (SignedSortKey.binary (T+3) 0), CompareMachine.word (N 0), CompareMachine.word (N 1),
    CompareMachine.word (N 2), CompareMachine.word (N 3), CompareMachine.word 4,
    frame (SignedSortKey.binary (T+3) 4)]

/-- Which source word each SYM master port receives (`none` = blank). -/
def symSel (i : Fin 254) : Option (Fin 17) :=
  match i.val with
  | 2 => some 0 | 3 => some 1 | 4 => some 2 | 5 => some 3 | 111 => some 3
  | 6 => some 4 | 122 => some 4 | 7 => some 5 | 105 => some 6 | 108 => some 7 | 112 => some 8 | 124 => some 9
  | 128 => some 10 | 129 => some 10 | 130 => some 10 | 131 => some 10 | 132 => some 10
  | 135 => some 11 | 136 => some 12 | 137 => some 13 | 138 => some 14 | 139 => some 15 | 144 => some 16
  | _ => none

/-- One port of the table: evaluate the SYM input at the literal port, reduce the table, close with the pad lemmas. -/
macro "sym_port" : tactic => `(tactic| first
  | (bank_nf RowsConstruction.SymVerdict.input <;>
      simp (disch := first | assumption | (intro hne; exact absurd hne (by decide))) only [symSel, symSrc, Option.elim, Matrix.cons_val, ZeroPadding.pad_zero,
        MasterFan.pad_rep, MasterFan.pad_pad', MasterFan.word0] <;> rfl))

section Chunks

end Chunks

/-! ## The sources for every request -/

section Sym

end Sym

/-! ## The fanout -/




end
end RowsInit.SymLoopFan
