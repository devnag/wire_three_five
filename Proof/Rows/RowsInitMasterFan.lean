import Proof.Rows.RowsBaseLayout

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.MasterFan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-- The 23 request-level source words (`w = 12T+19`, `v = T`; `U`, `F` the cell parameters; `cnt` the circuit
count; `native`, `mask`, `top` the request's own fields). -/
def thrSrc (q T U F cnt : Nat) (native mask top : List Bool) : Fin 23 → List Bool :=
  ![List.replicate (T+1) true, frame (SignedSortKey.binary (T+1) 0),
    List.replicate (P1Closure.HardwireBudget.C (T+1)) true, CompareMachine.word q, CompareMachine.word 0,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.R T q (T+1)) true,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.U T q (T+1)) true, mask,
    List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.H T q (T+1)) true, native,
    List.replicate (2*(12*T+19)+1) true, frame (SignedSortKey.binary (12*T+19) 0),
    CompareMachine.word (2*(2*(12*T+19)+1)), frame (SignedSortKey.binary (12*T+19) 1),
    List.replicate U true, List.replicate F true, CompareMachine.word 1, CompareMachine.word 2,
    CompareMachine.word 3, UnaryTemplate.tape 0, UnaryTemplate.tape cnt, List.replicate T true, top]

/-- Which source word each master port receives (`none` = blank). -/
def thrSel (i : Fin 254) : Option (Fin 23) :=
  match i.val with
  | 2 => some 0 | 3 => some 1 | 4 => some 2 | 5 => some 3 | 111 => some 3
  | 6 => some 4 | 122 => some 4 | 150 => some 4 | 154 => some 4 | 219 => some 4 | 233 => some 4
  | 241 => some 4 | 252 => some 4 | 253 => some 4
  | 7 => some 5 | 105 => some 6 | 108 => some 7 | 112 => some 8 | 124 => some 9 | 137 => some 10
  | 147 => some 11 | 148 => some 11 | 153 => some 11 | 207 => some 11 | 208 => some 11 | 213 => some 11
  | 217 => some 11 | 238 => some 11 | 239 => some 11 | 250 => some 11 | 251 => some 11
  | 152 => some 12 | 156 => some 13 | 190 => some 14 | 248 => some 14 | 216 => some 15
  | 234 => some 16 | 235 => some 17 | 236 => some 18 | 223 => some 19 | 237 => some 20 | 227 => some 21
  | 232 => some 22
  | _ => none

theorem pad_rep (R n : Nat) (h : n ≤ R) : ZeroPadding.pad R (List.replicate n false) = ZeroPadding.pad R [] := by
  simp only [ZeroPadding.pad, List.length_replicate, List.length_nil, Nat.sub_zero, List.nil_append]
  rw [← List.replicate_add]
  congr 1
  omega

theorem pad_pad' (R n : Nat) (l : List Bool) (h : n ≤ R) :
    ZeroPadding.pad R (ZeroPadding.pad n l) = ZeroPadding.pad R l := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc]
  rw [← List.replicate_add]
  congr 2
  omega

theorem word0 : [false] = CompareMachine.word 0 := rfl

/-- One port of the table: evaluate the input at the literal port, reduce the table, close with the pad lemmas. -/
macro "fan_port" : tactic => `(tactic| first
  | (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input <;>
      simp (disch := first | assumption | (intro hne; exact absurd hne (by decide))) only [thrSel, thrSrc, Option.elim, Matrix.cons_val, ZeroPadding.pad_zero,
        pad_rep, pad_pad', word0] <;> rfl))

end
end RowsInit.MasterFan
