import Proof.Rows.RowsKeyStep
import Proof.Packets.PacketsCursorOrder

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.KeySucc
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc
open RowsConstruction.BaseLayout
noncomputable section

/-! ## 1. The compiled census of the THR traversal input -/

section Census
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (I : Finset (Fin r.q)) (T L target w F U v : Nat)

variable (sel : ThresholdRows.Selection a r) (x : BitInput r.q) {cutoff : Nat} (prime : PrimeIndex cutoff)
  (o : Fin prime.val)

theorem thr_242 : PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v 242 =
    frame (SignedSortKey.binary w o.val) := by
  bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input
  rfl

theorem pad_zero (l : List Bool) : ZeroPadding.pad 0 l = l := by
  simp [ZeroPadding.pad]

theorem thr_prime_ports (i : Fin 254) (hi : i = 149 ∨ i = 218 ∨ i = 240) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i =
      frame (SignedSortKey.binary w prime.val) := by
  rcases hi with rfl | rfl | rfl <;>
    (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input; simp only [pad_zero])

theorem thr_209 : PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v 209 =
    ZeroPadding.pad F (frame (SignedSortKey.binary w prime.val)) := by
  bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input
  simp only [pad_zero]

theorem thr_220 : PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v 220 =
    ZeroPadding.pad U (frame (SignedSortKey.binary w (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel))) := by
  bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input
  simp only [pad_zero]

theorem thr_digit_ports (c : Fin 4) :
    PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v
      ⟨228+c.val, by omega⟩ =
      frame (SignedSortKey.binary v ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).digits c)) := by
  fin_cases c <;> (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input; rfl)

end Census

section Succ
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

abbrev keys := RCFive.RowKeys.thrKeys a r L target
abbrev dig := thrDigitsOf a r L target
abbrev spec := cursorSpec a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target)
abbrev cut := CloseoutFinalC10ThresholdRows.primeCutoff a r target

include four in
theorem dig_res (k : RCFive.RowKeys.ThrKey a r L target) : dig a r L target k 6 = k.residue.val := by
  have h : ¬ ((6 : Fin 8).val < r.circuits.length) := by simp; omega
  unfold dig thrDigitsOf
  rw [dif_neg h]
  rfl

include four in
theorem dig_prime (k : RCFive.RowKeys.ThrKey a r L target) :
    dig a r L target k 4 = (primeIndexFinEquiv (cut a r target) k.prime).val := by
  have h : ¬ ((4 : Fin 8).val < r.circuits.length) := by simp; omega
  unfold dig thrDigitsOf
  rw [dif_neg h]
  rfl

include four in
theorem primeAt_dig (k : RCFive.RowKeys.ThrKey a r L target) :
    primeAt (cut a r target) (dig a r L target k 4) = k.prime.val := by
  rw [dig_prime a r four L target k]
  unfold primeAt
  rw [dif_pos (Fin.isLt _)]
  simp

include four in
theorem dig_sel (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin r.circuits.length) :
    dig a r L target k ⟨i.val, by omega⟩ = (k.selection i).val := by
  unfold dig thrDigitsOf
  rw [dif_pos i.isLt]


end Succ

end
end RowsConstruction.KeySucc
