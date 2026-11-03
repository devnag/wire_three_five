import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ6
import Proof.Wire_3_5.Primitive.Writers.SymDecCall

/-! # T3 THR decode front, packaging part 7: the call's index links

At a THR call, the front's arithmetic on the unit index `j` (`t = j / EU / N²`, then `t / Σp / |𝒢|`, `t / Σp mod |𝒢|`,
`t mod Σp`) is `Enum.thrIndexEquiv`'s mixed radix (seed major, then the selection, then the prime row): the seed's
index, the selection's index and the prime row `(p, s)` of `ThrDecOut` (`seed_val`, `sel_val`, `prime_val`). The
unit count `thrTOT` is the front's `2^{seedBits}·|𝒢|·Σp·2^{2k_h}·EU` (`tot_eq`).

Paper quantity of the main type: the THR state `(e, g, p, s)` of a request unit (P3:2543-2558, 2573-2580). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine

section Nums2
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (D capT : ℕ)

theorem hashNums_get2 : (ThrData.hashNums P Cs carriers alg D capT).getD 2 0 = Fintype.card (ThrEq P Cs alg) := by
  simp [ThrData.hashNums, ThrData.thrNumList, PrimThrW.Joins.ThrNumVals.get, PrimThrW.Joins.thrNumVals]

theorem hashNums_get8 : (ThrData.hashNums P Cs carriers alg D capT).getD 8 0 = (thrOccs P Cs).length := by
  simp [ThrData.hashNums, ThrData.thrNumList, PrimThrW.Joins.ThrNumVals.get, PrimThrW.Joins.thrNumVals]

theorem thr_slice_len (r : ℕ) (hr : r < carriers.length) (hr1 : r ≤ 1) :
    ((Records.thrSlices P Cs carriers).getD r []).length =
      SymDec.fbL r ((carriers.map List.length).getD 0 0) ((carriers.map List.length).getD 1 0) := by
  unfold Records.thrSlices
  rw [Records.prefix_carrier carriers _ r hr, SymDec.mask_len]
  have e : ∀ k < carriers.length, (carriers.getD k []).length = (carriers.map List.length).getD k 0 := fun k hk => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  unfold SymDec.fbL
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with h | h <;> subst h
  · rw [if_pos rfl, e 0 hr]
  · rw [if_neg (by decide), e 1 hr]

theorem thr_slice_off (r : ℕ) (hr : r < carriers.length) (hr1 : r ≤ 1) :
    Records.sliceOff (Records.thrSlices P Cs carriers) r = SymDec.fbOff r ((carriers.map List.length).getD 0 0) := by
  unfold SymDec.fbOff
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr1 with h | h <;> subst h
  · simp [Records.sliceOff]
  · rcases carriers with _ | ⟨X, t⟩
    · simp at hr
    · simp [Records.sliceOff, Records.thrSlices, SymDec.mask_len]

theorem thr_off (hk : carriers.length ≤ 2) :
    Records.thrOff P Cs carriers = 2 * ((carriers.map List.length).getD 0 0 + (carriers.map List.length).getD 1 0) := by
  rw [Records.thrOff_eq, SymDec.sum_two _ (by rw [List.length_map]; exact hk)]

theorem thr_pool (hk : carriers.length ≤ 2) :
    (Records.thrPool P Cs carriers).length =
      2 * ((carriers.map List.length).getD 0 0 + (carriers.map List.length).getD 1 0) +
        (ThrData.hashNums P Cs carriers alg D capT).getD 8 0 := by
  rw [RadBnd.thrPool_length, thr_off P Cs carriers hk, hashNums_get8]

end Nums2

section Idx

section Vals

end Vals

end Idx

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
