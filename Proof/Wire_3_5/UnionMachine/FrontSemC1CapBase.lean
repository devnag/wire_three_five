import Proof.Wire_3_5.UnionMachine.FrontSemCarPre
import Proof.Wire_3_5.UnionMachine.C1SizeBase

/-! # C6 front, the semantic core (17): C1's caps at a guess (P3:3669-3673; `star:selection`, P3:1324-1362)

From the carriers' code bits `≤ K` (and `q`, the variable count, `2^{cb+2}`, the grid, the atoms' and parities'
description bits, `r` all `≤ K`): C1's converter capacity **`capNeed_le`**, the gate totals **`gtF_le`**, `npF_le`,
the per-variable register capacity **`capR_le`**, the carrier-table fuel, the request word **`cap2_le`**, the
selection's output **`capC1_le`**, the entries' code width **`WnG_le`**, and C1's precondition **`pre_of`**.

Paper quantity of the main types: C1's request at the union's carriers and the union machine's per-variable work. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemC1Cap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord intWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (natWord_le natWord_bits)

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem intWord_pred (t : ℤ) : (intWord (t - 1)).length ≤ (intWord t).length + 2 := by
  rw [GateConv.intWord_len', GateConv.intWord_len']
  have h1 : (t - 1).natAbs ≤ t.natAbs + 1 := by
    have := Int.natAbs_sub_le t 1; simpa using this
  have h2 := nbl_mono h1
  have h3 := FrontSemGate.nbl_succ_le t.natAbs
  omega

theorem sum_map_le {α : Type} (X : List α) (f g : α → ℕ) (h : ∀ a ∈ X, f a ≤ g a) :
    (X.map f).sum ≤ (X.map g).sum := by
  induction X with
  | nil => simp
  | cons a X ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem sum_map_affine {α : Type} (X : List α) (b : α → ℕ) (c d : ℕ) :
    (X.map fun a => c * b a + d).sum = c * (X.map b).sum + X.length * d := by
  induction X with
  | nil => simp
  | cons a X ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- **C1's converter capacity at a carrier.** -/
theorem capNeed_le {q : ℕ} (X : Stars.Carrier q) (K : ℕ) (hq : q ≤ K) (hb : natBitLength X.code ≤ K) :
    GateConv.capNeed X ≤ 24 * K + K * (68 * K + 168) := by
  obtain ⟨h1, h2⟩ := FrontSemGate.carrier_bits X
  unfold GateConv.capNeed
  have key : ∀ gt ∈ X, 2 * (GateConv.selGate gt).length + 10 * ((GateConv.gateW gt).length + 2) + 2 ≤
      24 * natBitLength (FrontSemGate.gcode gt) + (68 * q + 168) := by
    intro gt _
    have hs := FrontSemGate.selGate_len gt
    have hw := GateConv.gateW_len gt
    have hp := intWord_pred gt.threshold
    have hsel : (GateConv.selGate gt).length = ((List.ofFn gt.weight).flatMap intWord).length +
        (intWord gt.threshold).length := by simp [GateConv.selGate]
    have hn := natWord_le q
    omega
  have hle := sum_map_le X _ _ key
  rw [sum_map_affine] at hle
  have hX : X.length * (68 * q + 168) ≤ K * (68 * K + 168) :=
    Nat.mul_le_mul (le_trans h2 hb) (by omega)
  have hS : (X.map fun gt => natBitLength (FrontSemGate.gcode gt)).sum ≤ K := le_trans h1 hb
  omega

section Gates
variable {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ)

theorem gtF_le (L : ℕ) (h : ∀ j, (Cs j).length ≤ L) : ∀ x, C1Gates.gtF Cs lits x ≤ x * L
  | 0 => by simp [C1Gates.gtF]
  | x + 1 => by
    have ih := gtF_le L h x
    have hx := h x
    simp only [C1Gates.gtF]
    split_ifs <;> rw [Nat.add_mul, one_mul] <;> omega

theorem npF_le : ∀ x, C1Gates.npF lits x ≤ x
  | 0 => by simp [C1Gates.npF]
  | x + 1 => by
    have ih := npF_le x
    simp only [C1Gates.npF]
    split_ifs <;> omega

end Gates

/-- The dyadic weight's word. -/
theorem ratWord_cnt_le (c e M : ℕ) (hc : c ≤ 2 ^ e) (hM : 2 ^ e ≤ M) :
    (ratWord ((c : ℚ) / 2 ^ e)).length ≤ 4 * M + 7 := by
  rw [C1Rat.ratWord_dyadic, List.length_append, GateConv.intWord_len']
  have hc1 := C1Rat.rstepN_le c e
  have hd := C1Rat.rstepN_d c e
  have hp : 2 ^ (C1Rat.rstepN e (c, false, 0)).2.2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hd
  have e1 := C1Size.nw_le (2 ^ (C1Rat.rstepN e (c, false, 0)).2.2)
  have e2 := PrimAsm.CopyNat.natBitLength_le_self_succ (((C1Rat.rstepN e (c, false, 0)).1 : ℤ).natAbs)
  simp only [Int.natAbs_natCast] at e2 ⊢
  omega

section Guess

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemC1Cap
