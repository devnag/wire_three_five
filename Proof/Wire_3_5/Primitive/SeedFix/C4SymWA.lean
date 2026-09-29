import Proof.Wire_3_5.Primitive.SeedFix.C4WIface
import Proof.Wire_3_5.Primitive.SeedFix.C4CapC

/-! # C4 SYM stage, part 1: the decision loop's slots on the SYM setup's bank

"The processor writes the pool, the enumeration's rulers and constants, and the compiler request's numbers before the
loop" (P3:3011-3016). The SYM child family (`C4Sym.symFam`, `C4Child.chFam` at C6's assembler, `6` tapes) keeps
`32` tapes across the decisions: the compiler fields `PRE`, `POST` (tapes `0`, `2`), the arm's ten rulers and the
prefix (`6`, `8 … 17`), the seventeen constants (`73 … 89`), the printer child's `1^{Q'}` and mask (`199 + PD`,
`200 + PD`, `PD` the printer's tape count); with the loop's log, driver and counter (`410 + 2PD` …) they sit on the
setup's tapes (`gPRE`, `gPOST`, `gW`, the stage's port `1` for the batch, `gMA`, `gUU`, `gLG`, `gRR`); every
other tape of the loop sits on the loop region (`oLP`), where the setup leaves `2^ρ` falses.

* `isK` (the loop's tapes on the setup's), `tgtV` (their targets), `tgtV_lt`, `tgtV_port`, `tgtV_inj`;
* **`symExt`** (the `ext` of `C4Wrap.LoopEntry`, generic in the loop's tape count), `symExt_some`, `symExt_inj`,
  `symExt_lt`, `symExt_port`.

Paper quantity of the main type: the loop's kept words on the setup's tapes. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set

section Slots
variable (L : Lay) (pd : ℕ)

/-- **The loop's tapes on the setup's tapes** (the child's kept tapes, the loop's log, driver and counter). -/
def isK (v : ℕ) : Prop :=
  v = 0 ∨ v = 2 ∨ v = 6 ∨ (8 ≤ v ∧ v ≤ 17) ∨ (73 ≤ v ∧ v ≤ 89) ∨ v = 199 + pd ∨ v = 200 + pd ∨
    v = 410 + 2 * pd ∨ v = 411 + 2 * pd ∨ v = 412 + 2 * pd

instance (v : ℕ) : Decidable (isK pd v) := by unfold isK; infer_instance

/-- **Their targets**: `gPRE`, `gPOST`, the words `gW 0 … 27` (stream `symO j` of the numbers machine), the port `1`,
`gMA`, `gUU`, `gLG`, `gRR`. -/
def tgtV (v : ℕ) : ℕ :=
  if v = 0 then 10659 + 3 * L.U + L.S3.preS.val
  else if v = 2 then 10659 + 3 * L.U + L.S3.postS.val
  else if v = 6 then 10045 + 3 * L.U
  else if v ≤ 17 then 10038 + 3 * L.U + v
  else if v = 76 then 1
  else if v ≤ 82 then 9983 + 3 * L.U + v
  else if v = 83 then 10613 + 3 * L.U
  else if v ≤ 89 then 9982 + 3 * L.U + v
  else if v = 199 + pd then 10072 + 3 * L.U
  else if v = 200 + pd then 10643 + 3 * L.U
  else if v = 410 + 2 * pd then 10659 + 3 * L.U + L.S3.t
  else if v = 411 + 2 * pd then 10655 + 3 * L.U
  else 10073 + 3 * L.U

theorem pre_lt : L.S3.preS.val < L.S3.t := L.S3.preS.isLt
theorem post_lt : L.S3.postS.val < L.S3.t := L.S3.postS.isLt

theorem pre_ne_post : L.S3.preS.val ≠ L.S3.postS.val := fun e => by
  have hd := L.S3.distinct
  have h : L.S3.preS = L.S3.postS := Fin.ext e
  rw [h] at hd
  simp at hd

theorem tv0 (v : ℕ) (h : v = 0) : tgtV L pd v = 10659 + 3 * L.U + L.S3.preS.val := by
  unfold tgtV
  rw [if_pos h]

theorem tv1 (v : ℕ) (h : v = 2) : tgtV L pd v = 10659 + 3 * L.U + L.S3.postS.val := by
  unfold tgtV
  rw [if_neg (by omega), if_pos h]

theorem tv2 (v : ℕ) (h : v = 6) : tgtV L pd v = 10045 + 3 * L.U := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_pos h]

theorem tv3 (v : ℕ) (h1 : 8 ≤ v) (h2 : v ≤ 17) : tgtV L pd v = 10038 + 3 * L.U + v := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tv4 (v : ℕ) (h : v = 76) : tgtV L pd v = 1 := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem tv5 (v : ℕ) (h1 : 73 ≤ v) (h2 : v ≤ 82) (h3 : v ≠ 76) : tgtV L pd v = 9983 + 3 * L.U + v := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tv6 (v : ℕ) (h : v = 83) : tgtV L pd v = 10613 + 3 * L.U := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem tv7 (v : ℕ) (h1 : 84 ≤ v) (h2 : v ≤ 89) : tgtV L pd v = 9982 + 3 * L.U + v := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tv8 (v : ℕ) (h : v = 199 + pd) : tgtV L pd v = 10072 + 3 * L.U := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem tv9 (v : ℕ) (h : v = 200 + pd) : tgtV L pd v = 10643 + 3 * L.U := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem tv10 (v : ℕ) (h : v = 410 + 2 * pd) : tgtV L pd v = 10659 + 3 * L.U + L.S3.t := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem tv11 (v : ℕ) (h : v = 411 + 2 * pd) : tgtV L pd v = 10655 + 3 * L.U := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

theorem tv12 (v : ℕ) (h : v = 412 + 2 * pd) : tgtV L pd v = 10073 + 3 * L.U := by
  unfold tgtV
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The targets, case by case. -/
theorem tgtV_spec (v : ℕ) (hv : isK pd v) :
    (v = 0 ∧ tgtV L pd v = 10659 + 3 * L.U + L.S3.preS.val) ∨
    (v = 2 ∧ tgtV L pd v = 10659 + 3 * L.U + L.S3.postS.val) ∨
    (v = 6 ∧ tgtV L pd v = 10045 + 3 * L.U) ∨
    (8 ≤ v ∧ v ≤ 17 ∧ tgtV L pd v = 10038 + 3 * L.U + v) ∨
    (v = 76 ∧ tgtV L pd v = 1) ∨
    (73 ≤ v ∧ v ≤ 82 ∧ v ≠ 76 ∧ tgtV L pd v = 9983 + 3 * L.U + v) ∨
    (v = 83 ∧ tgtV L pd v = 10613 + 3 * L.U) ∨
    (84 ≤ v ∧ v ≤ 89 ∧ tgtV L pd v = 9982 + 3 * L.U + v) ∨
    (v = 199 + pd ∧ tgtV L pd v = 10072 + 3 * L.U) ∨
    (v = 200 + pd ∧ tgtV L pd v = 10643 + 3 * L.U) ∨
    (v = 410 + 2 * pd ∧ tgtV L pd v = 10659 + 3 * L.U + L.S3.t) ∨
    (v = 411 + 2 * pd ∧ tgtV L pd v = 10655 + 3 * L.U) ∨
    (v = 412 + 2 * pd ∧ tgtV L pd v = 10073 + 3 * L.U) := by
  unfold isK at hv
  rcases hv with h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h | h | h | h | h
  · exact Or.inl ⟨h, tv0 L pd v h⟩
  · exact Or.inr <| Or.inl ⟨h, tv1 L pd v h⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨h, tv2 L pd v h⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h1, h2, tv3 L pd v h1 h2⟩
  · by_cases a : v = 76
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨a, tv4 L pd v a⟩
    · by_cases b : v ≤ 82
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h1, b, a, tv5 L pd v h1 b a⟩
      · by_cases c : v = 83
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨c, tv6 L pd v c⟩
        · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨by omega, h2, tv7 L pd v (by omega) h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h, tv8 L pd v h⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h, tv9 L pd v h⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h, tv10 L pd v h⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h, tv11 L pd v h⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨h, tv12 L pd v h⟩

theorem tgtV_lt (v : ℕ) (hv : isK pd v) : tgtV L pd v < L.oLP := by
  have := pre_lt L
  have := post_lt L
  have := tgtV_spec L pd v hv
  unfold Lay.oLP
  omega

theorem tgtV_port (v : ℕ) (hv : isK pd v) : tgtV L pd v ≠ 0 ∧ tgtV L pd v ≠ 2 := by
  have := tgtV_spec L pd v hv
  omega

theorem tgtV_inj (v w : ℕ) (hv : isK pd v) (hw : isK pd w) (h : tgtV L pd v = tgtV L pd w) : v = w := by
  have := pre_lt L
  have := post_lt L
  have := pre_ne_post L
  have := tgtV_spec L pd v hv
  have := tgtV_spec L pd w hw
  omega

theorem oLP_le : L.oLP ≤ L.N := by rw [Lay.N_eq]; unfold Lay.oLP; omega

/-- **The loop's slot table** on the SYM setup's bank (generic in the loop's tape count). -/
def symExt {n : ℕ} (j : Fin n) : Option (Fin L.N) :=
  if h : isK pd j.val then some ⟨tgtV L pd j.val, lt_of_lt_of_le (tgtV_lt L pd j.val h) (oLP_le L)⟩ else none

theorem symExt_some {n : ℕ} {j : Fin n} {g : Fin L.N} (h : symExt L pd j = some g) :
    isK pd j.val ∧ g.val = tgtV L pd j.val := by
  unfold symExt at h
  split_ifs at h with hk
  · exact ⟨hk, by rw [← Option.some.inj h]⟩

theorem symExt_isK {n : ℕ} {j : Fin n} (h : isK pd j.val) :
    symExt L pd j = some ⟨tgtV L pd j.val, lt_of_lt_of_le (tgtV_lt L pd j.val h) (oLP_le L)⟩ := by
  unfold symExt
  rw [dif_pos h]

theorem symExt_inj {n : ℕ} (i j : Fin n) (g : Fin L.N) (hi : symExt L pd i = some g) (hj : symExt L pd j = some g) :
    i = j := by
  obtain ⟨ki, ei⟩ := symExt_some L pd hi
  obtain ⟨kj, ej⟩ := symExt_some L pd hj
  exact Fin.ext (tgtV_inj L pd _ _ ki kj (ei.symm.trans ej))

theorem symExt_lt {n : ℕ} (i : Fin n) (g : Fin L.N) (hi : symExt L pd i = some g) : g.val < L.oLP := by
  obtain ⟨ki, ei⟩ := symExt_some L pd hi
  rw [ei]; exact tgtV_lt L pd _ ki

theorem symExt_port {n : ℕ} (i : Fin n) (g : Fin L.N) (hi : symExt L pd i = some g) : g.val ≠ 0 ∧ g.val ≠ 2 := by
  obtain ⟨ki, ei⟩ := symExt_some L pd hi
  rw [ei]; exact tgtV_port L pd _ ki

end Slots

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
