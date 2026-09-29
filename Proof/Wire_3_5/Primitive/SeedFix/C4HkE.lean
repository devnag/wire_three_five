import Proof.Wire_3_5.Primitive.SeedFix.C4HkD

/-! # The HASH stage, part 5: the decision loop's dock on the HASH bank

"For each candidate child prefix [...] Choose a child with no larger value" (P3:2327-2336). The decision loop of the
HASH child family (C4H-a's `HashFamAt2`) is docked on the bank after the pre-loop stage: its kept tapes onto their
words (the compiler's fields on `gPRE`, `gPOST`; the Hb unit's 94 framed words on `hkT`; the prefix on `off + 1`;
`1^{Q'}` on `hqT`; the mask on `gUU`), its log, driver and counter onto `gLG`, `gRR` and `off + 2`, every other tape
onto the loop's cells at `off + 12` (`hashExt`).

* `gS`, `hashTgt`, `hashExt`, `tgt_cases`, `hashExt_some`, **`ext_inj`**, `ext_lt`, `ext_port`, `ext_pfx`.

Paper quantity of the main type: the loop's dock (its entry words' tapes). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.C4H

noncomputable section

section Ext
variable {x : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (A : C4Iface.AsmStage)
  (wa : RepairRepresentation.WilliamsAlgorithm) (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x)) (off : ℕ)
  (hr : off + 3 ≤ 3 + x)

/-- A layout tape on the big bank. -/
def gS (g : Fin L.N) : Fin (3 + x) := ⟨g.val, lt_of_lt_of_le g.isLt hLx⟩

/-- The kept tape `v`'s word. -/
def hashTgt (v : ℕ) : Fin (3 + x) :=
  if v < A.t then (if v = A.pA.val then gS L hLx L.gPRE else gS L hLx L.gPOST)
  else if h : v - A.t < 94 then hkT ⟨v - A.t, h⟩
  else if v - A.t = 94 then ⟨off + 1, by omega⟩
  else if v - A.t - HU = (C4Pipe.childQQ wa).val then hqT else gS L hLx L.gUU

/-- **The loop's dock**: the kept tapes onto their words, the log, driver and counter, every other tape `none`. -/
def hashExt (FT : ℕ) (j : Fin (FT + 1 + 1 + 1)) : Option (Fin (3 + x)) :=
  if j.val < CTH A wa ∧ hKeepN A wa j.val = true then some (hashTgt L hLx A wa hkT hqT off hr j.val)
  else if j.val = FT then some (gS L hLx L.gLG) else if j.val = FT + 1 then some (gS L hLx L.gRR)
  else if j.val = FT + 2 then some ⟨off + 2, by omega⟩ else none

theorem gS_val (g : Fin L.N) : (gS L hLx g).val = g.val := rfl

/-- The kept tapes and their words. -/
theorem tgt_cases (v : ℕ) (hv : v < CTH A wa) (hk : hKeepN A wa v = true) :
    (v = A.pA.val ∧ hashTgt L hLx A wa hkT hqT off hr v = gS L hLx L.gPRE) ∨
    (v = A.pB.val ∧ hashTgt L hLx A wa hkT hqT off hr v = gS L hLx L.gPOST) ∨
    (∃ h : v - A.t < 94, A.t ≤ v ∧ hashTgt L hLx A wa hkT hqT off hr v = hkT ⟨v - A.t, h⟩) ∨
    (v = A.t + 94 ∧ hashTgt L hLx A wa hkT hqT off hr v = ⟨off + 1, by omega⟩) ∨
    (A.t + HU ≤ v ∧ v - A.t - HU = (C4Pipe.childQQ wa).val ∧ hashTgt L hLx A wa hkT hqT off hr v = hqT) ∨
    (A.t + HU ≤ v ∧ v - A.t - HU = (C4Pipe.childUU wa).val ∧ hashTgt L hLx A wa hkT hqT off hr v = gS L hLx L.gUU) := by
  unfold hKeepN at hk
  unfold hashTgt
  have hQU : (C4Pipe.childQQ wa).val ≠ (C4Pipe.childUU wa).val := by
    simp [C4Pipe.childQQ, C4Pipe.childUU]
  by_cases h1 : v < A.t
  · rw [if_pos h1] at hk ⊢
    simp only [decide_eq_true_eq] at hk
    rcases hk with e | e
    · exact Or.inl ⟨e, by rw [if_pos e]⟩
    · have : v ≠ A.pA.val := fun e' => A.hAB (Fin.ext (e'.symm.trans e))
      exact Or.inr (Or.inl ⟨e, by rw [if_neg this]⟩)
  · rw [if_neg h1] at hk ⊢
    by_cases h2 : v < A.t + HU
    · rw [if_pos h2] at hk
      simp only [decide_eq_true_eq] at hk
      by_cases h3 : v - A.t < 94
      · exact Or.inr (Or.inr (Or.inl ⟨h3, by omega, by rw [dif_pos h3]⟩))
      · have h4 : v - A.t = 94 := by omega
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by rw [dif_neg h3, if_pos h4]⟩)))
    · rw [if_neg h2, if_pos hv] at hk
      simp only [decide_eq_true_eq] at hk
      have hU : HU = 253 := rfl
      have h3 : ¬ v - A.t < 94 := by omega
      have h4 : v - A.t ≠ 94 := by omega
      rw [dif_neg h3, if_neg h4]
      rcases hk with e | e
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, e, by rw [if_pos e]⟩))))
      · have : v - A.t - HU ≠ (C4Pipe.childQQ wa).val := fun e' => hQU (e'.symm.trans e)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, e, by rw [if_neg this]⟩))))

theorem hashExt_some (FT : ℕ) {j : Fin (FT + 1 + 1 + 1)} {g : Fin (3 + x)}
    (h : hashExt L hLx A wa hkT hqT off hr FT j = some g) :
    (j.val < CTH A wa ∧ hKeepN A wa j.val = true ∧ g = hashTgt L hLx A wa hkT hqT off hr j.val) ∨
    (j.val = FT ∧ g = gS L hLx L.gLG) ∨ (j.val = FT + 1 ∧ g = gS L hLx L.gRR) ∨
    (j.val = FT + 2 ∧ g.val = off + 2) := by
  unfold hashExt at h
  split_ifs at h with h1 h2 h3 h4 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp_all

/-- The layout's words below its tape count, the kept words from it up to `off`. -/
theorem tgt_range (hB : ∀ j, L.N ≤ (hkT j).val ∧ (hkT j).val < off) (hQ : L.N ≤ hqT.val ∧ hqT.val < off)
    (v : ℕ) (hv : v < CTH A wa) (hk : hKeepN A wa v = true) :
    (hashTgt L hLx A wa hkT hqT off hr v).val < off + 2 ∧ 3 ≤ (hashTgt L hLx A wa hkT hqT off hr v).val := by
  have hN := C4Set.Lay.N_eq L
  have hpre := L.S3.preS.isLt
  have hpost := L.S3.postS.isLt
  rcases tgt_cases L hLx A wa hkT hqT off hr v hv hk with ⟨_, e⟩ | ⟨_, e⟩ | ⟨h, _, e⟩ | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
    rw [e]
  · simp only [gS_val, C4Set.Lay.gPRE]; have := (hB ⟨0, by omega⟩).2; omega
  · simp only [gS_val, C4Set.Lay.gPOST]; have := (hB ⟨0, by omega⟩).2; omega
  · have := hB ⟨v - A.t, h⟩; omega
  · simp only; have := (hB ⟨0, by omega⟩).1; omega
  · omega
  · simp only [gS_val, C4Set.Lay.gUU]; have := (hB ⟨0, by omega⟩).2; omega

end Ext

end

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
