import Proof.Wire_3_5.UnionMachine.FrontKit

/-! # C6 front, U3: the restriction's capacity `1^cap` (the G3 entry)

The padded producer (`Transfer.CaseTwoPadG.osourceG_run`, G3) reads, besides the hierarchy word, the raw oracle
descriptor and `1^q`, a unary capacity `1^cap` with `64·(O.size + q + 4) + 1 ≤ cap`. This stage writes
`1^{64·(q + |x|)}` from the framed input `x` and `1^q`, on its own `22` tapes, with base parts only: the input length
as `CompareMachine.word |x|` (base `CloseoutSchedule.Metadata.length_run`), a copy of `1^q` (base
`ClockUnarySum.sum_ready q 0`), and base's fixed scaling (`CloseoutSchedule.Scale.scale_run 64 q |x|`). The capacity
suffices once `O.size + 5 ≤ |x|` (**`cap_enough`**; a decodable oracle of a `⌊N/16⌋`-bit witness has
`O.size ≤ ⌊N/16⌋ + 1`, `FrontSize.size_le_payload`).
Main statement: **`cap_ready`**. Paper quantity: the unary capacity of the restriction program. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCapStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutSchedule

/-! ## Layout: `0` input, `1` width; `2–8` the length count; `9–11` the copy; `12–21` the scaling (`20` its result)
-/

abbrev CT : ℕ := 22

/-- The capacity: `64·(q + |x|)`. -/
def capOf (x : List Bool) (q : ℕ) : ℕ := 64 * (q + x.length)

theorem cap_enough (x : List Bool) (q s : ℕ) (h : s + 5 ≤ x.length) : 64 * (s + q + 4) + 1 ≤ capOf x q := by
  unfold capOf; omega

def mtC (j : Fin 8) : Fin CT := ⟨if j.val = 0 then 0 else 1 + j.val, by have := j.isLt; simp only [CT]; split <;> omega⟩
def smC : Fin 4 → Fin CT := ![1, 9, 10, 11]
def scC (j : Fin 12) : Fin CT := ⟨if j.val = 0 then 10 else if j.val = 1 then 2 else 10 + j.val,
  by have := j.isLt; simp only [CT]; split_ifs <;> omega⟩

theorem mtC_inj : Function.Injective mtC := by
  intro a b h; have := congrArg Fin.val h; simp only [mtC] at this; apply Fin.ext; split_ifs at this <;> omega
theorem smC_inj : Function.Injective smC := by decide
theorem scC_inj : Function.Injective scC := by
  intro a b h; have := congrArg Fin.val h; simp only [scC] at this; apply Fin.ext; split_ifs at this <;> omega

theorem mtC_ne (i : Fin CT) (hi : i.val = 1 ∨ 9 ≤ i.val) : ∀ j, mtC j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; simp only [mtC] at e; split_ifs at e <;> omega
theorem smC_ne (i : Fin CT) (hi : i.val = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 8) ∨ 12 ≤ i.val) : ∀ j, smC j ≠ i := by
  intro j h; fin_cases j <;> simp [smC] at h <;> subst h <;> simp [CT] at hi
theorem scC_ne (i : Fin CT) (hi : i.val ≤ 1) : ∀ j, scC j ≠ i := by
  intro j h; have := j.isLt; have e := congrArg Fin.val h; simp only [scC] at e; split_ifs at e <;> omega

/-- **The capacity stage.** -/
noncomputable def capMachine :=
  Composition.machine (RecoveryFocus.machine mtC Metadata.lengthProgram)
  (Composition.machine (RecoveryFocus.machine smC ClockUnarySum.machine)
    (RecoveryFocus.machine scC (Scale.machine 64)))

def capIn (x : List Bool) (q : ℕ) : Fin CT → List Bool := fun i =>
  if i.val = 0 then frame x else if i.val = 1 then List.replicate q true else []

def capCost (x : List Bool) (q : ℕ) : ℕ :=
  (4 * x.length + 5) + 1 + ((2 * (q + 0) + 6) + 1 + Scale.budget 64 q x.length)

/-- **The capacity stage**: `1^{64·(q + |x|)}` on tape `20`; the input and the width kept. -/
theorem cap_ready (x : List Bool) (q : ℕ) :
    ∃ out : Fin CT → List Bool, ClockJoin.ReadyRun capMachine (capCost x q) (capIn x q) out ∧
      out 20 = List.replicate (capOf x q) true ∧ out 0 = frame x ∧ out 1 = List.replicate q true := by
  -- 1. `word |x|` on tape 2
  have g1 := (Metadata.length_run x).focus mtC mtC_inj (capIn x q) (by
    intro j; fin_cases j <;> simp [capIn, mtC, Metadata.input, CT])
  set a1 := install mtC (capIn x q) (Metadata.counted x) with ha1
  have a1_0 : a1 0 = frame x := by rw [ha1, show (0 : Fin CT) = mtC 0 from rfl, install_slot _ mtC_inj]; rfl
  have a1_2 : a1 2 = RepairSource.VerifierDecoding.CompareMachine.word x.length := by
    rw [ha1, show (2 : Fin CT) = mtC 1 from rfl, install_slot _ mtC_inj]; rfl
  have a1_1 : a1 1 = List.replicate q true := by
    rw [ha1, install_other _ _ _ _ (mtC_ne 1 (by decide))]; simp [capIn, CT]
  have a1_hi : ∀ i : Fin CT, 9 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (mtC_ne i (by omega))]
    unfold capIn; split_ifs <;> first | rfl | omega
  -- 2. a copy of `1^q` on tape 10
  have g2 := (ClockUnarySum.sum_ready q 0).focus smC smC_inj a1 (by
    intro j; fin_cases j
    · exact a1_1
    all_goals (simp [smC]; exact a1_hi _ (by decide)))
  set a2 := install smC a1 ![List.replicate q true, List.replicate 0 true, List.replicate (q + 0) true,
    List.replicate (q + 0 + 2) false] with ha2
  have a2_other : ∀ i : Fin CT, (i.val = 0 ∨ (2 ≤ i.val ∧ i.val ≤ 8) ∨ 12 ≤ i.val) → a2 i = a1 i := by
    intro i hi; rw [ha2, install_other _ _ _ _ (smC_ne i hi)]
  have a2_1 : a2 1 = List.replicate q true := by
    rw [ha2, show (1 : Fin CT) = smC 0 from rfl, install_slot _ smC_inj]; rfl
  have a2_10 : a2 10 = List.replicate q true := by
    rw [ha2, show (10 : Fin CT) = smC 2 from rfl, install_slot _ smC_inj]; simp
  -- 3. the scaling
  obtain ⟨o3, h3, h3o⟩ := Scale.scale_run 64 q x.length
  have g3 := h3.focus scC scC_inj a2 (by
    intro j; fin_cases j
    · exact a2_10
    · show a2 2 = _
      rw [a2_other _ (by decide), a1_2]; rfl
    all_goals (show a2 _ = _; rw [a2_other _ (by simp [scC])]; simp [Scale.input, scC]; exact a1_hi _ (by decide)))
  refine ⟨install scC a2 o3, ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2 g3), ?_, ?_, ?_⟩
  · rw [show (20 : Fin CT) = scC 10 from rfl, install_slot _ scC_inj, h3o]; rfl
  · rw [install_other _ _ _ _ (scC_ne 0 (by decide)), a2_other _ (by decide), a1_0]
  · rw [install_other _ _ _ _ (scC_ne 1 (by decide)), a2_1]

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCapStage
