import Proof.Wire_3_5.Primitive.SeedFix.C4KWd

/-! # C4KW, part 12 (C): the kept words writer from its four stages

**`kwwOf b1 b2 b3 b4 : KWW`**: the four stages docked in sequence on the writer's bank (outputs `0 … 93`, inputs
`94 … 105`, scratch from `106`). Stage `p` is docked by `slP oS iS off` (its outputs onto the writer's outputs `oS j`,
its inputs onto `94 + iS i`, its scratch onto `106 + off + k`, the offsets `0, x₁, x₁ + x₂, x₁ + x₂ + x₃`). The
invariant `View W S` (the kept words `W` written framed, the others blank, the inputs kept, the scratch below `S`
falses, above blank) is carried by **`part_dock`**; B1–B4 cover all 94 kept words (`cover`). The cost is the sum of
the stages' costs plus the three bridge steps.

Paper quantity of the main type: the Hb printer's static words before cell `0` (P3:2253-2290), framed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.Cmp
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

noncomputable section

variable {X : ℕ}

/-- The writer's output tape `j`, input tape `i`, scratch tape `k`. -/
def outT (j : Fin 94) : Fin (94 + 12 + X) := Fin.castAdd X (Fin.castAdd 12 j)
def inT (i : Fin 12) : Fin (94 + 12 + X) := Fin.castAdd X (Fin.natAdd 94 i)
def scT (k : Fin X) : Fin (94 + 12 + X) := Fin.natAdd (94 + 12) k

@[simp] theorem outT_val (j : Fin 94) : (outT (X := X) j).val = j.val := rfl
@[simp] theorem inT_val (i : Fin 12) : (inT (X := X) i).val = 94 + i.val := rfl
@[simp] theorem scT_val (k : Fin X) : (scT k).val = 106 + k.val := rfl

/-- The slot value of a stage's tape `c`. -/
def slV {no ni x : ℕ} (oS : Fin no → Fin 94) (iS : Fin ni → Fin 12) (off : ℕ) (c : Fin (no + ni + x)) : ℕ :=
  if h : c.val < no then (oS ⟨c.val, h⟩).val
  else if h2 : c.val < no + ni then 94 + (iS ⟨c.val - no, by omega⟩).val
  else 106 + off + (c.val - no - ni)

/-- **A stage's slot map** on the writer's bank. -/
def slP {no ni x : ℕ} (oS : Fin no → Fin 94) (iS : Fin ni → Fin 12) (off : ℕ) (hx : off + x ≤ X)
    (c : Fin (no + ni + x)) : Fin (94 + 12 + X) :=
  ⟨slV oS iS off c, by
    have := c.isLt
    unfold slV
    split_ifs with h1 h2
    · have := (oS ⟨c.val, h1⟩).isLt; omega
    · have := (iS ⟨c.val - no, by omega⟩).isLt; omega
    · omega⟩

section Slots
variable {no ni x : ℕ} (oS : Fin no → Fin 94) (iS : Fin ni → Fin 12) (off : ℕ) (hx : off + x ≤ X)

theorem slP_out (a : Fin no) : slP oS iS off hx (Fin.castAdd x (Fin.castAdd ni a)) = outT (oS a) := by
  apply Fin.ext
  show slV oS iS off _ = _
  unfold slV
  rw [dif_pos (by simp)]
  rfl

theorem slP_in (a : Fin ni) : slP oS iS off hx (Fin.castAdd x (Fin.natAdd no a)) = inT (iS a) := by
  apply Fin.ext
  show slV oS iS off _ = _
  unfold slV
  rw [dif_neg (by simp), dif_pos (by simp)]
  simp only [inT_val]
  congr 3
  apply Fin.ext; simp

theorem slP_scr (k : Fin x) : slP oS iS off hx (Fin.natAdd (no + ni) k) = scT ⟨off + k.val, by omega⟩ := by
  apply Fin.ext
  show slV oS iS off _ = _
  unfold slV
  rw [dif_neg (by simp only [Fin.val_natAdd]; omega), dif_neg (by simp only [Fin.val_natAdd]; omega)]
  simp only [scT_val, Fin.val_natAdd]
  omega

theorem slP_inj (ho : Function.Injective oS) (hi : Function.Injective iS) : Function.Injective (slP oS iS off hx) := by
  intro a b h
  have hv : slV oS iS off a = slV oS iS off b := congrArg Fin.val h
  have ha := a.isLt; have hb := b.isLt
  apply Fin.ext
  unfold slV at hv
  by_cases h1 : a.val < no
  · rw [dif_pos h1] at hv
    have hoa := (oS ⟨a.val, h1⟩).isLt
    by_cases h2 : b.val < no
    · rw [dif_pos h2] at hv
      have := ho (Fin.ext hv); simp only [Fin.mk.injEq] at this; exact this
    · rw [dif_neg h2] at hv
      split_ifs at hv <;> omega
  · rw [dif_neg h1] at hv
    by_cases h1' : a.val < no + ni
    · rw [dif_pos h1'] at hv
      by_cases h2 : b.val < no
      · rw [dif_pos h2] at hv; have := (oS ⟨b.val, h2⟩).isLt; omega
      · rw [dif_neg h2] at hv
        by_cases h2' : b.val < no + ni
        · rw [dif_pos h2'] at hv
          have := hi (Fin.ext (Nat.add_left_cancel hv)); simp only [Fin.mk.injEq] at this; omega
        · rw [dif_neg h2'] at hv; have := (iS ⟨a.val - no, by omega⟩).isLt; omega
    · rw [dif_neg h1'] at hv
      by_cases h2 : b.val < no
      · rw [dif_pos h2] at hv; have := (oS ⟨b.val, h2⟩).isLt; omega
      · rw [dif_neg h2] at hv
        by_cases h2' : b.val < no + ni
        · rw [dif_pos h2'] at hv; have := (iS ⟨b.val - no, by omega⟩).isLt; omega
        · rw [dif_neg h2'] at hv; omega

theorem slP_ne_out (j : Fin 94) (h : ∀ a, oS a ≠ j) (c : Fin (no + ni + x)) : slP oS iS off hx c ≠ outT j := by
  intro e
  have hv : slV oS iS off c = j.val := congrArg Fin.val e
  have := j.isLt
  unfold slV at hv
  split_ifs at hv with h1 h2
  · exact h _ (Fin.ext hv)
  · omega
  · omega

theorem slP_ne_in (i : Fin 12) (h : ∀ a, iS a ≠ i) (c : Fin (no + ni + x)) : slP oS iS off hx c ≠ inT i := by
  intro e
  have hv : slV oS iS off c = 94 + i.val := congrArg Fin.val e
  have := i.isLt
  unfold slV at hv
  split_ifs at hv with h1 h2
  · have := (oS ⟨c.val, h1⟩).isLt; omega
  · exact h ⟨c.val - no, by omega⟩ (Fin.ext (by omega))
  · omega

theorem slP_ne_scr (k : Fin X) (h : k.val < off ∨ off + x ≤ k.val) (c : Fin (no + ni + x)) :
    slP oS iS off hx c ≠ scT k := by
  intro e
  have hv : slV oS iS off c = 106 + k.val := congrArg Fin.val e
  have := c.isLt
  unfold slV at hv
  split_ifs at hv with h1 h2
  · have := (oS ⟨c.val, h1⟩).isLt; omega
  · have := (iS ⟨c.val - no, by omega⟩).isLt; omega
  · omega

end Slots

/-- **The writer's bank after some stages**: the kept words `W` framed, the others blank, the inputs kept, the scratch
below `S` falses (within `C`), above it blank. -/
structure View (D : HashData) (cap C : ℕ) (W : Fin 94 → Prop) (S : ℕ) (A : Fin (94 + 12 + X) → List Bool) : Prop where
  wr : ∀ j, W j → A (outT j) = frame (kw D cap j)
  bl : ∀ j, ¬ W j → A (outT j) = []
  inp : ∀ i, A (inT i) = kwIns D cap i
  sd : ∀ k : Fin X, k.val < S → ∃ m ≤ C, A (scT k) = List.replicate m false
  sb : ∀ k : Fin X, S ≤ k.val → A (scT k) = []

/-- **One stage docked on the writer's bank.** -/
theorem part_dock {no ni : ℕ} {oS : Fin no → Fin 94} {iS : Fin ni → Fin 12} (P : KWPart oS iS)
    (ho : Function.Injective oS) (hi : Function.Injective iS) (off : ℕ) (hx : off + P.x ≤ X)
    (D : HashData) (cap C : ℕ) (hC : P.cost D cap ≤ C) (W : Fin 94 → Prop) (A : Fin (94 + 12 + X) → List Bool)
    (hV : View D cap C W off A) (hW : ∀ a, ¬ W (oS a)) (S' : ℕ) (hS : off + P.x = S') :
    ∃ B : Fin (94 + 12 + X) → List Bool,
      Step (RecoveryFocus.machine (slP oS iS off hx) P.M) (P.cost D cap) (fun _ => 0) A (fun _ => 0) B ∧
      View D cap C (fun j => W j ∨ ∃ a, oS a = j) S' B := by
  subst hS
  classical
  obtain ⟨Bl, hs, hout, hinp, hscr⟩ := P.run D cap
  have hinj := slP_inj oS iS off hx ho hi
  have hentry : ∀ c, A (slP oS iS off hx c) = partIn (no := no) iS P.x D cap c := by
    intro c
    induction c using Fin.addCases with
    | left c' =>
      induction c' using Fin.addCases with
      | left a =>
        rw [slP_out, hV.bl _ (hW a), partIn_val, dif_neg (by simp)]
      | right a =>
        rw [slP_in, hV.inp, partIn_val, dif_pos (by simp)]
        congr 2; apply Fin.ext; simp
    | right k =>
      rw [slP_scr, hV.sb _ (by simp), partIn_val, dif_neg (by simp)]
  have hd := Block.dockKeep hs (slP oS iS off hx) hinj (fun _ => 0) A (fun _ => rfl) hentry
  refine ⟨install (slP oS iS off hx) A Bl, hd, ⟨fun j hj => ?_, fun j hj => ?_, fun i => ?_, fun k hk => ?_,
    fun k hk => ?_⟩⟩
  · by_cases hj2 : ∃ a, oS a = j
    · obtain ⟨a, rfl⟩ := hj2
      rw [← slP_out oS iS off hx a, install_slot _ hinj, hout a]
    · have hj1 : W j := by rcases hj with h | h; exact h; exact absurd h hj2
      rw [install_other _ _ _ _ (slP_ne_out oS iS off hx j (fun a e => hj2 ⟨a, e⟩)), hV.wr j hj1]
  · have hj1 : ¬ W j := fun h => hj (Or.inl h)
    have hj2 : ∀ a, oS a ≠ j := fun a e => hj (Or.inr ⟨a, e⟩)
    rw [install_other _ _ _ _ (slP_ne_out oS iS off hx j hj2), hV.bl j hj1]
  · by_cases hi2 : ∃ a, iS a = i
    · obtain ⟨a, rfl⟩ := hi2
      rw [← slP_in oS iS off hx a, install_slot _ hinj, hinp a]
    · rw [install_other _ _ _ _ (slP_ne_in oS iS off hx i (fun a e => hi2 ⟨a, e⟩)), hV.inp i]
  · by_cases hk2 : k.val < off
    · rw [install_other _ _ _ _ (slP_ne_scr oS iS off hx k (Or.inl hk2))]; exact hV.sd k hk2
    · have e : k = ⟨off + (k.val - off), by omega⟩ := Fin.ext (by simp; omega)
      have e2 := slP_scr oS iS off hx (⟨k.val - off, by omega⟩ : Fin P.x)
      rw [e, ← e2, install_slot _ hinj]
      obtain ⟨m, hm, hB⟩ := hscr ⟨k.val - off, by omega⟩
      exact ⟨m, hm.trans hC, hB⟩
  · rw [install_other _ _ _ _ (slP_ne_scr oS iS off hx k (Or.inr hk))]; exact hV.sb k (by omega)

/-! ## The four stages -/

theorem oB1_inj : Function.Injective oB1 := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [oB1] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem oB2_inj : Function.Injective oB2 := fun a b _ => Subsingleton.elim a b
theorem oB3_inj : Function.Injective oB3 := fun a b _ => Subsingleton.elim a b
theorem oB4_inj : Function.Injective oB4 := by decide
theorem iB1_inj : Function.Injective iB1 := by decide
theorem iB2_inj : Function.Injective iB2 := by decide
theorem iB3_inj : Function.Injective iB3 := by decide
theorem iB4_inj : Function.Injective iB4 := by decide

theorem oB1_ne (a : Fin 90) : (oB1 a).val ≠ 3 ∧ (oB1 a).val ≠ 4 ∧ (oB1 a).val ≠ 5 ∧ (oB1 a).val ≠ 71 := by
  have := a.isLt
  simp only [oB1]
  split_ifs <;> omega

/-- **The four stages cover the 94 kept words.** -/
theorem cover (j : Fin 94) :
    (((False ∨ ∃ a, oB1 a = j) ∨ ∃ a, oB2 a = j) ∨ ∃ a, oB3 a = j) ∨ ∃ a, oB4 a = j := by
  have hj := j.isLt
  by_cases h3 : j.val = 3
  · exact Or.inr ⟨0, Fin.ext (by rw [h3]; rfl)⟩
  by_cases h4 : j.val = 4
  · exact Or.inr ⟨1, Fin.ext (by rw [h4]; rfl)⟩
  by_cases h5 : j.val = 5
  · exact Or.inl (Or.inl (Or.inr ⟨0, Fin.ext (by rw [h5]; rfl)⟩))
  by_cases h71 : j.val = 71
  · exact Or.inl (Or.inr ⟨0, Fin.ext (by rw [h71]; rfl)⟩)
  refine Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨if j.val < 3 then j.val else if j.val < 71 then j.val - 3 else j.val - 4,
    by split_ifs <;> omega⟩, Fin.ext ?_⟩)))
  simp only [oB1]
  split_ifs <;> omega

/-- The writer's cost from its stages' costs. -/
def kwCost (b1 : PartB1) (b2 : PartB2) (b3 : PartB3) (b4 : PartB4) (D : HashData) (cap : ℕ) : ℕ :=
  b1.cost D cap + 1 + b2.cost D cap + 1 + b3.cost D cap + 1 + b4.cost D cap

theorem kwCost_le (b1 : PartB1) (b2 : PartB2) (b3 : PartB3) (b4 : PartB4) (D : HashData) (cap : ℕ) :
    kwCost b1 b2 b3 b4 D cap ≤ (b1.K + b2.K + b3.K + b4.K + 3) * (kwS D cap + 1) ^ 2 +
      (b1.K + b2.K + b3.K + b4.K + 3) * (kwT D + 1) ^ (max (max b1.Dg b2.Dg) (max b3.Dg b4.Dg)) := by
  set G := max (max b1.Dg b2.Dg) (max b3.Dg b4.Dg) with hG
  have hp : ∀ d, d ≤ G → (kwT D + 1) ^ d ≤ (kwT D + 1) ^ G := fun d hd => Nat.pow_le_pow_right (by omega) hd
  have h1 := b1.cost_le D cap; have h2 := b2.cost_le D cap; have h3 := b3.cost_le D cap; have h4 := b4.cost_le D cap
  have q1 := Nat.mul_le_mul_left b1.K (hp b1.Dg (by omega))
  have q2 := Nat.mul_le_mul_left b2.K (hp b2.Dg (by omega))
  have q3 := Nat.mul_le_mul_left b3.K (hp b3.Dg (by omega))
  have q4 := Nat.mul_le_mul_left b4.K (hp b4.Dg (by omega))
  have hs : 1 ≤ (kwS D cap + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e1 : (b1.K + b2.K + b3.K + b4.K + 3) * (kwS D cap + 1) ^ 2 = b1.K * (kwS D cap + 1) ^ 2 +
      b2.K * (kwS D cap + 1) ^ 2 + b3.K * (kwS D cap + 1) ^ 2 + b4.K * (kwS D cap + 1) ^ 2 + 3 * (kwS D cap + 1) ^ 2 := by
    ring
  have e2 : (b1.K + b2.K + b3.K + b4.K + 3) * (kwT D + 1) ^ G = b1.K * (kwT D + 1) ^ G + b2.K * (kwT D + 1) ^ G +
      b3.K * (kwT D + 1) ^ G + b4.K * (kwT D + 1) ^ G + 3 * (kwT D + 1) ^ G := by ring
  unfold kwCost
  rw [e1, e2]
  omega

/-- **The kept words writer from its four stages** (C). -/
def kwwOf (b1 : PartB1) (b2 : PartB2) (b3 : PartB3) (b4 : PartB4) : KWW where
  x := b1.x + b2.x + b3.x + b4.x
  s := _
  M := Composition.machine (Composition.machine (Composition.machine
      (RecoveryFocus.machine (slP (X := b1.x + b2.x + b3.x + b4.x) oB1 iB1 0 (by omega)) b1.M)
      (RecoveryFocus.machine (slP (X := b1.x + b2.x + b3.x + b4.x) oB2 iB2 b1.x (by omega)) b2.M))
      (RecoveryFocus.machine (slP (X := b1.x + b2.x + b3.x + b4.x) oB3 iB3 (b1.x + b2.x) (by omega)) b3.M))
      (RecoveryFocus.machine (slP (X := b1.x + b2.x + b3.x + b4.x) oB4 iB4 (b1.x + b2.x + b3.x) (by omega)) b4.M)
  cost := kwCost b1 b2 b3 b4
  K := b1.K + b2.K + b3.K + b4.K + 3
  Dg := max (max b1.Dg b2.Dg) (max b3.Dg b4.Dg)
  cost_le := kwCost_le b1 b2 b3 b4
  run := fun D cap => by
    have v0 : View (X := b1.x + b2.x + b3.x + b4.x) D cap (kwCost b1 b2 b3 b4 D cap) (fun _ => False) 0
        (partIn (no := 94) (id : Fin 12 → Fin 12) (b1.x + b2.x + b3.x + b4.x) D cap) := by
      refine ⟨fun j h => h.elim, fun j _ => ?_, fun i => ?_, fun k hk => absurd hk (by omega), fun k _ => ?_⟩
      · show partIn (no := 94) id _ D cap (outT j) = []
        have := j.isLt
        rw [partIn_val, dif_neg (by simp only [outT_val]; omega)]
      · show partIn (no := 94) id _ D cap (inT i) = _
        have := i.isLt
        rw [partIn_val, dif_pos (by simp only [inT_val]; omega)]
        congr 1; apply Fin.ext; simp
      · show partIn (no := 94) id _ D cap (scT k) = []
        rw [partIn_val, dif_neg (by simp only [scT_val]; omega)]
    have c1 : b1.cost D cap ≤ kwCost b1 b2 b3 b4 D cap := by unfold kwCost; omega
    have c2 : b2.cost D cap ≤ kwCost b1 b2 b3 b4 D cap := by unfold kwCost; omega
    have c3 : b3.cost D cap ≤ kwCost b1 b2 b3 b4 D cap := by unfold kwCost; omega
    have c4 : b4.cost D cap ≤ kwCost b1 b2 b3 b4 D cap := by unfold kwCost; omega
    obtain ⟨A1, s1, v1⟩ := part_dock b1 oB1_inj iB1_inj 0 (by omega) D cap _ c1 (fun _ => False) _ v0
      (fun _ h => h) b1.x (by omega)
    obtain ⟨A2, s2, v2⟩ := part_dock b2 oB2_inj iB2_inj b1.x (by omega) D cap _ c2
      (fun j => False ∨ ∃ a, oB1 a = j) _ v1
      (fun a h => by
        rcases h with h | ⟨a', e⟩
        · exact h
        · have := (oB1_ne a').2.2.1; rw [e] at this; exact this (by fin_cases a; rfl))
      (b1.x + b2.x) rfl
    obtain ⟨A3, s3, v3⟩ := part_dock b3 oB3_inj iB3_inj (b1.x + b2.x) (by omega) D cap _ c3
      (fun j => (False ∨ ∃ a, oB1 a = j) ∨ ∃ a, oB2 a = j) _ v2
      (fun a h => by
        rcases h with (h | ⟨a', e⟩) | ⟨a', e⟩
        · exact h
        · have := (oB1_ne a').2.2.2; rw [e] at this; exact this (by fin_cases a; rfl)
        · fin_cases a; fin_cases a'; exact absurd (congrArg Fin.val e) (by decide))
      (b1.x + b2.x + b3.x) rfl
    obtain ⟨A4, s4, v4⟩ := part_dock b4 oB4_inj iB4_inj (b1.x + b2.x + b3.x) (by omega) D cap _ c4
      (fun j => ((False ∨ ∃ a, oB1 a = j) ∨ ∃ a, oB2 a = j) ∨ ∃ a, oB3 a = j) _ v3
      (fun a h => by
        rcases h with ((h | ⟨a', e⟩) | ⟨a', e⟩) | ⟨a', e⟩
        · exact h
        · have h1 := oB1_ne a'; rw [e] at h1; fin_cases a
          · exact h1.1 rfl
          · exact h1.2.1 rfl
        · fin_cases a <;> fin_cases a' <;> exact absurd (congrArg Fin.val e) (by decide)
        · fin_cases a <;> fin_cases a' <;> exact absurd (congrArg Fin.val e) (by decide))
      (b1.x + b2.x + b3.x + b4.x) rfl
    exact ⟨A4, Step.seq (Step.seq (Step.seq s1 s2) s3) s4, fun j => v4.wr j (cover j), fun i => v4.inp i,
      fun k => v4.sd k k.isLt⟩

end

end NearCubicWires.WireExponent3_5.PrimT.C4KW.Cmp
