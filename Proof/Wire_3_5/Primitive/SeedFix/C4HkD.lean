import Proof.Wire_3_5.Primitive.SeedFix.C4HkC

/-! # The HASH stage, part 4: the pre-loop stage on the setup's exit bank

P3:3011-3016 (the words the processor writes before the loop). On the HASH setup's exit bank (C4H-a's `HBank2` at
the region offset `off`), the pre-loop stage runs the writer `preW` docked on the request's port, the Hb bank's
ruler `frame 1^L` and `frame 1^{T2}` (two of the kept words), and three blank tapes `off`, `off + 1`, `off + 2`
(the request's copy, the prefix `[false]`, the counter `false :: 1^m`, `L = T2 + m`), then base's `SelectedErase` from
the driver `1^R` (`R = 2^ρ`) filling the loop's cells `[off + 12, off + 12 + n)` with `R` falses (its log `off + 11`).
**`pre_run`**: the bank after both (`PreBank`): the tapes below `off` unchanged, the three words, the cells, blank above.

* `hb0_ruler`, `hb0_two`, `preM`, `preExt`, `eMask`, `preZ`, `PreBank`, **`pre_run`**.

Paper quantity of the main type: the loop's entry words written before the loop. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4Set (slx stageE eraseS)

/-- The Hb bank's ruler `1^L` is its kept word `23` (stream `22`). -/
theorem hb0_ruler (X : HbM.HbX) : C4H.hb0 X ⟨23, by omega⟩ = List.replicate X.L true := by
  unfold C4H.hb0
  rw [HbM.hbBank_lt _ _ _ _ 23 (by omega)]
  rfl

/-- The Hb bank's `1^{T2}` is its kept word `16` (stream `15`). -/
theorem hb0_two (X : HbM.HbX) : C4H.hb0 X ⟨16, by omega⟩ = List.replicate X.T2 true := by
  unfold C4H.hb0
  rw [HbM.hbBank_lt _ _ _ _ 16 (by omega)]
  rfl

/-- The writer's machine: its compiled program under base's masked reset (`8` tapes). -/
noncomputable def preM := MaskedReset.machine (preW.toProg.compile) (fun _ => true)

section Pre
variable {x : ℕ} (off : ℕ) (hr : off + 12 ≤ 3 + x) (hkT : Fin 94 → Fin (3 + x))

/-- The writer's dock: the request's port, the copy, the ruler, `1^{T2}`, the prefix, the counter. -/
def preExt (j : Fin (5 + 2 + 0 + 1)) : Option (Fin (3 + x)) :=
  if j.val = 0 then some ⟨0, by omega⟩ else if j.val = 2 then some ⟨off, by omega⟩
  else if j.val = 3 then some (hkT ⟨23, by omega⟩) else if j.val = 4 then some (hkT ⟨16, by omega⟩)
  else if j.val = 5 then some ⟨off + 1, by omega⟩ else if j.val = 6 then some ⟨off + 2, by omega⟩ else none

/-- The loop's cells `[off + 12, off + 12 + n)`. -/
def eMask (n : ℕ) (i : Fin (3 + x)) : Bool := decide (off + 12 ≤ i.val ∧ i.val < off + 12 + n)

/-- **The pre-loop stage**: the docked writer, then the cells' erase (driver `drv`, log `off + 11`). -/
noncomputable def preZ (n : ℕ) (drv : Fin (3 + x)) :=
  Composition.machine (RecoveryFocus.machine (slx (off + 3) (by omega) (preExt off hr hkT)) preM)
    (CloseoutWitness.SelectedErase.machine (eMask off n) drv ⟨off + 11, by omega⟩)

/-- **The bank after the pre-loop stage.** -/
structure PreBank (n : ℕ) (hn : off + 12 + n ≤ 3 + x) (B B2 : Fin (3 + x) → List Bool) (w : List Bool)
    (m R : ℕ) : Prop where
  keep : ∀ i : Fin (3 + x), i.val < off → i.val ≠ 0 → B2 i = B i
  p0 : B2 ⟨0, by omega⟩ = frame w
  wT : B2 ⟨off, by omega⟩ = frame w
  pT : B2 ⟨off + 1, by omega⟩ = [false]
  cT : B2 ⟨off + 2, by omega⟩ = false :: List.replicate m true
  cells : ∀ i : Fin (3 + x), off + 12 ≤ i.val → i.val < off + 12 + n → B2 i = List.replicate R false
  blank : ∀ i : Fin (3 + x), off + 12 + n ≤ i.val → B2 i = []

omit hr in
theorem preExt_some {hr : off + 12 ≤ 3 + x} {j : Fin (5 + 2 + 0 + 1)} {g : Fin (3 + x)}
    (h : preExt off hr hkT j = some g) :
    (j.val = 0 ∧ g.val = 0) ∨ (j.val = 2 ∧ g.val = off) ∨ (j.val = 3 ∧ g = hkT ⟨23, by omega⟩) ∨
      (j.val = 4 ∧ g = hkT ⟨16, by omega⟩) ∨ (j.val = 5 ∧ g.val = off + 1) ∨ (j.val = 6 ∧ g.val = off + 2) := by
  unfold preExt at h
  split_ifs at h with h0 h2 h3 h4 h5 h6 <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp_all

/-- **The pre-loop stage's run.** -/
theorem pre_run (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (B : Fin (3 + x) → List Bool) (w v PRE POST : List Bool)
    (KW : Fin 94 → List Bool) (q uu ρ : ℕ) (hqT : Fin (3 + x))
    (hB : C4H.HBank2 L hLx B w v PRE POST KW q uu ρ hkT hqT off) (T2 m : ℕ)
    (hKL : KW ⟨23, by omega⟩ = List.replicate (T2 + m) true) (hKT : KW ⟨16, by omega⟩ = List.replicate T2 true)
    (n : ℕ) (hn : off + 12 + n ≤ 3 + x) :
    ∃ B2 : Fin (3 + x) → List Bool,
      Step (preZ off hr hkT n ⟨L.gRR.val, by omega⟩) (2 * preCost w T2 m + 2 + 1 + (2 * 2 ^ ρ + 4)) (fun _ => 0) B
        (fun _ => 0) B2 ∧ PreBank off hr n hn B B2 w m (2 ^ ρ) := by
  obtain ⟨τ, hw, e0, e1, e2, e3, e4, e5⟩ := preW_spec w T2 m
  obtain ⟨A', st, hA⟩ := C4Pipe.wm_blank 0 (preCost w T2 m) preW (preSt w (T2 + m) T2) τ _ hw
    (fun _ => rfl) (fun r => Fin.elim0 r) rfl le_rfl
  have hLN : 3 ≤ L.N := by rw [C4Set.Lay.N_eq]; omega
  have hk23 := (hB.koff ⟨23, by omega⟩)
  have hk16 := (hB.koff ⟨16, by omega⟩)
  have h2316 : hkT ⟨23, by omega⟩ ≠ hkT ⟨16, by omega⟩ := fun e => by
    have := hB.kinj e; simp at this
  obtain ⟨B1, s1, bl1, un1, pv1, ex1⟩ := stageE st (off + 3) (by omega) (preExt off hr hkT)
    (fun i j g hi hj => by
      rcases preExt_some off hkT hi with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      rcases preExt_some off hkT hj with ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ | ⟨c, d⟩ <;>
      first
        | exact Fin.ext (by omega)
        | (exfalso; subst_vars; simp_all [Fin.ext_iff]; omega)
        | (exfalso; subst_vars; exact h2316 rfl)
        | (exfalso; subst_vars; exact h2316 (by simpa using b.symm.trans d))
        | skip)
    (fun i g hi => by
      rcases preExt_some off hkT hi with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
      first | omega | (subst b; omega))
    B
    (fun j g hj => by
      rcases preExt_some off hkT hj with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · have ej : j = ⟨0, by decide⟩ := Fin.ext a
        subst ej
        rw [show g = ⟨0, by omega⟩ from Fin.ext b, hB.p0]; rfl
      · have ej : j = ⟨2, by decide⟩ := Fin.ext a
        subst ej
        rw [hB.blank g (by omega)]; rfl
      · have ej : j = ⟨3, by decide⟩ := Fin.ext a
        subst ej b
        rw [hB.hKW, hKL]; rfl
      · have ej : j = ⟨4, by decide⟩ := Fin.ext a
        subst ej b
        rw [hB.hKW, hKT]; rfl
      · have ej : j = ⟨5, by decide⟩ := Fin.ext a
        subst ej
        rw [hB.blank g (by omega)]; rfl
      · have ej : j = ⟨6, by decide⟩ := Fin.ext a
        subst ej
        rw [hB.blank g (by omega)]; rfl)
    (fun i hi => hB.blank i (by omega))
    (fun j hj => by
      unfold preExt at hj
      split_ifs at hj with h0 h2 h3 h4 h5 h6
      fin_cases j <;> simp_all <;> rfl)
  -- the writer's outputs
  have o0 : B1 ⟨0, by omega⟩ = frame w := by
    rw [ex1 ⟨0, by omega⟩ _ (by simp [preExt])]; have := hA 0; rw [e0] at this; exact this
  have oW : B1 ⟨off, by omega⟩ = frame w := by
    rw [ex1 ⟨2, by omega⟩ _ (by simp [preExt])]; have := hA 1; rw [e1] at this; exact this
  have oP : B1 ⟨off + 1, by omega⟩ = [false] := by
    rw [ex1 ⟨5, by omega⟩ _ (by simp [preExt])]; have := hA 4; rw [e4] at this; exact this
  have oC : B1 ⟨off + 2, by omega⟩ = false :: List.replicate m true := by
    rw [ex1 ⟨6, by omega⟩ _ (by simp [preExt])]; have := hA 5; rw [e5] at this; exact this
  have o23 : B1 (hkT ⟨23, by omega⟩) = B (hkT ⟨23, by omega⟩) := by
    rw [ex1 ⟨3, by omega⟩ _ (by simp [preExt]), hB.hKW, hKL]; have := hA 2; rw [e2] at this; exact this
  have o16 : B1 (hkT ⟨16, by omega⟩) = B (hkT ⟨16, by omega⟩) := by
    rw [ex1 ⟨4, by omega⟩ _ (by simp [preExt]), hB.hKW, hKT]; have := hA 3; rw [e3] at this; exact this
  have k1 : ∀ i : Fin (3 + x), i.val < off → i.val ≠ 0 → B1 i = B i := by
    intro i hi h0
    by_cases h23 : i = hkT ⟨23, by omega⟩
    · rw [h23]; exact o23
    · by_cases h16 : i = hkT ⟨16, by omega⟩
      · rw [h16]; exact o16
      · refine un1 i (by omega) (fun j hj => ?_)
        rcases preExt_some off hkT hj with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
        · exact h0 b
        · omega
        · exact h23 b
        · exact h16 b
        · omega
        · omega
  -- the erase
  have hdrv : B1 ⟨L.gRR.val, by omega⟩ = List.replicate (2 ^ ρ) true := by
    rw [k1 _ (show L.gRR.val < off by have := L.gRR.isLt; have := hB.koff ⟨0, by omega⟩; omega)
      (show L.gRR.val ≠ 0 by simp [C4Set.Lay.gRR]), hB.hRR]
  have s2 := eraseS (eMask off n) ⟨L.gRR.val, by omega⟩ ⟨off + 11, by omega⟩
    (by unfold eMask; simp only [decide_eq_false_iff_not, not_and]; have := L.gRR.isLt;
        have := hB.koff ⟨0, by omega⟩; omega)
    (by unfold eMask; simp)
    (by intro e; have := congrArg Fin.val e; simp at this; have := L.gRR.isLt; have := hB.koff ⟨0, by omega⟩; omega)
    (2 ^ ρ) B1
    (fun i hi => by
      unfold eMask at hi; simp only [decide_eq_true_eq] at hi
      rw [bl1 i (by omega)]; simp)
    hdrv (bl1 _ (by simp))
  refine ⟨_, Step.seq s1 s2, ?_⟩
  refine ⟨fun i hi h0 => ?_, ?_, ?_, ?_, ?_, fun i h1 h2 => ?_, fun i hi => ?_⟩
  · unfold CloseoutWitness.SelectedErase.output
    rw [if_neg (by unfold eMask; simp; omega), if_neg (fun e => by rw [e] at hi; simp at hi <;> omega)]
    exact k1 i hi h0
  · unfold CloseoutWitness.SelectedErase.output
    rw [if_neg (by unfold eMask; simp), if_neg (fun e => by have := congrArg Fin.val e; simp at this)]
    exact o0
  · unfold CloseoutWitness.SelectedErase.output
    rw [if_neg (by unfold eMask; simp), if_neg (fun e => by have := congrArg Fin.val e; simp at this)]
    exact oW
  · unfold CloseoutWitness.SelectedErase.output
    rw [if_neg (by unfold eMask; simp), if_neg (fun e => by have := congrArg Fin.val e; simp at this)]
    exact oP
  · unfold CloseoutWitness.SelectedErase.output
    rw [if_neg (by unfold eMask; simp), if_neg (fun e => by have := congrArg Fin.val e; simp at this)]
    exact oC
  · unfold CloseoutWitness.SelectedErase.output
    rw [if_pos (by unfold eMask; simp; omega)]
  · unfold CloseoutWitness.SelectedErase.output
    rw [if_neg (by unfold eMask; simp; omega), if_neg (fun e => by rw [e] at hi; simp at hi <;> omega)]
    exact bl1 i (by omega)

end Pre

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
