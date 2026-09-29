import Proof.Wire_3_5.Primitive.SeedFix.C4WA

/-! # c4 THR/HASH setups, the big bank: the layout plus room above it

The THR and HASH data stage (`ThrStage4U`) leaves scratch on `x3` extra tapes which no tape of the layout
(`C4Set.Lay`) may carry. The THR and HASH stages therefore run on a bank of `3 + x'` tapes whose first `3 + x` tapes are
the layout. This file lifts steps and the loop entry from the first `u` tapes to the big bank:
* `liftE` (the first `u` tapes of `u'`), **`liftStep`** (a step on the first tapes, run on the big bank by
  `RecoveryFocus`: the other tapes kept);
* `liftX` (a dock's `ext` lifted), `slx_lift`, **`entry_lift`** (`C4Wrap.LoopEntry` on the first tapes gives it on
  the big bank).

Paper quantity: none (the machine layout of P3:3011-3016's setup before the decision loop). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Set (slx slx_some slx_none)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (LoopEntry)

/-- The first `u` tapes of a bank of `u'` tapes. -/
def liftE {u u' : ℕ} (h : u ≤ u') (i : Fin u) : Fin u' := ⟨i.val, by have := i.isLt; omega⟩

theorem liftE_val {u u' : ℕ} (h : u ≤ u') (i : Fin u) : (liftE h i).val = i.val := rfl

theorem liftE_inj {u u' : ℕ} (h : u ≤ u') : Function.Injective (liftE h) :=
  fun a b e => Fin.ext (by have h2 := congrArg Fin.val e; exact h2)

/-- **A step on the first `u` tapes, on the big bank**: the first tapes as the step leaves them, the others kept. -/
theorem liftStep {u u' s n : ℕ} {M : Machine u s} {tin tout : Fin u → List Bool}
    (hM : Step M n (fun _ => 0) tin (fun _ => 0) tout) (h : u ≤ u') (B : Fin u' → List Bool)
    (hB : ∀ j, B (liftE h j) = tin j) :
    Step (RecoveryFocus.machine (liftE h) M) n (fun _ => 0) B (fun _ => 0) (install (liftE h) B tout) ∧
      (∀ j, install (liftE h) B tout (liftE h j) = tout j) ∧
      (∀ i : Fin u', u ≤ i.val → install (liftE h) B tout i = B i) := by
  refine ⟨GeoFront.dockZ hM (liftE h) (liftE_inj h) (fun _ => 0) B (fun _ => rfl) hB, fun j => ?_, fun i hi => ?_⟩
  · rw [install_slot _ (liftE_inj h)]
  · apply install_other
    intro j e
    have := congrArg Fin.val e
    rw [liftE_val] at this
    have := j.isLt
    omega

/-- A dock's `ext` on the first tapes, lifted to the big bank. -/
def liftX {t u u' : ℕ} (h : u ≤ u') (ext : Fin t → Option (Fin u)) : Fin t → Option (Fin u') :=
  fun j => (ext j).map (liftE h)

theorem liftX_some {t u u' : ℕ} (h : u ≤ u') (ext : Fin t → Option (Fin u)) (j : Fin t) (g : Fin u')
    (e : liftX h ext j = some g) : ∃ g0, ext j = some g0 ∧ g = liftE h g0 := by
  unfold liftX at e
  cases hj : ext j with
  | none => rw [hj] at e; simp at e
  | some g0 =>
    rw [hj] at e
    simp only [Option.map_some, Option.some.injEq] at e
    exact ⟨g0, rfl, e.symm⟩

theorem slx_lift {t u u' : ℕ} (h : u ≤ u') (off : ℕ) (hoff : off + t ≤ u) (hoff' : off + t ≤ u')
    (ext : Fin t → Option (Fin u)) (j : Fin t) : slx off hoff' (liftX h ext) j = liftE h (slx off hoff ext j) := by
  cases hj : ext j with
  | none =>
    have e : liftX h ext j = none := by unfold liftX; rw [hj]; rfl
    apply Fin.ext
    rw [slx_none e, liftE_val, slx_none hj]
  | some g =>
    have e : liftX h ext j = some (liftE h g) := by unfold liftX; rw [hj]; rfl
    rw [slx_some e, slx_some hj]

/-- **The loop entry on the first tapes gives it on the big bank.** -/
theorem entry_lift {x x' : ℕ} (hx : 3 + x ≤ 3 + x') (F : PrimT.C4Loop.ChildFam) (R L off : ℕ)
    (hoff : off + (F.T + 1 + 1 + 1) ≤ 3 + x) (hoff' : off + (F.T + 1 + 1 + 1) ≤ 3 + x')
    (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin (3 + x))) (w v : List Bool) (B : Fin (3 + x) → List Bool)
    (B' : Fin (3 + x') → List Bool) (hBB : ∀ i, B' (liftE hx i) = B i) (hE : LoopEntry F R L off hoff ext w v B) :
    LoopEntry F R L off hoff' (liftX hx ext) w v B' where
  hR := hE.hR
  hL := hE.hL
  h3 := hE.h3
  inj := fun i j g hi hj => by
    obtain ⟨gi, ei, rfl⟩ := liftX_some hx ext i g hi
    obtain ⟨gj, ej, e⟩ := liftX_some hx ext j _ hj
    have : gi = gj := liftE_inj hx e
    subst this
    exact hE.inj i j gi ei ej
  lt := fun i g hi => by
    obtain ⟨g0, e0, rfl⟩ := liftX_some hx ext i g hi
    rw [liftE_val]
    exact hE.lt i g0 e0
  port := fun i g hi => by
    obtain ⟨g0, e0, rfl⟩ := liftX_some hx ext i g hi
    rw [liftE_val]
    exact hE.port i g0 e0
  pfx := fun g hg => by
    obtain ⟨g0, e0, rfl⟩ := liftX_some hx ext _ g hg
    rw [liftE_val]
    exact hE.pfx g0 e0
  entry := fun j => by
    rw [slx_lift hx off hoff hoff' ext j, hBB]
    exact hE.entry j
  p0 := by
    have e : (⟨0, by omega⟩ : Fin (3 + x')) = liftE hx ⟨0, by omega⟩ := rfl
    rw [e, hBB]
    exact hE.p0
  p1 := by
    have e : (⟨1, by omega⟩ : Fin (3 + x')) = liftE hx ⟨1, by omega⟩ := rfl
    rw [e, hBB]
    exact hE.p1
  p2 := by
    have e : (⟨2, by omega⟩ : Fin (3 + x')) = liftE hx ⟨2, by omega⟩ := rfl
    rw [e, hBB]
    exact hE.p2

end NearCubicWires.WireExponent3_5.PrimAsm.BigBank
