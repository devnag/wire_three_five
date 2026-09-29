import Proof.Wire_3_5.Primitive.SeedFix.C4HfG

/-! # The HASH child family, part 8: the Hb unit

`filt:soft`, P3:2253-2290: the Hb unit on `HU` tapes (the kept framed words `0 … 93`, the prefix `94`, the working Hb
bank `95 … 188`, scratch): the prep (`prepW`, masked), the printer on the working bank (`hashLoopM`), and the
terminator (`appW`, masked) on the printer's output and its ruler. **`unit_step`**: from the kept words and the prefix,
the working bank's output tape (`95`) holds `exprWord (hV D (p ++ [b]))`, the kept words and the prefix unchanged.

Paper quantity of the main type: the printed conditional objective `V_{p ++ [b]}` as the expression word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

theorem HU_eq : HU = 253 := rfl

/-- The prep's tapes on the unit (C5's order: stream `0`, the cell, streams `1 …`, the registers, the log). -/
def prepSl (t : Fin (188 + 2 + 2 + 1)) : Fin HU :=
  ⟨if t.val = 0 then 0 else if t.val = 1 then 189 else if t.val ≤ 189 then t.val - 1 else t.val, by
    rw [HU_eq]; have := t.isLt; split_ifs <;> omega⟩

theorem prepSl_val (t : Fin (188 + 2 + 2 + 1)) :
    (prepSl t).val = if t.val = 0 then 0 else if t.val = 1 then 189 else if t.val ≤ 189 then t.val - 1 else t.val := rfl

theorem prepSl_inj : Function.Injective prepSl := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [prepSl_val, prepSl_val] at hv
  have := a.isLt; have := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The working bank's tapes. -/
def hbSl (j : Fin 94) : Fin HU := ⟨95 + j.val, by rw [HU_eq]; omega⟩

theorem hbSl_inj : Function.Injective hbSl := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [hbSl] at this; omega)

/-- The terminator's tapes: the output `95`, its cell `193`, the ruler `97`, its log `194`. -/
def appSl (t : Fin (1 + 2 + 0 + 1)) : Fin HU :=
  ⟨if t.val = 0 then 95 else if t.val = 1 then 193 else if t.val = 2 then 97 else 194, by
    rw [HU_eq]; split_ifs <;> omega⟩

theorem appSl_inj : Function.Injective appSl := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [appSl] at hv
  have := a.isLt; have := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The prep machine of the child bit `b`. -/
noncomputable def prepZ (b : Bool) := MaskedReset.machine (prepW b).toProg.compile (fun _ => true)

/-- The terminator machine. -/
noncomputable def appZ := MaskedReset.machine appW.toProg.compile (fun _ => true)

/-- **The Hb unit** of the child bit `b`. -/
noncomputable def unitM (b : Bool) :=
  Composition.machine (RecoveryFocus.machine prepSl (prepZ b))
    (Composition.machine (RecoveryFocus.machine hbSl hashLoopM) (RecoveryFocus.machine appSl appZ))

/-- The unit's entry: the framed kept words, the framed prefix, every other tape blank. -/
def uIn (KW : Fin 94 → List Bool) (p : List Bool) (u : Fin HU) : List Bool :=
  if h : u.val < 94 then frame (KW ⟨u.val, h⟩) else if u.val = 94 then frame p else []

theorem role_stream {ns nr : ℕ} (v : ℕ) (hv : v < ns + 2 + nr) (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≤ ns + 1) :
    role (ns := ns) (nr := nr) ⟨v, hv⟩ = .stream ⟨v - 1, by omega⟩ := by
  unfold role; rw [dif_neg h0, dif_neg h1, dif_pos h2]

theorem role_reg {ns nr : ℕ} (v : ℕ) (hv : v < ns + 2 + nr) (h2 : ¬ v ≤ ns + 1) :
    role (ns := ns) (nr := nr) ⟨v, hv⟩ = .reg ⟨v - (ns + 2), by omega⟩ := by
  have h0 : v ≠ 0 := by omega
  have h1 : v ≠ 1 := by omega
  unfold role; rw [dif_neg h0, dif_neg h1, dif_neg h2]

/-- The prep's entry is the unit's entry on its tapes. -/
theorem prep_entry (KW : Fin 94 → List Bool) (p : List Bool) (t : Fin (188 + 2 + 2 + 1)) :
    uIn KW p (prepSl t) = Fin.addCases (m := 188 + 2 + 2) (n := 1) (C4Pipe.wblank (prepIn KW p))
      (fun _ : Fin 1 => []) t := by
  obtain ⟨v, hv⟩ := t
  by_cases hlog : v = 192
  · subst hlog
    have e : (⟨192, hv⟩ : Fin (188 + 2 + 2 + 1)) = Fin.natAdd (188 + 2 + 2) (0 : Fin 1) := rfl
    rw [e, Fin.addCases_right]
    simp [uIn, prepSl]
  · have e : (⟨v, hv⟩ : Fin (188 + 2 + 2 + 1)) = Fin.castAdd 1 (⟨v, by omega⟩ : Fin (188 + 2 + 2)) := rfl
    rw [e, Fin.addCases_left]
    by_cases h0 : v = 0
    · subst h0; rfl
    · by_cases h1 : v = 1
      · subst h1; rfl
      · by_cases h2 : v ≤ 189
        · have hr := role_stream (ns := 188) (nr := 2) v (by omega) h0 h1 h2
          simp only [C4Pipe.wblank]
          rw [hr]
          simp only [uIn, prepSl, prepIn, Fin.val_castAdd, if_neg h0, if_neg h1, if_pos h2]
        · have hr := role_reg (ns := 188) (nr := 2) v (by omega) h2
          simp only [C4Pipe.wblank]
          rw [hr]
          have hv1 : ¬ v < 94 := by omega
          have hv2 : v ≠ 94 := by omega
          simp only [uIn, prepSl, Fin.val_castAdd, if_neg h0, if_neg h1, if_neg h2, dif_neg hv1, if_neg hv2]

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
