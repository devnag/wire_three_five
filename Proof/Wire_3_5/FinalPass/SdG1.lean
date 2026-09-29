import Proof.Wire_3_5.FinalPass.SdRunT

/-! # S4 (the seeds phase), part 41: the seeds phase's layout (P3:3170-3178)

S4's machine runs on one word layout (`gns` streams): the body's streams (`fsB`, the identity on indices), then the
tables writer's tapes (`tmW`: its input port docked on the body's stream `28`, its output port on the tables word
`tTW`, every other tape on its own stream past the body), then the denominator's stream `gD`. The registers are the
body's. **`gLay E tw`**: the layout as S4's seam's `SdLay` (the front's words on the body's `tW`, the numerator on
`tN`, the denominator on `gD`).

Paper quantity: none beyond the machine model (the seeds phase's streams and registers, P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 SdLay)

/-- The seeds phase's stream count: the body's, the writer's tapes, the denominator. -/
def gns (nw nsc tw : ℕ) : ℕ := bns nw nsc + tw + 1

section GLay
variable {nw nsc tw : ℕ}

/-- A body stream in the seeds phase's layout. -/
def fsB (j : Fin (bns nw nsc + 1)) : Fin (gns nw nsc tw + 1) := ⟨j.val, by unfold gns; omega⟩

theorem fsB_inj : Function.Injective (fsB (nw := nw) (nsc := nsc) (tw := tw)) := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simpa [fsB] using this)

/-- The denominator's stream. -/
def gD : Fin (gns nw nsc tw + 1) := ⟨bns nw nsc + 1 + tw, by unfold gns; omega⟩

theorem fsB_ne_gD (j : Fin (bns nw nsc + 1)) : fsB (tw := tw) j ≠ gD := by
  intro h; have := congrArg Fin.val h; simp [fsB, gD] at this; omega

/-- The tables writer's tape `x`: the input port on stream `28`, the output port on `tTW`, the others past the body. -/
def tmW (win wout : Fin tw) (x : Fin tw) : Fin (gns nw nsc tw + 1) :=
  if x = win then fsB (bst 28 (by omega)) else if x = wout then fsB tTW
  else ⟨bns nw nsc + 1 + x.val, by unfold gns; omega⟩

theorem tmW_val (win wout x : Fin tw) :
    (tmW (nw := nw) (nsc := nsc) win wout x).val =
      if x = win then 28 else if x = wout then 27 else bns nw nsc + 1 + x.val := by
  unfold tmW
  split_ifs <;> rfl

theorem tmW_inj (win wout : Fin tw) :
    Function.Injective (tmW (nw := nw) (nsc := nsc) win wout) := by
  intro a b h
  have e := congrArg Fin.val h
  rw [tmW_val, tmW_val] at e
  have hb : 46 ≤ bns nw nsc := by unfold bns; omega
  by_cases ha1 : a = win <;> by_cases hb1 : b = win
  · rw [ha1, hb1]
  · rw [if_pos ha1, if_neg hb1] at e
    split_ifs at e <;> omega
  · rw [if_neg ha1, if_pos hb1] at e
    split_ifs at e <;> omega
  · rw [if_neg ha1, if_neg hb1] at e
    by_cases ha2 : a = wout <;> by_cases hb2 : b = wout
    · rw [ha2, hb2]
    · rw [if_pos ha2, if_neg hb2] at e; omega
    · rw [if_neg ha2, if_pos hb2] at e; omega
    · rw [if_neg ha2, if_neg hb2] at e; exact Fin.ext (by omega)

theorem tmW_ne_gD (win wout x : Fin tw) : tmW (nw := nw) (nsc := nsc) win wout x ≠ gD := by
  intro h
  have e := congrArg Fin.val h
  rw [tmW_val] at e
  simp only [gD] at e
  have := x.isLt
  split_ifs at e <;> unfold bns at e <;> omega

/-- A writer tape other than the ports is off the body. -/
theorem tmW_off (win wout x : Fin tw) (h1 : x ≠ win) (h2 : x ≠ wout) (j : Fin (bns nw nsc + 1)) :
    tmW (nw := nw) (nsc := nsc) win wout x ≠ fsB j := by
  intro h
  have e := congrArg Fin.val h
  rw [tmW_val, if_neg h1, if_neg h2] at e
  simp only [fsB] at e
  have := j.isLt
  omega

/-- The body streams the writer touches: the two ports. -/
theorem tmW_body (win wout x : Fin tw) (j : Fin (bns nw nsc + 1)) (h : tmW (nw := nw) (nsc := nsc) win wout x = fsB j) :
    j.val = 28 ∨ j.val = 27 := by
  have e := congrArg Fin.val h
  rw [tmW_val] at e
  simp only [fsB] at e
  have := j.isLt
  split_ifs at e <;> omega

end GLay

/-- **The seeds phase's layout** as S4's seam's `SdLay`. -/
def gLay (E : SymPtEval2) (tw : ℕ) : SdLay E.toWords where
  ns := gns E.nw E.nsc tw
  nr := bnr E.nn E.nrs
  wdS := fun k => fsB (tW k)
  sN := fsB tN
  sD := gD
  wdInj := fun a b h => by
    have e := congrArg Fin.val h
    simp only [fsB, tW] at e
    exact Fin.ext (by omega)
  nd := fsB_ne_gD _
  wdN := fun k h => by
    have e := congrArg Fin.val h
    simp only [fsB, tW, tN, bst] at e
    omega
  wdD := fun k => fsB_ne_gD _

end NearCubicWires.WireExponent3_5.FinalPass.Sd
