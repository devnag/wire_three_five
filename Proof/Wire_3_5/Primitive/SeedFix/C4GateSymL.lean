import Proof.Wire_3_5.Primitive.SeedFix.C4GatesZ
import Proof.Wire_3_5.Primitive.Writers.DataBlank
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase
import Proof.Wire_3_5.Primitive.SeedFix.C4Geo
import Proof.Wire_3_5.Primitive.Writers.GeoFront

/-! # G2, the SYM gate-frame writer, part 1: the layout (P3:1655-1664, 3119-3120)

"The algorithm receives polynomial-bit integer circuit descriptions" (P3:3119-3120); C3a's gate field is the call's
pool (P3:1655-1664). The SYM gate writer is five docked stages on one layout: the front (`GeoFront` F1–F3: the
request, `1^n`, `1^W`), a copy (`1^W` for the data stage's `1^L`, `1^n` for the converter), PA's data stage
(`Data.data_step_blank`: the slot tables), and the converter (`C4Gates.convAll`: C3a's gate field). This part fixes the
layout `GLt Dv + (DT + (8 + 34))`: the front tapes, the data stage's tapes (its request, `1^n`, `1^W` on the
front's), the copy's, the converter's (its tables on the data stage's slot streams, its arity ruler on the copy's
output), and the slot maps `dS`, `kS`, `cS` with their injectivity.

Paper quantity: none (the writer's plumbing; the run's type carries C3a's gate field). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4GateSym
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GLt ws gIN gNT gCT wt)

/-- The data stage's tapes (its register-language layout and its log). -/
abbrev DT : ℕ := PrimAsm.Data.DS + 2 + PrimAsm.Data.DR + 1

/-- The writer's tapes. -/
abbrev GT (Dv : ℕ) : ℕ := GLt Dv + (DT + (8 + 34))

section Layout
variable {Dv : ℕ}

def gl (i : Fin (GLt Dv)) : Fin (GT Dv) := Fin.castAdd _ i
def dReg (d : Fin DT) : Fin (GT Dv) := Fin.natAdd (GLt Dv) (Fin.castAdd (8 + 34) d)
def kReg (c : Fin 8) : Fin (GT Dv) := Fin.natAdd (GLt Dv) (Fin.natAdd DT (Fin.castAdd 34 c))
def cReg (c : Fin 34) : Fin (GT Dv) := Fin.natAdd (GLt Dv) (Fin.natAdd DT (Fin.natAdd 8 c))

theorem gl_val (i : Fin (GLt Dv)) : (gl i).val = i.val := rfl
theorem dReg_val (d : Fin DT) : (dReg (Dv := Dv) d).val = GLt Dv + d.val := rfl
theorem kReg_val (c : Fin 8) : (kReg (Dv := Dv) c).val = GLt Dv + (DT + c.val) := rfl
theorem cReg_val (c : Fin 34) : (cReg (Dv := Dv) c).val = GLt Dv + (DT + (8 + c.val)) := rfl

/-- A data stream's tape in the data stage's layout. -/
def dPos (s : Fin (PrimAsm.Data.DS + 1)) : Fin DT := Fin.castAdd 1 (sTape (nr := PrimAsm.Data.DR) s)

theorem dPos_val (s : Fin (PrimAsm.Data.DS + 1)) : (dPos s).val = if s.val = 0 then 0 else s.val + 1 := rfl

/-- **The data stage's tapes**: its request, `1^n` and `1^W` on the front's, the rest in its region. -/
def dS (d : Fin DT) : Fin (GT Dv) :=
  if d = dPos PrimAsm.Data.sIN then gl (ws gIN) else if d = dPos PrimAsm.Data.sNT then gl (ws gNT)
  else if d = dPos PrimAsm.Data.sCT then gl (ws gCT) else dReg d

theorem dS_val (d : Fin DT) : (dS (Dv := Dv) d).val =
    if d.val = 0 then 0 else if d.val = 2 then 2 else if d.val = 4 then 3 else GLt Dv + d.val := by
  unfold dS
  have e1 : (dPos PrimAsm.Data.sIN).val = 0 := rfl
  have e2 : (dPos PrimAsm.Data.sNT).val = 2 := rfl
  have e3 : (dPos PrimAsm.Data.sCT).val = 4 := rfl
  by_cases h1 : d = dPos PrimAsm.Data.sIN
  · rw [if_pos h1, h1, e1]; rfl
  · have h1' : d.val ≠ 0 := fun h => h1 (Fin.ext (by rw [h, e1]))
    rw [if_neg h1, if_neg h1']
    by_cases h2 : d = dPos PrimAsm.Data.sNT
    · rw [if_pos h2, h2, e2]; rfl
    · have h2' : d.val ≠ 2 := fun h => h2 (Fin.ext (by rw [h, e2]))
      rw [if_neg h2, if_neg h2']
      by_cases h3 : d = dPos PrimAsm.Data.sCT
      · rw [if_pos h3, h3, e3]; rfl
      · have h3' : d.val ≠ 4 := fun h => h3 (Fin.ext (by rw [h, e3]))
        rw [if_neg h3, if_neg h3']; rfl

theorem dS_inj : Function.Injective (dS (Dv := Dv)) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [dS_val, dS_val] at hv
  apply Fin.ext
  have hG : 16 ≤ GLt Dv := by show 16 ≤ 78 + (14 + (14 + 2 * Dv)); omega
  have hDT : DT = 9902 := rfl
  split_ifs at hv <;> omega

/-- The converter's arity ruler `1^n`, in its layout (stream `10`). -/
def nsPos : Fin 34 := Fin.castAdd 1 (sTape (ns := 11) (nr := 20) C4Gates.sNS)

/-- **The copy's tapes** (`WM 4 1` and its log): `1^W` from the front's onto the data stage's `1^L`, `1^n` from the
front's onto the converter's arity ruler. -/
def kS (c : Fin 8) : Fin (GT Dv) :=
  if c.val = 0 then gl (ws gCT) else if c.val = 2 then dReg (dPos PrimAsm.Data.sLT) else if c.val = 3 then gl (ws gNT)
  else if c.val = 4 then cReg nsPos else kReg c

theorem kS_val (c : Fin 8) : (kS (Dv := Dv) c).val =
    if c.val = 0 then 3 else if c.val = 2 then GLt Dv + 3 else if c.val = 3 then 2
    else if c.val = 4 then GLt Dv + (DT + 19) else GLt Dv + (DT + c.val) := by
  unfold kS; split_ifs <;> rfl

theorem kS_inj : Function.Injective (kS (Dv := Dv)) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [kS_val, kS_val] at hv
  apply Fin.ext
  have hG : 16 ≤ GLt Dv := by show 16 ≤ 78 + (14 + (14 + 2 * Dv)); omega
  have hDT : DT = 9902 := rfl
  have := a.isLt; have := b.isLt
  split_ifs at hv <;> omega

/-- The data stream of converter table `j`: the carriers' slots, then the circuits'. -/
def tabStream (j : Fin 6) : Fin (PrimAsm.Data.DS + 1) :=
  if h : j.val < 2 then PrimAsm.Data.sCar ⟨j.val, h⟩ 3 else PrimAsm.Data.sSym ⟨j.val - 2, by omega⟩ 3

theorem tabStream_val (j : Fin 6) : (tabStream j).val = if j.val < 2 then 7173 + 1357 * j.val
    else 17 + 1789 * (j.val - 2) := by
  unfold tabStream; split_ifs <;> simp [PrimAsm.Data.sCar, PrimAsm.Data.sSym] <;> omega

/-- **The converter's tapes**: its tables on the data stage's slot streams, the rest in its region. -/
def cS (c : Fin 34) : Fin (GT Dv) :=
  if h : 2 ≤ c.val ∧ c.val < 8 then dReg (dPos (tabStream ⟨c.val - 2, by omega⟩)) else cReg c

theorem cS_val (c : Fin 34) : (cS (Dv := Dv) c).val =
    if 2 ≤ c.val ∧ c.val < 8 then GLt Dv + (if c.val - 2 < 2 then 7174 + 1357 * (c.val - 2)
      else 18 + 1789 * (c.val - 4)) else GLt Dv + (DT + (8 + c.val)) := by
  unfold cS
  split_ifs with h1 <;> simp only [dReg_val, dPos_val, tabStream_val, cReg_val] <;> split_ifs <;> omega

theorem cS_inj : Function.Injective (cS (Dv := Dv)) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [cS_val, cS_val] at hv
  apply Fin.ext
  have := a.isLt; have := b.isLt
  have hDT : DT = 9902 := rfl
  split_ifs at hv <;> omega

end Layout

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym
