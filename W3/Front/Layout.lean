import W3.Joins.Front
import OuterM.ARun
import Succinct.H2Final
import Setup.PhaseK
import CheckedPCPP.DescW
import TabMachine.Back

set_option autoImplicit false

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP

namespace W3.NearCubicWires.RepairSource.Outer3.Front

structure H2D where
  t : ℕ
  st : ℕ
  M : Machine t st
  iW : Fin t
  iD : Fin t
  o : Fin t
  K : ℕ
  e : ℕ
  nodup : [iW, iD, o].Nodup
  run : ∀ (oc : NearCubicWires.Bindings.MW20.OracleOutput) {q : ℕ} (B : BooleanCircuit q),
    ∃ out, ClockJoin.ReadyRun M (K * (oc.word.length + (PCPPNative.descriptor B).length + q + 1) ^ e)
        (CheckedPCPP.portBank t iW iD oc.word (PCPPNative.descriptor B)) out ∧
      out o = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity) ∧
      out iW = oc.word ∧ out iD = PCPPNative.descriptor B

theorem h2D_nonempty : Nonempty H2D := by
  obtain ⟨t, st, M, iW, iD, o, K, e, nd, run⟩ := Succinct.H2.h2Ready
  exact ⟨⟨t, st, M, iW, iD, o, K, e, nd, run⟩⟩

/-- The stream count minus one. -/
def nsF (ta th : ℕ) : ℕ := 12 + ta + th

section Layout
variable (ta th : ℕ)

/-- Stream `k < 13`. -/
def fx (k : ℕ) (hk : k < 13) : Fin (nsF ta th + 1) := ⟨k, by unfold nsF; omega⟩

abbrev sZ := fx ta th 0 (by decide)
abbrev sFL := fx ta th 1 (by decide)
abbrev sNU := fx ta th 2 (by decide)
abbrev sS := fx ta th 3 (by decide)
abbrev sW := fx ta th 4 (by decide)
abbrev sPf := fx ta th 5 (by decide)
abbrev sOUT := fx ta th 6 (by decide)
abbrev sSZ := fx ta th 7 (by decide)
abbrev sAR := fx ta th 8 (by decide)
abbrev sPT := fx ta th 9 (by decide)
abbrev sVV := fx ta th 10 (by decide)
abbrev sTT := fx ta th 11 (by decide)
abbrev sFT := fx ta th 12 (by decide)

@[simp] theorem fx_val (k : ℕ) (hk : k < 13) : (fx ta th k hk).val = k := rfl

/-- The A-run's private block. -/
def bA (j : ℕ) (hj : j < ta) : Fin (nsF ta th + 1) := ⟨13 + j, by unfold nsF; omega⟩

def bH (j : ℕ) (hj : j < th) : Fin (nsF ta th + 1) := ⟨13 + ta + j, by unfold nsF; omega⟩

end Layout

section Maps
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G) (A : OuterM.ARun mw SV) (h : H2D)

/-- The A-run's tape map. -/
def mA (j : Fin A.t) : Fin (nsF A.t h.t + 1) :=
  if j = A.dIn then sS A.t h.t else if j = A.nIn then sNU A.t h.t else if j = A.fOut then sFL A.t h.t
  else if j = A.wOut then sW A.t h.t else bA A.t h.t j.val j.isLt

def mH (j : Fin h.t) : Fin (nsF A.t h.t + 1) :=
  if j = h.iW then sW A.t h.t else if j = h.iD then sPf A.t h.t else if j = h.o then sOUT A.t h.t
  else bH A.t h.t j.val j.isLt

theorem mA_val (j : Fin A.t) : (mA mw SV A h j).val =
    if j = A.dIn then 3 else if j = A.nIn then 2 else if j = A.fOut then 1 else if j = A.wOut then 4
    else 13 + j.val := by
  unfold mA; split_ifs <;> rfl

theorem mH_val (j : Fin h.t) : (mH mw SV A h j).val =
    if j = h.iW then 4 else if j = h.iD then 5 else if j = h.o then 6 else 13 + A.t + j.val := by
  unfold mH; split_ifs <;> rfl

theorem mA_inj : Function.Injective (mA mw SV A h) := by
  have nd := A.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  obtain ⟨⟨hdn, hdf, hdw⟩, ⟨hnf, hnw⟩, hfw⟩ := nd
  intro i j hij
  have hv := congrArg Fin.val hij
  rw [mA_val, mA_val] at hv
  split_ifs at hv <;>
    first | (subst_vars; rfl) | (exfalso; omega) | (exact Fin.ext (by omega))

theorem mH_inj : Function.Injective (mH mw SV A h) := by
  have nd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  obtain ⟨⟨hwd, hwo⟩, hdo⟩ := nd
  intro i j hij
  have hv := congrArg Fin.val hij
  rw [mH_val, mH_val] at hv
  split_ifs at hv <;> first | (subst_vars; rfl) | (exfalso; omega) | (exact Fin.ext (by omega))

end Maps

/-! ## The program -/

/-- The registers of the size/arity reader: `0 … 18` (free in the gates register file below `regE`'s use). -/
def Hr : Fin 19 ↪ Fin nrW :=
  ⟨fun i => ⟨i.val, by have := i.isLt; show i.val < 128; omega⟩, fun a b e => Fin.ext (by simpa using congrArg Fin.val e)⟩

@[simp] theorem Hr_val (i : Fin 19) : (Hr i).val = i.val := rfl

section Prog
variable (ta th : ℕ)

/-- **Phase K** (on the flag): `nN := N`, `lp := size ν`, `lb := size (ν^{G+2} + 4)`, CHECK on `S` against `Z`
(paper (C.10.0)), `FL := [CheckAt]`. -/
noncomputable def phKF (G : ℕ) : WMX (nsF ta th) nrW :=
  .seq (.wm (Codec.dupR rN (EK .nN) dS))
  (.seq (sizeNuW (EK (.e .lp)))
  (.seq (powNuW (G + 2) pX2)
  (.seq (.wm (CheckedPCPP.NodeEmit.incN pX2 4))
  (.seq (Recovery.HTParts.sizeW pX2 pH pB (EK (.e .lb)))
  (.seq (.wm (Succinct.checkW (sS ta th) (sPT ta th) (sVV ta th) (sTT ta th) (sZ ta th) EK))
  (.ifr (EK .f) WMX.skip (WMX.wr (sFL ta th) false)))))))

end Prog

section Program
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G) (A : OuterM.ARun mw SV) (h : H2D)

/-- **The front end's program.** -/
noncomputable def frontP : WMX (nsF A.t h.t) nrW :=
  .seq (BinW.width (sZ A.t h.t) rN tW)
  (.seq (powP (sFT A.t h.t))
  (.seq (.wm (NearCubicWires.WireExponent3_5.PrimAsm.HashCell.wrU (sNU A.t h.t) pT1 rNu pT2 pT3))
  (.seq (.mach A.M (mA mw SV A h))
  (.seq (.mach h.M (mH mw SV A h))
  (.seq (.wm (CheckedPCPP.DescW.readG Hr (sOUT A.t h.t) 9))
  (.seq (.wm (CheckedPCPP.DescW.readG Hr (sOUT A.t h.t) 10))
  (.seq (TabMachine.writeOnes (sSZ A.t h.t) (Hr 10) (Hr 11))
  (.seq (TabMachine.writeOnes (sAR A.t h.t) (Hr 9) (Hr 11))
  (.ifs (sFL A.t h.t) (phKF A.t h.t G) WMX.skip)))))))))

end Program

end W3.NearCubicWires.RepairSource.Outer3.Front
