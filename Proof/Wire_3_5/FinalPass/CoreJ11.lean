import Lean
import Proof.Wire_3_5.FinalPass.CoreJ10
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core over the writers with arbitrary residues, part J11: the core half's layout and machine (P3:3170-3181)

* **`CoreWritersJ l`** (the four writers: S4's words part A and part B, the numbers, the SYM words, machine forms of
  `CoreIfaceM`), their blocks' sizes and offsets, **`mCoreOfJ W`** (the core's room at `l`: the count `5`, the mode `5`,
  then the writers' layouts);
* on a bank `L` with the core's room: the reference `TcJ` (the count's output tape), the count's template `cTtJ`, the
  mode tape `MbJ`, the writers' output maps `outA`, `outB`, `outN`, `outS` and their injectivity, `regList` (every
  register tape off the words, the numbers and the reference);
* **`coreMJ`**: the count ; the mode ; part A ; part B ; the numbers ; if SYM then the SYM words ; every register tape
  padded against `TcJ` ; `TcJ` erased.

Paper quantity: none (the front's machine assembly, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- **The core half's writers** at `l` (the machine forms). -/
structure CoreWritersJ (l : Literals) where
  SA : S4WordsMAJ l
  SB : S4WordsMBJ l
  NW : NumsMJ l
  SW : SymWordsMJ l

section Lay
variable {l : Literals} (W : CoreWritersJ l)

def szAJ : ℕ := W.SA.ns + 2 + W.SA.nr
def szBJ : ℕ := W.SB.ns + 2 + W.SB.nr
def szNJ : ℕ := W.NW.ns + 2 + W.NW.nr
def szSJ : ℕ := W.SW.ns + 2 + W.SW.nr
def oBJ : ℕ := 10 + szAJ W
def oNJ : ℕ := oBJ W + szBJ W
def oSJ : ℕ := oNJ W + szNJ W

/-- **The core's room** at `l`: the count, the mode, the four writers' blocks. -/
def mCoreOfJ : ℕ := oSJ W + szSJ W

theorem h5WJ : 0 + (3 + 2 + 0) ≤ mCoreOfJ W := by unfold mCoreOfJ oSJ oNJ oBJ; omega
theorem h10WJ : 5 + (3 + 2 + 0) ≤ mCoreOfJ W := by unfold mCoreOfJ oSJ oNJ oBJ; omega
theorem hAWJ : 10 + (W.SA.ns + 2 + W.SA.nr) ≤ mCoreOfJ W := by unfold mCoreOfJ oSJ oNJ oBJ szAJ; omega
theorem hBWJ : oBJ W + (W.SB.ns + 2 + W.SB.nr) ≤ mCoreOfJ W := by unfold mCoreOfJ oSJ oNJ szBJ; omega
theorem hNWJ : oNJ W + (W.NW.ns + 2 + W.NW.nr) ≤ mCoreOfJ W := by unfold mCoreOfJ oSJ szNJ; omega
theorem hSWJ : oSJ W + (W.SW.ns + 2 + W.SW.nr) ≤ mCoreOfJ W := by unfold mCoreOfJ szSJ; omega

end Lay

section Tapes
variable {l : Literals} (W : CoreWritersJ l) {mTh : ℕ} (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- The reference's index in the room: the count's output stream. -/
def iTcJ : Fin (mCoreOfJ W) :=
  ⟨(sTape (ns := 3) (nr := 0) (cOut L.Dc)).val, by
    have := (sTape (ns := 3) (nr := 0) (cOut L.Dc)).isLt; have := h5WJ W; omega⟩

theorem iTc_ltJ : (iTcJ W L).val < 5 := (sTape (ns := 3) (nr := 0) (cOut L.Dc)).isLt

/-- **The reference** `sent c`: the count's output tape. -/
noncomputable def TcJ : Fin L.t := hR.coreE (iTcJ W L)

theorem Tc_eqJ : TcJ W L hR = blk L hR 0 (3 + 2 + 0) (h5WJ W) (sTape (nr := 0) (cOut L.Dc)) := by
  unfold TcJ blk iTcJ; congr 1; exact Fin.ext (by simp)

/-- The count's template `sent N`. -/
noncomputable def cTtJ : Fin L.t := blk L hR 0 (3 + 2 + 0) (h5WJ W) (sTape (nr := 0) cT)

/-- The mode tape `[mb]`. -/
noncomputable def MbJ : Fin L.t := blk L hR 5 (3 + 2 + 0) (h10WJ W) (sTape (nr := 0) mM)

theorem wd_neRJ (k : Fin (17 + Sw0.nw)) (i : Fin (mCoreOfJ W)) : L.wd k ≠ hR.coreE i := fun e =>
  (core_off L hR i).2.1 k e.symm

theorem outN_neRJ (k : Fin 2) (i : Fin (mCoreOfJ W)) : outN L k ≠ hR.coreE i := by
  fin_cases k
  · exact fun e => (core_off L hR i).2.2.1 (by simp [outN] at e; exact e.symm)
  · exact fun e => (core_off L hR i).2.2.2 (by simp [outN] at e; exact e.symm)

end Tapes

section Mach
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) {mTh : ℕ} (L : S5Lay Sw0.nw)
  (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- The final pad: every register tape padded against `TcJ`, then `TcJ` erased. -/
noncomputable def finPJ : Prog L.t := .seq (padList (TcJ W L hR) (regList L (TcJ W L hR))) (eraseS (TcJ W L hR))

/-- **The core half's machine.** -/
noncomputable def coreMJ :=
  Composition.machine (cntM L hR (h5WJ W) L.Kc L.Dc)
   (Composition.machine (modeM L hR (h10WJ W) (cTtJ W L hR))
    (Composition.machine (wstageM L hR (W.SA.M F) W.SA.sIn W.SA.sOut (outA L) 10 (hAWJ W) (TcJ W L hR))
     (Composition.machine (wstageM L hR (W.SB.M F) W.SB.sIn W.SB.sOut (outB L) (oBJ W) (hBWJ W) (TcJ W L hR))
      (Composition.machine (wstageM L hR (W.NW.M F) W.NW.sIn W.NW.sOut (outN L) (oNJ W) (hNWJ W) (TcJ W L hR))
       (Composition.machine (iteMachine (MbJ W L hR) (Prog.skip : Prog L.t).compile
          (wstageM L hR (W.SW.M F) W.SW.sIn W.SW.sOut (outS L) (oSJ W) (hSWJ W) (TcJ W L hR)))
        (finPJ W L hR).compile)))))

end Mach

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
