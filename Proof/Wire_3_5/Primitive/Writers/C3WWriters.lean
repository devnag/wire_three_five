import Proof.Wire_3_5.Primitive.Writers.C3WFront

/-! # C3 request writer, part 8: the writers, docked

Paper quantity: none (the machine plumbing of alg:compiler's request writer, P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock

/-- The five field writers: the gate field, the halves, the width, the flips, the columns. -/
structure Wr5 where
  G : WriterIface.WriterStage
  S : WriterIface.WriterStage
  W : WriterIface.WriterStage
  F : WriterIface.WriterStage
  C : WriterIface.WriterStage

/-- The layout of the writers, C3a's `Ua` tapes and the fill polynomial. -/
def Wr5.lay (P : Wr5) (Ua Dv Cv : ℕ) : Lay := ⟨P.G.t, P.S.t, P.W.t, P.F.t, P.C.t, Ua, Dv, Cv⟩

namespace Lay
variable (L : Lay)

theorem hG1 : L.oG1 + L.tG ≤ L.U := by have := L.offs; omega
theorem hG2 : L.oG2 + L.tG ≤ L.U := by have := L.offs; omega
theorem hS : L.oS + L.tS ≤ L.U := by have := L.offs; omega
theorem hW : L.oW + L.tW ≤ L.U := by have := L.offs; omega
theorem hF1 : L.oF1 + L.tF ≤ L.U := by have := L.offs; omega
theorem hF2 : L.oF2 + L.tF ≤ L.U := by have := L.offs; omega
theorem hC1 : L.oC1 + L.tC ≤ L.U := by have := L.offs; omega
theorem hC2 : L.oC2 + L.tC ≤ L.U := by have := L.offs; omega

end Lay

namespace Wr5
variable (P : Wr5) (Ua Dv Cv : ℕ)

/-- **The writers' machine**: the gate field twice, the halves, the width, the flips twice, the columns twice. -/
noncomputable def wrM :=
  let L := P.lay Ua Dv Cv
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (Composition.machine
    (RecoveryFocus.machine (portSl P.G.inS P.G.outS (L.ws cIN) (L.ws sGF1) L.oG1 L.hG1) P.G.M)
    (RecoveryFocus.machine (portSl P.G.inS P.G.outS (L.ws cIN) (L.ws sGF2) L.oG2 L.hG2) P.G.M))
    (RecoveryFocus.machine (portSl P.S.inS P.S.outS (L.ws cIN) (L.ws sSF) L.oS L.hS) P.S.M))
    (RecoveryFocus.machine (portSl P.W.inS P.W.outS (L.ws cIN) (L.ws sWF) L.oW L.hW) P.W.M))
    (RecoveryFocus.machine (portSl P.F.inS P.F.outS (L.ws cIN) (L.ws sFF1) L.oF1 L.hF1) P.F.M))
    (RecoveryFocus.machine (portSl P.F.inS P.F.outS (L.ws cIN) (L.ws sFF2) L.oF2 L.hF2) P.F.M))
    (RecoveryFocus.machine (portSl P.C.inS P.C.outS (L.ws cIN) (L.ws sCF1) L.oC1 L.hC1) P.C.M))
    (RecoveryFocus.machine (portSl P.C.inS P.C.outS (L.ws cIN) (L.ws sCF2) L.oC2 L.hC2) P.C.M)

/-- The streams after the writers. -/
def wrSt (st : Fin (CN + 1) → List Bool) (GF SF WF FF CF : List Bool) : Fin (CN + 1) → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update st sGF1 GF) sGF2 GF) sSF SF) sWF WF) sFF1 FF) sFF2 FF) sCF1 CF) sCF2 CF

/-- The writers' steps. -/
def wrCost (BG BS BW BF BC : ℕ) : ℕ := BG + 1 + BG + 1 + BS + 1 + BW + 1 + BF + 1 + BF + 1 + BC + 1 + BC

/-- **The writers' run**: each field from `frame w` on `cIN` to its streams. -/
theorem wr_run (w GF SF WF FF CF : List Bool) (BG BS BW BF BC : ℕ)
    (hG : WriterIfaceJ.WriterRun P.G.M BG P.G.inS P.G.outS w GF)
    (hS : WriterIfaceJ.WriterRun P.S.M BS P.S.inS P.S.outS w SF)
    (hW : WriterIfaceJ.WriterRun P.W.M BW P.W.inS P.W.outS w WF)
    (hF : WriterIfaceJ.WriterRun P.F.M BF P.F.inS P.F.outS w FF)
    (hC : WriterIfaceJ.WriterRun P.C.M BC P.C.inS P.C.outS w CF)
    (B : Fin (P.lay Ua Dv Cv).U → List Bool) (st : Fin (CN + 1) → List Bool)
    (hI : (P.lay Ua Dv Cv).Inv B st (P.lay Ua Dv Cv).oG1) (hin : st cIN = frame w)
    (h1 : st sGF1 = []) (h2 : st sGF2 = []) (h3 : st sSF = []) (h4 : st sWF = []) (h5 : st sFF1 = [])
    (h6 : st sFF2 = []) (h7 : st sCF1 = []) (h8 : st sCF2 = []) :
    ∃ B', Step (P.wrM Ua Dv Cv) (wrCost BG BS BW BF BC) (fun _ => 0) B (fun _ => 0) B' ∧
      (P.lay Ua Dv Cv).Inv B' (wrSt st GF SF WF FF CF) (P.lay Ua Dv Cv).oA := by
  have hWT : WT = 64 := rfl
  have hb := (P.lay Ua Dv Cv).offs
  obtain ⟨B1, s1, i1⟩ := (P.lay Ua Dv Cv).wstage P.G.hio hG sGF1 (by decide) (P.lay Ua Dv Cv).oG1 hb.1 (P.lay Ua Dv Cv).hG1 B st hI hin h1
  obtain ⟨B2, s2, i2⟩ := (P.lay Ua Dv Cv).wstage P.G.hio hG sGF2 (by decide) (P.lay Ua Dv Cv).oG2 (by omega) (P.lay Ua Dv Cv).hG2 B1 _ i1
    (by rw [Function.update_of_ne (by decide), hin]) (by rw [Function.update_of_ne (by decide), h2])
  obtain ⟨B3, s3, i3⟩ := (P.lay Ua Dv Cv).wstage P.S.hio hS sSF (by decide) (P.lay Ua Dv Cv).oS (by omega) (P.lay Ua Dv Cv).hS B2 _ i2
    (by simp only [Function.update_of_ne (show cIN ≠ sGF2 by decide), Function.update_of_ne (show cIN ≠ sGF1 by decide), hin])
    (by simp only [Function.update_of_ne (show sSF ≠ sGF2 by decide), Function.update_of_ne (show sSF ≠ sGF1 by decide), h3])
  obtain ⟨B4, s4, i4⟩ := (P.lay Ua Dv Cv).wstage P.W.hio hW sWF (by decide) (P.lay Ua Dv Cv).oW (by omega) (P.lay Ua Dv Cv).hW B3 _ i3
    (by simp only [Function.update_of_ne (show cIN ≠ sSF by decide), Function.update_of_ne (show cIN ≠ sGF2 by decide),
      Function.update_of_ne (show cIN ≠ sGF1 by decide), hin])
    (by simp only [Function.update_of_ne (show sWF ≠ sSF by decide), Function.update_of_ne (show sWF ≠ sGF2 by decide),
      Function.update_of_ne (show sWF ≠ sGF1 by decide), h4])
  obtain ⟨B5, s5, i5⟩ := (P.lay Ua Dv Cv).wstage P.F.hio hF sFF1 (by decide) (P.lay Ua Dv Cv).oF1 (by omega) (P.lay Ua Dv Cv).hF1 B4 _ i4
    (by simp only [Function.update_of_ne (show cIN ≠ sWF by decide), Function.update_of_ne (show cIN ≠ sSF by decide),
      Function.update_of_ne (show cIN ≠ sGF2 by decide), Function.update_of_ne (show cIN ≠ sGF1 by decide), hin])
    (by simp only [Function.update_of_ne (show sFF1 ≠ sWF by decide), Function.update_of_ne (show sFF1 ≠ sSF by decide),
      Function.update_of_ne (show sFF1 ≠ sGF2 by decide), Function.update_of_ne (show sFF1 ≠ sGF1 by decide), h5])
  obtain ⟨B6, s6, i6⟩ := (P.lay Ua Dv Cv).wstage P.F.hio hF sFF2 (by decide) (P.lay Ua Dv Cv).oF2 (by omega) (P.lay Ua Dv Cv).hF2 B5 _ i5
    (by simp only [Function.update_of_ne (show cIN ≠ sFF1 by decide), Function.update_of_ne (show cIN ≠ sWF by decide),
      Function.update_of_ne (show cIN ≠ sSF by decide), Function.update_of_ne (show cIN ≠ sGF2 by decide),
      Function.update_of_ne (show cIN ≠ sGF1 by decide), hin])
    (by simp only [Function.update_of_ne (show sFF2 ≠ sFF1 by decide), Function.update_of_ne (show sFF2 ≠ sWF by decide),
      Function.update_of_ne (show sFF2 ≠ sSF by decide), Function.update_of_ne (show sFF2 ≠ sGF2 by decide),
      Function.update_of_ne (show sFF2 ≠ sGF1 by decide), h6])
  obtain ⟨B7, s7, i7⟩ := (P.lay Ua Dv Cv).wstage P.C.hio hC sCF1 (by decide) (P.lay Ua Dv Cv).oC1 (by omega) (P.lay Ua Dv Cv).hC1 B6 _ i6
    (by simp only [Function.update_of_ne (show cIN ≠ sFF2 by decide), Function.update_of_ne (show cIN ≠ sFF1 by decide),
      Function.update_of_ne (show cIN ≠ sWF by decide), Function.update_of_ne (show cIN ≠ sSF by decide),
      Function.update_of_ne (show cIN ≠ sGF2 by decide), Function.update_of_ne (show cIN ≠ sGF1 by decide), hin])
    (by simp only [Function.update_of_ne (show sCF1 ≠ sFF2 by decide), Function.update_of_ne (show sCF1 ≠ sFF1 by decide),
      Function.update_of_ne (show sCF1 ≠ sWF by decide), Function.update_of_ne (show sCF1 ≠ sSF by decide),
      Function.update_of_ne (show sCF1 ≠ sGF2 by decide), Function.update_of_ne (show sCF1 ≠ sGF1 by decide), h7])
  obtain ⟨B8, s8, i8⟩ := (P.lay Ua Dv Cv).wstage P.C.hio hC sCF2 (by decide) (P.lay Ua Dv Cv).oC2 (by omega) (P.lay Ua Dv Cv).hC2 B7 _ i7
    (by simp only [Function.update_of_ne (show cIN ≠ sCF1 by decide), Function.update_of_ne (show cIN ≠ sFF2 by decide),
      Function.update_of_ne (show cIN ≠ sFF1 by decide), Function.update_of_ne (show cIN ≠ sWF by decide),
      Function.update_of_ne (show cIN ≠ sSF by decide), Function.update_of_ne (show cIN ≠ sGF2 by decide),
      Function.update_of_ne (show cIN ≠ sGF1 by decide), hin])
    (by simp only [Function.update_of_ne (show sCF2 ≠ sCF1 by decide), Function.update_of_ne (show sCF2 ≠ sFF2 by decide),
      Function.update_of_ne (show sCF2 ≠ sFF1 by decide), Function.update_of_ne (show sCF2 ≠ sWF by decide),
      Function.update_of_ne (show sCF2 ≠ sSF by decide), Function.update_of_ne (show sCF2 ≠ sGF2 by decide),
      Function.update_of_ne (show sCF2 ≠ sGF1 by decide), h8])
  exact ⟨B8, Step.seq (Step.seq (Step.seq (Step.seq (Step.seq (Step.seq (Step.seq s1 s2) s3) s4) s5) s6) s7) s8, i8⟩

end Wr5

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
