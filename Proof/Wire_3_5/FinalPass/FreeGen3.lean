import Proof.Wire_3_5.FinalPass.FreeGen2

/-! # The free numbers' program, part 2: the program `freeW κ` and its run

**`freeW κ`** (C5's word language on the numbers program's layout `LNS 0`, `LNR`): from the call's numbers in their
registers (`n` in `dN`, `kh` in `SGb 8`, `nc` in `dNC`, `a` in `dA`, `M` in `dMS`), `β` (`betaW`), `β²`, `β⁴`, `β⁶`
(`sqW`, `mulW`), the constant multiples (`cmulW`), `Cap = 2^{dC·β²}` (`pow2W`), the walk length `W` (`SymQM.wlW`), the
factor count `m` (`mW`) and the pad's exponent `ρ` (`rhoW`), into the free numbers' block `FB` (registers
`130 … 136`), on the scratch `177 … 199`. **`freeW_run`**: the block `FB` holds `freeVal κ x`, every register off
`130 … 136` and `177 … 199` and every stream, head and the cell as they were, within `200` units at any capacity above
**`need κ x`**.

Paper quantity of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.SymQM NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- **The program's registers**: `FB` (`0 … 6`), the scratch `177 … 199` (`7 … 29`), the numbers read (`30 … 34`:
`dN`, `SGb 8`, `dNC`, `dA`, `dMS`). -/
def Gall : Fin 35 ↪ Fin LNR := ⟨![⟨130, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩, ⟨133, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨179, by decide⟩, ⟨180, by decide⟩, ⟨181, by decide⟩, ⟨182, by decide⟩, ⟨183, by decide⟩, ⟨184, by decide⟩, ⟨185, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨188, by decide⟩, ⟨189, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨192, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨320, by decide⟩, ⟨258, by decide⟩, ⟨322, by decide⟩, ⟨321, by decide⟩, ⟨334, by decide⟩], by decide⟩

def eB : Fin 11 ↪ Fin 35 := ⟨![30, 8, 7, 9, 10, 11, 12, 13, 14, 15, 16], by decide⟩
@[simp] theorem eB_apply (i : Fin 11) : eB i = ![30, 8, 7, 9, 10, 11, 12, 13, 14, 15, 16] i := rfl
def eS1 : Fin 5 ↪ Fin 35 := ⟨![8, 17, 26, 27, 28], by decide⟩
@[simp] theorem eS1_apply (i : Fin 5) : eS1 i = ![8, 17, 26, 27, 28] i := rfl
def eS2 : Fin 5 ↪ Fin 35 := ⟨![17, 18, 26, 27, 28], by decide⟩
@[simp] theorem eS2_apply (i : Fin 5) : eS2 i = ![17, 18, 26, 27, 28] i := rfl
def eM3 : Fin 6 ↪ Fin 35 := ⟨![18, 17, 19, 26, 27, 28], by decide⟩
@[simp] theorem eM3_apply (i : Fin 6) : eM3 i = ![18, 17, 19, 26, 27, 28] i := rfl
def eT : Fin 5 ↪ Fin 35 := ⟨![17, 0, 26, 27, 28], by decide⟩
@[simp] theorem eT_apply (i : Fin 5) : eT i = ![17, 0, 26, 27, 28] i := rfl
def eQ : Fin 5 ↪ Fin 35 := ⟨![17, 2, 26, 27, 28], by decide⟩
@[simp] theorem eQ_apply (i : Fin 5) : eQ i = ![17, 2, 26, 27, 28] i := rfl
def eH : Fin 5 ↪ Fin 35 := ⟨![17, 3, 26, 27, 28], by decide⟩
@[simp] theorem eH_apply (i : Fin 5) : eH i = ![17, 3, 26, 27, 28] i := rfl
def eP : Fin 5 ↪ Fin 35 := ⟨![19, 5, 26, 27, 28], by decide⟩
@[simp] theorem eP_apply (i : Fin 5) : eP i = ![19, 5, 26, 27, 28] i := rfl
def eC : Fin 5 ↪ Fin 35 := ⟨![17, 20, 26, 27, 28], by decide⟩
@[simp] theorem eC_apply (i : Fin 5) : eC i = ![17, 20, 26, 27, 28] i := rfl
def eW2 : Fin 4 ↪ Fin 35 := ⟨![20, 1, 26, 27], by decide⟩
@[simp] theorem eW2_apply (i : Fin 4) : eW2 i = ![20, 1, 26, 27] i := rfl
def eL : Fin 10 ↪ Fin 35 := ⟨![8, 21, 26, 27, 28, 29, 9, 10, 11, 12], by decide⟩
@[simp] theorem eL_apply (i : Fin 10) : eL i = ![8, 21, 26, 27, 28, 29, 9, 10, 11, 12] i := rfl
def eMm : Fin 9 ↪ Fin 35 := ⟨![23, 24, 21, 25, 4, 26, 27, 28, 29], by decide⟩
@[simp] theorem eMm_apply (i : Fin 9) : eMm i = ![23, 24, 21, 25, 4, 26, 27, 28, 29] i := rfl
def eR : Fin 14 ↪ Fin 35 := ⟨![30, 22, 8, 17, 6, 26, 27, 28, 29, 9, 10, 11, 12, 13], by decide⟩
@[simp] theorem eR_apply (i : Fin 14) : eR i = ![30, 22, 8, 17, 6, 26, 27, 28, 29, 9, 10, 11, 12, 13] i := rfl

/-- **The free numbers' program.** -/
def freeW (κ : FreeK) : WM (LNS 0) LNR :=
  (.seq (betaW (eB.trans Gall))
    (.seq (sqW (eS1.trans Gall))
    (.seq (sqW (eS2.trans Gall))
    (.seq (mulW (eM3.trans Gall))
    (.seq (cmulW κ.dT (eT.trans Gall))
    (.seq (cmulW κ.dQ (eQ.trans Gall))
    (.seq (cmulW κ.dH (eH.trans Gall))
    (.seq (cmulW κ.dP (eP.trans Gall))
    (.seq (cmulW κ.dC (eC.trans Gall))
    (.seq (pow2W (eW2.trans Gall))
    (.seq (wlW (eL.trans Gall))
    (.seq (FinalPass.Hash4.wcopyR (Gall 31) (Gall 22) (Gall 26))
    (.seq (FinalPass.Hash4.wcopyR (Gall 32) (Gall 23) (Gall 26))
    (.seq (FinalPass.Hash4.wcopyR (Gall 33) (Gall 24) (Gall 26))
    (.seq (FinalPass.Hash4.wcopyR (Gall 34) (Gall 25) (Gall 26))
    (.seq (mW κ.mA κ.mB κ.mC κ.mD κ.mF κ.mE (eMm.trans Gall))
    (rhoW κ.dA κ.dR (eR.trans Gall))))))))))))))))))

/-- **The capacity the program needs.** -/
def need (κ : FreeK) (x : FreeIn) : ℕ :=
  (x.n + 4) + x.kh + x.nc + x.a + x.M + (β x + 8) + β x * β x + β x * β x * (β x * β x) +
    β x * β x * (β x * β x) * (β x * β x) + κ.dT * (β x * β x) + κ.dQ * (β x * β x) + κ.dH * (β x * β x) +
    κ.dP * (β x * β x * (β x * β x) * (β x * β x)) + κ.dC * (β x * β x) + 2 ^ (κ.dC * (β x * β x) + 1) +
    (κ.mA + κ.mB + κ.mC + κ.mD + κ.mF + W x + x.a * W x +
      (κ.mA * x.nc + κ.mB * (x.a * W x) + κ.mC * W x + κ.mD * x.a + κ.mF * x.M + κ.mE)) +
    (κ.dA + κ.dR + κ.dA * β x + κ.dR * (β x * β x)) + (κ.dT + κ.dQ + κ.dH + κ.dP + κ.dC) + 1

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

