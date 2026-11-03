import Proof.Wire_3_5.Primitive.Writers.SBTypesBase
import Proof.Wire_3_5.Primitive.Writers.SBHi

/-! # SB, part (1): the register program P1

From the state after the carrier pipeline (the request on `I`, `1^{c0}`, `1^{c1}`, `1^{nc}` on the count
streams, the output streams `O6`, `O7` blank, every register `0`), P1 reads `n` and the mode bit, reads the three
counts, runs the eight phases of `SBNums`, and emits S4's words `6` (`1^{e/4+1} 0`) and `7` (`unaryList sbList`):

* `p1_pre`, `p1_mid1`, `sp_vals`, `p1_mid2`, `sx_vals`, `LR`, `p1_emit`, `p1W` (the parts; `p1_run` in the next
  module).

Paper quantities of the main types: S4's words `6`, `7` (the walk's threshold, `s4Small2`, P3:3170-3181) and the
field width `ℓ` (`GapParams.fieldBits`, P3:2039-2054). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.PrimAsm.SBParse NearCubicWires.WireExponent3_5.PrimAsm.SBEmit
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes

section Run
variable {ns : ℕ} (cap : ℕ)

/-- Slot `7`'s registers, in `sbList`'s order. -/
def LR : List (Fin NRB) := [92, 21, 20, 22, 41, 42, 23, 43, 39, 89, 90, 49, 88, 38, 69, 26]

/-- Parse and the three counts. -/
theorem p1_pre (I S0 S1 S6 : Fin (ns + 1)) (P : Shared.StarParams) (m : Mode) (codes cc : List ℕ) (tl : List Bool)
    (c0 c1 nc : ℕ) (σ : WState ns NRB)
    (hI : σ.st I = frame (Data.reqW P.n (Codec.modeBit m) codes cc tl)) (hIh : σ.sh I = 0)
    (hS0 : σ.st S0 = List.replicate c0 true) (hS0h : σ.sh S0 = 0)
    (hS1 : σ.st S1 = List.replicate c1 true) (hS1h : σ.sh S1 = 0)
    (hS6 : σ.st S6 = List.replicate nc true) (hS6h : σ.sh S6 = 0) (hv : ∀ q, σ.val q = 0)
    (hc : 2 * (Data.reqW P.n (Codec.modeBit m) codes cc tl).length ≤ cap) (hcn : 2 ^ (natBitLength P.n + 1) ≤ cap)
    (hc0 : c0 + 1 ≤ cap) (hc1 : c1 + 1 ≤ cap) (hnc : nc + 1 ≤ cap) :
    WExec cap (.seq (parseW I) (.seq (countW S0 93 89) (.seq (countW S1 93 90) (countW S6 93 88)))) σ
      (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc)
      (parseCost cap (Data.reqW P.n (Codec.modeBit m) codes cc tl).length P.n + 1 +
        ((11 * c0 + 7 + 1 + (5 * (c0 + 1) + 1)) + 1 + ((11 * c1 + 7 + 1 + (5 * (c1 + 1) + 1)) + 1 +
          (11 * nc + 7 + 1 + (5 * (nc + 1) + 1))))) := by
  have e1 := parse_spec cap I P.n (Codec.modeBit m) codes cc tl σ hI hIh (hv _) (hv _) (hv _) (hv _) (hv _) (hv _)
    (hv _) (hv _) (hv _) hc hcn
  have e2 := count_spec cap S0 93 89 (by decide) c0 ((σ.setv 16 P.n).setv 60 (mbOf m)) hS0 hS0h
    (by simp [Function.update_apply, hv]) (by simp [Function.update_apply, hv]) hc0
  have e3 := count_spec cap S1 93 90 (by decide) c1 (((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0) hS1 hS1h
    (by simp [Function.update_apply, hv]) (by simp [Function.update_apply, hv]) hc1
  have e4 := count_spec cap S6 93 88 (by decide) nc ((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1) hS6
    hS6h (by simp [Function.update_apply, hv]) (by simp [Function.update_apply, hv]) hnc
  exact WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))

/-- Phases A, B1, B2a. -/
theorem p1_mid1 (cr : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (hrP : P.r = Ledger.rowBr cr P.n) (mb c0 c1 nc : ℕ) (σ : WState ns NRB)
    (hv : ∀ q, σ.val q = 0) (hm : decide (mb ≠ 0) = Codec.modeBit m)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : SymDec.CapNeed C m P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ cap) (hpw : (P.n + 1) ^ 26 ≤ cap)
    (t1 : tB1 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ cap) (t2 : tB2a P h0 h1 Cδ C m fe mb nc c0 c1 ≤ cap) :
    WExec cap (.seq (aW cr fe ζ Cδ C) (.seq b1W b2aW)) (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe)
      (aCost cap P h0 h1 Cδ C m fe cr + 1 + (b1Cost cap P h0 h1 Cδ C m fe + 1 + b2aCost cap P h0 h1 Cδ C m fe)) := by
  have h4z : ∀ r : Fin NRB, r ≠ 16 → r ≠ 60 → r ≠ 88 → r ≠ 89 → r ≠ 90 → (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc).val r = 0 := by
    intro r a b c d e
    simp [Function.update_apply, a, b, c, d, e, hv]
  have e_a := a_run cap cr h0 h1 Cδ C m fe P hrP (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) (by simp [Function.update_apply])
    (by rw [show (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc).val (60 : Fin NRB) = mb by simp [Function.update_apply]]; exact hm) h4z hcS hcP hcC hlam
  obtain ⟨a16, a17, a19, a20, a21, a22, a23, a24, a25, a26, a60, a69, a88, a89, a90, az36, az37, az38, az39, az40, az41, az42, az43, az44, az45, az46, az47, az48, az49, az50, az51, az52, az53, az54, az55, az56, az57, az58, az59, az91, az92, az96⟩ := a_vals P h0 h1 Cδ C m fe (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) mb nc c0 c1 (by simp [Function.update_apply])
    (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply]) h4z
  have e_b1 := b1_run cap P h0 h1 Cδ C m fe (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) mb nc c0 c1 a16 a17 a19 a20 a21 a22 a23 a24 a25 a26 a60 a69 a88 a89 a90 az36 az37 az38 az39 az40 az41 az42 az43 az44 az45 az46 az47 az48 az49 az50 az51 az52 az53 az54 az55 az56 az57 az58 az59 az91 az92 az96 hpw t1
  obtain ⟨b16, b17, b19, b20, b21, b22, b23, b24, b25, b26, b60, b69, b88, b89, b90, b38, b43, b44, b45, b96, bz36, bz37, bz39, bz40, bz41, bz42, bz46, bz47, bz48, bz49, bz50, bz51, bz52, bz53, bz54, bz55, bz56, bz57, bz58, bz59, bz91, bz92⟩ := b1_vals P h0 h1 Cδ C m fe (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) mb nc c0 c1 a16 a17 a19 a20 a21 a22 a23 a24 a25 a26 a60 a69 a88 a89 a90 az36 az37 az38 az39 az40 az41 az42 az43 az44 az45 az46 az47 az48 az49 az50 az51 az52 az53 az54 az55 az56 az57 az58 az59 az91 az92 az96
  have e_b2a := b2a_run cap P h0 h1 Cδ C m fe (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 b16 b17 b19 b20 b21 b22 b23 b24 b25 b26 b60 b69 b88 b89 b90 b38 b43 b44 b45 b96 bz36 bz37 bz39 bz40 bz41 bz42 bz46 bz47 bz48 bz49 bz50 bz51 bz52 bz53 bz54 bz55 bz56 bz57 bz58 bz59 bz91 bz92 t2
  exact WExec.seq e_a (WExec.seq e_b1 e_b2a)

/-- The registers after phase B2a. -/
theorem sp_vals (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb c0 c1 nc : ℕ) (σ : WState ns NRB) (hv : ∀ q, σ.val q = 0) :
    (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((16 : Fin NRB)) = P.n ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((17 : Fin NRB)) = Nat.clog 2 (P.n + 2) ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((19 : Fin NRB)) = P.r ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((20 : Fin NRB)) = P.s ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((21 : Fin NRB)) = P.b ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((22 : Fin NRB)) = P.r / 2 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((23 : Fin NRB)) = P.n - P.r * P.b ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((24 : Fin NRB)) = P.s * (P.r / 2) ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((25 : Fin NRB)) = P.k ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((26 : Fin NRB)) = fe * Nat.clog 2 (P.n + 2) ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((60 : Fin NRB)) = mb ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((69 : Fin NRB)) = Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((88 : Fin NRB)) = nc ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((89 : Fin NRB)) = c0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((90 : Fin NRB)) = c1 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((38 : Fin NRB)) = (((P.n) + (1)) ^ 26) * (2) ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((96 : Fin NRB)) = (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4) ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((48 : Fin NRB)) = (((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((36 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((37 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((39 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((40 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((41 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((42 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((43 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((44 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((45 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((46 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((47 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((49 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((50 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((51 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((52 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((53 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((54 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((55 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((56 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((57 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((58 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((59 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((91 : Fin NRB)) = 0 ∧ (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe).val ((92 : Fin NRB)) = 0 := by
  have h4z : ∀ r : Fin NRB, r ≠ 16 → r ≠ 60 → r ≠ 88 → r ≠ 89 → r ≠ 90 → (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc).val r = 0 := by
    intro r a b c d e
    simp [Function.update_apply, a, b, c, d, e, hv]
  obtain ⟨a16, a17, a19, a20, a21, a22, a23, a24, a25, a26, a60, a69, a88, a89, a90, az36, az37, az38, az39, az40, az41, az42, az43, az44, az45, az46, az47, az48, az49, az50, az51, az52, az53, az54, az55, az56, az57, az58, az59, az91, az92, az96⟩ := a_vals P h0 h1 Cδ C m fe (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) mb nc c0 c1 (by simp [Function.update_apply])
    (by simp [Function.update_apply]) (by simp [Function.update_apply]) (by simp [Function.update_apply])
    (by simp [Function.update_apply]) h4z
  obtain ⟨b16, b17, b19, b20, b21, b22, b23, b24, b25, b26, b60, b69, b88, b89, b90, b38, b43, b44, b45, b96, bz36, bz37, bz39, bz40, bz41, bz42, bz46, bz47, bz48, bz49, bz50, bz51, bz52, bz53, bz54, bz55, bz56, bz57, bz58, bz59, bz91, bz92⟩ := b1_vals P h0 h1 Cδ C m fe (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) mb nc c0 c1 a16 a17 a19 a20 a21 a22 a23 a24 a25 a26 a60 a69 a88 a89 a90 az36 az37 az38 az39 az40 az41 az42 az43 az44 az45 az46 az47 az48 az49 az50 az51 az52 az53 az54 az55 az56 az57 az58 az59 az91 az92 az96
  exact b2a_vals P h0 h1 Cδ C m fe (b1Out (aOut (((((σ.setv 16 P.n).setv 60 mb).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 b16 b17 b19 b20 b21 b22 b23 b24 b25 b26 b60 b69 b88 b89 b90 b38 b43 b44 b45 b96 bz36 bz37 bz39 bz40 bz41 bz42 bz46 bz47 bz48 bz49 bz50 bz51 bz52 bz53 bz54 bz55 bz56 bz57 bz58 bz59 bz91 bz92

/-- Phases B2b … C3 from B2a's registers. -/
theorem p1_mid2 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) (σ : WState ns NRB) (p16 : σ.val ((16 : Fin NRB)) = P.n) (p17 : σ.val ((17 : Fin NRB)) = Nat.clog 2 (P.n + 2)) (p19 : σ.val ((19 : Fin NRB)) = P.r) (p20 : σ.val ((20 : Fin NRB)) = P.s) (p21 : σ.val ((21 : Fin NRB)) = P.b) (p22 : σ.val ((22 : Fin NRB)) = P.r / 2) (p23 : σ.val ((23 : Fin NRB)) = P.n - P.r * P.b) (p24 : σ.val ((24 : Fin NRB)) = P.s * (P.r / 2)) (p25 : σ.val ((25 : Fin NRB)) = P.k) (p26 : σ.val ((26 : Fin NRB)) = fe * Nat.clog 2 (P.n + 2)) (p60 : σ.val ((60 : Fin NRB)) = mb) (p69 : σ.val ((69 : Fin NRB)) = Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (p88 : σ.val ((88 : Fin NRB)) = nc) (p89 : σ.val ((89 : Fin NRB)) = c0) (p90 : σ.val ((90 : Fin NRB)) = c1) (p38 : σ.val ((38 : Fin NRB)) = (((P.n) + (1)) ^ 26) * (2)) (p96 : σ.val ((96 : Fin NRB)) = (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) (p48 : σ.val ((48 : Fin NRB)) = (((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) (pz36 : σ.val ((36 : Fin NRB)) = 0) (pz37 : σ.val ((37 : Fin NRB)) = 0) (pz39 : σ.val ((39 : Fin NRB)) = 0) (pz40 : σ.val ((40 : Fin NRB)) = 0) (pz41 : σ.val ((41 : Fin NRB)) = 0) (pz42 : σ.val ((42 : Fin NRB)) = 0) (pz43 : σ.val ((43 : Fin NRB)) = 0) (pz44 : σ.val ((44 : Fin NRB)) = 0) (pz45 : σ.val ((45 : Fin NRB)) = 0) (pz46 : σ.val ((46 : Fin NRB)) = 0) (pz47 : σ.val ((47 : Fin NRB)) = 0) (pz49 : σ.val ((49 : Fin NRB)) = 0) (pz50 : σ.val ((50 : Fin NRB)) = 0) (pz51 : σ.val ((51 : Fin NRB)) = 0) (pz52 : σ.val ((52 : Fin NRB)) = 0) (pz53 : σ.val ((53 : Fin NRB)) = 0) (pz54 : σ.val ((54 : Fin NRB)) = 0) (pz55 : σ.val ((55 : Fin NRB)) = 0) (pz56 : σ.val ((56 : Fin NRB)) = 0) (pz57 : σ.val ((57 : Fin NRB)) = 0) (pz58 : σ.val ((58 : Fin NRB)) = 0) (pz59 : σ.val ((59 : Fin NRB)) = 0) (pz91 : σ.val ((91 : Fin NRB)) = 0) (pz92 : σ.val ((92 : Fin NRB)) = 0)
    (t3 : tB2b P h0 h1 Cδ C m fe mb nc c0 c1 ≤ cap) (t4 : tB2c P h0 h1 Cδ C m fe mb nc c0 c1 ≤ cap) (t5 : tC1 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ cap) (t6 : tC2 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ cap)
    (t7 : tC3 P h0 h1 Cδ C m fe mb nc c0 c1 ≤ cap) :
    WExec cap (.seq b2bW (.seq b2cW (.seq c1W (.seq c2W c3W)))) σ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1)
      (b2bCost cap P h0 h1 Cδ C m fe + 1 + (b2cCost cap P h0 h1 Cδ C m fe + 1 + (c1Cost cap P h0 h1 Cδ C m fe + 1 + (c2Cost cap P h0 h1 Cδ C m fe + 1 + c3Cost cap P h0 h1 Cδ C m fe)))) := by
  have e_b2b := b2b_run cap P h0 h1 Cδ C m fe σ mb nc c0 c1 p16 p17 p19 p20 p21 p22 p23 p24 p25 p26 p60 p69 p88 p89 p90 p38 p96 p48 pz36 pz37 pz39 pz40 pz41 pz42 pz43 pz44 pz45 pz46 pz47 pz49 pz50 pz51 pz52 pz53 pz54 pz55 pz56 pz57 pz58 pz59 pz91 pz92 t3
  obtain ⟨q16, q17, q19, q20, q21, q22, q23, q24, q25, q26, q60, q69, q88, q89, q90, q38, q96, q48, q49, q91, qz36, qz37, qz39, qz40, qz41, qz42, qz43, qz44, qz45, qz46, qz47, qz50, qz51, qz52, qz53, qz54, qz55, qz56, qz57, qz58, qz59, qz92⟩ := b2b_vals P h0 h1 Cδ C m fe σ mb nc c0 c1 p16 p17 p19 p20 p21 p22 p23 p24 p25 p26 p60 p69 p88 p89 p90 p38 p96 p48 pz36 pz37 pz39 pz40 pz41 pz42 pz43 pz44 pz45 pz46 pz47 pz49 pz50 pz51 pz52 pz53 pz54 pz55 pz56 pz57 pz58 pz59 pz91 pz92
  have e_b2c := b2c_run cap P h0 h1 Cδ C m fe (b2bOut σ P h0 h1 Cδ C m fe) mb nc c0 c1 q16 q17 q19 q20 q21 q22 q23 q24 q25 q26 q60 q69 q88 q89 q90 q38 q96 q48 q49 q91 qz36 qz37 qz39 qz40 qz41 qz42 qz43 qz44 qz45 qz46 qz47 qz50 qz51 qz52 qz53 qz54 qz55 qz56 qz57 qz58 qz59 qz92 t4
  obtain ⟨u16, u17, u19, u20, u21, u22, u23, u24, u25, u26, u60, u69, u88, u89, u90, u38, u96, u91, u49, uz36, uz37, uz39, uz40, uz41, uz42, uz43, uz44, uz45, uz46, uz47, uz48, uz50, uz51, uz52, uz53, uz54, uz55, uz56, uz57, uz58, uz59, uz92⟩ := b2c_vals P h0 h1 Cδ C m fe (b2bOut σ P h0 h1 Cδ C m fe) mb nc c0 c1 q16 q17 q19 q20 q21 q22 q23 q24 q25 q26 q60 q69 q88 q89 q90 q38 q96 q48 q49 q91 qz36 qz37 qz39 qz40 qz41 qz42 qz43 qz44 qz45 qz46 qz47 qz50 qz51 qz52 qz53 qz54 qz55 qz56 qz57 qz58 qz59 qz92
  have e_c1 := c1_run cap P h0 h1 Cδ C m fe (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 u16 u17 u19 u20 u21 u22 u23 u24 u25 u26 u60 u69 u88 u89 u90 u38 u96 u91 u49 uz36 uz37 uz39 uz40 uz41 uz42 uz43 uz44 uz45 uz46 uz47 uz48 uz50 uz51 uz52 uz53 uz54 uz55 uz56 uz57 uz58 uz59 uz92 t5
  obtain ⟨v16, v17, v19, v20, v21, v22, v23, v24, v25, v26, v60, v69, v88, v89, v90, v38, v96, v91, v49, v41, v42, vz36, vz37, vz39, vz40, vz43, vz44, vz45, vz46, vz47, vz48, vz50, vz51, vz52, vz53, vz54, vz55, vz56, vz57, vz58, vz59, vz92⟩ := c1_vals P h0 h1 Cδ C m fe (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 u16 u17 u19 u20 u21 u22 u23 u24 u25 u26 u60 u69 u88 u89 u90 u38 u96 u91 u49 uz36 uz37 uz39 uz40 uz41 uz42 uz43 uz44 uz45 uz46 uz47 uz48 uz50 uz51 uz52 uz53 uz54 uz55 uz56 uz57 uz58 uz59 uz92
  have e_c2 := c2_run cap P h0 h1 Cδ C m fe (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 v16 v17 v19 v20 v21 v22 v23 v24 v25 v26 v60 v69 v88 v89 v90 v38 v96 v91 v49 v41 v42 vz36 vz37 vz39 vz40 vz43 vz44 vz45 vz46 vz47 vz48 vz50 vz51 vz52 vz53 vz54 vz55 vz56 vz57 vz58 vz59 vz92 t6
  obtain ⟨w16, w17, w19, w20, w21, w22, w23, w24, w25, w26, w60, w69, w88, w89, w90, w38, w96, w91, w49, w41, w42, w43, w39, wz36, wz37, wz40, wz44, wz45, wz46, wz47, wz48, wz50, wz51, wz52, wz53, wz54, wz55, wz56, wz57, wz58, wz59, wz92⟩ := c2_vals P h0 h1 Cδ C m fe (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 v16 v17 v19 v20 v21 v22 v23 v24 v25 v26 v60 v69 v88 v89 v90 v38 v96 v91 v49 v41 v42 vz36 vz37 vz39 vz40 vz43 vz44 vz45 vz46 vz47 vz48 vz50 vz51 vz52 vz53 vz54 vz55 vz56 vz57 vz58 vz59 vz92
  have e_c3 := c3_run cap P h0 h1 Cδ C m fe (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 w16 w17 w19 w20 w21 w22 w23 w24 w25 w26 w60 w69 w88 w89 w90 w38 w96 w91 w49 w41 w42 w43 w39 wz36 wz37 wz40 wz44 wz45 wz46 wz47 wz48 wz50 wz51 wz52 wz53 wz54 wz55 wz56 wz57 wz58 wz59 wz92 t7
  exact WExec.seq e_b2b (WExec.seq e_b2c (WExec.seq e_c1 (WExec.seq e_c2 e_c3)))

/-- The registers after phase C3 that P1 emits (slot `7`, the threshold, `ℓ`). -/
theorem sx_vals (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) (σ : WState ns NRB) (p16 : σ.val ((16 : Fin NRB)) = P.n) (p17 : σ.val ((17 : Fin NRB)) = Nat.clog 2 (P.n + 2)) (p19 : σ.val ((19 : Fin NRB)) = P.r) (p20 : σ.val ((20 : Fin NRB)) = P.s) (p21 : σ.val ((21 : Fin NRB)) = P.b) (p22 : σ.val ((22 : Fin NRB)) = P.r / 2) (p23 : σ.val ((23 : Fin NRB)) = P.n - P.r * P.b) (p24 : σ.val ((24 : Fin NRB)) = P.s * (P.r / 2)) (p25 : σ.val ((25 : Fin NRB)) = P.k) (p26 : σ.val ((26 : Fin NRB)) = fe * Nat.clog 2 (P.n + 2)) (p60 : σ.val ((60 : Fin NRB)) = mb) (p69 : σ.val ((69 : Fin NRB)) = Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (p88 : σ.val ((88 : Fin NRB)) = nc) (p89 : σ.val ((89 : Fin NRB)) = c0) (p90 : σ.val ((90 : Fin NRB)) = c1) (p38 : σ.val ((38 : Fin NRB)) = (((P.n) + (1)) ^ 26) * (2)) (p96 : σ.val ((96 : Fin NRB)) = (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) (p48 : σ.val ((48 : Fin NRB)) = (((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) (pz36 : σ.val ((36 : Fin NRB)) = 0) (pz37 : σ.val ((37 : Fin NRB)) = 0) (pz39 : σ.val ((39 : Fin NRB)) = 0) (pz40 : σ.val ((40 : Fin NRB)) = 0) (pz41 : σ.val ((41 : Fin NRB)) = 0) (pz42 : σ.val ((42 : Fin NRB)) = 0) (pz43 : σ.val ((43 : Fin NRB)) = 0) (pz44 : σ.val ((44 : Fin NRB)) = 0) (pz45 : σ.val ((45 : Fin NRB)) = 0) (pz46 : σ.val ((46 : Fin NRB)) = 0) (pz47 : σ.val ((47 : Fin NRB)) = 0) (pz49 : σ.val ((49 : Fin NRB)) = 0) (pz50 : σ.val ((50 : Fin NRB)) = 0) (pz51 : σ.val ((51 : Fin NRB)) = 0) (pz52 : σ.val ((52 : Fin NRB)) = 0) (pz53 : σ.val ((53 : Fin NRB)) = 0) (pz54 : σ.val ((54 : Fin NRB)) = 0) (pz55 : σ.val ((55 : Fin NRB)) = 0) (pz56 : σ.val ((56 : Fin NRB)) = 0) (pz57 : σ.val ((57 : Fin NRB)) = 0) (pz58 : σ.val ((58 : Fin NRB)) = 0) (pz59 : σ.val ((59 : Fin NRB)) = 0) (pz91 : σ.val ((91 : Fin NRB)) = 0) (pz92 : σ.val ((92 : Fin NRB)) = 0) :
    (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((92 : Fin NRB)) = 1 ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((21 : Fin NRB)) = P.b ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((20 : Fin NRB)) = P.s ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((22 : Fin NRB)) = P.r / 2 ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((41 : Fin NRB)) = ((P.n - P.r * P.b) + (1)) / (2) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((42 : Fin NRB)) = (P.n - P.r * P.b) / (2) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((23 : Fin NRB)) = P.n - P.r * P.b ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((43 : Fin NRB)) = (((P.b) - (P.s)) * (P.r / 2)) + (((P.n - P.r * P.b) + (1)) / (2)) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((39 : Fin NRB)) = (((P.b) - (P.s)) * (P.r / 2)) + ((P.n - P.r * P.b) / (2)) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((89 : Fin NRB)) = (c0) * (2) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((90 : Fin NRB)) = (c1) * (2) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((49 : Fin NRB)) = (((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256)) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((88 : Fin NRB)) = nc ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((38 : Fin NRB)) = (((P.n) + (1)) ^ 26) * (2) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((69 : Fin NRB)) = Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((26 : Fin NRB)) = fe * Nat.clog 2 (P.n + 2) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((91 : Fin NRB)) = ((fe * Nat.clog 2 (P.n + 2)) / (4)) + (1) ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val ((96 : Fin NRB)) = (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4) := by
  obtain ⟨q16, q17, q19, q20, q21, q22, q23, q24, q25, q26, q60, q69, q88, q89, q90, q38, q96, q48, q49, q91, qz36, qz37, qz39, qz40, qz41, qz42, qz43, qz44, qz45, qz46, qz47, qz50, qz51, qz52, qz53, qz54, qz55, qz56, qz57, qz58, qz59, qz92⟩ := b2b_vals P h0 h1 Cδ C m fe σ mb nc c0 c1 p16 p17 p19 p20 p21 p22 p23 p24 p25 p26 p60 p69 p88 p89 p90 p38 p96 p48 pz36 pz37 pz39 pz40 pz41 pz42 pz43 pz44 pz45 pz46 pz47 pz49 pz50 pz51 pz52 pz53 pz54 pz55 pz56 pz57 pz58 pz59 pz91 pz92
  obtain ⟨u16, u17, u19, u20, u21, u22, u23, u24, u25, u26, u60, u69, u88, u89, u90, u38, u96, u91, u49, uz36, uz37, uz39, uz40, uz41, uz42, uz43, uz44, uz45, uz46, uz47, uz48, uz50, uz51, uz52, uz53, uz54, uz55, uz56, uz57, uz58, uz59, uz92⟩ := b2c_vals P h0 h1 Cδ C m fe (b2bOut σ P h0 h1 Cδ C m fe) mb nc c0 c1 q16 q17 q19 q20 q21 q22 q23 q24 q25 q26 q60 q69 q88 q89 q90 q38 q96 q48 q49 q91 qz36 qz37 qz39 qz40 qz41 qz42 qz43 qz44 qz45 qz46 qz47 qz50 qz51 qz52 qz53 qz54 qz55 qz56 qz57 qz58 qz59 qz92
  obtain ⟨v16, v17, v19, v20, v21, v22, v23, v24, v25, v26, v60, v69, v88, v89, v90, v38, v96, v91, v49, v41, v42, vz36, vz37, vz39, vz40, vz43, vz44, vz45, vz46, vz47, vz48, vz50, vz51, vz52, vz53, vz54, vz55, vz56, vz57, vz58, vz59, vz92⟩ := c1_vals P h0 h1 Cδ C m fe (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 u16 u17 u19 u20 u21 u22 u23 u24 u25 u26 u60 u69 u88 u89 u90 u38 u96 u91 u49 uz36 uz37 uz39 uz40 uz41 uz42 uz43 uz44 uz45 uz46 uz47 uz48 uz50 uz51 uz52 uz53 uz54 uz55 uz56 uz57 uz58 uz59 uz92
  obtain ⟨w16, w17, w19, w20, w21, w22, w23, w24, w25, w26, w60, w69, w88, w89, w90, w38, w96, w91, w49, w41, w42, w43, w39, wz36, wz37, wz40, wz44, wz45, wz46, wz47, wz48, wz50, wz51, wz52, wz53, wz54, wz55, wz56, wz57, wz58, wz59, wz92⟩ := c2_vals P h0 h1 Cδ C m fe (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 v16 v17 v19 v20 v21 v22 v23 v24 v25 v26 v60 v69 v88 v89 v90 v38 v96 v91 v49 v41 v42 vz36 vz37 vz39 vz40 vz43 vz44 vz45 vz46 vz47 vz48 vz50 vz51 vz52 vz53 vz54 vz55 vz56 vz57 vz58 vz59 vz92
  obtain ⟨x16, x17, x19, x20, x21, x22, x23, x24, x25, x26, x60, x69, x88, x38, x96, x91, x49, x41, x42, x43, x39, x89, x90, x92, xz36, xz37, xz40, xz44, xz45, xz46, xz47, xz48, xz50, xz51, xz52, xz53, xz54, xz55, xz56, xz57, xz58, xz59⟩ := c3_vals P h0 h1 Cδ C m fe (c2Out (c1Out (b2cOut (b2bOut σ P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) mb nc c0 c1 w16 w17 w19 w20 w21 w22 w23 w24 w25 w26 w60 w69 w88 w89 w90 w38 w96 w91 w49 w41 w42 w43 w39 wz36 wz37 wz40 wz44 wz45 wz46 wz47 wz48 wz50 wz51 wz52 wz53 wz54 wz55 wz56 wz57 wz58 wz59 wz92
  exact ⟨x92, x21, x20, x22, x41, x42, x23, x43, x39, x89, x90, x49, x88, x38, x69, x26, x91, x96⟩

theorem LR_nodup : LR.Nodup := by decide

theorem LR_ne : ∀ R ∈ LR, R ≠ 97 := by decide

theorem LR_lt : ∀ R ∈ LR, R.val < 97 := by decide

theorem LR_96 : (96 : Fin NRB) ∉ LR := by decide

theorem LR_length : LR.length = 16 := rfl

theorem sbList_length (P : Shared.StarParams) (CAP e c0 c1 nc : ℕ) : (sbList P CAP e c0 c1 nc).length = 16 := rfl

/-- Slot `7`'s registers hold `sbList`. -/
theorem lr_get (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (c0 c1 nc : ℕ) (Y : WState ns NRB) (y92 : Y.val ((92 : Fin NRB)) = 1) (y21 : Y.val ((21 : Fin NRB)) = P.b) (y20 : Y.val ((20 : Fin NRB)) = P.s) (y22 : Y.val ((22 : Fin NRB)) = P.r / 2) (y41 : Y.val ((41 : Fin NRB)) = ((P.n - P.r * P.b) + (1)) / (2)) (y42 : Y.val ((42 : Fin NRB)) = (P.n - P.r * P.b) / (2)) (y23 : Y.val ((23 : Fin NRB)) = P.n - P.r * P.b) (y43 : Y.val ((43 : Fin NRB)) = (((P.b) - (P.s)) * (P.r / 2)) + (((P.n - P.r * P.b) + (1)) / (2))) (y39 : Y.val ((39 : Fin NRB)) = (((P.b) - (P.s)) * (P.r / 2)) + ((P.n - P.r * P.b) / (2))) (y89 : Y.val ((89 : Fin NRB)) = (c0) * (2)) (y90 : Y.val ((90 : Fin NRB)) = (c1) * (2)) (y49 : Y.val ((49 : Fin NRB)) = (((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256))) (y88 : Y.val ((88 : Fin NRB)) = nc) (y38 : Y.val ((38 : Fin NRB)) = (((P.n) + (1)) ^ 26) * (2)) (y69 : Y.val ((69 : Fin NRB)) = Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (y26 : Y.val ((26 : Fin NRB)) = fe * Nat.clog 2 (P.n + 2)) :
    ∀ i (h : i < LR.length) (hv' : i < (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc).length), Y.val (LR.get ⟨i, h⟩) = (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc).get ⟨i, hv'⟩ := by
  intro i h hv'
  have hi : i < 16 := h
  interval_cases i
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y92]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y21]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y20]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y22]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y41]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y42]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y23]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y43]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y39]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y89]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y90]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y49]; rfl
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y88]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y38]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y69]
  · simp only [LR, sbList, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [y26]

/-- The state after emitting `1^t 0` on `O6` (counter `97`) and rewinding. -/
def e6St (X : WState ns NRB) (O6 : Fin (ns + 1)) (t : ℕ) : WState ns NRB :=
  ((appendO (X.setv 91 0) O6 97 (List.replicate t true ++ [false])).setv 97 0).seth O6
    ((appendO (X.setv 91 0) O6 97 (List.replicate t true ++ [false])).sh O6 - (t + 1))

theorem e6_run (O6 : Fin (ns + 1)) (X : WState ns NRB) (t : ℕ) (x91 : X.val 91 = t) (x97 : X.val 97 = 0)
    (hO6 : X.st O6 = []) (hO6h : X.sh O6 = 0) (ht : t + 1 ≤ cap) :
    WExec cap (.seq (emitU O6 97 91) (WM.rewind O6 97)) X (e6St X O6 t) ((11 * t + 9) + 1 + (5 * (t + 1) + 1)) := by
  have e_u := emitU_spec cap O6 97 91 (by decide) t X x91 (by rw [hO6, hO6h]; rfl) (by rw [x97]; omega)
  have e_r := wrewind_spec cap O6 97 (t + 1) (appendO (X.setv 91 0) O6 97 (List.replicate t true ++ [false]))
    (by simp [x97]) (by simp [x97]; omega)
  exact WExec.seq e_u e_r

theorem e6_val (X : WState ns NRB) (O6 : Fin (ns + 1)) (t : ℕ) (R : Fin NRB) (a : R ≠ 91) (b : R ≠ 97) :
    (e6St X O6 t).val R = X.val R := by
  simp only [e6St, WState.seth_val, WState.setv_val, appendO_val, Function.update_of_ne a, Function.update_of_ne b]

theorem e6_val97 (X : WState ns NRB) (O6 : Fin (ns + 1)) (t : ℕ) : (e6St X O6 t).val 97 = 0 := by
  simp only [e6St, WState.seth_val, WState.setv_val, Function.update_self]

theorem e6_st (X : WState ns NRB) (O6 : Fin (ns + 1)) (t : ℕ) (hO6 : X.st O6 = []) :
    (e6St X O6 t).st = Function.update X.st O6 (List.replicate t true ++ [false]) := by
  simp only [e6St, WState.seth_st, WState.setv_st, appendO_st, hO6]; rfl

theorem e6_sh (X : WState ns NRB) (O6 : Fin (ns + 1)) (t : ℕ) (hO6 : X.st O6 = []) (hO6h : X.sh O6 = 0) :
    (e6St X O6 t).sh = X.sh := by
  funext j; by_cases hj : j = O6
  · subst hj; simp [e6St, hO6, hO6h]
  · simp only [e6St, WState.seth_sh, WState.setv_sh, appendO_sh, Function.update_of_ne hj]

/-- `emitList` on `O7` (counter `97`) and the rewind. -/
theorem e7_run (O7 : Fin (ns + 1)) (vs : List ℕ) (Y : WState ns NRB) (hlen : LR.length = vs.length)
    (hvals : ∀ i (h : i < LR.length) (hv' : i < vs.length), Y.val (LR.get ⟨i, h⟩) = vs.get ⟨i, hv'⟩)
    (y97 : Y.val 97 = 0) (hO7 : Y.st O7 = []) (hO7h : Y.sh O7 = 0) (hL : (Data.unaryList vs).length ≤ cap) :
    ∃ τ : WState ns NRB, WExec cap (.seq (emitList O7 97 LR) (WM.rewind O7 97)) Y τ
        (SBEmit.emitListCost vs + 1 + (5 * (Data.unaryList vs).length + 1)) ∧
      τ.st O7 = Data.unaryList vs ∧ (∀ s, s ≠ O7 → τ.st s = Y.st s) ∧ (∀ s, τ.sh s = Y.sh s) ∧
      (∀ r, r ∉ LR → r ≠ 97 → τ.val r = Y.val r) ∧ τ.val 97 = 0 := by
  obtain ⟨s15, e_l, h15st, h15sh, h15v, -, h15o, h15sts, h15shs, -⟩ := emitList_spec cap O7 97 LR vs Y hlen
    LR_nodup LR_ne hvals (by rw [hO7, hO7h]; rfl) (by rw [y97, Nat.zero_add]; exact hL)
  have e_r := wrewind_spec cap O7 97 (Data.unaryList vs).length s15 (by rw [h15v, y97, Nat.zero_add])
    (by rw [h15v, y97, Nat.zero_add]; exact hL)
  have h15O7 : s15.st O7 = Data.unaryList vs := by rw [h15st, hO7]; rfl
  refine ⟨_, WExec.seq e_l e_r, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st, WState.setv_st]; exact h15O7
  · intro s a
    simp only [WState.seth_st, WState.setv_st]; exact h15sts s a
  · intro s
    simp only [WState.seth_sh, WState.setv_sh]
    by_cases hs : s = O7
    · subst hs; rw [Function.update_self, h15sh, h15O7, hO7h]; simp
    · rw [Function.update_of_ne hs, h15shs s hs]
  · intro r a b
    simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne b, h15o r a b]
  · simp only [WState.seth_val, WState.setv_val, Function.update_self]

/-- The two emissions (counter `97`) with their rewinds. -/
theorem p1_emit (O6 O7 : Fin (ns + 1)) (h67 : O6 ≠ O7) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (c0 c1 nc : ℕ) (X : WState ns NRB) (x92 : X.val ((92 : Fin NRB)) = 1) (x21 : X.val ((21 : Fin NRB)) = P.b) (x20 : X.val ((20 : Fin NRB)) = P.s) (x22 : X.val ((22 : Fin NRB)) = P.r / 2) (x41 : X.val ((41 : Fin NRB)) = ((P.n - P.r * P.b) + (1)) / (2)) (x42 : X.val ((42 : Fin NRB)) = (P.n - P.r * P.b) / (2)) (x23 : X.val ((23 : Fin NRB)) = P.n - P.r * P.b) (x43 : X.val ((43 : Fin NRB)) = (((P.b) - (P.s)) * (P.r / 2)) + (((P.n - P.r * P.b) + (1)) / (2))) (x39 : X.val ((39 : Fin NRB)) = (((P.b) - (P.s)) * (P.r / 2)) + ((P.n - P.r * P.b) / (2))) (x89 : X.val ((89 : Fin NRB)) = (c0) * (2)) (x90 : X.val ((90 : Fin NRB)) = (c1) * (2)) (x49 : X.val ((49 : Fin NRB)) = (((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256))) (x88 : X.val ((88 : Fin NRB)) = nc) (x38 : X.val ((38 : Fin NRB)) = (((P.n) + (1)) ^ 26) * (2)) (x69 : X.val ((69 : Fin NRB)) = Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (x26 : X.val ((26 : Fin NRB)) = fe * Nat.clog 2 (P.n + 2)) (x91 : X.val ((91 : Fin NRB)) = ((fe * Nat.clog 2 (P.n + 2)) / (4)) + (1)) (x96 : X.val ((96 : Fin NRB)) = (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))
    (h12 : ∀ r : Fin NRB, 97 ≤ r.val → X.val r = 0)
    (hO6 : X.st O6 = []) (hO6h : X.sh O6 = 0) (hO7 : X.st O7 = []) (hO7h : X.sh O7 = 0)
    (hE6 : (fe * Nat.clog 2 (P.n + 2)) / 4 + 2 ≤ cap) (hE7 : (Data.unaryList (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length ≤ cap) :
    ∃ τ : WState ns NRB, WExec cap (.seq (.seq (emitU O6 97 91) (WM.rewind O6 97)) (.seq (emitList O7 97 LR)
        (WM.rewind O7 97))) X τ
        (((11 * ((fe * Nat.clog 2 (P.n + 2)) / 4 + 1) + 9) + 1 + (5 * ((fe * Nat.clog 2 (P.n + 2)) / 4 + 1 + 1) + 1)) + 1 + (SBEmit.emitListCost (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc) + 1 +
          (5 * (Data.unaryList (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length + 1))) ∧
      τ.st O6 = FinalPass.ListEval.unary ((fe * Nat.clog 2 (P.n + 2)) / 4 + 1) ∧ τ.st O7 = Data.unaryList (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc) ∧
      (∀ s, s ≠ O6 → s ≠ O7 → τ.st s = X.st s) ∧ (∀ s, τ.sh s = X.sh s) ∧
      τ.val 96 = ellOf P.n ∧ (∀ r : Fin NRB, 97 ≤ r.val → τ.val r = 0) := by
  have e6 := e6_run cap O6 X ((fe * Nat.clog 2 (P.n + 2)) / 4 + 1) x91 (h12 97 (by decide)) hO6 hO6h (by clear * - hE6; omega)
  have hvals := lr_get P h0 h1 Cδ C m fe c0 c1 nc (e6St X O6 ((fe * Nat.clog 2 (P.n + 2)) / 4 + 1)) (by rw [e6_val X O6 _ 92 (by decide) (by decide), x92]) (by rw [e6_val X O6 _ 21 (by decide) (by decide), x21]) (by rw [e6_val X O6 _ 20 (by decide) (by decide), x20]) (by rw [e6_val X O6 _ 22 (by decide) (by decide), x22]) (by rw [e6_val X O6 _ 41 (by decide) (by decide), x41]) (by rw [e6_val X O6 _ 42 (by decide) (by decide), x42]) (by rw [e6_val X O6 _ 23 (by decide) (by decide), x23]) (by rw [e6_val X O6 _ 43 (by decide) (by decide), x43]) (by rw [e6_val X O6 _ 39 (by decide) (by decide), x39]) (by rw [e6_val X O6 _ 89 (by decide) (by decide), x89]) (by rw [e6_val X O6 _ 90 (by decide) (by decide), x90]) (by rw [e6_val X O6 _ 49 (by decide) (by decide), x49]) (by rw [e6_val X O6 _ 88 (by decide) (by decide), x88]) (by rw [e6_val X O6 _ 38 (by decide) (by decide), x38]) (by rw [e6_val X O6 _ 69 (by decide) (by decide), x69]) (by rw [e6_val X O6 _ 26 (by decide) (by decide), x26])
  obtain ⟨τ, e7, h7O7, h7st, h7sh, h7v, h797⟩ := e7_run cap O7 (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc) (e6St X O6 ((fe * Nat.clog 2 (P.n + 2)) / 4 + 1))
    (LR_length.trans (sbList_length _ _ _ _ _ _).symm) hvals
    (e6_val97 X O6 _) (by rw [e6_st X O6 _ hO6, Function.update_of_ne (Ne.symm h67), hO7])
    (by rw [e6_sh X O6 _ hO6 hO6h, hO7h]) hE7
  refine ⟨τ, WExec.seq e6 e7, ?_, h7O7, ?_, ?_, ?_, ?_⟩
  · rw [h7st O6 h67, e6_st X O6 _ hO6, Function.update_self]; rfl
  · intro s a b
    rw [h7st s b, e6_st X O6 _ hO6, Function.update_of_ne a]
  · intro s
    rw [h7sh s, e6_sh X O6 _ hO6 hO6h]
  · rw [h7v 96 LR_96 (by decide), e6_val X O6 _ 96 (by decide) (by decide), x96]
    rfl
  · intro r hr
    by_cases h97 : r = 97
    · subst h97; exact h797
    · rw [h7v r (fun hm => absurd hr (Nat.not_le.mpr (LR_lt r hm))) h97,
        e6_val X O6 _ r (by intro e; subst e; revert hr; decide) h97, h12 r hr]

/-- **P1**: parse, the three counts, the eight phases, the two emissions (counter `97`) with their rewinds. -/
def p1W (I S0 S1 S6 O6 O7 : Fin (ns + 1)) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM ns NRB :=
  .seq (.seq (parseW I) (.seq (countW S0 93 89) (.seq (countW S1 93 90) (countW S6 93 88))))
    (.seq (.seq (aW cr fe ζ Cδ C) (.seq b1W b2aW)) (.seq (.seq b2bW (.seq b2cW (.seq c1W (.seq c2W c3W))))
      (.seq (.seq (emitU O6 97 91) (WM.rewind O6 97)) (.seq (emitList O7 97 LR) (WM.rewind O7 97)))))

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.SBNums
