import Proof.Wire_3_5.Primitive.Writers.SBP1

/-! # SB, part (1): P1 as one run

* **`p1_run`**: from the state after the carrier pipeline (the request on `I`, the counts `1^{c0}`, `1^{c1}`,
  `1^{nc}`, the output streams `O6`, `O7` blank, every register `0`), P1 leaves `1^{e/4+1} 0` on `O6` and
  `unaryList sbList` on `O7`, every other stream and every head as it was, `ℓ = ellOf n` in register `96`, registers
  `97 …` at `0`, within `p1Cost` (SBTypes).

Paper quantities of the main type: S4's words `6`, `7` (the walk's threshold, `s4Small2`, P3:3170-3181) and the
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

theorem s4_hi (P : Shared.StarParams) (m : Mode) (c0 c1 nc : ℕ) (σ : WState ns NRB) (hv : ∀ q, σ.val q = 0)
    (r : Fin NRB) (hr : 97 ≤ r.val) : (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc).val r = 0 := by
  simp only [WState.setv_val]
  repeat rw [Function.update_of_ne (fun e => by rw [e] at hr; revert hr; decide)]
  exact hv r

theorem sx_hi (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode)
    (fe c0 c1 nc : ℕ) (σ : WState ns NRB) (hv : ∀ q, σ.val q = 0) (r : Fin NRB) (hr : 97 ≤ r.val) :
    (c3Out (c2Out (c1Out (b2cOut (b2bOut (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).val r = 0 := by
  rw [c3_hi _ _ _ _ _ _ _ _ _ _ r hr, c2_hi _ _ _ _ _ _ _ _ r hr, c1_hi _ _ _ _ _ _ _ _ r hr,
    b2c_hi _ _ _ _ _ _ _ _ r hr, b2b_hi _ _ _ _ _ _ _ _ r hr, b2a_hi _ _ _ _ _ _ _ _ r hr,
    b1_hi _ _ _ _ _ _ _ _ r hr, a_hi _ _ _ _ _ _ _ _ r hr]
  exact s4_hi P m c0 c1 nc σ hv r hr

theorem sx_st (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode)
    (fe c0 c1 nc : ℕ) (σ : WState ns NRB) : (c3Out (c2Out (c1Out (b2cOut (b2bOut (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).st = σ.st ∧ (c3Out (c2Out (c1Out (b2cOut (b2bOut (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1).sh = σ.sh := by
  constructor <;>
  simp only [c3Out, c2Out, c1Out, b2cOut, b2bOut, b2aOut, b1Out, aOut, StarNums.starOut, WState.setv_st,
    WState.setv_sh]

/-- **P1 as one run.** -/
theorem p1_run (I S0 S1 S6 O6 O7 : Fin (ns + 1)) (h67 : O6 ≠ O7) (cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
    (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n)
    (codes cc : List ℕ) (tl : List Bool) (c0 c1 nc : ℕ) (σ : WState ns NRB)
    (hI : σ.st I = frame (Data.reqW P.n (Codec.modeBit m) codes cc tl)) (hIh : σ.sh I = 0)
    (hS0 : σ.st S0 = List.replicate c0 true) (hS0h : σ.sh S0 = 0)
    (hS1 : σ.st S1 = List.replicate c1 true) (hS1h : σ.sh S1 = 0)
    (hS6 : σ.st S6 = List.replicate nc true) (hS6h : σ.sh S6 = 0)
    (hO6 : σ.st O6 = []) (hO6h : σ.sh O6 = 0) (hO7 : σ.st O7 = []) (hO7h : σ.sh O7 = 0)
    (hv : ∀ q, σ.val q = 0)
    (hc : 2 * (Data.reqW P.n (Codec.modeBit m) codes cc tl).length ≤ cap) (hcn : 2 ^ (natBitLength P.n + 1) ≤ cap)
    (hc0 : c0 + 1 ≤ cap) (hc1 : c1 + 1 ≤ cap) (hnc : nc + 1 ≤ cap)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : SymDec.CapNeed C m P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ cap) (hpw : (P.n + 1) ^ 26 ≤ cap)
    (t1 : tB1 P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 ≤ cap) (t2 : tB2a P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 ≤ cap) (t3 : tB2b P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 ≤ cap)
    (t4 : tB2c P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 ≤ cap) (t5 : tC1 P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 ≤ cap) (t6 : tC2 P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 ≤ cap) (t7 : tC3 P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 ≤ cap)
    (hE6 : (fe * Nat.clog 2 (P.n + 2)) / 4 + 2 ≤ cap) (hE7 : (Data.unaryList (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length ≤ cap) :
    ∃ τ : WState ns NRB, WExec cap (p1W I S0 S1 S6 O6 O7 cr fe ζ Cδ C) σ τ
        (p1Cost cap (Data.reqW P.n (Codec.modeBit m) codes cc tl).length P h0 h1 Cδ C m fe cr c0 c1 nc) ∧
      τ.st O6 = FinalPass.ListEval.unary ((fe * Nat.clog 2 (P.n + 2)) / 4 + 1) ∧ τ.st O7 = Data.unaryList (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc) ∧
      (∀ s, s ≠ O6 → s ≠ O7 → τ.st s = σ.st s) ∧ (∀ s, τ.sh s = σ.sh s) ∧
      τ.val 96 = ellOf P.n ∧ (∀ r : Fin NRB, 97 ≤ r.val → τ.val r = 0) := by
  have ep := p1_pre cap I S0 S1 S6 P m codes cc tl c0 c1 nc σ hI hIh hS0 hS0h hS1 hS1h hS6 hS6h hv hc hcn hc0 hc1 hnc
  have em1 := p1_mid1 cap cr P h0 h1 Cδ C m fe hrP (mbOf m) c0 c1 nc σ hv (by cases hb : Codec.modeBit m <;> simp [mbOf, hb])
    hcS hcP hcC hlam hpw t1 t2
  obtain ⟨p16, p17, p19, p20, p21, p22, p23, p24, p25, p26, p60, p69, p88, p89, p90, p38, p96, p48, pz36, pz37, pz39, pz40, pz41, pz42, pz43, pz44, pz45, pz46, pz47, pz49, pz50, pz51, pz52, pz53, pz54, pz55, pz56, pz57, pz58, pz59, pz91, pz92⟩ := sp_vals P h0 h1 Cδ C m fe (mbOf m) c0 c1 nc σ hv
  have em2 := p1_mid2 cap P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) p16 p17 p19 p20 p21 p22 p23 p24 p25 p26 p60 p69 p88 p89 p90 p38 p96 p48 pz36 pz37 pz39 pz40 pz41 pz42 pz43 pz44 pz45 pz46 pz47 pz49 pz50 pz51 pz52 pz53 pz54 pz55 pz56 pz57 pz58 pz59 pz91 pz92 t3 t4 t5 t6 t7
  obtain ⟨x92, x21, x20, x22, x41, x42, x23, x43, x39, x89, x90, x49, x88, x38, x69, x26, x91, x96⟩ := sx_vals P h0 h1 Cδ C m fe (mbOf m) nc c0 c1 (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) p16 p17 p19 p20 p21 p22 p23 p24 p25 p26 p60 p69 p88 p89 p90 p38 p96 p48 pz36 pz37 pz39 pz40 pz41 pz42 pz43 pz44 pz45 pz46 pz47 pz49 pz50 pz51 pz52 pz53 pz54 pz55 pz56 pz57 pz58 pz59 pz91 pz92
  have h12 := sx_hi P h0 h1 Cδ C m fe c0 c1 nc σ hv
  obtain ⟨hXst, hXsh⟩ := sx_st P h0 h1 Cδ C m fe c0 c1 nc σ
  obtain ⟨τ, ee, q1, q2, q3, q4, q5, q6⟩ := p1_emit cap O6 O7 h67 P h0 h1 Cδ C m fe c0 c1 nc (c3Out (c2Out (c1Out (b2cOut (b2bOut (b2aOut (b1Out (aOut (((((σ.setv 16 P.n).setv 60 (mbOf m)).setv 89 c0).setv 90 c1).setv 88 nc) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe) P h0 h1 Cδ C m fe c0 c1) x92 x21 x20 x22 x41 x42 x23 x43 x39 x89 x90 x49 x88 x38 x69 x26 x91 x96 h12
    (by rw [hXst]; exact hO6) (by rw [hXsh]; exact hO6h) (by rw [hXst]; exact hO7) (by rw [hXsh]; exact hO7h) hE6 hE7
  refine ⟨τ, WExec.mono (WExec.seq ep (WExec.seq em1 (WExec.seq em2 ee))) ?_, q1, q2, ?_, ?_, q5, q6⟩
  · unfold p1Cost; clear * -; omega
  · intro s a b; rw [q3 s a b, hXst]
  · intro s; rw [q4 s, hXsh]

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.SBNums
