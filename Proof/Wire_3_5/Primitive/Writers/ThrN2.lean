import Proof.Wire_3_5.Primitive.SeedFix.C4SB
import Proof.Wire_3_5.Primitive.Writers.ThrN1

/-! # c4 THR block, numbers part 2: the star numbers, the THR filter's seeds, the THR count `Q`

After the first stage (`p1T_spec`): the call's star numbers (`StarNums.starNumsM`: `r, s, b, r/2, kh = s·(r/2), k`,
`fe·L`), the THR filter's cap `capT = hashNums[1]` into `Hb 13`, the digit count `dig = hashNums[7]` into `dMS`, the THR filter's gap numbers
(`nAW`: `2^{seedBits}` into `G 21`), `|𝒢| = hashNums[2]` into `G 41`, `Σ_{p ≤ cutoff} p = hashNums[6]` into `G 52`,
and the THR count `Q = sampleCount(kh, 1, n, 2^{seedBits}·(|𝒢|·Σp)·(2|𝒢|·cutoff+1)² + 1)` into `KB 52`.

Paper quantity: the THR sample count (samp:q at a THR call, P3:2987-2988, 3154-3162; `ThrQ.thrCount_eq`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimT.C4Set (KB KB_val)

variable (cap : ℕ)

/-! ## The count's registers (`472 … 511`, above PA's decode blocks) -/

/-- The sample count's inputs and output (`SymQM.qW`'s block). -/
def qS : Fin 12 ↪ Fin LNR := ⟨fun i => ⟨472 + i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩

theorem qS_val (i : Fin 12) : (qS i).val = 472 + i.val := rfl

/-- The product's scratch. -/
def tqA : Fin LNR := ⟨484, by decide⟩
def tqB : Fin LNR := ⟨485, by decide⟩
def tqM2 : Fin LNR := ⟨486, by decide⟩
def tqM3 : Fin LNR := ⟨487, by decide⟩
def tqM4 : Fin LNR := ⟨488, by decide⟩
def tqC : Fin LNR := ⟨489, by decide⟩
def tqD : Fin LNR := ⟨490, by decide⟩
def tqT : Fin LNR := ⟨511, by decide⟩

theorem rv_tqA : tqA.val = 484 := rfl
theorem rv_tqB : tqB.val = 485 := rfl
theorem rv_tqM2 : tqM2.val = 486 := rfl
theorem rv_tqM3 : tqM3.val = 487 := rfl
theorem rv_tqM4 : tqM4.val = 488 := rfl
theorem rv_tqC : tqC.val = 489 := rfl
theorem rv_tqD : tqD.val = 490 := rfl
theorem rv_tqT : tqT.val = 511 := rfl
theorem rv_xT : xT.val = 296 := rfl

def mA : Fin 5 ↪ Fin LNR := ⟨![tqA, tqB, tqM2, tqM3, tqM4], by decide⟩
def mB : Fin 5 ↪ Fin LNR := ⟨![tqC, tqD, tqM2, tqM3, tqM4], by decide⟩
def mC : Fin 5 ↪ Fin LNR := ⟨![tqA, tqC, tqM2, tqM3, tqM4], by decide⟩
@[simp] theorem mA_apply (i : Fin 5) : mA i = ![tqA, tqB, tqM2, tqM3, tqM4] i := rfl
@[simp] theorem mB_apply (i : Fin 5) : mB i = ![tqC, tqD, tqM2, tqM3, tqM4] i := rfl
@[simp] theorem mC_apply (i : Fin 5) : mC i = ![tqA, tqC, tqM2, tqM3, tqM4] i := rfl

/-- The register-arithmetic simp set of this file. -/
macro "tsimp" : tactic => `(tactic| simp [*, WState.setv_val, Function.update_apply, Fin.ext_iff, Hb_val, G_val,
  SGb_val, qS_val, rv_dN, rv_TM, rv_XA, rv_dMS, rv_tqA, rv_tqB, rv_tqM2, rv_tqM3, rv_tqM4, rv_tqC, rv_tqD, rv_tqT])

/-! ## The star numbers -/

/-- `n` into `SGb 0`, then the star numbers. -/
def sTW (cr fe : ℕ) : WM (LNS 0) LNR := .seq (FinalPass.Hash4.wcopyR dN (SGb 0) xT) (StarNums.starNumsM cr fe SGb)

theorem starCost_le (n cr fe : ℕ) (h : (fe + 4) * (n + 3) + 2 * cr + 20 ≤ cap) :
    StarNums.starCost n cr fe ≤ 3 * UnaryPow.sq cap := by
  unfold StarNums.starCost UnaryPow.sq
  have h1 : n + 2 ≤ cap + 2 := by nlinarith
  have h2 : fe * (n + 2) ≤ cap := by nlinarith
  have h3 : cr ≤ cap := by nlinarith
  nlinarith

theorem sT_spec (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (σ : WState (LNS 0) LNR)
    (hn : σ.val dN = P.n) (hSG : ∀ i, σ.val (SGb i) = 0) (hx : σ.val xT = 0)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap) :
    WExec cap (sTW cr fe) σ (StarNums.starOut (σ.setv (SGb 0) P.n) SGb P fe) (5 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hsc := starCost_le cap P.n cr fe hcS
  have hnc : P.n ≤ cap := by nlinarith
  have e1 := copy1 cap dN (SGb 0) xT (by decide) (by decide) (by decide) P.n σ hn (hSG 0) hx hnc
  have e2 := StarNums.starNums_spec cap cr fe SGb P hrP (σ.setv (SGb 0) P.n) (by simp)
    (fun i hi => by simp [Function.update_apply, SGb.injective.ne hi, hSG]) hcS
  exact WExec.mono (WExec.seq e1 e2) (by omega)

/-! ## The THR filter's cap and the digit count -/

/-- `Hb 13 := capT` (`hashNums[1]`), `dMS := dig` (`hashNums[7]`, the free numbers' `M` at THR). -/
def hTW : WM (LNS 0) LNR :=
  .seq (WM.clear (Hb 13)) (.seq (FinalPass.Hash4.wcopyR (Hb 1) (Hb 13) TM) (FinalPass.Hash4.wcopyR (Hb 7) dMS TM))

theorem hT_spec (σ : WState (LNS 0) LNR) (e13 v1 M : ℕ) (h13 : σ.val (Hb 13) = e13) (h1 : σ.val (Hb 1) = v1)
    (hXA : σ.val (Hb 7) = M) (hTM : σ.val TM = 0) (hMS : σ.val dMS = 0) (c13 : e13 ≤ cap) (c1 : v1 ≤ cap)
    (cM : M ≤ cap) :
    WExec cap hTW σ (((σ.setv (Hb 13) 0).setv (Hb 13) v1).setv dMS M) (5 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold hTW
  refine seqD cap _ 1 (clear1 cap (Hb 13) e13 σ h13 c13) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Hb 1) (Hb 13) TM (by decide) (by decide) (by decide) v1 _ (by tsimp) (by tsimp)
    (by tsimp) c1) (by omega) (by omega) ?_
  exact endD cap _ 1 (copy1 cap (Hb 7) dMS TM (by decide) (by decide) (by decide) M _ (by tsimp) (by tsimp) (by tsimp) cM)
    rfl (by omega) (by omega)

/-! ## The THR filter's gap numbers (`nAW` at direct capacity hypotheses) -/

theorem nAT_spec (σ : WState (LNS 0) LNR) (n capS err : ℕ)
    (vC : σ.val (Hb 13) = capS) (vN : σ.val dN = n) (vE : σ.val (SGb 10) = err) (hz : ∀ i, σ.val (G i) = 0)
    (c1 : 1 ≤ capS) (cS : capS * 32 + 2 ≤ cap) (cL : 2 * (n + 1) ^ 26 + 8 ≤ cap) (cE : err + 4 ≤ cap)
    (cSB : 2 ^ ((gP n capS err).seedBits + 1) ≤ cap)
    (cLB : (gP n capS err).labelBits + (gP n capS err).fieldBits + (gP n capS err).walkLen + 512 ≤ cap) :
    WExec cap (nAW 0) σ (aOut 0 σ n capS err) (234 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have p26 : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have hsb : 1 ≤ 2 ^ (gP n capS err).seedBits := Nat.one_le_two_pow
  unfold nAW
  refine seqD cap _ 1 (copy1 cap (Hb 13) (G 0) (G 63) (by decide) (by decide) (by decide) capS _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap dN (G 57) (G 63) (by decide) (by decide) (by decide) n _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (G 57) n _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 108 (pow1 cap (pw26.trans G) (n + 1) 26 _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, pw26_apply, Function.Embedding.trans_apply]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap (G 1) (G 58) (by decide) ((n + 1) ^ 26) _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (G 57) (n + 1) _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (SGb 10) (G 2) (G 63) (by decide) (by decide) (by decide) err _ (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE]) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 110 (GapNums.gapNums_spec cap (KG.trans G) _ (gP n capS err) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply, gP]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply, gP]) (by simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply, gP]) (fun i hi => by fin_cases i <;> simp [WState.setv_val, Function.update_apply, hz, nHb, ndN, nSG10, vC, vN, vE, KG_apply, Function.Embedding.trans_apply] at hi ⊢) (by simp [gP]; exact c1) (by simp [gP]; omega) (by omega) cS (by simp [gP]; omega) (by simp [gP]; omega) cSB cLB) ?_ (by omega) (by omega)
  simp only [aOut, Function.Embedding.trans_apply, KG_apply, pw26_apply, Matrix.cons_val]

theorem aOut_other (σ : WState (LNS 0) LNR) (n capS err : ℕ) (r : Fin LNR) (h : r.val < 408 ∨ 472 ≤ r.val) :
    (aOut 0 σ n capS err).val r = σ.val r := by
  have h' : ∀ i : Fin 64, r ≠ G i := fun i e => by
    have := congrArg Fin.val e; rw [G_val] at this; have := i.isLt; omega
  unfold aOut
  simp [Function.update_apply, h']

/-! ## `|𝒢|` and `Σ p` into the seed block's inputs -/

def gTW : WM (LNS 0) LNR := .seq (FinalPass.Hash4.wcopyR (Hb 2) (G 41) (G 63)) (FinalPass.Hash4.wcopyR (Hb 6) (G 52) (G 63))

theorem gT_spec (σ : WState (LNS 0) LNR) (g p : ℕ) (e2 : σ.val (Hb 2) = g) (e6 : σ.val (Hb 6) = p)
    (z41 : σ.val (G 41) = 0) (z52 : σ.val (G 52) = 0) (z63 : σ.val (G 63) = 0) (cg : g ≤ cap) (cp : p ≤ cap) :
    WExec cap gTW σ ((σ.setv (G 41) g).setv (G 52) p) (3 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold gTW
  refine seqD cap _ 1 (copy1 cap (Hb 2) (G 41) (G 63) (by decide) (by decide) (by decide) g σ e2 z41 z63 cg)
    (by omega) (by omega) ?_
  exact endD cap _ 1 (copy1 cap (Hb 6) (G 52) (G 63) (by decide) (by decide) (by decide) p _ (by tsimp) (by tsimp)
    (by tsimp) cp) rfl (by omega) (by omega)

/-! ## The count's input `I = 2^{seedBits}·|𝒢|·Σp·(2|𝒢|·cutoff+1)² + 1` -/

/-- `tqA := g·p·t·(2gc+1)²+1` (copied to `qS 0`), `qS 1 := kh`, `qS 2 := n`. -/
def qIW : WM (LNS 0) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Hb 2) tqA tqT) <|
  .seq (FinalPass.Hash4.wcopyR (Hb 6) tqB tqT) <|
  .seq (SparseNum.mulByW mA) <|
  .seq (WM.clear tqB) <|
  .seq (FinalPass.Hash4.wcopyR (G 21) tqB tqT) <|
  .seq (SparseNum.mulByW mA) <|
  .seq (WM.clear tqB) <|
  .seq (FinalPass.Hash4.wcopyR (Hb 2) tqC tqT) <|
  .seq (FinalPass.Hash4.wcopyR (Hb 4) tqD tqT) <|
  .seq (SparseNum.mulByW mB) <|
  .seq (WM.clear tqD) <|
  .seq (dbl tqC tqT) <|
  .seq (.inc tqC) <|
  .seq (SparseNum.mulByW mC) <|
  .seq (SparseNum.mulByW mC) <|
  .seq (WM.clear tqC) <|
  .seq (.inc tqA) <|
  .seq (FinalPass.Hash4.wcopyR tqA (qS 0) tqT) <|
  .seq (FinalPass.Hash4.wcopyR (SGb 8) (qS 1) tqT) <|
  FinalPass.Hash4.wcopyR dN (qS 2) tqT

/-- Its end state. -/
def qIOut (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) : WState (LNS 0) LNR :=
  σ |>.setv tqA g |>.setv tqB p |>.setv tqA (g * p) |>.setv tqB 0 |>.setv tqB t |>.setv tqA (g * p * t)
    |>.setv tqB 0 |>.setv tqC g |>.setv tqD c |>.setv tqC (g * c) |>.setv tqD 0 |>.setv tqC (2 * (g * c))
    |>.setv tqC (2 * (g * c) + 1) |>.setv tqA (g * p * t * (2 * (g * c) + 1))
    |>.setv tqA (g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1)) |>.setv tqC 0
    |>.setv tqA (g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1)
    |>.setv (qS 0) (g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) |>.setv (qS 1) kh |>.setv (qS 2) n

theorem qI_spec (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) (e2 : σ.val (Hb 2) = g) (e4 : σ.val (Hb 4) = c)
    (e6 : σ.val (Hb 6) = p) (e21 : σ.val (G 21) = t) (e8 : σ.val (SGb 8) = kh) (eN : σ.val dN = n)
    (hz : ∀ r : Fin LNR, 472 ≤ r.val → σ.val r = 0) (ht : 1 ≤ t) (cg : g ≤ cap) (cp : p ≤ cap) (cc : c ≤ cap)
    (ctc : t ≤ cap) (ck : kh ≤ cap) (cn : n ≤ cap) (cB : 2 * (g * c) + 2 ≤ cap)
    (cI : g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1 ≤ cap) :
    WExec cap qIW σ (qIOut σ g p t c kh n) (50 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hB : 0 < 2 * (g * c) + 1 := by omega
  have b1 : g * p ≤ g * p * t := Nat.le_mul_of_pos_right _ ht
  have b2 : g * p * t ≤ g * p * t * (2 * (g * c) + 1) := Nat.le_mul_of_pos_right _ hB
  have b3 : g * p * t * (2 * (g * c) + 1) ≤ g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1) :=
    Nat.le_mul_of_pos_right _ hB
  have zA : σ.val tqA = 0 := hz _ (by decide)
  have zB : σ.val tqB = 0 := hz _ (by decide)
  have z2 : σ.val tqM2 = 0 := hz _ (by decide)
  have z3 : σ.val tqM3 = 0 := hz _ (by decide)
  have z4 : σ.val tqM4 = 0 := hz _ (by decide)
  have zC : σ.val tqC = 0 := hz _ (by decide)
  have zD : σ.val tqD = 0 := hz _ (by decide)
  have zT : σ.val tqT = 0 := hz _ (by decide)
  have zq0 : σ.val (qS 0) = 0 := hz _ (by decide)
  have zq1 : σ.val (qS 1) = 0 := hz _ (by decide)
  have zq2 : σ.val (qS 2) = 0 := hz _ (by decide)
  clear hz
  unfold qIW
  refine seqD cap _ 1 (copy1 cap (Hb 2) tqA tqT (by decide) (by decide) (by decide) g _ (by tsimp) (by tsimp) (by tsimp) cg) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Hb 6) tqB tqT (by decide) (by decide) (by decide) p _ (by tsimp) (by tsimp) (by tsimp) cp) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap mA g p _ (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by omega) cg cp) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap tqB p _ (by tsimp) cp) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (G 21) tqB tqT (by decide) (by decide) (by decide) t _ (by tsimp) (by tsimp) (by tsimp) ctc) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap mA (g * p) t _ (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by omega) (by omega) ctc) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap tqB t _ (by tsimp) ctc) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Hb 2) tqC tqT (by decide) (by decide) (by decide) g _ (by tsimp) (by tsimp) (by tsimp) cg) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (Hb 4) tqD tqT (by decide) (by decide) (by decide) c _ (by tsimp) (by tsimp) (by tsimp) cc) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap mB g c _ (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by omega) cg cc) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap tqD c _ (by tsimp) cc) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap tqC tqT (by decide) (g * c) _ (by tsimp) (by tsimp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap tqC (2 * (g * c)) _ (by tsimp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap mC (g * p * t) (2 * (g * c) + 1) _ (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap mC (g * p * t * (2 * (g * c) + 1)) (2 * (g * c) + 1) _ (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by tsimp) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap tqC (2 * (g * c) + 1) _ (by tsimp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap tqA (g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1)) _ (by tsimp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap tqA (qS 0) tqT (by decide) (by decide) (by decide) (g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) _ (by tsimp) (by tsimp) (by tsimp) cI) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (SGb 8) (qS 1) tqT (by decide) (by decide) (by decide) kh _ (by tsimp) (by tsimp) (by tsimp) ck) (by omega) (by omega) ?_
  exact endD cap _ 1 (copy1 cap dN (qS 2) tqT (by decide) (by decide) (by decide) n _ (by tsimp) (by tsimp) (by tsimp) cn) rfl (by omega) (by omega)

theorem qIOut_st (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) :
    (qIOut σ g p t c kh n).st = σ.st ∧ (qIOut σ g p t c kh n).sh = σ.sh ∧ (qIOut σ g p t c kh n).cell = σ.cell := by
  unfold qIOut
  simp only [WState.setv_st, WState.setv_sh, WState.setv_cell, and_self]

theorem qIOut_q0 (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) :
    (qIOut σ g p t c kh n).val (qS 0) = g * p * t * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1 := by
  have n01 : qS 0 ≠ qS 1 := by decide
  have n02 : qS 0 ≠ qS 2 := by decide
  simp only [qIOut, WState.setv_val]
  rw [Function.update_of_ne n02, Function.update_of_ne n01, Function.update_self]

theorem qIOut_q1 (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) : (qIOut σ g p t c kh n).val (qS 1) = kh := by
  have n12 : qS 1 ≠ qS 2 := by decide
  simp only [qIOut, WState.setv_val]
  rw [Function.update_of_ne n12, Function.update_self]

theorem qIOut_q2 (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) : (qIOut σ g p t c kh n).val (qS 2) = n := by
  simp only [qIOut, WState.setv_val]
  rw [Function.update_self]

theorem qIOut_qS (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) (i : Fin 12) (hi : 3 ≤ i.val) :
    (qIOut σ g p t c kh n).val (qS i) = σ.val (qS i) := by
  have hne : ∀ s : Fin LNR, (s.val < 475 ∨ 484 ≤ s.val) → qS i ≠ s := fun s hs e => by
    have := congrArg Fin.val e; rw [qS_val] at this; have := i.isLt; omega
  have h1 := hne tqA (by decide)
  have h2 := hne tqB (by decide)
  have h3 := hne tqC (by decide)
  have h4 := hne tqD (by decide)
  have h5 := hne (qS 0) (by decide)
  have h6 := hne (qS 1) (by decide)
  have h7 := hne (qS 2) (by decide)
  simp only [qIOut, WState.setv_val, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

theorem qIOut_low (σ : WState (LNS 0) LNR) (g p t c kh n : ℕ) (r : Fin LNR) (hr : r.val < 472) :
    (qIOut σ g p t c kh n).val r = σ.val r := by
  have hne : ∀ s : Fin LNR, 472 ≤ s.val → r ≠ s := fun s hs e => by subst e; omega
  have h1 := hne tqA (by decide)
  have h2 := hne tqB (by decide)
  have h3 := hne tqC (by decide)
  have h4 := hne tqD (by decide)
  have h5 := hne (qS 0) (by decide)
  have h6 := hne (qS 1) (by decide)
  have h7 := hne (qS 2) (by decide)
  simp only [qIOut, WState.setv_val, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

/-! ## The count and its register -/

/-- `SymQM.qW` on the block `qS`: `qS 3 := 2^{(5kh+3)/4}·(I·8192·n·n)`. -/
def qWT : WM (LNS 0) LNR := .seq (SymQM.qAW qS) (.seq (SymQM.qB1W qS) (SymQM.qB2W qS))

/-- `KB 52 := Q`. -/
def kTW : WM (LNS 0) LNR := FinalPass.Hash4.wcopyR (qS 3) (KB 52) tqT

end NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
