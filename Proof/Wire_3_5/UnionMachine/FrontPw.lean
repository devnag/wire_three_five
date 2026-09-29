import Proof.Wire_3_5.UnionMachine.FrontNum
import Proof.Wire_3_5.UnionMachine.FrontTailStage

/-! # C6 front, the table writer's word program `Pw` (the tail's first part)

The tail stage (`FrontTailStage.tailStage_step`) takes the table writer's word program `Pw : WM 10 56` and its
run as a hypothesis. This module builds `Pw` (P3:3669-3691, 3483-3489):
* **`prefixW`**: read `q` off the header, set the rewind budget `BIG := Kb·(q+1)^Db`, rewind the header, clear the
  scratch, set the constant's envelope flag `CDF` (the numbers need every register clear but `BIG` and `CDF`);
* `numP` (M18 `numT`: `q`, `sys`, `aux`, `cb`, `p = L(q)`, `Λ̄`, `s`), `twP` (M16/M17 `twT`/`twSem`: the table and `OK`),
  the thresholds `thrOps` (M18 `accStart_eq`);
* **`pw_spec`**: from all registers clear, the tail's demands: `q` in `54`, the table word on stream `0` (head at its end,
  length in `0`), `p` in `52`, the accumulators' start in `24 … 29` (`threshAcc` of the slack thresholds), `OK` in `12`.

Paper quantity of the main type: the call table, `p = unionBits q`, the slack thresholds (the loop's kept data). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontPw
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW NearCubicWires.WireExponent3_5.UnionMachine.FrontOps
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.RepairRepresentation (natWord)

/-! ## The prefix -/

section Prefix
variable (cap : ℕ)

/-- The prefix's register maps: the power `(q+1)^Db` and `BIG += (q+1)^Db·Kb`. -/
def pR : Fin 5 ↪ Fin NR := ⟨![rX, rY, 30, 31, 32], by decide⟩
def mR : Fin 5 ↪ Fin NR := ⟨![rY, 33, rBIG, 30, 31], by decide⟩

/-- **The prefix**: `q` off the header, `BIG := Kb·(q+1)^Db`, the header rewound, the scratch cleared, `CDF := cdf`. -/
def prefixW (Kb Db : ℕ) (cdf : Bool) : WM 10 NR :=
  .seq (readNatM true sHd rF rC rX rP rTT) (.seq (.inc rX) (.seq (UnaryPow.powConstW pR Db)
  (.seq (StarNums.incN 33 Kb) (.seq (UnaryArith.mulAddW mR) (.seq (rewB sHd rBIG rT)
  (.seq (WM.clear rX) (.seq (WM.clear rY) (.seq (WM.clear 33) (if cdf then .inc rCDF else .skip)))))))))

/-- The registers after the prefix: `BIG = B`, `CDF = [cdf]`, all others `0`. -/
def bigV (B : ℕ) (cdf : Bool) : Fin NR → ℕ :=
  Function.update (Function.update (fun _ => 0) rBIG B) rCDF (if cdf then 1 else 0)

theorem bigV_big (B : ℕ) (cdf : Bool) : bigV B cdf rBIG = B := by simp +decide [bigV]
theorem bigV_cdf (B : ℕ) (cdf : Bool) : bigV B cdf rCDF = if cdf then 1 else 0 := by simp [bigV]
theorem bigV_zero (B : ℕ) (cdf : Bool) (r : Fin NR) (h1 : r ≠ rBIG) (h2 : r ≠ rCDF) : bigV B cdf r = 0 := by
  simp [bigV, Function.update_of_ne h1, Function.update_of_ne h2]

/-- The prefix's cost. -/
def prefixCost (q Db B sqc : ℕ) : ℕ :=
  (natBitLength q + 2) * (40 * 2 ^ natBitLength q + 40) + (Db + 10) * (4 * sqc) + 16 * B + 20

theorem prefix_spec (src : Fin 11 → List Bool) (cl : Bool) (Kb Db : ℕ) (cdf : Bool) (q : ℕ) (restH : List Bool)
    (hH : src sHd = enc true (natWord q) ++ restH) (hB : 2 * (natWord q).length ≤ Kb * (q + 1) ^ Db)
    (hK : Kb ≤ cap) (hq : 2 ^ (natBitLength q + 1) ≤ cap) (hq1 : q + 2 ≤ cap)
    (hPw : ∀ k ≤ Db, (q + 1) ^ k ≤ cap) (hBc : Kb * (q + 1) ^ Db ≤ cap) :
    WExec cap (prefixW Kb Db cdf) (ts src 0 [] (fun _ => 0) cl) (ts src 0 [] (bigV (Kb * (q + 1) ^ Db) cdf) cl)
      (prefixCost q Db (Kb * (q + 1) ^ Db) (UnaryPow.sq cap)) := by
  have hs := UnaryPow.lin_le_sq cap
  set σ0 := ts src 0 [] (fun _ => 0) cl with hσ0
  have v0 : ∀ r, σ0.val r = 0 := fun r => by simp [σ0, ts, Function.update_apply]
  have e1 := readNatM_spec cap true sHd rF rC rX rP rTT (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) q [] restH σ0
    (by rw [hσ0, ts_st src _ _ _ _ _ (by decide)]; simpa using hH)
    (by rw [hσ0, ts_sh_src src _ _ _ _ _ (by decide) (by decide)]; rfl)
    (v0 _) (v0 _) (v0 _) (v0 _) (by rw [v0]; omega)
  set σ1 := (σ0.seth sHd ([].length + stp true * (natWord q).length)).setv rX (σ0.val rX + q) with hσ1
  have e2 := inc1 cap rX q σ1 (by simp [σ1, v0]) (by omega)
  set σ2 := σ1.setv rX (q + 1) with hσ2
  have e3 := pow1 cap pR (q + 1) Db σ2 (by simp [σ2, pR]) (by simp +decide [σ2, σ1, pR, Function.update_apply, v0])
    (by simp +decide [σ2, σ1, pR, Function.update_apply, v0]) (by simp +decide [σ2, σ1, pR, Function.update_apply, v0])
    (by simp +decide [σ2, σ1, pR, Function.update_apply, v0]) (by omega) (by omega) (hPw Db le_rfl)
  set σ3 := σ2.setv (pR 1) ((q + 1) ^ Db) with hσ3
  have e4 := incN0 cap 33 Kb σ3 (by simp +decide [σ3, σ2, σ1, pR, Function.update_apply, v0]) hK
  set σ4 := σ3.setv 33 Kb with hσ4
  have e5 := mulAdd1 cap mR ((q + 1) ^ Db) Kb 0 σ4 (by simp +decide [σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0])
    (by simp +decide [σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0])
    (by simp +decide [σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0])
    (by simp +decide [σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0])
    (by simp +decide [σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0])
    (by rw [Nat.mul_comm]; omega) (hPw Db le_rfl) hK
  set σ5 := σ4.setv (mR 2) (0 + (q + 1) ^ Db * Kb) with hσ5
  have b5 : σ5.val rBIG = Kb * (q + 1) ^ Db := by
    simp +decide [σ5, σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0]; ring
  have hsh5 : σ5.sh sHd = 2 * (natWord q).length := by simp [σ5, σ4, σ3, σ2, σ1, stp]
  have e6 := rewB_spec cap sHd rBIG rT (by decide) σ5
    (by simp +decide [σ5, σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0])
    (by rw [hsh5, b5]; exact hB) (by rw [b5]; exact hBc)
  rw [b5] at e6
  set σ6 := σ5.seth sHd 0 with hσ6
  have e7 := clear1 cap rX (q + 1) σ6 (by simp +decide [σ6, σ5, σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0])
    (by omega)
  set σ7 := σ6.setv rX 0 with hσ7
  have e8 := clear1 cap rY ((q + 1) ^ Db) σ7
    (by simp +decide [σ7, σ6, σ5, σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0]) (hPw Db le_rfl)
  set σ8 := σ7.setv rY 0 with hσ8
  have e9 := clear1 cap 33 Kb σ8
    (by simp +decide [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0]) hK
  set σ9 := σ8.setv 33 0 with hσ9
  have hfin : ∀ τ : WState 10 NR, τ.sh = σ0.sh → τ.st = σ0.st → τ.cell = σ0.cell →
      (∀ r, τ.val r = bigV (Kb * (q + 1) ^ Db) cdf r) → τ = ts src 0 [] (bigV (Kb * (q + 1) ^ Db) cdf) cl := by
    intro τ h1 h2 h3 h4
    apply WState.eq
    · rw [h1]; rfl
    · rw [h2]; rfl
    · funext r; rw [h4, ts_val_eq src 0 _ cl (by simp +decide [bigV])]
    · rw [h3]; rfl
  have sh9 : σ9.sh = σ0.sh := by
    funext i; by_cases hi : i = sHd
    · subst hi; simp [σ9, σ8, σ7, σ6, hσ0]; exact (ts_sh_src src _ _ _ _ _ (by decide) (by decide)).symm
    · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_of_ne hi]
  have va9 : ∀ r, r ≠ rCDF → σ9.val r = bigV (Kb * (q + 1) ^ Db) cdf r := by
    intro r hr
    fin_cases r <;> simp +decide [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, pR, mR, bigV, Function.update_apply, v0] at hr ⊢ <;>
      ring
  have cd9 : σ9.val rCDF = 0 := by simp +decide [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, pR, mR, Function.update_apply, v0]
  have hcost : (Db + 10) * (4 * UnaryPow.sq cap) = (Db + 1) * (4 * UnaryPow.sq cap) + 36 * UnaryPow.sq cap := by ring
  cases cdf
  · have e10 := WExec.skip (cap := cap) σ9
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
      (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 e10))))))))) (hfin σ9 sh9 rfl rfl (fun r => ?_)) ?_
    · by_cases hr : r = rCDF
      · subst hr; rw [cd9, bigV_cdf]; rfl
      · exact va9 r hr
    · unfold prefixCost; omega
  · have e10 := inc1 cap rCDF 0 σ9 cd9 (by omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
      (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 e10))))))))) (hfin _ sh9 rfl rfl (fun r => ?_)) ?_
    · by_cases hr : r = rCDF
      · subst hr; simp [bigV_cdf]
      · simp only [WState.setv_val]; rw [Function.update_of_ne hr]; exact va9 r hr
    · unfold prefixCost; omega

end Prefix

/-! ## The word program -/

section Pw
variable (cap : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The table writer's word program**: the prefix, the numbers, the table, the thresholds. -/
def pwW (Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ aV bV aT bT : ℕ) : WM 10 NR :=
  .seq (prefixW Kb Db cdf) (.seq (numP ζ Cδ) (.seq twP (compileL (thrOps aV bV aT bT))))

/-- The numbers' registers after the prefix (`p = L(q)`, `Λ̄ = Λ̄(q)`, `s = s(q)`). -/
noncomputable def nV (Kb Db : ℕ) (cdf : Bool) (Cδ q sys aux cb : ℕ) : Fin NR → ℕ :=
  numV (bigV (Kb * (q + 1) ^ Db) cdf) q sys aux cb (Ledger.Lq q) (Ledger.rowBLambda h0 h1 2 q)
    (Ledger.rowBSparse h0 h1 2 Cδ q)

theorem nV_out (Kb Db : ℕ) (cdf : Bool) (Cδ q sys aux cb : ℕ) :
    NumOut (nV h0 h1 Kb Db cdf Cδ q sys aux cb) (Kb * (q + 1) ^ Db) (if cdf then 1 else 0) q sys aux cb (Ledger.Lq q)
      (Ledger.rowBLambda h0 h1 2 q) (Ledger.rowBSparse h0 h1 2 Cδ q) := by
  have h := numV_out (bigV (Kb * (q + 1) ^ Db) cdf) q sys aux cb (Ledger.Lq q) (Ledger.rowBLambda h0 h1 2 q)
    (Ledger.rowBSparse h0 h1 2 Cδ q) (fun r h1 h2 => bigV_zero _ _ r h1 h2)
  rw [bigV_big, bigV_cdf] at h
  exact h

/-- The table writer's exit registers are the numbers' with `OK` set. -/
theorem regsOf_eq_update (w : Fin NR → ℕ) {B cdf q sys aux cb p Λ s : ℕ} (h : NumOut w B cdf q sys aux cb p Λ s)
    (ok : ℕ) : regsOf w Z4 Z4 Z4 ok = Function.update w rOK ok := by
  funext r
  unfold regsOf
  split_ifs with h1 h2 h3 h4
  · rw [h1]; simp
  · rw [Function.update_of_ne h1]; exact (h.zero r (digits_not_kept r ⟨h2.1, by omega⟩)).symm
  · rw [Function.update_of_ne h1]; exact (h.zero r (digits_not_kept r ⟨by omega, by omega⟩)).symm
  · rw [Function.update_of_ne h1]; exact (h.zero r (digits_not_kept r ⟨by omega, h4.2⟩)).symm
  · rw [Function.update_of_ne h1]

/-- The word program's cost. -/
noncomputable def pwCost (Kb Db : ℕ) (aV bV aT bT q sys aux cb nTW : ℕ) : ℕ :=
  prefixCost q Db (Kb * (q + 1) ^ Db) (UnaryPow.sq cap) + 1 +
    (numCost cap h0 h1 q sys aux cb (Kb * (q + 1) ^ Db) + 1 +
      (nTW + 1 + (thrOps aV bV aT bT).length * (200 * (cap + 2) * (cap + 2) + 1)))

theorem thr_frame (aV bV aT bT : ℕ) (u : Fin NR → ℕ) (r : Fin NR)
    (hr : r = rOP ∨ r = rOK ∨ r = rQQ ∨ r = rLL) : evalL (thrOps aV bV aT bT) u r = u r := by
  apply evalL_frame
  rcases hr with rfl | rfl | rfl | rfl <;> simp +decide [thrOps, writes]

/-- **The word program's run**: from every register clear, the table word on stream `0` (head at its end, its length
in `0`), `q` in `54`, `p = L(q)` in `52`, `OK` in `12`, and the accumulators' start `threshAcc` of the slack thresholds
in `24 … 29`, given the table writer's run on the numbers' registers. -/
theorem pw_spec (src : Fin 11 → List Bool) (cl : Bool) (Kb Db : ℕ) (cdf : Bool) (Cδ aV bV aT bT q sys aux cb : ℕ)
    (restH restP : List Bool) (hH : src sHd = enc true (natWord q) ++ restH)
    (hP : src sPO = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
    (hB : 2 * (natWord q).length ≤ Kb * (q + 1) ^ Db) (hK : Kb ≤ cap) (hq4 : q + 4 ≤ cap)
    (hPw : ∀ k ≤ Db, (q + 1) ^ k ≤ cap) (hBc : Kb * (q + 1) ^ Db ≤ cap)
    (hB2 : (natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length ≤
      Kb * (q + 1) ^ Db)
    (cq : 2 ^ (natBitLength q + 1) ≤ cap) (c3 : 2 ^ (natBitLength 3 + 1) ≤ cap)
    (cs : 2 ^ (natBitLength sys + 1) ≤ cap) (ca : 2 ^ (natBitLength aux + 1) ≤ cap)
    (cc : 2 ^ (natBitLength cb + 1) ≤ cap)
    (hsp : sparseBound ζ Cδ (Ledger.Lq q) (Ledger.rowBt h0 h1 q - 1) ≤ cap)
    (hc : numCap (Ledger.rowBSparse h0 h1 2 Cδ q) (Ledger.rowBLambda h0 h1 2 q) q sys aux cb ≤ cap)
    (tbl : List Bool) (ok nTW : ℕ)
    (hTW : WExec cap twP (ts src 0 [] (nV h0 h1 Kb Db cdf Cδ q sys aux cb) cl)
      (ts src 0 tbl (regsOf (nV h0 h1 Kb Db cdf Cδ q sys aux cb) Z4 Z4 Z4 ok) cl) nTW)
    (hbV : 1 ≤ bV) (hbT : 1 ≤ bT)
    (hthr : thrCap (Ledger.rowBSparse h0 h1 2 Cδ q * Ledger.rowBSparse h0 h1 2 Cδ q * Ledger.rowBSparse h0 h1 2 Cδ q *
      Ledger.rowBSparse h0 h1 2 Cδ q) (Ledger.Lq q) (2 ^ cb) (Ledger.rowBLambda h0 h1 2 q) aV bV aT bT ≤ cap)
    (D : Transfer.UnionCheckData) (hsD : D.s = Ledger.rowBSparse h0 h1 2 Cδ q)
    (hmD : D.mass = (Ledger.rowBLambda h0 h1 2 q : ℚ)) (hcbD : D.pcpp.clauseBits = cb) (v0 τ : ℚ)
    (hv0 : v0 = (aV : ℚ) / bV) (hτ : τ = (aT : ℚ) / bT) :
    ∃ τT : WState 10 NR, WExec cap (pwW Kb Db cdf ζ Cδ aV bV aT bT) (ts src 0 [] (fun _ => 0) cl) τT
        (pwCost cap h0 h1 Kb Db aV bV aT bT q sys aux cb nTW) ∧
      (∀ s, s ≠ sOut → τT.st s = src s) ∧ τT.cell = cl ∧
      τT.val rQQ = q ∧ τT.st sOut = tbl ∧ τT.sh sOut = tbl.length ∧ τT.val rOP = tbl.length ∧
      τT.val rLL = Ledger.Lq q ∧ τT.val rOK = ok ∧
      (fun i => τT.val (rAcc i)) = DecisionBridge.threshAcc
        ⌊Bridge.scaleVQ D (Ledger.Lq q) * (2 * v0 + slackOf D.mass (Ledger.Lq q))⌋
        ⌊Bridge.scaleVQ D (Ledger.Lq q) * (1 + v0 + slackOf D.mass (Ledger.Lq q))⌋
        ⌈Bridge.scaleMu D (Ledger.Lq q) * (τ - slackOf D.mass (Ledger.Lq q))⌉ := by
  set B := Kb * (q + 1) ^ Db with hBdef
  set w := nV h0 h1 Kb Db cdf Cδ q sys aux cb with hw
  have hN := nV_out h0 h1 Kb Db cdf Cδ q sys aux cb
  have e1 := prefix_spec cap src cl Kb Db cdf q restH hH hB hK cq (by omega) hPw hBc
  have e2 := numT cap src h0 h1 Cδ cl (bigV B cdf) q sys aux cb restH restP hH hP
    (fun r h1 h2 => bigV_zero _ _ r h1 h2) (by rw [bigV_big]; exact hB) (by rw [bigV_big]; exact hB2)
    (by rw [bigV_big]; exact hBc) cq c3 cs ca cc hq4 hsp hc
  rw [bigV_big] at e2
  set u := (ts src 0 tbl (regsOf w Z4 Z4 Z4 ok) cl).val with hu
  have ue : u = Function.update (Function.update w rOK ok) rOP tbl.length := by
    rw [hu, ← regsOf_eq_update w hN ok]; rfl
  have uw : ∀ r, r ≠ rOP → r ≠ rOK → u r = w r := fun r h1 h2 => by
    rw [ue, Function.update_of_ne h1, Function.update_of_ne h2]
  have hpre := thrOps_pre cap aV bV aT bT u _ _ _ _ (by rw [uw _ (by decide) (by decide)]; exact hN.ma)
    (by rw [uw _ (by decide) (by decide)]; exact hN.ll) (by rw [uw _ (by decide) (by decide)]; exact hN.mm)
    (by rw [uw _ (by decide) (by decide)]; exact hN.lam)
    (fun r hr => by
      rw [uw r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
      exact thrZero_numOut w hN r hr) hbV hbT hthr
  have e3 := opsT cap (thrOps aV bV aT bT) (ts src 0 tbl (regsOf w Z4 Z4 Z4 ok) cl) hpre
  have hcl := costL_le cap (thrOps aV bV aT bT) u hpre
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq hTW e3))) ?_, fun s hs => ?_, rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · unfold pwCost; rw [← hu, ← hBdef]; omega
  · show (ts src 0 tbl (regsOf w Z4 Z4 Z4 ok) cl).st s = src s
    exact ts_st src _ _ _ _ s hs
  · show evalL (thrOps aV bV aT bT) u rQQ = q
    rw [thr_frame _ _ _ _ _ _ (by simp), uw _ (by decide) (by decide)]; exact hN.qq
  · show (ts src 0 tbl (regsOf w Z4 Z4 Z4 ok) cl).st sOut = tbl
    exact ts_st_out src _ _ _ _
  · show (ts src 0 tbl (regsOf w Z4 Z4 Z4 ok) cl).sh sOut = tbl.length
    exact ts_sh_out src _ _ _ _
  · show evalL (thrOps aV bV aT bT) u rOP = tbl.length
    rw [thr_frame _ _ _ _ _ _ (by simp), ue]; simp
  · show evalL (thrOps aV bV aT bT) u rLL = Ledger.Lq q
    rw [thr_frame _ _ _ _ _ _ (by simp), uw _ (by decide) (by decide)]; exact hN.ll
  · show evalL (thrOps aV bV aT bT) u rOK = ok
    rw [thr_frame _ _ _ _ _ _ (by simp), ue, Function.update_of_ne (by decide)]; simp
  · show (fun i => evalL (thrOps aV bV aT bT) u (rAcc i)) = _
    exact accStart_eq D aV bV aT bT u _ _ _ cb (by rw [uw _ (by decide) (by decide)]; exact hN.ma)
      (by rw [uw _ (by decide) (by decide)]; exact hN.ll) (by rw [uw _ (by decide) (by decide)]; exact hN.mm)
      (by rw [uw _ (by decide) (by decide)]; exact hN.lam)
      (fun r hr => by
        rw [uw r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)]
        exact thrZero_numOut w hN r hr) hsD hmD hcbD v0 τ hv0 hτ (by omega) (by omega)

end Pw

end NearCubicWires.WireExponent3_5.UnionMachine.FrontPw
