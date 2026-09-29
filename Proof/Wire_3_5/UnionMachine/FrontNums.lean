import Proof.Wire_3_5.UnionMachine.FrontPw
import Proof.Wire_3_5.UnionMachine.FrontWfDock

/-! # C6 front, the chain: the numbers' counts (P3:3669-3674)

The chain's later stages read unary counts of the guess's sizes: the entries `1^E` (`E = (sys+aux)·s`), the grid size
`1^s`, the systematic and auxiliary variables `1^sys`, `1^aux`, `1^{nv}` (`nv = sys + aux`; also the parities' flag
string `sPF`, all ones), and the fold's count word `0 1^{nv}`. **`numsW`** computes them on the table writer's layout:
the prefix and the numbers (M43 `prefixW`, M18 `numP`: `sys`, `s`, `E` from the request head and the PCPP output),
`nv = E / s` and `aux = nv − sys` (`countOps`), then one unary emission per count onto the free streams.
**`nums_spec`**: the six count streams, the two read streams kept.

Paper quantity of the main type: the sizes of the guess (its entries, grid size, variables). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontNums
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW NearCubicWires.WireExponent3_5.UnionMachine.FrontOps
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit NearCubicWires.WireExponent3_5.UnionMachine.FrontPw
open NearCubicWires.RepairRepresentation (natWord)

section Counts
variable (cap : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- `nv := E / s` into `13`, `aux := nv − sys` into `14`. -/
def countOps : List (ROp NR) :=
  [.copy rEE 30 31, .div ⟨![30, rSS, 13, 32, 33, 34, 35, 36, 37], by decide⟩, .clear 30,
   .copy 13 14 31, .sub ⟨![14, rSYS, 32, 33], by decide⟩]

/-- The emissions: `1^E` (stream `0`), `1^s` (`2`), `1^sys` (`4`), `1^aux` (`5`), `1^{nv}` (`6`), `0 1^{nv}` (`7`). -/
def emitsW : WM 10 NR :=
  .seq (emitOnes 0 15 rEE 16) (.seq (emitOnes 2 17 rSS 16) (.seq (emitOnes 4 18 rSYS 16) (.seq (emitOnes 5 19 14 16)
  (.seq (emitOnes 6 20 13 16) (.seq (emitC 7 24 false) (emitOnes 7 24 13 16))))))

/-- **The numbers' counts program.** -/
def numsW (Kb Db : ℕ) (cdf : Bool) (ζ : ℚ) (Cδ : ℕ) : WM 10 NR :=
  .seq (prefixW Kb Db cdf) (.seq (numP ζ Cδ) (.seq (compileL countOps) emitsW))

theorem countOps_pre (u : Fin NR → ℕ) (E s sys nv : ℕ) (hE : u rEE = E) (hs : u rSS = s) (hsys : u rSYS = sys)
    (hz : ∀ r : Fin NR, r ∈ [13, 14, 30, 31, 32, 33, 34, 35, 36, 37] → u r = 0) (hs1 : 1 ≤ s) (hEs : E = nv * s)
    (hsn : sys ≤ nv) (hc : E + s + nv + 2 ≤ cap) : preL cap countOps u := by
  have z : ∀ r : Fin NR, r ∈ [13, 14, 30, 31, 32, 33, 34, 35, 36, 37] → u r = 0 := hz
  have hq : E / s = nv := by rw [hEs]; exact Nat.mul_div_cancel _ (by omega)
  have hm : E % s = 0 := by rw [hEs]; exact Nat.mul_mod_left _ _
  simp +decide [countOps, preL, pre, eval, Function.update_apply, hE, hs, hsys, z, hq, hm]
  omega

theorem countOps_val (u : Fin NR → ℕ) (E s sys nv : ℕ) (hE : u rEE = E) (hs : u rSS = s) (hsys : u rSYS = sys)
    (hz : ∀ r : Fin NR, r ∈ [13, 14, 30, 31, 32, 33, 34, 35, 36, 37] → u r = 0) (hs1 : 1 ≤ s) (hEs : E = nv * s) :
    evalL countOps u 13 = nv ∧ evalL countOps u 14 = nv - sys ∧ evalL countOps u rEE = E ∧
      evalL countOps u rSS = s ∧ evalL countOps u rSYS = sys ∧ ∀ r : Fin NR, r ∈ [15, 16, 17, 18, 19, 20, 24] →
        evalL countOps u r = u r := by
  have z : ∀ r : Fin NR, r ∈ [13, 14, 30, 31, 32, 33, 34, 35, 36, 37] → u r = 0 := hz
  have hq : E / s = nv := by rw [hEs]; exact Nat.mul_div_cancel _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp +decide [countOps, evalL, eval, Function.update_apply, hE, hs, hsys, z, hq]
  · simp +decide [countOps, evalL, eval, Function.update_apply, hE, hs, hsys, z, hq]
  · simp +decide [countOps, evalL, eval, Function.update_apply, hE, hs, hsys, z, hq]
  · simp +decide [countOps, evalL, eval, Function.update_apply, hE, hs, hsys, z, hq]
  · simp +decide [countOps, evalL, eval, Function.update_apply, hE, hs, hsys, z, hq]
  · intro r hr
    apply evalL_frame
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [countOps, writes]

end Counts

/-! ## The run -/

section Run
variable (cap : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- The counts program's cost. -/
noncomputable def numsCost (Kb Db q sys aux cb E s nv : ℕ) : ℕ :=
  prefixCost q Db (Kb * (q + 1) ^ Db) (UnaryPow.sq cap) + 1 +
    (numCost cap h0 h1 q sys aux cb (Kb * (q + 1) ^ Db) + 1 +
      (countOps.length * (200 * (cap + 2) * (cap + 2) + 1) + 1 + (22 * (E + s + sys + aux + 2 * nv) + 40)))

/-- **The counts' run**: from every register clear and the free streams blank, the six count streams. -/
theorem nums_spec (src : Fin 11 → List Bool) (cl : Bool) (Kb Db : ℕ) (cdf : Bool) (Cδ q sys aux cb : ℕ)
    (restH restP : List Bool) (hH : src sHd = enc true (natWord q) ++ restH)
    (hP : src sPO = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
    (hB : 2 * (natWord q).length ≤ Kb * (q + 1) ^ Db) (hK : Kb ≤ cap) (hq4 : q + 4 ≤ cap)
    (hPw : ∀ k ≤ Db, (q + 1) ^ k ≤ cap) (hBc : Kb * (q + 1) ^ Db ≤ cap)
    (hB2 : (natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length ≤
      Kb * (q + 1) ^ Db)
    (cq : 2 ^ (natBitLength q + 1) ≤ cap) (c3 : 2 ^ (natBitLength 3 + 1) ≤ cap)
    (cs : 2 ^ (natBitLength sys + 1) ≤ cap) (ca : 2 ^ (natBitLength aux + 1) ≤ cap)
    (cc : 2 ^ (natBitLength cb + 1) ≤ cap)
    (hsp : SparseNum.sparseBound ζ Cδ (Ledger.Lq q) (Ledger.rowBt h0 h1 q - 1) ≤ cap)
    (hc : numCap (Ledger.rowBSparse h0 h1 2 Cδ q) (Ledger.rowBLambda h0 h1 2 q) q sys aux cb ≤ cap)
    (hs1 : 1 ≤ Ledger.rowBSparse h0 h1 2 Cδ q)
    (hcE : (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q + Ledger.rowBSparse h0 h1 2 Cδ q + (sys + aux) + 2 ≤ cap)
    (hbl : src 2 = [] ∧ src 4 = [] ∧ src 5 = [] ∧ src 6 = [] ∧ src 7 = []) :
    ∃ τ : WState 10 NR, WExec cap (numsW Kb Db cdf ζ Cδ) (ts src 0 [] (fun _ => 0) cl) τ
        (numsCost cap h0 h1 Kb Db q sys aux cb ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q)
          (Ledger.rowBSparse h0 h1 2 Cδ q) (sys + aux)) ∧
      τ.st 0 = List.replicate ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) true ∧
      τ.st 2 = List.replicate (Ledger.rowBSparse h0 h1 2 Cδ q) true ∧ τ.st 4 = List.replicate sys true ∧
      τ.st 5 = List.replicate aux true ∧ τ.st 6 = List.replicate (sys + aux) true ∧
      τ.st 7 = false :: List.replicate (sys + aux) true ∧ τ.st sHd = src sHd ∧ τ.st sPO = src sPO := by
  have hN := nV_out h0 h1 Kb Db cdf Cδ q sys aux cb
  set s := Ledger.rowBSparse h0 h1 2 Cδ q with hsdef
  set V := nV h0 h1 Kb Db cdf Cδ q sys aux cb with hV
  have e1 := prefix_spec cap src cl Kb Db cdf q restH hH hB hK cq (by omega) hPw hBc
  have e2 := numT cap src h0 h1 Cδ cl (bigV (Kb * (q + 1) ^ Db) cdf) q sys aux cb restH restP hH hP
    (fun r h1 h2 => bigV_zero _ _ r h1 h2) (by rw [bigV_big]; exact hB) (by rw [bigV_big]; exact hB2)
    (by rw [bigV_big]; exact hBc) cq c3 cs ca cc hq4 hsp hc
  rw [bigV_big] at e2
  have hVz : ∀ r : Fin NR, r ∈ [13, 14, 30, 31, 32, 33, 34, 35, 36, 37] → V r = 0 := fun r hr =>
    hN.zero r (by revert r; decide)
  have hEE : V rEE = (sys + aux) * s := by rw [hN.ee]; ring
  have hpre := countOps_pre cap V ((sys + aux) * s) s sys (sys + aux) hEE hN.ss hN.sy hVz hs1 rfl (by omega)
    (by omega)
  have hVO : V rOP = 0 := hN.zero _ (by decide)
  have e3 := opsT cap countOps (ts src 0 [] V cl) (by rw [ts_val_eq src 0 V cl hVO]; exact hpre)
  rw [ts_val_eq src 0 V cl hVO] at e3
  obtain ⟨u13, u14, uE, uS, uY, ufr⟩ := countOps_val V ((sys + aux) * s) s sys (sys + aux) hEE hN.ss hN.sy hVz hs1 rfl
  set U := evalL countOps V with hU
  have hcl := costL_le cap countOps V hpre
  have hUO : U rOP = 0 := by rw [hU, evalL_frame _ _ rOP (by simp +decide [countOps, writes])]; exact hVO
  rw [withVal_ts src 0 V U cl hUO] at e3
  have uz : ∀ r : Fin NR, r ∈ [15, 16, 17, 18, 19, 20, 24] → U r = 0 := fun r hr => by
    rw [ufr r hr]; exact hN.zero r (by revert r hr; decide)
  set σA := ts src 0 [] U cl with hσA
  have vA : σA.val = Function.update U rOP 0 := rfl
  have stA : ∀ i : Fin 11, i ≠ sOut → σA.st i = src i := fun i hi => ts_st src _ _ _ _ i hi
  have shA : ∀ i : Fin 11, i ≠ sOut → i ≠ sPO → σA.sh i = 0 := fun i h1 h2 => ts_sh_src src _ _ _ _ i h1 h2
  have f1 := emitOnes_spec cap 0 15 rEE 16 (by decide) (by decide) (by decide) σA
    (by rw [vA]; simp +decide [uz]) (by simp [σA]) (by rw [vA]; simp +decide [uz, uE]; omega)
    (by rw [vA]; simp +decide [uE]; omega)
  rw [show σA.val rEE = (sys + aux) * s by rw [vA]; simp +decide [uE]] at f1
  set σB := appendO σA 0 15 (List.replicate ((sys + aux) * s) true) with hσB
  have f2 := emitOnes_spec cap 2 17 rSS 16 (by decide) (by decide) (by decide) σB
    (by simp +decide [σB, vA, uz]) (by simp +decide [σB, shA, stA, hbl.1])
    (by simp +decide [σB, vA, uz, uS]; omega) (by simp +decide [σB, vA, uS]; omega)
  rw [show σB.val rSS = s by simp +decide [σB, vA, uS]] at f2
  set σC := appendO σB 2 17 (List.replicate s true) with hσC
  have f3 := emitOnes_spec cap 4 18 rSYS 16 (by decide) (by decide) (by decide) σC
    (by simp +decide [σC, σB, vA, uz]) (by simp +decide [σC, σB, shA, stA, hbl.2.1])
    (by simp +decide [σC, σB, vA, uz, uY]; omega) (by simp +decide [σC, σB, vA, uY]; omega)
  rw [show σC.val rSYS = sys by simp +decide [σC, σB, vA, uY]] at f3
  set σD := appendO σC 4 18 (List.replicate sys true) with hσD
  have f4 := emitOnes_spec cap 5 19 14 16 (by decide) (by decide) (by decide) σD
    (by simp +decide [σD, σC, σB, vA, uz]) (by simp +decide [σD, σC, σB, shA, stA, hbl.2.2.1])
    (by simp +decide [σD, σC, σB, vA, uz, u14]; omega) (by simp +decide [σD, σC, σB, vA, u14]; omega)
  rw [show σD.val 14 = sys + aux - sys by simp +decide [σD, σC, σB, vA, u14]] at f4
  rw [show sys + aux - sys = aux by omega] at f4
  set σE := appendO σD 5 19 (List.replicate aux true) with hσE
  have f5 := emitOnes_spec cap 6 20 13 16 (by decide) (by decide) (by decide) σE
    (by simp +decide [σE, σD, σC, σB, vA, uz]) (by simp +decide [σE, σD, σC, σB, shA, stA, hbl.2.2.2.1])
    (by simp +decide [σE, σD, σC, σB, vA, uz, u13]; omega) (by simp +decide [σE, σD, σC, σB, vA, u13]; omega)
  rw [show σE.val 13 = sys + aux by simp +decide [σE, σD, σC, σB, vA, u13]] at f5
  set σF := appendO σE 6 20 (List.replicate (sys + aux) true) with hσF
  have f6 := emitC_spec cap 7 24 false σF (by simp +decide [σF, σE, σD, σC, σB, shA, stA, hbl.2.2.2.2])
    (by simp +decide [σF, σE, σD, σC, σB, vA, uz]; omega)
  set σG := ((σF.sets 7 (σF.st 7 ++ [false])).seth 7 (σF.sh 7 + 1)).setv 24 (σF.val 24 + 1) with hσG
  have f7 := emitOnes_spec cap 7 24 13 16 (by decide) (by decide) (by decide) σG
    (by simp +decide [σG, σF, σE, σD, σC, σB, vA, uz])
    (by simp +decide [σG, σF, σE, σD, σC, σB, shA, stA, hbl.2.2.2.2])
    (by simp +decide [σG, σF, σE, σD, σC, σB, vA, uz, u13]; omega)
    (by simp +decide [σG, σF, σE, σD, σC, σB, vA, u13]; omega)
  rw [show σG.val 13 = sys + aux by simp +decide [σG, σF, σE, σD, σC, σB, vA, u13]] at f7
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq f1 (WExec.seq f2 (WExec.seq f3
    (WExec.seq f4 (WExec.seq f5 (WExec.seq f6 f7))))))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold numsCost; omega
  all_goals simp +decide [σG, σF, σE, σD, σC, σB, σA, stA, hbl, ts]

end Run

end NearCubicWires.WireExponent3_5.UnionMachine.FrontNums
