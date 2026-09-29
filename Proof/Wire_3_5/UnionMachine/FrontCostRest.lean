import Proof.Wire_3_5.UnionMachine.FrontCostPh1

/-! # C6 front, the time (3): the chain after phase 2 is `O(n^D)` for atoms `≤ n` (P3:3669-3691)

With `n = N + 2` above every atom of the chain's costs (the input and rest lengths, `q`, the PCPP counts, the grid, the
width `W`, the data bound, the power budgets, …), each stage's cost is at most a fixed numeral times a fixed power
of `n` (`c6np`): **`ch3Cost_le`** (phase 3: the powers, the copies, the request head, the numbers, the entries).

Paper quantity of the main types: the front's per-stage time against the input length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostRest
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit

/-- A field read's cost. -/
theorem readC_le (x : ℕ) : FrontTW.readC x ≤ (x + 3) * (80 * x + 120) := by
  unfold FrontTW.readC
  have h1 := FrontSemEv.nbl_le_self x
  have h2 := C1Cnt.pow_nbl_le x
  calc (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (x + 3) * (40 * (2 * x + 2) + 40) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = (x + 3) * (80 * x + 120) := by ring

section Ch3
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **Phase 3's cost.** -/
theorem ch3Cost_le (Dw Kw Dl Kb Db Cδ q sys aux cb N : ℕ) (x r : List Bool) (hx : x.length ≤ N + 2)
    (hr : r.length ≤ N + 2) (hq : q ≤ N + 2) (hsys : sys ≤ N + 2) (haux : aux ≤ N + 2) (hcb : cb ≤ N + 2)
    (hW : Kw * (q + 1) ^ Dw ≤ N + 2) (hB : Kb * (q + 1) ^ Db ≤ N + 2) (hDb : Db ≤ N + 2)
    (hP1 : PCPSerializerCapacity.Power.budget Dw Kw q ≤ N + 2) (hP2 : PCPSerializerCapacity.Power.budget Dl 1 q ≤ N + 2)
    (hs : Ledger.rowBSparse h0 h1 2 Cδ q ≤ N + 2) (ht : Ledger.rowBt h0 h1 q ≤ N + 2) :
    FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb x r ≤ 10 ^ 30 * (N + 2) ^ 12 := by
  have hn : 1 ≤ N + 2 := by omega
  have hb1 := FrontSemEv.nbl_le_self q
  have hb2 := C1Cnt.pow_nbl_le q
  have hr1 := readC_le q
  have hr2 := readC_le 3
  have hr3 := readC_le sys
  have hr4 := readC_le aux
  have hr5 := readC_le cb
  have h4 : natBitLength 4 ≤ 3 := by decide
  have hno : FrontTW.numOps.length ≤ 100 := by decide
  have hco : FrontNums.countOps.length ≤ 100 := by decide
  unfold FrontCh3P.ch3Cost FrontFmtHd.hdCost FrontNums.numsCost FrontPw.prefixCost FrontTW.numCost FrontTW.readsCost
    PrimAsm.UnaryPow.sq FrontEntriesStage.esCost FrontEntries.entCost
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

end Ch3

/-! ## The atom stage -/

theorem roundsOf_le (q W L : ℕ) (m : Mode) (E : ℕ) (pay : ℕ → List Bool) : FrontAtomLoop.roundsOf q W L m E pay ≤ E := by
  classical
  unfold FrontAtomLoop.roundsOf
  split
  · rename_i h
    have := (Nat.find_spec h).1; omega
  · exact le_rfl

theorem payOf_le : ∀ (E : ℕ) (u : List Bool) (j : ℕ), (FrontDecode.payOf u E j).length ≤ u.length
  | 0, u, j => by simp [FrontDecode.payOf, FrontDecode.entsOf]
  | E + 1, u, j => by
    unfold FrontDecode.payOf FrontDecode.entsOf
    cases h : FrontEntriesRef.entStep u with
    | none => simp
    | some e =>
      obtain ⟨s, p, r⟩ := e
      obtain ⟨-, hu⟩ := FrontDecode.entStep_parts u s p r h
      have hl : u.length = (FrontDecode.entWord (s, p)).length + r.length := by rw [hu, List.length_append]
      have hw : (FrontDecode.entWord (s, p)).length = 2 * p.length + 5 := FrontDecode.entWord_length (s, p)
      cases j with
      | zero => simp; omega
      | succ j =>
        have ih := payOf_le E r j
        unfold FrontDecode.payOf at ih
        simp only [List.getD_cons_succ]
        omega

theorem KcOf_le (u : List Bool) (E : ℕ) :
    FrontSemPath.KcOf (FrontDecode.payOf u E) E ≤ 70 * (u.length + 2) := by
  unfold FrontSemPath.KcOf
  exact FrontSemFold.supR_le _ _ _ (fun j _ => by have := payOf_le E u j; omega)

theorem KdOf_le (nx : ℕ) (u : List Bool) (E : ℕ) :
    FrontSemPath.KdOf nx (FrontDecode.payOf u E) E ≤ 1000 * (u.length + 2) * (FrontAtomStageL.capP nx + 1) := by
  unfold FrontSemPath.KdOf
  refine FrontSemFold.supR_le _ _ _ (fun j _ => ?_)
  unfold CloseoutRowsCircuitWholeBudget.budget
  have := payOf_le E u j
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))

/-- **The atom stage's cost** at the chain's arguments. -/
theorem atCost_le (m : Mode) (r xs : List Bool) (q En L N : ℕ) (hr : r.length ≤ N) (hx : xs.length ≤ N)
    (hq : q ≤ N + 2) (hE : En ≤ N + 2) (hL : L ≤ N + 2) :
    FrontAtP.atCost m r xs.length q En xs.length L (FrontSemPath.KcOf (FrontDecode.payOf r En) En)
      (FrontSemPath.KdOf xs.length (FrontDecode.payOf r En) En) (FrontDecode.payOf r En) ≤ 10 ^ 80 * (N + 2) ^ 40 := by
  have hn : 1 ≤ N + 2 := by omega
  have hkc := KcOf_le r En
  have hkd := KdOf_le xs.length r En
  have hro := roundsOf_le q (FrontAtomStageL.capP xs.length) L m En (FrontDecode.payOf r En)
  have hcap : FrontAtomStageL.capP xs.length ≤ 1000000000000000000000000000000 * (xs.length + 1) ^ 26 :=
    le_of_eq (FrontAtomStageL.capP_eq xs.length).symm
  have hdp := CloseoutRowsEstimator.DriverPower.budget_linear 26 1000000000000000000000000000000 xs.length
    (by norm_num) (by norm_num)
  have hx1 : xs.length + 1 ≤ N + 2 := by omega
  have hx2 : xs.length ≤ N + 2 := by omega
  have hr2 : r.length ≤ N + 2 := by omega
  unfold FrontAtP.atCost FrontAtomStageL.setupCost FrontAtomLoop.roundCost
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

/-! ## Phase 5 (the formats and the writers' fold) -/

/-- **Phase 5's cost.** -/
theorem ch5Cost_le (m : Mode) (W r s Wn nv q sys aux cb n0 deg De Ce Dt Ct fnv cw N : ℕ) (hW : W ≤ N + 2)
    (hr : r ≤ N + 2) (hs : s ≤ N + 2) (hWn : Wn ≤ N + 2) (hnv : nv ≤ N + 2) (hq : q ≤ N + 2) (hsys : sys ≤ N + 2)
    (haux : aux ≤ N + 2) (hcb : cb ≤ N + 2) (hn0 : n0 ≤ N + 2) (hc : (CWConst.constWord m).length ≤ N + 2)
    (hp1 : PCPSerializerCapacity.Power.budget deg 1 q ≤ N + 2)
    (hp2 : PCPSerializerCapacity.Power.budget De Ce n0 ≤ N + 2)
    (hp3 : PCPSerializerCapacity.Power.budget Dt Ct n0 ≤ N + 2)
    (hv : BlockPlatform.UnaryCalc.value Dt Ct n0 ≤ N + 2) (hfnv : fnv ≤ N + 2) (hcw : cw ≤ N + 2) :
    FrontCh5.ch5Cost m W r s Wn nv q sys aux cb n0 deg De Ce Dt Ct fnv cw ≤ 10 ^ 12 * (N + 2) ^ 6 := by
  have hn : 1 ≤ N + 2 := by omega
  have b3 := FrontSemEv.nbl_le_self 3
  have b4 := FrontSemEv.nbl_le_self sys
  have b5 := FrontSemEv.nbl_le_self aux
  have b6 := FrontSemEv.nbl_le_self cb
  unfold FrontCh5.ch5Cost FrontFmtCA.caCost FrontFmtBM.bmCost FrontFoldStage.stageCost FrontFoldStage.setupCost
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostRest
