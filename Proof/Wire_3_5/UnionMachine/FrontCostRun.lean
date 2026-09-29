import Proof.Wire_3_5.UnionMachine.FrontCostVal

/-! # C6 front, the time (8): the chain after phase 2 and the front's cost, per branch (P3:3669-3691)

**`valid_ok`** (on the valid branch the decoded guess passes its atoms and grid signs, and its entries' word opens the
rest), **`nums_le`** (the numbers' caps bound the counts), **`rejECost_le`**, **`rejACost_le`**, **`restCostOf_le`** (the
chain after phase 2 costs at most `10^81·n^40 + 400·rOf + β` at `n = N + 2` on every branch, `β` C1's call's budget at
the width), **`costOf_le`** (past the onset the front's cost is at most `4N + 20` plus phase 1, phase 2 and the chain).

Paper quantity of the main types: the front's time against the input length, the loop's capacity and C1's call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostRun
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt (esOf)

section Branch
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}
  {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The valid branch's guess** passes its atoms and grid signs, and its entries' word opens the rest. -/
theorem valid_ok (Cδ : ℕ) (hsS : ∀ q, S.gridSize q = Ledger.rowBSparse h0 h1 2 Cδ q) {N : ℕ} (x : BitInput N)
    (b : Bool) (t : List Bool) (O : BooleanCircuit (S.pcp.nativeWidth N)) (hsc : scanOK t = true)
    (hdec : CanonicalWitnessCodec.decodeBooleanCircuit (S.pcp.nativeWidth N) (value (payload t)) = some O)
    (harity : (S.request x O).arity = S.pcp.nativeWidth N) (hx : (restOf t).length + 1 ≤ (List.ofFn x).length)
    (hE' : (entScan (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
      Ledger.rowBSparse h0 h1 2 Cδ (S.pcp.nativeWidth N)) (restOf t)).isSome = true)
    (hv0' : FrontAtomLoop.verdictOf (S.pcp.nativeWidth N) (FrontAtomStageL.capP (List.ofFn x).length)
      ((S.pcp.nativeWidth N + 1) ^ I.descDeg) (modeOf b) (((S.pcppOf x O).systematicBits +
        (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.pcp.nativeWidth N))
      (payOf (restOf t) (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
        Ledger.rowBSparse h0 h1 2 Cδ (S.pcp.nativeWidth N))) = 0) :
    PlanW3.AtomsOkG (gOf S x b O (restOf t)) ∧
      ((gOf S x b O (restOf t)).checkData (gOf S x b O (restOf t)).translation).signsOk = true ∧
      (FrontTW.entsW (esOf (gOf S x b O (restOf t)))).length ≤ (restOf t).length := by
  have hEN := FrontSemRun.entN_eq h0 h1 Cδ hsS x O harity
  have hvA : FrontAtomLoop.verdictOf (S.request x O).arity (FrontAtomStageL.capP (List.ofFn x).length)
      ((S.pcp.nativeWidth N + 1) ^ I.descDeg) (modeOf b) (entN S x O) (payOf (restOf t) (entN S x O)) = 0 := by
    rw [harity, hEN]; exact hv0'
  obtain ⟨hd, hsg⟩ := FrontSemDec.valid_of b t hsc O hdec (by rw [hEN]; exact hE') _ _ hvA
  set g := gOf S x b O (restOf t) with hgdef
  have hg : ∀ e ∈ entsG g, e.1 ∈ gridSet := (signs_iff g _).1 hsg
  obtain ⟨kz, hrz⟩ := FrontSemDec.rest_of hd
  change restOf t = _ at hrz
  have hEg : ((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
      Ledger.rowBSparse h0 h1 2 Cδ (S.pcp.nativeWidth N) = (entsG g).length := by
    rw [← hEN]; exact FrontSemDec.entN_eq g
  have hvg : FrontAtomLoop.verdictOf g.q (FrontAtomStageL.capP (List.ofFn x).length) ((g.q + 1) ^ I.descDeg) g.mode
      (entsG g).length (payOf (((entsG g).map encE).flatten ++ List.replicate kz false) (entsG g).length) = 0 := by
    have e := hv0'
    rw [hEg, hrz, ← harity] at e
    exact e
  have hrest := (restAfter_enc (entsG g) (List.replicate kz false) hg).1
  have hat : PlanW3.AtomsOkG g := FrontSemDec.atoms_ok g (List.replicate kz false) hg _ _ (fun j hj => by
    have hl := FrontSemRun.pay_le _ _ _ hrest j hj
    have hx' : (((entsG g).map encE).flatten ++ List.replicate kz false).length + 1 ≤ (List.ofFn x).length := by
      rw [← hrz]; exact hx
    exact (FrontAtomStageL.capP_covers _ _ (by omega)).1) hvg
  refine ⟨hat, hsg, ?_⟩
  have e1 : FrontTW.entsW (esOf g) = ((entsG g).map encE).flatten := FrontSemEnt.entsW_esOf g hg
  have e2 : (restOf t).length = (((entsG g).map encE).flatten).length + kz := by
    rw [hrz, List.length_append, List.length_replicate]
  rw [e1, e2]
  omega

/-- **The numbers' caps bound the counts.** -/
theorem nums_le {cap Kb Db Cδ q sys aux cb : ℕ} (h : FrontCh3P.NumsCaps cap h0 h1 Kb Db Cδ q sys aux cb) :
    q ≤ cap ∧ sys ≤ cap ∧ aux ≤ cap ∧ cb ≤ cap ∧ Ledger.rowBSparse h0 h1 2 Cδ q ≤ cap ∧
      (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q ≤ cap ∧ Kb * (q + 1) ^ Db ≤ cap := by
  have hc1 := h.hcE
  have hc2 := h.cc
  have hc3 := CompilerMachine.Pool.lt_pow_natBitLength cb
  rw [pow_succ] at hc2
  have hc4 := h.hq4
  have hc5 := h.hBc
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The entries fail**: the chain's cost. -/
theorem rejECost_le (Dw Kw Dl Kb Db Cδ q sys aux cb N : ℕ) (xs r : List Bool) (hx : xs.length ≤ N + 2)
    (hr : r.length ≤ N + 2) (hnums : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (h2W : 2 * (Kw * (q + 1) ^ Dw) + 2 ≤ N + 2) (hDb : Db ≤ N + 2)
    (hP1 : PCPSerializerCapacity.Power.budget Dw Kw q ≤ N + 2) (hP2 : PCPSerializerCapacity.Power.budget Dl 1 q ≤ N + 2)
    (ht : Ledger.rowBt h0 h1 q ≤ N + 2) :
    FrontSemRun.rejECost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb xs r ≤ 10 ^ 31 * (N + 2) ^ 12 := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := nums_le h0 h1 hnums
  have b := FrontCostRest.ch3Cost_le h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb N xs r hx hr (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hDb hP1 hP2 (by omega) ht
  have p1 : N + 2 ≤ (N + 2) ^ 12 := Nat.le_self_pow (by norm_num) _
  unfold FrontSemRun.rejECost
  omega

/-- **An atom fails**: the chain's cost. -/
theorem rejACost_le (m : Mode) (Dw Kw Dl Kb Db Cδ q sys aux cb N : ℕ) (xs r : List Bool) (hx : xs.length ≤ N)
    (hr : r.length ≤ N) (hnums : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (h2W : 2 * (Kw * (q + 1) ^ Dw) + 2 ≤ N + 2) (hDb : Db ≤ N + 2)
    (hP1 : PCPSerializerCapacity.Power.budget Dw Kw q ≤ N + 2) (hP2 : PCPSerializerCapacity.Power.budget Dl 1 q ≤ N + 2)
    (ht : Ledger.rowBt h0 h1 q ≤ N + 2) (hL : (q + 1) ^ Dl ≤ N + 2) :
    FrontSemRun.rejACost m h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb xs r ≤ 10 ^ 81 * (N + 2) ^ 40 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := nums_le h0 h1 hnums
  have b := FrontCostRest.ch3Cost_le h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb N xs r (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hDb hP1 hP2 (by omega) ht
  have b2 := FrontCostRest.atCost_le m r xs q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) ((q + 1) ^ Dl) N hr hx
    (by omega) (by omega) hL
  have hn : 1 ≤ N + 2 := by omega
  have p1 : N + 2 ≤ (N + 2) ^ 40 := Nat.le_self_pow (by norm_num) _
  have p12 : (N + 2) ^ 12 ≤ (N + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  unfold FrontSemRun.rejACost
  omega

/-- **The chain after phase 2**: on every branch at most `10^81·n^40 + 400·rOf + β`, `n = N + 2`, `β` C1's call's
budget at the width. -/
theorem restCostOf_le (Kw Dw De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT Λ K : ℕ) {d : ℕ} (c : Plan.C1At d)
    {N : ℕ} (x : BitInput N) (b : Bool) (t : List Bool) (O : BooleanCircuit (S.pcp.nativeWidth N))
    (hsS : ∀ q, S.gridSize q = Ledger.rowBSparse h0 h1 2 Cδ q) (hr' : ∀ q, B.rOf q = Ledger.rowBr cr q)
    (hsc : scanOK t = true)
    (hdec : CanonicalWitnessCodec.decodeBooleanCircuit (S.pcp.nativeWidth N) (value (payload t)) = some O)
    (harity : (S.request x O).arity = S.pcp.nativeWidth N) (hx : (restOf t).length + 1 ≤ (List.ofFn x).length)
    (hnums : FrontCh3P.NumsCaps (2 * (Kw * (S.pcp.nativeWidth N + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ (S.pcp.nativeWidth N)
      (S.pcppOf x O).systematicBits (S.pcppOf x O).auxiliaryBits (S.pcppOf x O).clauseBits)
    (hcaps : ∀ g : UnionGuess S x, g.oracle = O → PlanW3.AtomsOkG g → (g.checkData g.translation).signsOk = true →
      FrontSemPath.PathCaps g h0 h1 Kw Dw I.descDeg De Ce Dt Ct Kb Db Cδ cr Vb c ∧
      FrontSemTW.EndCaps h0 h1 g (Kw * (g.q + 1) ^ Dw) Kb Db Cδ aV bV aT bT crT KT AT ∧
      (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf g))
    (hgenv : ∀ g : UnionGuess S x, g.oracle = O → PlanW3.AtomsOkG g → FrontSemCap1.GEnv g Λ K)
    (hΛ : Ledger.rowBLambda h0 h1 2 (S.pcp.nativeWidth N) ≤ K) (hVb : Vb ≤ N + 2)
    (h2W : 2 * (Kw * (S.pcp.nativeWidth N + 1) ^ Dw) + 2 ≤ N + 2)
    (hKW : 2 * (K * K * K * K) + 2 * K + 1 ≤ Kw * (S.pcp.nativeWidth N + 1) ^ Dw) (hDb : Db ≤ N + 2)
    (hP1 : PCPSerializerCapacity.Power.budget Dw Kw (S.pcp.nativeWidth N) ≤ N + 2)
    (hP2 : PCPSerializerCapacity.Power.budget I.descDeg 1 (S.pcp.nativeWidth N) ≤ N + 2)
    (hP3 : PCPSerializerCapacity.Power.budget I.carrierDeg 1 (S.pcp.nativeWidth N) ≤ N + 2)
    (hP4 : PCPSerializerCapacity.Power.budget De Ce (Kw * (S.pcp.nativeWidth N + 1) ^ Dw) ≤ N + 2)
    (hP5 : PCPSerializerCapacity.Power.budget Dt Ct (Kw * (S.pcp.nativeWidth N + 1) ^ Dw) ≤ N + 2)
    (hv : BlockPlatform.UnaryCalc.value Dt Ct (Kw * (S.pcp.nativeWidth N + 1) ^ Dw) ≤ N + 2)
    (hL : (S.pcp.nativeWidth N + 1) ^ I.descDeg ≤ N + 2) (ht : Ledger.rowBt h0 h1 (S.pcp.nativeWidth N) ≤ N + 2) :
    FrontSemRun.restCostOf h0 h1 Kw Dw De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c x b t O ≤
      10 ^ 81 * (N + 2) ^ 40 + 400 * FrontTail.rOf crT KT AT (S.pcp.nativeWidth N) +
        c.budgetAt B (S.pcp.nativeWidth N) := by
  have hxl : (List.ofFn x).length = N := List.length_ofFn
  have hn : 1 ≤ N + 2 := by omega
  have p12 : (N + 2) ^ 12 ≤ (N + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  unfold FrontSemRun.restCostOf
  dsimp only
  split_ifs with hE hv' hpre
  · have := rejECost_le h0 h1 Dw Kw I.descDeg Kb Db Cδ (S.pcp.nativeWidth N) (S.pcppOf x O).systematicBits
      (S.pcppOf x O).auxiliaryBits (S.pcppOf x O).clauseBits N (List.ofFn x) (restOf t) (by omega) (by omega)
      hnums h2W hDb hP1 hP2 ht
    omega
  · have := rejACost_le h0 h1 (modeOf b) Dw Kw I.descDeg Kb Db Cδ (S.pcp.nativeWidth N)
      (S.pcppOf x O).systematicBits (S.pcppOf x O).auxiliaryBits (S.pcppOf x O).clauseBits N (List.ofFn x) (restOf t)
      (by omega) (by omega) hnums h2W hDb hP1 hP2 ht hL
    omega
  · have hE' : (entScan (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
        Ledger.rowBSparse h0 h1 2 Cδ (S.pcp.nativeWidth N)) (restOf t)).isSome = true := by
      cases h : (entScan (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
          Ledger.rowBSparse h0 h1 2 Cδ (S.pcp.nativeWidth N)) (restOf t)).isSome
      · exact absurd h hE
      · rfl
    have hv0 := not_not.mp hv'
    obtain ⟨hat, hsg, hlen⟩ := valid_ok h0 h1 Cδ hsS x b t O hsc hdec harity hx hE' hv0
    obtain ⟨hPC, hEC, -⟩ := hcaps _ rfl hat hsg
    have hG := hgenv _ rfl hat
    have hgq : (gOf S x b O (restOf t)).q = S.pcp.nativeWidth N := harity
    have hb := FrontCostVal.validCost_le h0 h1 (gOf S x b O (restOf t)) c hpre (List.ofFn x)
      ((restOf t).length - (FrontTW.entsW (esOf (gOf S x b O (restOf t)))).length) hG hPC hEC
      (hr' _) (hsS (gOf S x b O (restOf t)).q) (by rw [hgq]; exact hΛ) (M := N) (by omega) (by omega) hVb
      (by rw [hgq]; exact h2W) (by rw [hgq]; exact hKW) hDb (by rw [hgq]; exact hP1) (by rw [hgq]; exact hP2)
      (by rw [hgq]; exact hP3) (by rw [hgq]; exact hP4) (by rw [hgq]; exact hP5) (by rw [hgq]; exact hv)
      (by rw [hgq]; exact hL) (by rw [hgq]; exact ht)
    have eb : (Plan.c1sized d c.E₁ c.c₁).budget ⟨FrontSelReq.selReqOf (gOf S x b O (restOf t)), hpre⟩ =
        c.budgetAt B (gOf S x b O (restOf t)).q := rfl
    rw [eb, hgq] at hb
    exact hb
  · exact Nat.zero_le _

end Branch

section Top
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}
  {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The front's cost past the onset**: at most `4N + 20` plus phase 1, phase 2 and the chain after it. -/
theorem costOf_le (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)
    (k Ap G Dw De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (C : ℕ) (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2)))
    (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (Kw Kb Db Cδ Ce Ct cr Vb aV bV aT bT crT KT AT : ℕ) {N : ℕ}
    (x : BitInput N) (w : List Bool) (hCN : C ≤ N) (P1 P2 R : ℕ)
    (hph1 : FrontTop.ph1C k Ap G (List.ofFn x) w ≤ P1)
    (hph2 : ∀ O : BooleanCircuit (S.pcp.nativeWidth N),
      O.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G (S.pcp.nativeWidth N) →
      ∀ hq : PCPPNativeHierarchyNodes.width source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x ≤
        S.pcp.nativeWidth N, FrontTop.ph2C source a k Hh Cpad hpad x (S.pcp.nativeWidth N) hq O ≤ P2)
    (hrest : ∀ O : BooleanCircuit (S.pcp.nativeWidth N), FrontOracleField.okOf w = true →
      CanonicalWitnessCodec.decodeBooleanCircuit (S.pcp.nativeWidth N) (value (payload w.tail)) = some O →
      O.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G (S.pcp.nativeWidth N) →
      FrontSemRun.restCostOf h0 h1 Kw Dw De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c x (w.headD false) w.tail O ≤
        R) :
    FrontSemRun.costOf (S := S) source a k Ap G Dw De Dt c C Hh Cpad hpad Kw h0 h1 Kb Db Cδ Ce Ct cr Vb aV bV aT bT
      crT KT AT x w ≤ 4 * N + 20 + P1 + P2 + R := by
  unfold FrontSemRun.costOf
  rw [if_neg (by omega)]
  by_cases hO : FrontOracleField.okOf w = false
  · rw [if_pos hO]; omega
  rw [if_neg hO]
  have hO' : FrontOracleField.okOf w = true := by
    cases h : FrontOracleField.okOf w
    · exact absurd h hO
    · rfl
  split
  · omega
  · rename_i O hdec
    by_cases hsz : O.size ≤ RecoveryScheduleEnvelope.oracleSizeBound G (S.pcp.nativeWidth N)
    · rw [if_pos hsz]
      by_cases hq : PCPPNativeHierarchyNodes.width source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x ≤
          S.pcp.nativeWidth N
      · rw [dif_pos hq]
        have e1 := hph2 O hsz hq
        have e2 := hrest O hO' hdec hsz
        omega
      · rw [dif_neg hq]; omega
    · rw [if_neg hsz]; omega

end Top

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostRun
