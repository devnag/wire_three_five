import Lean
import Proof.Wire_3_5.UnionMachine.FrontCostRun
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontCaps
import Proof.Wire_3_5.UnionMachine.FrontCostLedger
import Proof.Wire_3_5.UnionMachine.FrontSemCap1
import Proof.Wire_3_5.UnionMachine.FrontSemEnvS
import Proof.Wire_3_5.UnionMachine.FrontSemEvS
import Proof.Wire_3_5.UnionMachine.FrontSemRun
import Proof.Wire_3_5.UnionMachine.FrontSemSUE
import Proof.Wire_3_5.UnionMachine.FrontSemTopS
import Proof.Wire_3_5.UnionMachine.PlanW2
import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Wire_3_5.UnionMachine.FrontCostSUEBase


noncomputable section
set_option maxRecDepth 120000


/-! # C6 front, the time (9): the front's cost at the pinned setup (P3:3632-3691, 3797-3811)

**`obE`**/**`obc`** (the guessed-oracle PCPP check's exponents at the gate, functions of the literals only),
**`costDeg`** (the front's polynomial degree `max 40 (obE + 4)`), **`KfT`** (the time factor `81600000·2^{A_main} + 1`),
**`atomQ`** (every width-level quantity the chain's cost reads, one polynomial of the width; **`atoms_ev`**: at most `N`
past a threshold), **`time_ev`** (the clock's bits within `N + 2`), and **`cost_ev`**: when `costDeg + 1 ≤ kE`, past a
threshold and the onset, on every input and witness the front's cost is at most `KfT·(q+1)^7·(callBudget q + β(q))`,
`β` C1's call's budget at the width.

Paper quantity of the main type: the front's time against the per-call budget and C1's call (`FrontAtW3.costAcc`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostSUE
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU PQ)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open Filter

/-- **The front's polynomial degree** in `N`: the chain's `40` (the cold front end's `(N+1)^2·q^{O(1)}` lies below it),
an absolute constant below the clock (`kclk + 1 = 42`). -/
def costDeg (_l : Literals) : ℕ := 40

/-- **The front's time factor** `81600000·2^{A_main} + 1`. -/
noncomputable def KfT (l : Literals) (F : GateFree l) : ℕ := 81600000 * 2 ^ (gate0 l F).E.Amain + 1

section SUE
variable (l : Literals) (F : GateFree l) (e coef A : ℕ) (L : Language) (hL : InNTIME (fun n => n ^ (kE l e + 2)) L)

/-- **Every width-level quantity the chain's cost reads**, one polynomial of the width. -/
noncomputable def atomQ (q : ℕ) : ℕ :=
  MSS l F e coef A L hL q + (2 * (KwS l F e coef A L hL * (q + 1) ^ DwS l F e coef A L hL) + 2) +
    DbS l F e coef A L hL +
    BlockPlatform.UnaryCalc.polyCoefficient (DwS l F e coef A L hL) (KwS l F e coef A L hL) *
      (q + 2) ^ (DwS l F e coef A L hL + 1) +
    BlockPlatform.UnaryCalc.polyCoefficient (IUE l F e coef A).descDeg 1 * (q + 2) ^ ((IUE l F e coef A).descDeg + 1) +
    BlockPlatform.UnaryCalc.polyCoefficient (IUE l F e coef A).carrierDeg 1 *
      (q + 2) ^ ((IUE l F e coef A).carrierDeg + 1) +
    BlockPlatform.UnaryCalc.polyCoefficient (DeS l F e coef A) (CeS l F e coef A) *
      (KwS l F e coef A L hL * (q + 1) ^ DwS l F e coef A L hL + 2) ^ (DeS l F e coef A + 1) +
    BlockPlatform.UnaryCalc.polyCoefficient (DtS l F e coef A L hL) (CtS l F e coef A L hL) *
      (KwS l F e coef A L hL * (q + 1) ^ DwS l F e coef A L hL + 2) ^ (DtS l F e coef A L hL + 1) +
    BlockPlatform.UnaryCalc.value (DtS l F e coef A L hL) (CtS l F e coef A L hL)
      (KwS l F e coef A L hL * (q + 1) ^ DwS l F e coef A L hL) +
    (q + 1) ^ (IUE l F e coef A).descDeg + (JS l * (q + 2) + 1) + q

theorem atomQ_pq : PQ (atomQ l F e coef A L hL) := by
  have hM := MSS_pq l F e coef A L hL
  unfold atomQ BlockPlatform.UnaryCalc.value
  c6pq

/-- **The chain's atoms are at most `N`** past a threshold. -/
theorem atoms_ev : ∀ᶠ N : ℕ in atTop, atomQ l F e coef A L hL ((BU l F e coef A).q N) ≤ N := by
  obtain ⟨c, d, h⟩ := atomQ_pq l F e coef A L hL
  filter_upwards [FrontSemEv.polyq_le (kE l e) (gateApad l) c d] with N hN
  rw [FrontSemEvS.bu_q]
  exact (h _).trans hN

/-- **The front's cost at the live pinned setup**: when `costDeg + 1 ≤ kE`, past a threshold, at every onset `C ≤ N`,
on every input and witness, the front's cost is at most `KfT·(q+1)^7·(callBudget q + β(q))`. -/
theorem cost_ev (h : L = recL l (kE l e)) (hcoef : 1 ≤ coef) (hdeg : costDeg l + 1 ≤ kE l e)
    (c : Plan.C1At (dS l F e coef A L hL)) :
    ∃ N₂ : ℕ, ∀ N, N₂ ≤ N → ∀ C, C ≤ N → ∀ (x : BitInput N) (w : List Bool), w.length = N / 16 →
      FrontSemRun.costOf (S := SUE l F e coef A L hL) (cnwS l F e coef A L hL) (kE l e) (gateApad l)
        (recOracleDeg l) (DwS l F e coef A L hL) (DeS l F e coef A) (DtS l F e coef A L hL) c C (KwS l F e coef A L hL)
        (gateZeta_pos l) (gateZeta_lt l) (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l)
        (CeS l F e coef A) (CtS l F e coef A L hL) F.cr
        (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
        (32 * coef + 1) (gate0 l F).E.Amain x w ≤
      KfT l F * ((BU l F e coef A).q N + 1) ^ (callDegMargin - 1) *
        ((BU l F e coef A).callBudget ((BU l F e coef A).q N) + c.budgetAt (BU l F e coef A) ((BU l F e coef A).q N)) := by
  obtain ⟨N₁, hN₁⟩ := topFacts_ev l F e coef A L hL h c
  obtain ⟨N₃, hN₃⟩ := FrontSemEvS.sue_ev l F e coef A L hL h
  obtain ⟨Cb, eb, hb⟩ := (cnwS l F e coef A L hL).budget_bound
  have hqt : Tendsto (BU l F e coef A).q atTop atTop := Ledger.tendsto_nativeWidth (kE l e) (gateApad l)
  have e1 := atoms_ev l F e coef A L hL
  have e2 := FrontCostLedger.cb_dom l F e coef A hcoef (10 ^ 83) 0 (costDeg l) hdeg
  have e3 := hqt.eventually_ge_atTop 1
  have e4 := FrontSemEv.polyq_le (kE l e) (gateApad l) Cb eb
  have e5 := eventually_ge_atTop (HierarchyReduction.shortCoefficient (kE l e + 2) 1 + capExp l + kE l e + gateApad l + 2)
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨max (max N₁ N₃) N₄, fun N hN C hCN x w hw => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := hN₄ N (by omega)
  obtain ⟨hnw, -, -, -, h4q, -, -, h16⟩ := hN₃ N (by omega)
  have TF := hN₁ N (by omega)
  have hn : 1 ≤ N + 2 := by omega
  have hxl : (List.ofFn x).length = N := List.length_ofFn
  have hwN : w.length ≤ N := by rw [hw]; exact Nat.div_le_self _ _
  have hd16 : 16 * (N / 16) ≤ N := Nat.mul_div_le N 16
  have hc1 : 1 ≤ capExp l := one_le_capExp l
  -- the width's atoms
  rw [← hnw] at a1
  unfold atomQ at a1
  have b1 := FrontFoldBound.budget_le (DwS l F e coef A L hL) (KwS l F e coef A L hL)
    ((SUE l F e coef A L hL).width N) _ le_rfl
  have b2 := FrontFoldBound.budget_le (IUE l F e coef A).descDeg 1 ((SUE l F e coef A L hL).width N) _ le_rfl
  have b3 := FrontFoldBound.budget_le (IUE l F e coef A).carrierDeg 1 ((SUE l F e coef A L hL).width N) _
    le_rfl
  have b4 := FrontFoldBound.budget_le (DeS l F e coef A) (CeS l F e coef A)
    (KwS l F e coef A L hL * ((SUE l F e coef A L hL).width N + 1) ^ DwS l F e coef A L hL) _ le_rfl
  have b5 := FrontFoldBound.budget_le (DtS l F e coef A L hL) (CtS l F e coef A L hL)
    (KwS l F e coef A L hL * ((SUE l F e coef A L hL).width N + 1) ^ DwS l F e coef A L hL) _ le_rfl
  have b6 := FrontSemCap3.rowBt_le (gateZeta_pos l) (gateZeta_lt l) (JS_spec l) ((SUE l F e coef A L hL).width N)
  have b7 := Lq_le ((SUE l F e coef A L hL).width N)
  have b8 : JS l * (Lq ((SUE l F e coef A L hL).width N) + 1) ≤
      JS l * ((SUE l F e coef A L hL).width N + 2) := Nat.mul_le_mul_left _ (by omega)
  have hWr := KwS_spec l F e coef A L hL ((SUE l F e coef A L hL).width N)
  unfold Wreq at hWr
  have hk4 := k4_le (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N))
  have hΛ : rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 ((SUE l F e coef A L hL).width N) ≤
      MSS l F e coef A L hL ((SUE l F e coef A L hL).width N) :=
    (FrontSemEnvS.lam_le l _).trans (FrontSemEnvS.MS_ge l F e coef A L hL (c0S l) _).2.2.1
  -- phase 1
  have hpay : (payload w.tail).length ≤ w.length := by
    unfold payload; rw [List.length_take]; have := List.length_drop (l := w.tail) (i := FrontWalkRef.ones w.tail + 1)
    have : w.tail.length ≤ w.length := by simp
    omega
  have hq' : nativeWidth (kE l e) (gateApad l) N ≤ N := by
    have := h4q; rw [FrontSemEvS.bu_q] at this; omega
  have hph1 := FrontCostPh1.ph1C_le (kE l e) (gateApad l) (recOracleDeg l) N (List.ofFn x) w hxl hwN (by omega)
    (by omega) hq' (by omega) (by omega) (by omega) (by
      have : 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) = capExp l := rfl
      omega)
  -- phase 2: the walk stage, the copy, the cold front end (`C (N+1)^2 (q+1)^e`)
  have hraw : 16 * (payload w.tail).length ≤ N := by omega
  have hbud := hb N x (payload w.tail) hraw
  have hqw : (SUE l F e coef A L hL).width N = (BU l F e coef A).q N := hnw
  have hCq : Cb * ((SUE l F e coef A L hL).width N + 1) ^ eb ≤ N := by
    rw [hqw, FrontSemEvS.bu_q]; exact a4
  have hbud2 : (cnwS l F e coef A L hL).budget N x (payload w.tail) ≤ (N + 2) ^ 3 := by
    have e1 : Cb * (N + 1) ^ 2 * ((SUE l F e coef A L hL).width N + 1) ^ eb =
        (N + 1) ^ 2 * (Cb * ((SUE l F e coef A L hL).width N + 1) ^ eb) := by ring
    have e2 : (N + 1) ^ 2 * (Cb * ((SUE l F e coef A L hL).width N + 1) ^ eb) ≤ (N + 2) ^ 2 * (N + 2) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by omega)
    have e3 : (N + 2) ^ 2 * (N + 2) = (N + 2) ^ 3 := by ring
    have hb' : (cnwS l F e coef A L hL).budget N x (payload w.tail) ≤
        Cb * (N + 1) ^ 2 * (NearCubicGates.Close.Outer.width (SUE l F e coef A L hL).mw (SUE l F e coef A L hL).SV N + 1) ^ eb :=
      hbud
    have e4 : NearCubicGates.Close.Outer.width (SUE l F e coef A L hL).mw (SUE l F e coef A L hL).SV N =
        (SUE l F e coef A L hL).width N := rfl
    rw [e4] at hb'
    omega
  have hph2 : Front35.Top.ph2C (cnwS l F e coef A L hL) x w ≤ 10 ^ 9 * (N + 2) ^ 40 := by
    have p3 : (N + 2) ^ 3 ≤ (N + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
    have p1 : N + 2 ≤ (N + 2) ^ 40 := Nat.le_self_pow (by norm_num) _
    have hw' : Front35.Walk.wkCost w ≤ 230 * N + 250 := by
      unfold Front35.Walk.wkCost FrontOracleField.walkCost; omega
    have e0 : Front35.Top.ph2C (cnwS l F e coef A L hL) x w = Front35.Walk.wkCost w + 1 +
        ((8 * (List.ofFn x).length + 14) + 1 + (cnwS l F e coef A L hL).budget N x (payload w.tail)) := rfl
    rw [e0, hxl]
    generalize (cnwS l F e coef A L hL).budget N x (payload w.tail) = bd at hbud2 ⊢
    generalize Front35.Walk.wkCost w = wk at hw' ⊢
    generalize (N + 2) ^ 40 = P40 at p3 p1 ⊢
    generalize (N + 2) ^ 3 = P3 at p3 hbud2 ⊢
    omega
  -- the chain
  have hrest : ∀ O : NearCubicGates.Close.Outer.OuterGuess ((SUE l F e coef A L hL).width N),
      FrontOracleField.okOf w = true → (cnwS l F e coef A L hL).passed (List.ofFn x) (payload w.tail) = true →
      NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf ((SUE l F e coef A L hL).width N)
        (payload w.tail) = some O →
      FrontSemRun.restCostOf (gateZeta_pos l) (gateZeta_lt l) (KwS l F e coef A L hL) (DwS l F e coef A L hL)
        (DeS l F e coef A) (CeS l F e coef A) (DtS l F e coef A L hL) (CtS l F e coef A L hL) (KbS l F e coef A L hL)
        (DbS l F e coef A L hL) (gateCδ1 l) F.cr
        (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
        (32 * coef + 1) (gate0 l F).E.Amain c x (w.headD false) w.tail O ≤
      10 ^ 81 * (N + 2) ^ 40 + 400 * FrontTail.rOf F.cr (32 * coef + 1) (gate0 l F).E.Amain
        ((SUE l F e coef A L hL).width N) +
        c.budgetAt (BU l F e coef A) ((SUE l F e coef A L hL).width N) := by
    intro O hO hpas hdec
    obtain ⟨hNd, -, -, -, B, hB, hsrc, hpf, hfit, hcheck⟩ :=
      ((cnwS l F e coef A L hL).passed_iff x (payload w.tail)).1 hpas
    have hBO : B = O := by
      have := (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf_iff_decodes _ _ _).2 hB
      rw [hdec] at this
      exact (Option.some.inj this).symm
    subst hBO
    have hguard : ∀ g : UnionGuess (SUE l F e coef A L hL) x, g.pair = B →
        UnionGuards (SUE l F e coef A L hL) x g := fun g e => by
      subst e; exact ⟨TF.hlive, hNd, TF.hon, hsrc, hpf, hfit, hcheck⟩
    have hsc : scanOK w.tail = true := by
      cases w with
      | nil => exact absurd hO (by simp [FrontOracleField.okOf])
      | cons b t => exact hO
    have hx : (restOf w.tail).length + 1 ≤ (List.ofFn x).length := by
      have h1 : (restOf w.tail).length ≤ w.tail.length := by unfold restOf; rw [List.length_drop]; omega
      have h2 : w.tail.length ≤ w.length := by simp
      omega
    have harity : ((SUE l F e coef A L hL).request x B).arity = (SUE l F e coef A L hL).width N :=
      FrontSemRun.request_arity x B TF.hmin
    exact FrontCostRun.restCostOf_le (gateZeta_pos l) (gateZeta_lt l) (KwS l F e coef A L hL) (DwS l F e coef A L hL)
      (DeS l F e coef A) (CeS l F e coef A) (DtS l F e coef A L hL) (CtS l F e coef A L hL) (KbS l F e coef A L hL)
      (DbS l F e coef A L hL) (gateCδ1 l) F.cr
      (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
      (32 * coef + 1) (gate0 l F).E.Amain
      (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 ((SUE l F e coef A L hL).width N))
      (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) c x (w.headD false) w.tail B
      (FrontSemSUE.sue_gridSize l F e coef A L hL) (fun _ => rfl) hsc hdec harity hx (TF.nums x B hNd hpf)
      (fun g ho hat hsg => TF.caps x g (hguard g ho) hat hsg)
      (fun g ho hat => by
        have hgq : g.q = (SUE l F e coef A L hL).width N := by
          rw [q_eq_width _ g hNd TF.hon]
        have hG := FrontSemEnvS.genv_of l F e coef A L hL (c0S l) x g (hguard g ho) hat
          (by rw [hgq]; exact TF.hStar)
        rw [hgq] at hG
        exact hG)
      hΛ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hc := FrontCostRun.costOf_le (gateZeta_pos l) (gateZeta_lt l) (S := SUE l F e coef A L hL)
    (cnwS l F e coef A L hL) (kE l e) (gateApad l) (recOracleDeg l) (DwS l F e coef A L hL) (DeS l F e coef A)
    (DtS l F e coef A L hL) c C
    (KwS l F e coef A L hL) (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l) (CeS l F e coef A)
    (CtS l F e coef A L hL) F.cr (MSS l F e coef A L hL ((SUE l F e coef A L hL).width N)) (aVS l) (bVS l)
    (aTS l) (bTS l) F.cr (32 * coef + 1) (gate0 l F).E.Amain x w hCN _ _ _ hph1 hph2 hrest
  refine hc.trans ?_
  -- the closing arithmetic
  have hD40 : costDeg l = 40 := rfl
  have d1 : (N + 2) ^ 26 ≤ (N + 2) ^ costDeg l := Nat.pow_le_pow_right hn (by omega)
  have d3 : (N + 2) ^ 40 ≤ (N + 2) ^ costDeg l := Nat.pow_le_pow_right hn (by omega)
  have d4 : N + 2 ≤ (N + 2) ^ costDeg l := Nat.le_self_pow (by omega) _
  rw [pow_zero, mul_one] at a2
  have hP : 4 * N + 20 + 10 ^ 31 * (N + 2) ^ 26 + 10 ^ 9 * (N + 2) ^ 40 + 10 ^ 81 * (N + 2) ^ 40 ≤
      (BU l F e coef A).callBudget ((BU l F e coef A).q N) := by omega
  have hcap := FrontCaps.capQ_le l F e coef A hcoef _ a3
  have hRQ : FrontTail.rOf F.cr (32 * coef + 1) (gate0 l F).E.Amain ((BU l F e coef A).q N) =
      1000 * ((BU l F e coef A).q N + 6) * FrontCaps.capQ l F e coef A ((BU l F e coef A).q N) := by
    rw [← RQ_eq]; rfl
  have hX : (BU l F e coef A).q N + 1 ≤ ((BU l F e coef A).q N + 1) ^ (callDegMargin - 1) :=
    Nat.le_self_pow (by decide) _
  have hf := fin_le _ (c.budgetAt (BU l F e coef A) ((BU l F e coef A).q N)) _ _ _ _ _ hX hP hcap
  rw [hnw, hRQ]
  unfold KfT
  omega

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostSUE

end
