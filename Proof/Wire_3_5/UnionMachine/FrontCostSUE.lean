import Proof.Wire_3_5.UnionMachine.FrontCostRun
import Proof.Wire_3_5.Recovery.CaseTwoPadGBudget

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
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (BU PQ)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open Filter

/-- The guessed-oracle PCPP check's exponent in the input length at the gate. -/
noncomputable def obE (l : Literals) : ℕ :=
  Classical.choose (CaseTwoPadG.obudgetG_poly (gateSource l) (gatePCPP l) (recOracleDeg l))

/-- The guessed-oracle PCPP check's exponent in the width at the gate. -/
noncomputable def obc (l : Literals) : ℕ :=
  Classical.choose (Classical.choose_spec (CaseTwoPadG.obudgetG_poly (gateSource l) (gatePCPP l) (recOracleDeg l)))

/-- **The front's polynomial degree**: the chain's `40` and phase 2's `obE + 4`, a function of the literals only. -/
noncomputable def costDeg (l : Literals) : ℕ := max 40 (obE l + 4)

/-- **The front's time factor** `81600000·2^{A_main} + 1`. -/
noncomputable def KfT (l : Literals) (F : GateFree l) : ℕ := 81600000 * 2 ^ (gate0 l F).E.Amain + 1

theorem k4_le (K : ℕ) : 2 * (K * K * K * K) + 2 * K + 1 ≤ FrontSemCap2.PW K := by
  unfold FrontSemCap2.PW
  have h1 : K * K * K * K ≤ (K + 1) ^ 9 := by
    calc K * K * K * K ≤ (K + 1) * (K + 1) * (K + 1) * (K + 1) := by gcongr <;> omega
      _ = (K + 1) ^ 4 := by ring
      _ ≤ (K + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : K + 1 ≤ (K + 1) ^ 9 := Nat.le_self_pow (by norm_num) _
  omega

/-- The front's closing arithmetic: a polynomial part within the per-call budget, the loop's scratch `400·RQ` and C1's
call fit `KfT·X·(callBudget + β)` for `X ≥ q + 1`. -/
theorem fin_le (P ba cb capv q Am X : ℕ) (hX : q + 1 ≤ X) (hP : P ≤ cb) (hcap : capv + 1 ≤ 34 * 2 ^ Am * cb) :
    P + 400 * (1000 * (q + 6) * capv) + ba ≤ (81600000 * 2 ^ Am + 1) * X * (cb + ba) := by
  have h1 : 1 ≤ X := by omega
  have e1 : (q + 6) * capv ≤ (6 * X) * (34 * 2 ^ Am * cb) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : cb ≤ X * cb := Nat.le_mul_of_pos_left _ h1
  have e3 : ba ≤ X * ba := Nat.le_mul_of_pos_left _ h1
  have r1 : 400 * (1000 * (q + 6) * capv) = 400000 * ((q + 6) * capv) := by ring
  have r2 : 400000 * ((6 * X) * (34 * 2 ^ Am * cb)) = 81600000 * 2 ^ Am * (X * cb) := by ring
  have r3 : (81600000 * 2 ^ Am + 1) * X * (cb + ba) =
      81600000 * 2 ^ Am * (X * cb) + 81600000 * 2 ^ Am * (X * ba) + X * cb + X * ba := by ring
  have e4 : 400000 * ((q + 6) * capv) ≤ 400000 * ((6 * X) * (34 * 2 ^ Am * cb)) := Nat.mul_le_mul_left _ e1
  omega

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
    (q + 1) ^ (IUE l F e coef A).descDeg + (JS l * (q + 2) + 1) + q + (q + 1) ^ obc l

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

include F coef A in
/-- **The clock's bits** are within `N + 2` past a threshold. -/
theorem time_ev : ∀ᶠ N : ℕ in atTop, ((FrontSemSUE.hhOf l e L hL).time N).bits.length ≤ N + 2 := by
  filter_upwards [FrontCaps.two_pow_small l F e coef A (2 * (FrontSemSUE.hhOf l e L hL).coefficient) (kE l e + 2)]
    with N hN
  rw [Nat.size_eq_bits_len, Nat.size_le]
  have h1 : 2 ^ (N - (BU l F e coef A).kOf N / 4) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have h2 : N ^ (kE l e + 2) ≤ (N + 1) ^ (kE l e + 2) := Nat.pow_le_pow_left (Nat.le_succ N) _
  have h3 : 1 ≤ (N + 1) ^ (kE l e + 2) := Nat.one_le_pow _ _ (by omega)
  have h4 : 2 ^ N < 2 ^ (N + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  show (FrontSemSUE.hhOf l e L hL).coefficient * (N ^ (kE l e + 2) + 1) < 2 ^ (N + 2)
  have h5 : (FrontSemSUE.hhOf l e L hL).coefficient * (N ^ (kE l e + 2) + 1) ≤
      2 * (FrontSemSUE.hhOf l e L hL).coefficient * (N + 1) ^ (kE l e + 2) := by
    calc (FrontSemSUE.hhOf l e L hL).coefficient * (N ^ (kE l e + 2) + 1)
        ≤ (FrontSemSUE.hhOf l e L hL).coefficient * ((N + 1) ^ (kE l e + 2) + (N + 1) ^ (kE l e + 2)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (FrontSemSUE.hhOf l e L hL).coefficient * (N + 1) ^ (kE l e + 2) := by ring
  omega

/-- **The front's cost at the pinned setup**: when `costDeg + 1 ≤ kE`, past a threshold, at every onset `C ≤ N`, on
every input and witness, the front's cost is at most `KfT·(q+1)^7·(callBudget q + β(q))`. -/
theorem cost_ev (hcoef : 1 ≤ coef) (hdeg : costDeg l + 1 ≤ kE l e) (c : Plan.C1At (dS l F e coef A L hL)) :
    ∃ N₂ : ℕ, ∀ N, N₂ ≤ N → ∀ C, C ≤ N → ∀ (x : BitInput N) (w : List Bool), w.length = N / 16 →
      FrontSemRun.costOf (S := SUE l F e coef A L hL) (gateSource l) (gatePCPP l) (kE l e) (gateApad l)
        (recOracleDeg l) (DwS l F e coef A L hL) (DeS l F e coef A) (DtS l F e coef A L hL) c C
        (FrontSemSUE.hhOf l e L hL) (cpadOf (FrontSemSUE.hhOf l e L hL)) (le_max_right _ _) (KwS l F e coef A L hL)
        (gateZeta_pos l) (gateZeta_lt l) (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l)
        (CeS l F e coef A) (CtS l F e coef A L hL) F.cr
        (MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
        (32 * coef + 1) (gate0 l F).E.Amain x w ≤
      KfT l F * ((BU l F e coef A).q N + 1) ^ (callDegMargin - 1) *
        ((BU l F e coef A).callBudget ((BU l F e coef A).q N) + c.budgetAt (BU l F e coef A) ((BU l F e coef A).q N)) := by
  obtain ⟨N₁, hN₁⟩ := topFacts_ev l F e coef A L hL c
  obtain ⟨N₃, hN₃⟩ := FrontSemEvS.sue_ev l F e coef A L hL
  obtain ⟨C0, hC0⟩ := (Classical.choose_spec (Classical.choose_spec
    (CaseTwoPadG.obudgetG_poly (gateSource l) (gatePCPP l) (recOracleDeg l))))
    (FrontSemSUE.hhOf l e L hL) (cpadOf (FrontSemSUE.hhOf l e L hL)) (le_max_left _ _) (le_max_right _ _)
  have hqt : Tendsto (BU l F e coef A).q atTop atTop := Ledger.tendsto_nativeWidth (kE l e) (gateApad l)
  have e1 := atoms_ev l F e coef A L hL
  have e2 := FrontCostLedger.cb_dom l F e coef A hcoef (10 ^ 83) 0 (costDeg l) hdeg
  have e3 := hqt.eventually_ge_atTop 1
  have e4 := time_ev l F e coef A L hL
  have e5 := eventually_ge_atTop (C0 + CloseoutHierarchyRequest.coefficient (kE l e)
    (FrontSemSUE.hhOf l e L hL).coefficient + 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) + kE l e +
      HierarchyReduction.shortCoefficient (kE l e + 2) 1 + gateApad l + 2)
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and e5))))
  refine ⟨max (max N₁ N₃) N₄, fun N hN C hCN x w hw => ?_⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := hN₄ N (by omega)
  obtain ⟨hnw, -, -, -, h4q, -, -, h16⟩ := hN₃ N (by omega)
  have TF := hN₁ N (by omega)
  have hn : 1 ≤ N + 2 := by omega
  have hxl : (List.ofFn x).length = N := List.length_ofFn
  have hwN : w.length ≤ N := by rw [hw]; exact Nat.div_le_self _ _
  have hd16 : 16 * (N / 16) ≤ N := Nat.mul_div_le N 16
  have hc1 : 1 ≤ 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l) := Nat.one_le_two_pow
  -- the width's atoms
  rw [← hnw] at a1
  unfold atomQ at a1
  have b1 := FrontFoldBound.budget_le (DwS l F e coef A L hL) (KwS l F e coef A L hL)
    ((SUE l F e coef A L hL).pcp.nativeWidth N) _ le_rfl
  have b2 := FrontFoldBound.budget_le (IUE l F e coef A).descDeg 1 ((SUE l F e coef A L hL).pcp.nativeWidth N) _ le_rfl
  have b3 := FrontFoldBound.budget_le (IUE l F e coef A).carrierDeg 1 ((SUE l F e coef A L hL).pcp.nativeWidth N) _
    le_rfl
  have b4 := FrontFoldBound.budget_le (DeS l F e coef A) (CeS l F e coef A)
    (KwS l F e coef A L hL * ((SUE l F e coef A L hL).pcp.nativeWidth N + 1) ^ DwS l F e coef A L hL) _ le_rfl
  have b5 := FrontFoldBound.budget_le (DtS l F e coef A L hL) (CtS l F e coef A L hL)
    (KwS l F e coef A L hL * ((SUE l F e coef A L hL).pcp.nativeWidth N + 1) ^ DwS l F e coef A L hL) _ le_rfl
  have b6 := FrontSemCap3.rowBt_le (gateZeta_pos l) (gateZeta_lt l) (JS_spec l) ((SUE l F e coef A L hL).pcp.nativeWidth N)
  have b7 := Lq_le ((SUE l F e coef A L hL).pcp.nativeWidth N)
  have b8 : JS l * (Lq ((SUE l F e coef A L hL).pcp.nativeWidth N) + 1) ≤
      JS l * ((SUE l F e coef A L hL).pcp.nativeWidth N + 2) := Nat.mul_le_mul_left _ (by omega)
  have hWr := KwS_spec l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N)
  unfold Wreq at hWr
  have hk4 := k4_le (MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N))
  have hΛ : rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 ((SUE l F e coef A L hL).pcp.nativeWidth N) ≤
      MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N) :=
    (FrontSemEnvS.lam_le l _).trans (FrontSemEnvS.MS_ge l F e coef A L hL (c0S l) _).2.2.1
  have harity : ∀ O : BooleanCircuit ((SUE l F e coef A L hL).pcp.nativeWidth N),
      ((SUE l F e coef A L hL).request x O).arity = (SUE l F e coef A L hL).pcp.nativeWidth N := fun O => by
    show max ((SUE l F e coef A L hL).pcp.nativeWidth N) (SUE l F e coef A L hL).pcppAlg.minimumArity = _
    exact max_eq_left TF.hmin
  -- phase 1
  have hpay : (payload w.tail).length ≤ w.length := by
    unfold payload; rw [List.length_take]; have := List.length_drop (l := w.tail) (i := FrontWalkRef.ones w.tail + 1)
    have : w.tail.length ≤ w.length := by simp
    omega
  have hq' : nativeWidth (kE l e) (gateApad l) N ≤ N := by
    have := h4q; rw [FrontSemEvS.bu_q] at this; omega
  have hph1 := FrontCostPh1.ph1C_le (kE l e) (gateApad l) (recOracleDeg l) N (List.ofFn x) w hxl hwN (by omega)
    (by omega) hq' (by omega) (by omega) (by omega) (by omega)
  -- phase 2
  have hph2 : ∀ O : BooleanCircuit ((SUE l F e coef A L hL).pcp.nativeWidth N),
      O.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l) ((SUE l F e coef A L hL).pcp.nativeWidth N) →
      ∀ hq : PCPPNativeHierarchyNodes.width (gateSource l) (kE l e) (FrontSemSUE.hhOf l e L hL).coefficient
          (cpadOf (FrontSemSUE.hhOf l e L hL)) (VerifierEncoding.code (FrontSemSUE.hhOf l e L hL).verifier) x ≤
        (SUE l F e coef A L hL).pcp.nativeWidth N,
      FrontTop.ph2C (gateSource l) (gatePCPP l) (kE l e) (FrontSemSUE.hhOf l e L hL)
        (cpadOf (FrontSemSUE.hhOf l e L hL)) (le_max_right _ _) x ((SUE l F e coef A L hL).pcp.nativeWidth N) hq O ≤
      10 ^ 9 * (N + 2) ^ (obE l + 4) := fun O hsz hq =>
    FrontCostPh1.ph2C_le (gateSource l) (gatePCPP l) (kE l e) (FrontSemSUE.hhOf l e L hL)
      (cpadOf (FrontSemSUE.hhOf l e L hL)) (le_max_right _ _) x ((SUE l F e coef A L hL).pcp.nativeWidth N) hq O
      (obE l) (obc l) C0 (hC0 ⟨N, x⟩ _ hq O _ hsz) (by omega) (by omega) (by omega) (by omega) a4
  -- the chain
  have hrest : ∀ O : BooleanCircuit ((SUE l F e coef A L hL).pcp.nativeWidth N), FrontOracleField.okOf w = true →
      CanonicalWitnessCodec.decodeBooleanCircuit ((SUE l F e coef A L hL).pcp.nativeWidth N)
        (RepairOrdinary.RadixSemantics.value (payload w.tail)) = some O →
      O.size ≤ RecoveryScheduleEnvelope.oracleSizeBound (recOracleDeg l) ((SUE l F e coef A L hL).pcp.nativeWidth N) →
      FrontSemRun.restCostOf (gateZeta_pos l) (gateZeta_lt l) (KwS l F e coef A L hL) (DwS l F e coef A L hL)
        (DeS l F e coef A) (CeS l F e coef A) (DtS l F e coef A L hL) (CtS l F e coef A L hL) (KbS l F e coef A L hL)
        (DbS l F e coef A L hL) (gateCδ1 l) F.cr
        (MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
        (32 * coef + 1) (gate0 l F).E.Amain c x (w.headD false) w.tail O ≤
      10 ^ 81 * (N + 2) ^ 40 + 400 * FrontTail.rOf F.cr (32 * coef + 1) (gate0 l F).E.Amain
        ((SUE l F e coef A L hL).pcp.nativeWidth N) +
        c.budgetAt (BU l F e coef A) ((SUE l F e coef A L hL).pcp.nativeWidth N) := by
    intro O hO hdec hsz
    have hsc : scanOK w.tail = true := by
      cases w with
      | nil => exact absurd hO (by simp [FrontOracleField.okOf])
      | cons b t => exact hO
    have hx : (restOf w.tail).length + 1 ≤ (List.ofFn x).length := by
      have h1 : (restOf w.tail).length ≤ w.tail.length := by unfold restOf; rw [List.length_drop]; omega
      have h2 : w.tail.length ≤ w.length := by simp
      omega
    exact FrontCostRun.restCostOf_le (gateZeta_pos l) (gateZeta_lt l) (KwS l F e coef A L hL) (DwS l F e coef A L hL)
      (DeS l F e coef A) (CeS l F e coef A) (DtS l F e coef A L hL) (CtS l F e coef A L hL) (KbS l F e coef A L hL)
      (DbS l F e coef A L hL) (gateCδ1 l) F.cr
      (MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N)) (aVS l) (bVS l) (aTS l) (bTS l) F.cr
      (32 * coef + 1) (gate0 l F).E.Amain
      (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 ((SUE l F e coef A L hL).pcp.nativeWidth N))
      (MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N)) c x (w.headD false) w.tail O
      (FrontSemSUE.sue_gridSize l F e coef A L hL) (fun _ => rfl) hsc hdec (harity O) hx (TF.nums x O hsz)
      (fun g ho hat hsg => TF.caps x g (by rw [ho]; exact hsz) hat hsg)
      (fun g ho hat => by
        have hgq : g.q = (SUE l F e coef A L hL).pcp.nativeWidth N := by
          show max ((SUE l F e coef A L hL).pcp.nativeWidth N) (SUE l F e coef A L hL).pcppAlg.minimumArity = _
          exact max_eq_left TF.hmin
        have hG := FrontSemEnvS.genv_of l F e coef A L hL (c0S l) x g
          (by rw [ho, FrontSemSUE.sue_G]; exact hsz) hat hgq (by rw [hgq]; exact TF.hStar)
        rw [hgq] at hG
        exact hG)
      hΛ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hc := FrontCostRun.costOf_le (gateZeta_pos l) (gateZeta_lt l) (S := SUE l F e coef A L hL) (gateSource l)
    (gatePCPP l) (kE l e) (gateApad l) (recOracleDeg l) (DwS l F e coef A L hL) (DeS l F e coef A)
    (DtS l F e coef A L hL) c C (FrontSemSUE.hhOf l e L hL) (cpadOf (FrontSemSUE.hhOf l e L hL)) (le_max_right _ _)
    (KwS l F e coef A L hL) (KbS l F e coef A L hL) (DbS l F e coef A L hL) (gateCδ1 l) (CeS l F e coef A)
    (CtS l F e coef A L hL) F.cr (MSS l F e coef A L hL ((SUE l F e coef A L hL).pcp.nativeWidth N)) (aVS l) (bVS l)
    (aTS l) (bTS l) F.cr (32 * coef + 1) (gate0 l F).E.Amain x w hCN _ _ _ hph1 hph2 hrest
  refine hc.trans ?_
  -- the closing arithmetic
  have hD40 : 40 ≤ costDeg l := le_max_left _ _
  have hDE : obE l + 4 ≤ costDeg l := le_max_right _ _
  have d1 : (N + 2) ^ 26 ≤ (N + 2) ^ costDeg l := Nat.pow_le_pow_right hn (by omega)
  have d2 : (N + 2) ^ (obE l + 4) ≤ (N + 2) ^ costDeg l := Nat.pow_le_pow_right hn hDE
  have d3 : (N + 2) ^ 40 ≤ (N + 2) ^ costDeg l := Nat.pow_le_pow_right hn hD40
  have d4 : N + 2 ≤ (N + 2) ^ costDeg l := Nat.le_self_pow (by omega) _
  rw [pow_zero, mul_one] at a2
  have hP : 4 * N + 20 + 10 ^ 31 * (N + 2) ^ 26 + 10 ^ 9 * (N + 2) ^ (obE l + 4) + 10 ^ 81 * (N + 2) ^ 40 ≤
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
