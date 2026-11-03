import Proof.Packets.BudgetCallCyc

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## The polynomial remainder -/

/-- `seedCount`'s bit length is linear in the arity once `smallSize ≤ 2^(q/4)` (the small class at exponent `0`). -/
theorem seedBits_le (a : DecompositionAlgorithm) (r : Request) (hS : (r.smallSize a)^1 ≤ 1*smallClass 4 0 r.q) :
    natBitLength (PacketsGlue.RequestMeta.seedCount a r) ≤ 41*r.q + 4 := by
  have h1 := PacketsMeta.Seed.seedCount_le_small a r
  have hS' : r.smallSize a ≤ 2^(r.q/4) := by
    unfold smallClass at hS; simpa using hS
  have h2 : (r.smallSize a)^163 ≤ (2^(r.q/4))^163 := Nat.pow_le_pow_left hS' 163
  have h3 : 8*(2^(r.q/4))^163 = 2^(3 + r.q/4*163) := by
    rw [← pow_mul, pow_add]; norm_num
  have h4 : PacketsGlue.RequestMeta.seedCount a r ≤ 2^(3 + r.q/4*163) := by
    rw [← h3]; exact h1.trans (Nat.mul_le_mul_left 8 h2)
  have h5 := natBitLength_le_of_le_pow h4
  omega

/-- **The rest's polynomial remainder** (denominator engine, input framing, cursor, slopes) at exponent `D`. -/
theorem restPoly_le (K : CallK) (md : ℕ) (a : DecompositionAlgorithm) (r : Request) (w Lg Mb Ms j c0 : ℕ)
    (hS : (r.smallSize a)^1 ≤ 1*smallClass 4 0 r.q)
    (hin : (r.input a).length ≤ K.inC*(r.q+1)^K.inE) (hw : w ≤ K.bC*(r.q+1)^K.bE)
    (hMb : Mb ≤ K.mC*(r.q+1)^K.mE) (hMs : Ms ≤ K.mC*(r.q+1)^K.mE) (hj : j ≤ K.jC*(r.q+1)^K.jE) (hc0 : c0 ≤ 100) :
    CompetitorDenominator.budget (natBitLength (PacketsGlue.RequestMeta.seedCount a r)) w r.q + 4*(r.input a).length +
        6*w + 2*r.q + 4*j + 2*(if 3 < Lg then Mb else Ms) + c0 ≤
      (128*((K.bC+1)*49) + 4*K.inC + 6*K.bC + 130 + 4*K.jC + 2*K.mC)*(r.q+1)^(K.D md) := by
  have hb := seedBits_le a r hS
  have hM : (if 3 < Lg then Mb else Ms) ≤ K.mC*(r.q+1)^K.mE := by split <;> assumption
  have hP1 : 1 ≤ (r.q+1)^K.bE := Nat.one_le_pow _ _ (by omega)
  have hw1 : w + 1 ≤ (K.bC+1)*(r.q+1)^K.bE := by rw [Nat.add_mul, one_mul]; omega
  have hnb : natBitLength (PacketsGlue.RequestMeta.seedCount a r) + r.q + 3 ≤ 49*(r.q+1)^1 := by rw [pow_one]; omega
  have hprod := poly_mul hw1 hnb
  have hq1 : 4*r.q + 24 + 2*r.q + 100 ≤ 130*(r.q+1)^1 := by rw [pow_one]; omega
  have hD : K.D md = K.rowsE + K.D0 md := rfl
  have e1' : 128*(w + 1)*(natBitLength (PacketsGlue.RequestMeta.seedCount a r) + r.q + 3) ≤
      (128*((K.bC+1)*49))*(r.q+1)^(K.bE+1) := by
    calc 128*(w + 1)*(natBitLength (PacketsGlue.RequestMeta.seedCount a r) + r.q + 3)
        = 128*((w + 1)*(natBitLength (PacketsGlue.RequestMeta.seedCount a r) + r.q + 3)) := by ring
      _ ≤ 128*(((K.bC+1)*49)*(r.q+1)^(K.bE+1)) := Nat.mul_le_mul_left 128 hprod
      _ = (128*((K.bC+1)*49))*(r.q+1)^(K.bE+1) := by ring
  have e2' : 4*(r.input a).length ≤ (4*K.inC)*(r.q+1)^K.inE := by
    have := Nat.mul_le_mul_left 4 hin; rw [← Nat.mul_assoc] at this; exact this
  have e3' : 6*w ≤ (6*K.bC)*(r.q+1)^K.bE := by
    have := Nat.mul_le_mul_left 6 hw; rw [← Nat.mul_assoc] at this; exact this
  have e5' : 4*j ≤ (4*K.jC)*(r.q+1)^K.jE := by
    have := Nat.mul_le_mul_left 4 hj; rw [← Nat.mul_assoc] at this; exact this
  have e6' : 2*(if 3 < Lg then Mb else Ms) ≤ (2*K.mC)*(r.q+1)^K.mE := by
    have := Nat.mul_le_mul_left 2 hM; rw [← Nat.mul_assoc] at this; exact this
  have e1 := poly_raise e1' (show K.bE + 1 ≤ K.D md by rw [hD]; unfold CallK.D0; omega)
  have e2 := poly_raise e2' (show K.inE ≤ K.D md by rw [hD]; unfold CallK.D0; omega)
  have e3 := poly_raise e3' (show K.bE ≤ K.D md by rw [hD]; unfold CallK.D0; omega)
  have e4 := poly_raise hq1 (show 1 ≤ K.D md by rw [hD]; unfold CallK.D0; omega)
  have e5 := poly_raise e5' (show K.jE ≤ K.D md by rw [hD]; unfold CallK.D0; omega)
  have e6 := poly_raise e6' (show K.mE ≤ K.D md by rw [hD]; unfold CallK.D0; omega)
  have hsum := poly_add' (poly_add' (poly_add' (poly_add' (poly_add' e1 e2) e3) e4) e5) e6
  unfold CompetitorDenominator.budget
  omega

/-! ## The two `Rc`-free rests at one call -/

section rests
variable {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
  (se : PacketsGlue.RequestMeta.UnaryStage a (PacketsGlue.RequestMeta.seedCount a))
  (sp : PacketsGlue.RequestMeta.UnaryStage a (PacketsGlue.RequestMeta.primeCountOf a)) (K : CallK) (md rd Dm : ℕ)

/-- The two unary stages and the two binary counts at one call, in the class `(D, H, S)`. -/
theorem stagesCounts (hDm : se.degree ≤ Dm ∧ sp.degree ≤ Dm ∧ 2*(163+3) ≤ Dm) (r : Request)
    (hsm : (r.smallSize a)^Dm ≤ 1*smallClass 4 0 r.q) :
    InClasses (K.D md) (K.H rd) K.S 4 r.liveScale r.q r.q 0 0 (se.coefficient*1 + sp.coefficient*1)
        (se.cost r + sp.cost r) ∧
      InClasses (K.D md) (K.H rd) K.S 4 r.liveScale r.q r.q 0 0 (992*(8+40001+1)^2*1)
        (CloseoutRowsCountBinary.budget (PacketsGlue.RequestMeta.seedCount a r) +
          CloseoutRowsCountBinary.budget (PacketsGlue.RequestMeta.primeCountOf a r)) := by
  have hS1 : 1 ≤ r.smallSize a := smallSize_pos a r
  have hsmall : ∀ d, d ≤ Dm → (r.smallSize a)^d ≤ 1*smallClass 4 0 r.q :=
    fun d hd => (Nat.pow_le_pow_right hS1 hd).trans hsm
  have hst := stages_small se sp r 4 1 0 1 0 (hsmall _ hDm.1) (hsmall _ hDm.2.1)
  have hcb := counts_at a r 4 1 0 (hsmall _ hDm.2.2)
  have hst0 : InClasses (K.D md) (K.H rd) (0+0) 4 r.liveScale r.q r.q 0 0 (se.coefficient*1 + sp.coefficient*1)
      (se.cost r + sp.cost r) := InClasses.small hst
  have hcb0 : InClasses (K.D md) (K.H rd) 0 4 r.liveScale r.q r.q 0 0 (992*(8+40001+1)^2*1)
      (CloseoutRowsCountBinary.budget (PacketsGlue.RequestMeta.seedCount a r) +
        CloseoutRowsCountBinary.budget (PacketsGlue.RequestMeta.primeCountOf a r)) := InClasses.small hcb
  exact ⟨InClasses.raise le_rfl le_rfl (Nat.zero_le _) hst0, InClasses.raise le_rfl le_rfl (Nat.zero_le _) hcb0⟩

/-- **The refill's rest `restCost|₀` at one call**, coefficients chosen before the call. -/
theorem rest0_cls (hDm : se.degree ≤ Dm ∧ sp.degree ≤ Dm ∧ 2*(163+3) ≤ Dm ∧ 1 ≤ Dm) :
    ∃ ZP ZT ZS : ℕ, ∀ (r : Request) (g7cost : ℕ → ℕ) (w Lg Mb Ms j : ℕ),
      (r.input a).length ≤ K.inC*(r.q+1)^K.inE →
      (r.smallSize a)^Dm ≤ 1*smallClass 4 0 r.q →
      w ≤ K.bC*(r.q+1)^K.bE → Mb ≤ K.mC*(r.q+1)^K.mE → Ms ≤ K.mC*(r.q+1)^K.mE → j ≤ K.jC*(r.q+1)^K.jE →
      g7cost (j+1) ≤ K.cG*(r.q+1)^K.dG →
      InClasses (K.D md) (K.H rd) K.S 4 r.liveScale r.q r.q ZP ZT ZS (Rest.restCost se sp g7cost r 0 w r.q Lg Mb Ms j) := by
  refine ⟨?zp, ?zt, ?zs, fun r g7cost w Lg Mb Ms j hin hsm hw hMb hMs hj hg7 => ?body⟩
  case body =>
    have hS1 : 1 ≤ r.smallSize a := smallSize_pos a r
    have hS : (r.smallSize a)^1 ≤ 1*smallClass 4 0 r.q := (Nat.pow_le_pow_right hS1 hDm.2.2.2).trans hsm
    obtain ⟨hst, hcb⟩ := stagesCounts se sp K md rd Dm ⟨hDm.1, hDm.2.1, hDm.2.2.1⟩ r hsm
    have hg7' : InClasses (K.D md) (K.H rd) K.S 4 r.liveScale r.q r.q K.cG 0 0 (g7cost (j+1)) :=
      InClasses.poly hg7 (by show K.dG ≤ K.rowsE + K.D0 md; unfold CallK.D0; omega)
    have hpoly := restPoly_le K md a r w Lg Mb Ms j 100 hS hin hw hMb hMs hj le_rfl
    exact restFree_inClasses se sp g7cost r w r.q Lg Mb Ms j hg7' hst hcb hpoly

/-- **The first cycle's rest `6·C + g7cost 0 + backCost|₀` at one call**, coefficients chosen before the call. -/
theorem first0_cls (hDm : se.degree ≤ Dm ∧ sp.degree ≤ Dm ∧ 2*(163+3) ≤ Dm ∧ 1 ≤ Dm) :
    ∃ ZP ZT ZS : ℕ, ∀ (r : Request) (g7cost : ℕ → ℕ) (w Lg Mb Ms C : ℕ),
      (r.input a).length ≤ K.inC*(r.q+1)^K.inE →
      (r.smallSize a)^Dm ≤ 1*smallClass 4 0 r.q →
      w ≤ K.bC*(r.q+1)^K.bE → Mb ≤ K.mC*(r.q+1)^K.mE → Ms ≤ K.mC*(r.q+1)^K.mE →
      g7cost 0 ≤ K.cG*(r.q+1)^K.dG → C ≤ K.cwC*(r.q+1)^K.cwE →
      InClasses (K.D md) (K.H rd) K.S 4 r.liveScale r.q r.q ZP ZT ZS
        (6*C + g7cost 0 + Rest.backCost se sp r 0 w r.q Lg Mb Ms) := by
  refine ⟨?zp, ?zt, ?zs, fun r g7cost w Lg Mb Ms C hin hsm hw hMb hMs hg7 hC => ?body⟩
  case body =>
    have hS1 : 1 ≤ r.smallSize a := smallSize_pos a r
    have hS : (r.smallSize a)^1 ≤ 1*smallClass 4 0 r.q := (Nat.pow_le_pow_right hS1 hDm.2.2.2).trans hsm
    obtain ⟨hst, hcb⟩ := stagesCounts se sp K md rd Dm ⟨hDm.1, hDm.2.1, hDm.2.2.1⟩ r hsm
    have hC6 : 6*C ≤ (6*K.cwC)*(r.q+1)^K.cwE := by
      have := Nat.mul_le_mul_left 6 hC; rw [← Nat.mul_assoc] at this; exact this
    have hC' : InClasses (K.D md) (K.H rd) K.S 4 r.liveScale r.q r.q (6*K.cwC) 0 0 (6*C) :=
      InClasses.poly hC6 (by show K.cwE ≤ K.rowsE + K.D0 md; unfold CallK.D0; omega)
    have hg7' : InClasses (K.D md) (K.H rd) K.S 4 r.liveScale r.q r.q K.cG 0 0 (g7cost 0) :=
      InClasses.poly hg7 (by show K.dG ≤ K.rowsE + K.D0 md; unfold CallK.D0; omega)
    have hpoly0 := restPoly_le K md a r w Lg Mb Ms 0 84 hS hin hw hMb hMs (Nat.zero_le _) (by omega)
    have hpoly : CompetitorDenominator.budget (natBitLength (PacketsGlue.RequestMeta.seedCount a r)) w r.q +
        4*(r.input a).length + 6*w + 2*r.q + 2*(if 3 < Lg then Mb else Ms) + 84 ≤
        (128*((K.bC+1)*49) + 4*K.inC + 6*K.bC + 130 + 4*K.jC + 2*K.mC)*(r.q+1)^(K.D md) := by
      have e : 4*0 = 0 := rfl
      omega
    exact ((hC'.add hg7').add (backFree_inClasses se sp r w r.q Lg Mb Ms hst hcb hpoly))

end rests

/-! ## `y` and `yF0` at one call -/

theorem ycall_cls (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (se : PacketsGlue.RequestMeta.UnaryStage a (PacketsGlue.RequestMeta.seedCount a))
    (sp : PacketsGlue.RequestMeta.UnaryStage a (PacketsGlue.RequestMeta.primeCountOf a))
    (degree target cc dc : ℕ)
    (hcold : ∀ (q : ℕ) (x : BinaryCacheColdJoin.Args q), BinaryCacheColdRun.budget x ≤
      cc * ((exactListWord x.gs).length + x.gs.length + q + 2^x.live.card + 1)^dc)
    (K : CallK) (Dm : ℕ) (hDm : packet.degree ≤ Dm ∧ rows.degree ≤ Dm ∧ (betaE a degree + 1)*dc ≤ Dm ∧
      se.degree ≤ Dm ∧ sp.degree ≤ Dm ∧ 2*(163+3) ≤ Dm ∧ 1 ≤ Dm) :
    ∃ ZP ZT ZS : ℕ, ∀ (den : ℕ) (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
      (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
      (caps : RowCaps) (g7cost : ℕ → ℕ) (w Mb Ms U0 V v j : ℕ),
      1 ≤ den → RequestAdmitted den degree target r →
      (r.input a).length ≤ K.inC*(r.q+1)^K.inE →
      (r.family a).rows.length + 1 ≤ K.rowsC*(r.q+1)^K.rowsE →
      (r.smallSize a)^Dm ≤ 1*smallClass 4 0 r.q →
      layout.w ≤ r.q → layout.degree ≤ r.q → layout.C ≤ K.capC*smallClass 4 K.capE r.q →
      caps.headerFuel ≤ K.hdC*smallClass 4 K.hdE r.q →
      caps.copyCap ≤ K.cpTC*tableClass r.liveScale K.cpTE r.q + K.cpSC*smallClass 4 K.cpSE r.q →
      caps.descriptorReserve ≤ K.dsTC*tableClass r.liveScale K.dsTE r.q + K.dsSC*smallClass 4 K.dsSE r.q →
      caps.rawReserve ≤ K.rwC*smallClass 4 K.rowsE r.q →
      RowCaps.Good selector a printer r layout facts caps →
      (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length + 1 ≤ K.betC*(r.q+1)^K.betE →
      Mb ≤ K.mC*(r.q+1)^K.mE → Ms ≤ K.mC*(r.q+1)^K.mE → U0 ≤ K.mC*(r.q+1)^K.mE →
      w ≤ K.bC*(r.q+1)^K.bE → v ≤ K.bC*(r.q+1)^K.bE → j ≤ K.jC*(r.q+1)^K.jE →
      V ≤ K.cVc*tableClass r.liveScale K.hV r.q →
      g7cost (j+1) ≤ K.cG*(r.q+1)^K.dG →
      InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q ZP ZT ZS
        (Rest.restCost se sp g7cost r 0 w r.q (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length
            Mb Ms j +
          Rest.cycFuel mask packet rows r layout facts caps
            (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length then Mb else Ms) U0
            (P1TopDownPaidReusableReserves.workspace printer V) (P1TopDownPaidReusableReserves.rewind printer V)
            (P1TopDownPaidReusableReserves.buffer V) v 0) := by
  obtain ⟨A1, A2, A3, hc⟩ := cyc0_cls mask packet rows degree target cc dc hcold K Dm ⟨hDm.1, hDm.2.1, hDm.2.2.1⟩
  obtain ⟨B1, B2, B3, hr⟩ := rest0_cls se sp K mask.degree rows.degree Dm ⟨hDm.2.2.2.1, hDm.2.2.2.2.1, hDm.2.2.2.2.2.1,
    hDm.2.2.2.2.2.2⟩
  refine ⟨B1 + A1, B2 + A2, B3 + A3, fun den r layout facts caps g7cost w Mb Ms U0 V v j hden hradm hin hrows hsm hlw hld hlC
    hhd hcp hds hraw hgood hgs hMb hMs hU0 hw hv hj hV hg7 => ?_⟩
  have hM2 : (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length then Mb else Ms) ≤
      K.mC*(r.q+1)^K.mE := by split <;> assumption
  exact (hr r g7cost w _ Mb Ms j hin hsm hw hMb hMs hj hg7).add
    (hc den r layout facts caps _ U0 V v hden hradm hin hrows hsm hlw hld hlC hhd hcp hds hraw hgood hgs hM2 hU0 hv hV)

/-- **`yF0` at one call**: `6·C + g7cost 0 + backCost|₀ + cycFuel … 0` in `(D, H, S)` with coefficients chosen before the call. -/
theorem yF0call_cls (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (se : PacketsGlue.RequestMeta.UnaryStage a (PacketsGlue.RequestMeta.seedCount a))
    (sp : PacketsGlue.RequestMeta.UnaryStage a (PacketsGlue.RequestMeta.primeCountOf a))
    (degree target cc dc : ℕ)
    (hcold : ∀ (q : ℕ) (x : BinaryCacheColdJoin.Args q), BinaryCacheColdRun.budget x ≤
      cc * ((exactListWord x.gs).length + x.gs.length + q + 2^x.live.card + 1)^dc)
    (K : CallK) (Dm : ℕ) (hDm : packet.degree ≤ Dm ∧ rows.degree ≤ Dm ∧ (betaE a degree + 1)*dc ≤ Dm ∧
      se.degree ≤ Dm ∧ sp.degree ≤ Dm ∧ 2*(163+3) ≤ Dm ∧ 1 ≤ Dm) :
    ∃ ZP ZT ZS : ℕ, ∀ (den : ℕ) (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
      (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
      (caps : RowCaps) (g7cost : ℕ → ℕ) (w Mb Ms U0 V v C : ℕ),
      1 ≤ den → RequestAdmitted den degree target r →
      (r.input a).length ≤ K.inC*(r.q+1)^K.inE →
      (r.family a).rows.length + 1 ≤ K.rowsC*(r.q+1)^K.rowsE →
      (r.smallSize a)^Dm ≤ 1*smallClass 4 0 r.q →
      layout.w ≤ r.q → layout.degree ≤ r.q → layout.C ≤ K.capC*smallClass 4 K.capE r.q →
      caps.headerFuel ≤ K.hdC*smallClass 4 K.hdE r.q →
      caps.copyCap ≤ K.cpTC*tableClass r.liveScale K.cpTE r.q + K.cpSC*smallClass 4 K.cpSE r.q →
      caps.descriptorReserve ≤ K.dsTC*tableClass r.liveScale K.dsTE r.q + K.dsSC*smallClass 4 K.dsSE r.q →
      caps.rawReserve ≤ K.rwC*smallClass 4 K.rowsE r.q →
      RowCaps.Good selector a printer r layout facts caps →
      (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length + 1 ≤ K.betC*(r.q+1)^K.betE →
      Mb ≤ K.mC*(r.q+1)^K.mE → Ms ≤ K.mC*(r.q+1)^K.mE → U0 ≤ K.mC*(r.q+1)^K.mE →
      w ≤ K.bC*(r.q+1)^K.bE → v ≤ K.bC*(r.q+1)^K.bE →
      V ≤ K.cVc*tableClass r.liveScale K.hV r.q →
      g7cost 0 ≤ K.cG*(r.q+1)^K.dG → C ≤ K.cwC*(r.q+1)^K.cwE →
      InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q ZP ZT ZS
        (6*C + g7cost 0 + Rest.backCost se sp r 0 w r.q
            (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length Mb Ms +
          Rest.cycFuel mask packet rows r layout facts caps
            (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length then Mb else Ms) U0
            (P1TopDownPaidReusableReserves.workspace printer V) (P1TopDownPaidReusableReserves.rewind printer V)
            (P1TopDownPaidReusableReserves.buffer V) v 0) := by
  obtain ⟨A1, A2, A3, hc⟩ := cyc0_cls mask packet rows degree target cc dc hcold K Dm ⟨hDm.1, hDm.2.1, hDm.2.2.1⟩
  obtain ⟨B1, B2, B3, hf⟩ := first0_cls se sp K mask.degree rows.degree Dm ⟨hDm.2.2.2.1, hDm.2.2.2.2.1, hDm.2.2.2.2.2.1,
    hDm.2.2.2.2.2.2⟩
  refine ⟨B1 + A1, B2 + A2, B3 + A3, fun den r layout facts caps g7cost w Mb Ms U0 V v C hden hradm hin hrows hsm hlw hld hlC
    hhd hcp hds hraw hgood hgs hMb hMs hU0 hw hv hV hg7 hC => ?_⟩
  have hM2 : (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length then Mb else Ms) ≤
      K.mC*(r.q+1)^K.mE := by split <;> assumption
  exact (hf r g7cost w _ Mb Ms C hin hsm hw hMb hMs hg7 hC).add
    (hc den r layout facts caps _ U0 V v hden hradm hin hrows hsm hlw hld hlC hhd hcp hds hraw hgood hgs hM2 hU0 hv hV)

end
end NearCubicWires.SourceBudget
end

