import Proof.Packets.BudgetCycRows
import Proof.Packets.BudgetClass
import Proof.Packets.BudgetFirst3
import Proof.Packets.BudgetCountsAt

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

/-- **The size constants of one call** (all `L`-free except where AD's own lemma reads `L`). -/
structure CallK where
  inC : ℕ
  inE : ℕ
  rowsC : ℕ
  rowsE : ℕ
  capC : ℕ
  capE : ℕ
  hdC : ℕ
  hdE : ℕ
  cpTC : ℕ
  cpTE : ℕ
  cpSC : ℕ
  cpSE : ℕ
  dsTC : ℕ
  dsTE : ℕ
  dsSC : ℕ
  dsSE : ℕ
  rwC : ℕ
  betC : ℕ
  betE : ℕ
  mC : ℕ
  mE : ℕ
  bC : ℕ
  bE : ℕ
  jC : ℕ
  jE : ℕ
  cG : ℕ
  dG : ℕ
  cwC : ℕ
  cwE : ℕ
  cVc : ℕ
  hV : ℕ

/-- The polynomial exponent before the family's row-count factor (`md` = the mask's degree). -/
def CallK.D0 (K : CallK) (md : ℕ) : ℕ :=
  K.inE*(md+1) + 3*(K.betE + K.mE + K.rowsE) + K.inE + K.bE + K.jE + K.dG + K.cwE + 2

/-- The table exponent before the row-count factor (`rd` = the row producer's degree). -/
def CallK.H0 (K : CallK) (rd : ℕ) : ℕ := (K.inE+1)*rd + K.cpTE + K.dsTE + K.hV

/-- The small exponent before the row-count factor. -/
def CallK.S0 (K : CallK) : ℕ := K.hdE + K.capE + K.cpSE + K.dsSE + K.rowsE

/-- The cycle's exponents: the row-count factor `rowsE` on top of each. -/
def CallK.D (K : CallK) (md : ℕ) : ℕ := K.rowsE + K.D0 md
def CallK.H (K : CallK) (rd : ℕ) : ℕ := K.rowsE + K.H0 rd
def CallK.S (K : CallK) : ℕ := K.rowsE + K.S0

/-! ## Polynomial bookkeeping -/

theorem poly_add' {a b A B e n : ℕ} (ha : a ≤ A*(n+1)^e) (hb : b ≤ B*(n+1)^e) : a + b ≤ (A+B)*(n+1)^e := by
  rw [Nat.add_mul]; omega

theorem one_le_poly (n e : ℕ) : 1 ≤ 1*(n+1)^e := by
  rw [one_mul]; exact Nat.one_le_pow _ _ (by omega)

/-- `natBitLength` below a power of two. -/
theorem natBitLength_le_of_le_pow {x k : ℕ} (h : x ≤ 2^k) : natBitLength x ≤ k + 1 := by
  unfold natBitLength
  have h1 : Nat.log 2 x ≤ Nat.log 2 (2^k) := Nat.log_mono_right h
  rw [Nat.log_pow (by norm_num)] at h1
  omega

/-! ## The cycle at one call -/

theorem cyc0_cls (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (degree target cc dc : ℕ)
    (hcold : ∀ (q : ℕ) (x : BinaryCacheColdJoin.Args q), BinaryCacheColdRun.budget x ≤
      cc * ((exactListWord x.gs).length + x.gs.length + q + 2^x.live.card + 1)^dc)
    (K : CallK) (Dm : ℕ) (hDm : packet.degree ≤ Dm ∧ rows.degree ≤ Dm ∧ (betaE a degree + 1)*dc ≤ Dm) :
    ∃ ZP ZT ZS : ℕ, ∀ (den : ℕ) (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
      (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
      (caps : RowCaps) (M2 U0 V v : ℕ),
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
      M2 ≤ K.mC*(r.q+1)^K.mE → U0 ≤ K.mC*(r.q+1)^K.mE → v ≤ K.bC*(r.q+1)^K.bE →
      V ≤ K.cVc*tableClass r.liveScale K.hV r.q →
      InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q ZP ZT ZS
        (Rest.cycFuel mask packet rows r layout facts caps M2 U0 (P1TopDownPaidReusableReserves.workspace printer V)
          (P1TopDownPaidReusableReserves.rewind printer V) (P1TopDownPaidReusableReserves.buffer V) v 0) := by
  refine ⟨?zp, ?zt, ?zs, fun den r layout facts caps M2 U0 V v hden hr hin hrows hsm hlw hld hlC hhd hcp hds hraw hgood hgs
    hM2 hU0 hv hV => ?body⟩
  case body =>
    have hS1 : 1 ≤ r.smallSize a := smallSize_pos a r
    have hsmall : ∀ d, d ≤ Dm → (r.smallSize a)^d ≤ 1*smallClass 4 0 r.q :=
      fun d hd => (Nat.pow_le_pow_right hS1 hd).trans hsm
    have hD0 : K.D mask.degree = K.rowsE + K.D0 mask.degree := rfl
    have hH0 : K.H rows.degree = K.rowsE + K.H0 rows.degree := rfl
    have hS0 : K.S = K.rowsE + K.S0 := rfl
    -- (1) the seed loader
    have h1 := seed_inClasses mask packet r K.inC K.inE hin 4 K.rowsC K.rowsE 1 0 (K.D mask.degree) (K.H rows.degree) hrows
      (hsmall _ hDm.1) (by rw [hD0]; unfold CallK.D0; omega)
    have h1' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q _ _ _
        (SourceRequest.seedFuel mask packet r) :=
      InClasses.raise le_rfl le_rfl (by rw [hS0]; unfold CallK.S0; omega) h1
    -- (2) the cold cache
    have h2 := cold_inClasses a hden r hr cc dc hcold 4 1 0 (hsmall _ hDm.2.2) (K.D mask.degree) (K.H rows.degree) r.q
    have h2' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q _ _ _
        (BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a))) :=
      InClasses.raise le_rfl le_rfl (Nat.zero_le _) h2
    -- (3) the setup
    have hinP : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q K.inC 0 0 (r.input a).length :=
      InClasses.poly hin (by rw [hD0]; unfold CallK.D0; omega)
    have hwd : layout.w + layout.degree ≤ 2*(r.q+1)^1 := by rw [pow_one]; omega
    have hB1a : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 2 0 0 (layout.w + layout.degree) :=
      InClasses.poly hwd (by rw [hD0]; unfold CallK.D0; omega)
    have hB1b0 : InClasses (K.D mask.degree) (K.H rows.degree) K.capE 4 r.liveScale r.q r.q 0 0 K.capC layout.C :=
      InClasses.small hlC
    have hB1b : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 0 0 K.capC layout.C :=
      InClasses.raise le_rfl le_rfl (by rw [hS0]; unfold CallK.S0; omega) hB1b0
    have hB1 := hB1a.add hB1b
    have hhd0 : InClasses (K.D mask.degree) (K.H rows.degree) K.hdE 4 r.liveScale r.q r.q 0 0 K.hdC caps.headerFuel :=
      InClasses.small hhd
    have hcp0 : InClasses (K.D mask.degree) K.cpTE K.cpSE 4 r.liveScale r.q r.q 0 K.cpTC K.cpSC caps.copyCap :=
      InClasses.table_small hcp
    have hds0 : InClasses (K.D mask.degree) K.dsTE K.dsSE 4 r.liveScale r.q r.q 0 K.dsTC K.dsSC caps.descriptorReserve :=
      InClasses.table_small hds
    have hrw0 : InClasses (K.D mask.degree) (K.H rows.degree) K.rowsE 4 r.liveScale r.q r.q 0 0 K.rwC caps.rawReserve :=
      InClasses.small hraw
    have hhd' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 0 0 K.hdC caps.headerFuel :=
      InClasses.raise le_rfl le_rfl (by rw [hS0]; unfold CallK.S0; omega) hhd0
    have hcp' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 0 K.cpTC K.cpSC caps.copyCap :=
      InClasses.raise le_rfl (by rw [hH0]; unfold CallK.H0; omega) (by rw [hS0]; unfold CallK.S0; omega) hcp0
    have hds' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 0 K.dsTC K.dsSC
        caps.descriptorReserve :=
      InClasses.raise le_rfl (by rw [hH0]; unfold CallK.H0; omega) (by rw [hS0]; unfold CallK.S0; omega) hds0
    have hrw' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 0 0 K.rwC caps.rawReserve :=
      InClasses.raise le_rfl le_rfl (by rw [hS0]; unfold CallK.S0; omega) hrw0
    have hB2 := ((hhd'.add hcp').add hds').add hrw'
    have h3 := setup_inClasses a r layout.w layout.degree layout.C caps hinP hB1 hB2
    -- (4) the row initializer
    have hrbD := rowBudget_inClasses a rows.coefficient rows.degree r layout.C caps 4 K.inC K.inE 1 0 K.hdC K.hdE K.capC K.capE
      K.cpTC K.cpTE K.cpSC K.cpSE (K.D mask.degree) r.q hin (hsmall _ hDm.2.1) hhd hlC hcp
    have hrbD' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q _ _ _
        (rowBudget a rows.coefficient rows.degree r layout.C caps) :=
      InClasses.raise le_rfl (by rw [hH0]; unfold CallK.H0; omega) (by rw [hS0]; unfold CallK.S0; omega) hrbD
    have hrowsD : (r.family a).rows.length ≤ K.rowsC*(r.q+1)^(K.D mask.degree) :=
      poly_raise (show (r.family a).rows.length ≤ K.rowsC*(r.q+1)^K.rowsE by omega) (by rw [hD0]; omega)
    have h4 := rowInit_inClasses a rows.coefficient rows.degree r layout.w layout.degree layout.C caps hrbD' hB1 hB2 hrowsD
    -- (5) the row family (the row count raises every exponent by `rowsE`)
    have hrb0 := rowBudget_inClasses a rows.coefficient rows.degree r layout.C caps 4 K.inC K.inE 1 0 K.hdC K.hdE K.capC K.capE
      K.cpTC K.cpTE K.cpSC K.cpSE (K.D0 mask.degree) r.q hin (hsmall _ hDm.2.1) hhd hlC hcp
    have hrb0' : InClasses (K.D0 mask.degree) (K.H0 rows.degree) K.S0 4 r.liveScale r.q r.q _ _ _
        (rowBudget a rows.coefficient rows.degree r layout.C caps) :=
      InClasses.raise le_rfl (by unfold CallK.H0; omega) (by unfold CallK.S0; omega) hrb0
    have hNn : (r.family a).rows.length ≤ K.rowsC*(r.q+1)^K.rowsE := by omega
    have h5 : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q _ _ _
        (PCJ38fbfed565f64139_Family.budget printer (r.family a) (rows.state r layout facts caps)) :=
      family_inClasses rows r layout facts caps hgood hrb0' hNn hNn
    -- (6) the descriptor reserve
    have h6 := hds'
    -- (7) the row width stage
    have hN : nOf selector a r layout facts = (r.family a).rows.length := by
      unfold nOf dataList; simp
    have hx7 : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length + M2 + U0 +
        nOf selector a r layout facts + 1 ≤
        (K.betC + K.mC + K.mC + K.rowsC)*(r.q+1)^(K.betE + K.mE + K.rowsE) := by
      rw [hN]
      have a1 := poly_raise hgs (show K.betE ≤ K.betE + K.mE + K.rowsE by omega)
      have a2 := poly_raise hM2 (show K.mE ≤ K.betE + K.mE + K.rowsE by omega)
      have a3 := poly_raise hU0 (show K.mE ≤ K.betE + K.mE + K.rowsE by omega)
      have a4 := poly_raise hNn (show K.rowsE ≤ K.betE + K.mE + K.rowsE by omega)
      have := poly_add' (poly_add' (poly_add' a1 a2) a3) a4
      omega
    have h7 := rowWidth_inClasses (dP := K.D mask.degree) (hT := K.H rows.degree) (hS := K.S) (m := 4) (L := r.liveScale)
      (n := r.q) (qn := r.q) _ M2 U0 _ _ _ hx7 (by rw [hD0]; unfold CallK.D0; omega)
    -- (8) the family init
    have hV' : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 0 K.cVc 0 V :=
      InClasses.raise le_rfl (by rw [hH0]; unfold CallK.H0; omega) le_rfl (V_inClasses hV)
    have hrwB : rwOf a r M2 U0 ≤ (K.mC*K.betC + K.mC)*(r.q+1)^(K.mE + K.betE) := by
      unfold rwOf RowWidth.rw
      have b1 := poly_mul hM2 hgs
      have b2 := poly_raise hU0 (show K.mE ≤ K.mE + K.betE by omega)
      have b3 := poly_add' b1 b2
      have e : M2 * ((exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length + 1) =
          M2 * ((exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length + 1) := rfl
      omega
    have hx8 : rwOf a r M2 U0 + v + nOf selector a r layout facts + nOf selector a r layout facts * rwOf a r M2 U0 + 1 ≤
        ((K.mC*K.betC + K.mC) + K.bC + K.rowsC + K.rowsC*(K.mC*K.betC + K.mC) + 1)*(r.q+1)^(K.D mask.degree) := by
      rw [hN]
      have c1 := poly_raise hrwB (show K.mE + K.betE ≤ K.D mask.degree by rw [hD0]; unfold CallK.D0; omega)
      have c2 := poly_raise hv (show K.bE ≤ K.D mask.degree by rw [hD0]; unfold CallK.D0; omega)
      have c3 := poly_raise hNn (show K.rowsE ≤ K.D mask.degree by rw [hD0]; unfold CallK.D0; omega)
      have c4 := poly_raise (poly_mul hNn hrwB) (show K.rowsE + (K.mE + K.betE) ≤ K.D mask.degree by
        rw [hD0]; unfold CallK.D0; omega)
      have c5 := poly_raise (one_le_poly r.q 0) (Nat.zero_le (K.D mask.degree))
      have := poly_add' (poly_add' (poly_add' (poly_add' c1 c2) c3) c4) c5
      omega
    have h8 := initFuel_inClasses printer hV' (rwOf a r M2 U0) v (nOf selector a r layout facts) _ hx8
    have hn : InClasses (K.D mask.degree) (K.H rows.degree) K.S 4 r.liveScale r.q r.q 0 0 0 0 := InClasses.zero
    exact cycFuel_inClasses mask packet rows r layout facts caps M2 U0 (P1TopDownPaidReusableReserves.workspace printer V)
      (P1TopDownPaidReusableReserves.rewind printer V) (P1TopDownPaidReusableReserves.buffer V) v 0
      hn h1' h2' h3 h4 h5 h6 h7 h8

end
end NearCubicWires.SourceBudget
end

