import Proof.Packets.BudgetUniformWidth
import Proof.SourceAssembly.AdmissionDegree

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.SupplierEstimator
open NearCubicWires.P1Closure NearCubicWires.RepairOrdinary
open NearCubicWires.Admission

noncomputable section

/-! ## 1. The width -/

abbrev wA (q L : ℕ) : ℕ := wU q L

/-- **The unary-writer form**: `wA q L = (q - 201·K) / (200·(K+2))`, `K = normalizedLiveCount q L` (one monus, one division by the
divisor SI's slopes already write). -/
theorem wA_eq_div (q L : ℕ) :
    wA q L = (q - 201*normalizedLiveCount q L) / (200*(normalizedLiveCount q L + 2)) := by
  unfold wA wU
  generalize normalizedLiveCount q L = K
  have h1 : (q - K)/200 - K = (q - 201*K)/200 := by omega
  rw [h1, Nat.div_div_eq_div_mul]

/-- **The load at `wA`** whenever `201·K ≤ q`. -/
theorem wA_load (q L : ℕ) (h : 201*normalizedLiveCount q L ≤ q) :
    200*(normalizedLiveCount q L + wA q L*(normalizedLiveCount q L + 2)) ≤ q - normalizedLiveCount q L := by
  rw [wA_eq_div]
  generalize normalizedLiveCount q L = K at h ⊢
  have hm := Nat.div_mul_le_self (q - 201*K) (200*(K+2))
  have e : 200*(K + (q - 201*K)/(200*(K+2))*(K+2)) = 200*K + (q - 201*K)/(200*(K+2))*(200*(K+2)) := by ring
  omega

theorem w_le_wA {q L : ℕ} {a : DecompositionAlgorithm} {F : Packets.Family q L} {g : Packets.Geometry F}
    (ℓ : Packets.Layout a F g) : ℓ.w ≤ wA q L := w_le_wU ℓ

/-- `fun q => cc·(q+1)^ce` is polynomially bounded. -/
theorem capPoly_polynomial (cc ce : ℕ) : PolynomiallyBounded (fun q => cc*(q+1)^ce) :=
  polynomiallyBounded_mul (polynomiallyBounded_constant cc)
    (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) ce)

/-- **`h_copy` at `C ≤ cc·smallClass 4 ce q`** (AD's `copy_class` with its `C ≤ streamCap` replaced by a fixed small-class bound on `C`;
same proof, `Ps := cc·(q+1)^ce`). One table term at an exponent fixed by `a degree printer`, the rest small. -/
theorem copy_classC (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) (degree target cc ce : ℕ) :
    ∃ copyTC copyTE copySC copySE : ℕ, ∀ den : ℕ, 1 ≤ den → ∀ r : Request,
      RequestAdmitted den degree target r →
      ∀ layout : Packets.Layout a (r.family a) (geometryOf selector a r), layout.degree ≤ r.q →
      layout.C ≤ cc*RuntimeShape.smallClass 4 ce r.q →
      (RCFive.RowCaps.chosen selector a printer r layout).copyCap ≤
        copyTC*RuntimeShape.tableClass r.liveScale copyTE r.q +
          copySC*RuntimeShape.smallClass 4 copySE r.q := by
  set e := CompetitorCrossScheduler.exponent printer
  set tc := CloseoutRowsEstimator.Driver.tableCoefficient printer
  have hPp := precisionPoly_polynomial a degree
  obtain ⟨CT, ET, _, hCT⟩ := polynomiallyBounded_pow (polynomiallyBounded_add
    (polynomiallyBounded_add polynomiallyBounded_id hPp) (polynomiallyBounded_constant 1)) e
  obtain ⟨CS, ES, _, hCS⟩ := polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_mul (polynomiallyBounded_constant 128) (polynomiallyBounded_add
      (capPoly_polynomial cc ce) (polynomiallyBounded_constant 1)))
    (polynomiallyBounded_mul (polynomiallyBounded_constant 4000000) (polynomiallyBounded_pow
      (polynomiallyBounded_add (polynomiallyBounded_add polynomiallyBounded_id hPp)
        (polynomiallyBounded_constant 2)) 3))) (polynomiallyBounded_constant 1)
  refine ⟨4*tc*CT, ET, CS, ES, ?_⟩
  intro den hden r hr layout hdw hlC
  obtain ⟨hcard, hx, hwq, hKq⟩ := layout_load_facts selector a r layout
  have hb := RequestAdmitted.radix_le hden a r hr
  have hprec : RCFive.NativeResources.precision a (r.family a) (geometryOf selector a r) layout ≤
      precisionPoly a degree r.q := by
    have h := precision_le a (r.family a) (geometryOf selector a r) layout hdw hKq
    unfold precisionPoly
    have := Nat.mul_le_mul_right (r.q*(r.q+1)) hb
    omega
  have hCs : layout.C ≤ 2^(r.q/4)*(cc*(r.q+1)^ce) := by
    have e0 : cc*RuntimeShape.smallClass 4 ce r.q = 2^(r.q/4)*(cc*(r.q+1)^ce) := by
      unfold RuntimeShape.smallClass; ring
    rw [← e0]; exact hlC
  have hdq : (Packets.residual (r.family a)+1)/2 ≤ r.q := by unfold Packets.residual; omega
  have hdr : 2*((Packets.residual (r.family a)+1)/2) ≤ Packets.residual (r.family a) + 1 := by omega
  have key := copy_arith ((Packets.residual (r.family a)+1)/2)
    (RCFive.NativeResources.precision a (r.family a) (geometryOf selector a r) layout)
    (RCFive.NativeResources.cutsCap a (r.family a) (geometryOf selector a r) layout) layout.C
    ((Packets.live (r.family a)).card + layout.w*((Packets.live (r.family a)).card+2)) r.q
    (Packets.residual (r.family a)) e tc (precisionPoly a degree r.q) (cc*(r.q+1)^ce)
    hx rfl hCs hprec hdq hdr
  have hres : Packets.residual (r.family a) = r.q - normalizedLiveCount r.q r.liveScale := by
    unfold Packets.residual; rfl
  change 2*RCFive.NativeResources.driverCap a (r.family a) (geometryOf selector a r) layout printer + 1 ≤ _
  unfold RCFive.NativeResources.driverCap CloseoutRowsEstimator.Driver.value
    CloseoutRowsEstimator.Driver.tableValue
  refine key.trans ?_
  rw [hres]
  unfold RuntimeShape.tableClass RuntimeShape.smallClass
  have t1 := Nat.mul_le_mul_right (2^(r.q - normalizedLiveCount r.q r.liveScale))
    (Nat.mul_le_mul_left (4*tc) (hCT r.q))
  have t2 := Nat.mul_le_mul_right (2^(r.q/4)) (hCS r.q)
  have e1 : 4*tc*(CT*(r.q+1)^ET)*2^(r.q - normalizedLiveCount r.q r.liveScale) =
      4*tc*CT*((r.q+1)^ET*2^(r.q - normalizedLiveCount r.q r.liveScale)) := by ring
  have e2 : CS*(r.q+1)^ES*2^(r.q/4) = CS*((r.q+1)^ES*2^(r.q/4)) := by ring
  exact Nat.add_le_add (t1.trans (le_of_eq e1)) (t2.trans (le_of_eq e2))

/-- **`chosen.descriptorReserve = rows·tapes·copyCap` at `C ≤ cc·smallClass 4 ce q`**: table exponent `rowsE + copyTE`, small
exponent `rowsE + copySE` (AD's `descriptor_class`, same proof, on `copy_classC`). -/
theorem descriptor_classC (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) (degree target cc ce : ℕ) :
    ∃ dTC dTE dSC dSE : ℕ, ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      ∀ layout : Packets.Layout a (r.family a) (geometryOf selector a r), layout.degree ≤ r.q →
      layout.C ≤ cc*RuntimeShape.smallClass 4 ce r.q →
      (RCFive.RowCaps.chosen selector a printer r layout).descriptorReserve ≤
        dTC*RuntimeShape.tableClass r.liveScale dTE r.q + dSC*RuntimeShape.smallClass 4 dSE r.q := by
  obtain ⟨rowsC, rowsE, hrows⟩ := rows_poly a degree target
  obtain ⟨cTC, cTE, cSC, cSE, hcopy⟩ := copy_classC selector a printer degree target cc ce
  refine ⟨rowsC*P1TopDownPaidPayload.tapes printer*cTC, rowsE+cTE,
    rowsC*P1TopDownPaidPayload.tapes printer*cSC, rowsE+cSE, ?_⟩
  intro den hden r hr layout hdw hlC
  have hR := hrows den hden r hr
  have hc := hcopy den hden r hr layout hdw hlC
  change (r.family a).rows.length*P1TopDownPaidPayload.tapes printer*
    (RCFive.RowCaps.chosen selector a printer r layout).copyCap ≤ _
  have h1 : (r.family a).rows.length ≤ rowsC*(r.q+1)^rowsE := by omega
  have h2 := Nat.mul_le_mul (Nat.mul_le_mul_right (P1TopDownPaidPayload.tapes printer) h1) hc
  refine h2.trans (le_of_eq ?_)
  unfold RuntimeShape.tableClass RuntimeShape.smallClass
  rw [pow_add, pow_add]
  ring

/-! ## 3. `V`'s class: ONE `(cVc, hV)` for `hD` and for `dR := Vv` -/

/-- A two-term class bound folds into ONE table term past the onset `K + q/4 ≤ q`. -/
theorem fold_table (L q TC TE SC SE x : ℕ) (hK : normalizedLiveCount q L + q/4 ≤ q)
    (hx : x ≤ TC*RuntimeShape.tableClass L TE q + SC*RuntimeShape.smallClass 4 SE q) (H : ℕ) (hH : TE + SE ≤ H) :
    x ≤ (TC + SC)*RuntimeShape.tableClass L H q := by
  have hs : RuntimeShape.smallClass 4 SE q ≤ RuntimeShape.tableClass L SE q := small_le_table L SE q hK
  have t1 : RuntimeShape.tableClass L TE q ≤ RuntimeShape.tableClass L H q := RuntimeShape.tableClass_mono (by omega)
  have t2 : RuntimeShape.tableClass L SE q ≤ RuntimeShape.tableClass L H q := RuntimeShape.tableClass_mono (by omega)
  have m1 := Nat.mul_le_mul_left TC t1
  have m2 := Nat.mul_le_mul_left SC (hs.trans t2)
  have e3 : (TC + SC)*RuntimeShape.tableClass L H q =
      TC*RuntimeShape.tableClass L H q + SC*RuntimeShape.tableClass L H q := by ring
  omega

theorem vcap_classC (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) (degree target cc ce : ℕ) :
    ∃ cVc hV : ℕ, ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      ∀ layout : Packets.Layout a (r.family a) (geometryOf selector a r), layout.degree ≤ r.q →
      layout.C ≤ cc*RuntimeShape.smallClass 4 ce r.q →
      normalizedLiveCount r.q r.liveScale + r.q/4 ≤ r.q →
      RCFive.NativeResources.driverCap a (r.family a) (geometryOf selector a r) layout printer ≤
          cVc*RuntimeShape.tableClass r.liveScale hV r.q ∧
        (RCFive.RowCaps.chosen selector a printer r layout).descriptorReserve ≤
          cVc*RuntimeShape.tableClass r.liveScale hV r.q := by
  obtain ⟨cTC, cTE, cSC, cSE, hcopy⟩ := copy_classC selector a printer degree target cc ce
  obtain ⟨dTC, dTE, dSC, dSE, hdesc⟩ := descriptor_classC selector a printer degree target cc ce
  refine ⟨cTC + cSC + (dTC + dSC), cTE + cSE + (dTE + dSE), ?_⟩
  intro den hden r hr layout hdw hlC hK
  have hc := hcopy den hden r hr layout hdw hlC
  have hd := hdesc den hden r hr layout hdw hlC
  have h2 : 2*RCFive.NativeResources.driverCap a (r.family a) (geometryOf selector a r) layout printer + 1 ≤
      cTC*RuntimeShape.tableClass r.liveScale cTE r.q + cSC*RuntimeShape.smallClass 4 cSE r.q := hc
  have fc := fold_table r.liveScale r.q cTC cTE cSC cSE _ hK h2 (cTE + cSE + (dTE + dSE)) (by omega)
  have fd := fold_table r.liveScale r.q dTC dTE dSC dSE _ hK hd (cTE + cSE + (dTE + dSE)) (by omega)
  have e : (cTC + cSC + (dTC + dSC))*RuntimeShape.tableClass r.liveScale (cTE + cSE + (dTE + dSE)) r.q =
      (cTC + cSC)*RuntimeShape.tableClass r.liveScale (cTE + cSE + (dTE + dSE)) r.q +
        (dTC + dSC)*RuntimeShape.tableClass r.liveScale (cTE + cSE + (dTE + dSE)) r.q := by ring
  constructor <;> omega

theorem streamCap_le_uniformC (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (degree target : ℕ) :
    ∃ cc ce : ℕ, ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      ∀ layout : Packets.Layout a (r.family a) (geometryOf selector a r), layout.degree ≤ r.q →
      RCFive.NativeResources.streamCap a (r.family a) (geometryOf selector a r) layout ≤
        cc*RuntimeShape.smallClass 4 ce r.q := by
  obtain ⟨C, E, _, hC⟩ := streamPoly_polynomial a degree
  refine ⟨C, E, fun den hden r hr layout hdw => ?_⟩
  have h := streamCap_small selector a hden r hr layout hdw
  unfold RuntimeShape.smallClass
  calc RCFive.NativeResources.streamCap a (r.family a) (geometryOf selector a r) layout
      ≤ 2^(r.q/4)*streamPoly a degree r.q := h
    _ ≤ 2^(r.q/4)*(C*(r.q+1)^E) := Nat.mul_le_mul_left _ (hC r.q)
    _ = C*((r.q+1)^E*2^(r.q/4)) := by ring

end
end NearCubicWires.SourceBudget

