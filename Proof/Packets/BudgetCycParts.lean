import Proof.Packets.BudgetCycFuel
import Proof.SourceAssembly.AdmissionInput

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section

/-! ## 1. Word lengths of a call -/

theorem flatMap_frame_const {α : Type} (xs : List α) (f : α → List Bool) (c : ℕ) (hf : ∀ x, (f x).length = c) :
    (xs.flatMap (fun x => RepairOrdinary.frame (f x))).length = xs.length * (2*c+1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, RepairOrdinary.frame_length, hf, ih, List.length_cons]
    ring

theorem ofFn_frame_flatten (m c : ℕ) (f : Fin m → List Bool) (hf : ∀ i, (f i).length = c) :
    ((List.ofFn (fun i => RepairOrdinary.frame (f i))).flatten).length = m*(2*c+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := ih (fun i => f i.succ) (fun i => hf i.succ)
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, RepairOrdinary.frame_length, hf 0, h]
    ring

/-- The support word is one frame of `q` bits per occurrence. -/
theorem supportWord_length (a : DecompositionAlgorithm) (r : Request) :
    (r.supportWord a).length = (r.family a).occurrences.length * (2*r.q+1) := by
  unfold Request.supportWord
  exact flatMap_frame_const _ _ r.q (fun g => by simp)

/-- The mask worker's support word has the same length. -/
theorem maskSupport_length (a : DecompositionAlgorithm) (r : Request) :
    (maskData a r).supportWord.length = (r.family a).occurrences.length * (2*r.q+1) := by
  unfold MaskData.supportWord
  exact ofFn_frame_flatten _ r.q _ (fun i => by simp [maskData])

/-- Every word of a call (and `q`, and the occurrence count) is below its input length. -/
theorem words_le_input (a : DecompositionAlgorithm) (r : Request) :
    r.q ≤ (r.input a).length ∧ r.nativeWord.length ≤ (r.input a).length ∧
    (r.supportWord a).length ≤ (r.input a).length ∧ (r.indexWord a).length ≤ (r.input a).length ∧
    (r.topWord a).length ≤ (r.input a).length ∧ (r.family a).occurrences.length ≤ (r.input a).length ∧
    (maskData a r).supportWord.length ≤ (r.input a).length := by
  have hin := Admission.input_length a r
  have hm := Admission.mask_length (r.family a).occurrences r.liveScale
  have hs := supportWord_length a r
  have hms := maskSupport_length a r
  have hocc : (r.family a).occurrences.length ≤ (r.family a).occurrences.length * (2*r.q+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  rw [hm] at hin
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## 2. The seed loader -/

theorem seed_arith (q K occ sW nW iW tW mSW X c d : ℕ) (hK : K ≤ q) (hq : q ≤ X) (hsW : sW ≤ X) (hnW : nW ≤ X)
    (hiW : iW ≤ X) (htW : tW ≤ X) (hocc : occ ≤ X) (hmSW : mSW ≤ X) :
    (4*q+2+1+(4*sW+8*(q+K+occ)+29)) + 1 + (c*(q+K+occ+mSW+1)^d + 1 + (8*q+16*(nW+sW+q+iW+tW)+75)) + 1 + 1 ≤
      (231 + c*4^d)*(X+1)^(d+1) := by
  have h1 : 1 ≤ (X+1)^d := Nat.one_le_pow _ _ (by omega)
  have hpow : (X+1)^(d+1) = (X+1)^d*(X+1) := pow_succ _ _
  have hlin : X + 1 ≤ (X+1)^(d+1) := by
    rw [hpow]; exact Nat.le_mul_of_pos_left _ h1
  have hm : (q+K+occ+mSW+1)^d ≤ (4*(X+1))^d := Nat.pow_le_pow_left (by omega) d
  have hm2 : (4*(X+1))^d = 4^d*(X+1)^d := mul_pow _ _ _
  have hm3 : (X+1)^d ≤ (X+1)^(d+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmask : c*(q+K+occ+mSW+1)^d ≤ (c*4^d)*(X+1)^(d+1) := by
    calc c*(q+K+occ+mSW+1)^d ≤ c*(4^d*(X+1)^d) := Nat.mul_le_mul_left _ (hm.trans (le_of_eq hm2))
      _ = (c*4^d)*(X+1)^d := by ring
      _ ≤ (c*4^d)*(X+1)^(d+1) := Nat.mul_le_mul_left _ hm3
  have e : (231 + c*4^d)*(X+1)^(d+1) = 231*(X+1)^(d+1) + (c*4^d)*(X+1)^(d+1) := by ring
  rw [e]
  have h231 : 231*(X+1) ≤ 231*(X+1)^(d+1) := Nat.mul_le_mul_left _ hlin
  omega

/-- **The seed loader in the classes**: source polynomial (lead, mask worker, suffix frames, at exponent `inE·(d+1)`)
plus the packet writer's small-class budget (AD `packetBudget_inClasses`). -/
theorem seed_inClasses (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    (packet : PacketWriter selector a) (r : Request) (inC inE : ℕ)
    (hin : (r.input a).length ≤ inC*(r.q+1)^inE)
    (m rowsC rowsE smallC smallE dP hT : ℕ)
    (h_rows : (r.family a).rows.length+1 ≤ rowsC*(r.q+1)^rowsE)
    (h_small : (r.smallSize a)^packet.degree ≤ smallC*smallClass m smallE r.q)
    (hdP : inE*(mask.degree+1) ≤ dP) :
    InClasses dP hT (rowsE+smallE) m r.liveScale r.q r.q
      ((231 + mask.coefficient*4^mask.degree)*(inC+1)^(mask.degree+1)) 0 (packet.coefficient*rowsC*smallC)
      (SourceRequest.seedFuel mask packet r) := by
  obtain ⟨hq, hnW, hsW, hiW, htW, hocc, hmSW⟩ := words_le_input a r
  set X := (r.input a).length with hX
  have hK : normalizedLiveCount r.q r.liveScale ≤ r.q := normalizedLiveCount_le _ _
  have harith := seed_arith r.q (normalizedLiveCount r.q r.liveScale) (r.family a).occurrences.length
    (r.supportWord a).length r.nativeWord.length (r.indexWord a).length (r.topWord a).length
    (maskData a r).supportWord.length X mask.coefficient mask.degree hK hq hsW hnW hiW htW hocc hmSW
  -- `(X+1)^(d+1) ≤ (inC+1)^(d+1) (q+1)^(inE(d+1))`
  have hX1 : X + 1 ≤ (inC+1)*(r.q+1)^inE := by
    have : 1 ≤ (r.q+1)^inE := Nat.one_le_pow _ _ (by omega)
    have e : (inC+1)*(r.q+1)^inE = inC*(r.q+1)^inE + (r.q+1)^inE := by ring
    omega
  have hXp : (X+1)^(mask.degree+1) ≤ (inC+1)^(mask.degree+1)*(r.q+1)^(inE*(mask.degree+1)) := by
    calc (X+1)^(mask.degree+1) ≤ ((inC+1)*(r.q+1)^inE)^(mask.degree+1) := Nat.pow_le_pow_left hX1 _
      _ = (inC+1)^(mask.degree+1)*(r.q+1)^(inE*(mask.degree+1)) := by rw [mul_pow, ← pow_mul]
  have hpoly : (4*r.q+2+1+(4*(r.supportWord a).length+8*(r.q+normalizedLiveCount r.q r.liveScale+
      (r.family a).occurrences.length)+29)) + 1 + (mask.coefficient*(r.q+normalizedLiveCount r.q r.liveScale+
      (r.family a).occurrences.length+(maskData a r).supportWord.length+1)^mask.degree + 1 +
      (8*r.q+16*(r.nativeWord.length+(r.supportWord a).length+r.q+(r.indexWord a).length+(r.topWord a).length)+75)) +
      1 + 1 ≤ ((231 + mask.coefficient*4^mask.degree)*(inC+1)^(mask.degree+1))*(r.q+1)^(inE*(mask.degree+1)) := by
    calc _ ≤ (231 + mask.coefficient*4^mask.degree)*(X+1)^(mask.degree+1) := harith
      _ ≤ (231 + mask.coefficient*4^mask.degree)*((inC+1)^(mask.degree+1)*(r.q+1)^(inE*(mask.degree+1))) :=
          Nat.mul_le_mul_left _ hXp
      _ = _ := by ring
  have hP : InClasses dP hT (rowsE+smallE) m r.liveScale r.q r.q
      ((231 + mask.coefficient*4^mask.degree)*(inC+1)^(mask.degree+1)) 0 0 _ := InClasses.poly hpoly hdP
  have hpk := packetBudget_inClasses a packet.coefficient packet.degree r m rowsC rowsE smallC smallE dP hT r.q
    h_rows h_small
  have hsum := hP.add hpk
  refine InClasses.mono (le_of_eq ?_) (hsum.coeff_mono (by simp) (by simp) (by simp))
  unfold SourceRequest.seedFuel SLoad.LeadDriver.prefixFuel SLoad.RequestLead.prefixFuel SLoad.Lead.cost maskBudget
    SLoad.SuffixFrame.cost
  simp only [maskData]
  ring

/-! ## 3. The setup loader -/

/-- **The setup loader in the classes**: linear in the call's input and in the metadata values `w, degree, C` and the
four caps (`natListWord_le`), so it lies in the classes of those values. -/
theorem setup_inClasses (a : DecompositionAlgorithm) (r : Request) (w deg C : ℕ) (caps : RowCaps)
    {dP hT hS m L n qn : ℕ} {c1P c1T c1S c2P c2T c2S c3P c3T c3S : ℕ}
    (hin : InClasses dP hT hS m L n qn c1P c1T c1S (r.input a).length)
    (hB1 : InClasses dP hT hS m L n qn c2P c2T c2S (w + deg + C))
    (hB2 : InClasses dP hT hS m L n qn c3P c3T c3S
      (caps.headerFuel + caps.copyCap + caps.descriptorReserve + caps.rawReserve)) :
    InClasses dP hT hS m L n qn (4*c1P + 24*c2P + 32*c3P + 177) (4*c1T + 24*c2T + 32*c3T) (4*c1S + 24*c2S + 32*c3S)
      (SLoad.Setup.cost (r.input a).length (SLoad.Setup.metaBits w deg C caps).length) := by
  have h1 := natListWord_le [w, deg, C] (w + deg + C) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  have h2 := natListWord_le [caps.headerFuel, caps.copyCap, caps.descriptorReserve, caps.rawReserve]
    (caps.headerFuel + caps.copyCap + caps.descriptorReserve + caps.rawReserve) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega)
  have hmb : (SLoad.Setup.metaBits w deg C caps).length ≤
      6*(w + deg + C) + 8*(caps.headerFuel + caps.copyCap + caps.descriptorReserve + caps.rawReserve) + 41 := by
    unfold SLoad.Setup.metaBits RowCaps.word
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 h2 ⊢
    omega
  have hs := (((hin.smul 4).add (hB1.smul 24)).add (hB2.smul 32)).add_const 177
  refine InClasses.mono ?_ (hs.coeff_mono (by omega) (by omega) (by omega))
  unfold SLoad.Setup.cost
  omega

/-! ## 4. The row-width stage -/

theorem rowWidth_arith (L M2 U0 N : ℕ) :
    RowWidth.cost L M2 U0 N ≤ 128*(L + M2 + U0 + N + 1)^3 := by
  set Z := L + M2 + U0 + N + 1 with hZ
  have hZ1 : 1 ≤ Z := by omega
  have hrw : RowWidth.rw M2 U0 L ≤ 2*(Z*Z) := by
    unfold RowWidth.rw
    have : M2*(L+1) ≤ Z*Z := Nat.mul_le_mul (by omega) (by omega)
    have : U0 ≤ Z*Z := le_trans (show U0 ≤ Z by omega) (Nat.le_mul_of_pos_left _ hZ1)
    omega
  have hZ3 : Z*Z*Z = Z^3 := by ring
  have hZZ : Z*Z ≤ Z*Z*Z := Nat.le_mul_of_pos_right _ hZ1
  have hZ : Z ≤ Z*Z := Nat.le_mul_of_pos_left _ hZ1
  have hb : M2*(2*(L+1)+3) ≤ 5*(Z*Z) := by
    have := Nat.mul_le_mul (show M2 ≤ Z by omega) (show 2*(L+1)+3 ≤ 5*Z by omega)
    have e : Z*(5*Z) = 5*(Z*Z) := by ring
    omega
  have hc : M2*(L+1) ≤ Z*Z := Nat.mul_le_mul (by omega) (by omega)
  have hf : RowWidth.rw M2 U0 L*(2*N+3) ≤ 10*(Z*Z*Z) := by
    have := Nat.mul_le_mul hrw (show 2*N+3 ≤ 5*Z by omega)
    have e : 2*(Z*Z)*(5*Z) = 10*(Z*Z*Z) := by ring
    omega
  have hg : RowWidth.rw M2 U0 L*N ≤ 2*(Z*Z*Z) := by
    have := Nat.mul_le_mul hrw (show N ≤ Z by omega)
    have e : 2*(Z*Z)*Z = 2*(Z*Z*Z) := by ring
    omega
  have hZ1' : 1 ≤ Z*Z*Z := le_trans hZ1 (hZ.trans hZZ)
  have hZ' : Z ≤ Z*Z*Z := hZ.trans hZZ
  unfold RowWidth.cost
  simp only
  rw [← hZ3]
  omega

/-- **The row-width stage in the classes** (a cubic in its four scalars). -/
theorem rowWidth_inClasses {dP hT hS m L n qn : ℕ} (Lg M2 U0 N xC xE : ℕ)
    (hx : Lg + M2 + U0 + N + 1 ≤ xC*(n+1)^xE) (hd : xE*3 ≤ dP) :
    InClasses dP hT hS m L n qn (128*xC^3) 0 0 (RowWidth.cost Lg M2 U0 N) := by
  refine InClasses.poly ((rowWidth_arith Lg M2 U0 N).trans ?_) hd
  calc 128*(Lg + M2 + U0 + N + 1)^3 ≤ 128*(xC*(n+1)^xE)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 3)
    _ = 128*xC^3*(n+1)^(xE*3) := by rw [mul_pow, ← pow_mul]; ring

end
end NearCubicWires.SourceBudget
end

