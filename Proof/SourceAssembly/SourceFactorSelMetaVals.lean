import Proof.SourceAssembly.SourceFactorSelMetaCost
import Proof.Packets.SrcMetaIface2

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceFactorSel.MetaPipe
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission NearCubicWires.SourceConstruction NearCubicWires.SourceStart.Meta
noncomputable section

/-! ## 1. The constants -/

/-- **The source's pipeline constants.** -/
def mcOf (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) : MC where
  mE := ce0 selector (decompositionOf s) p.clauseDegree (tgt s p)
  mC := cc0 selector (decompositionOf s) p.clauseDegree (tgt s p)
  hE := hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L
  hC := hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L
  tE := cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
  tC := cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
  sE := cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
  sC := cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
  vE := v0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
  vC := v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
  rE := rowsE (decompositionOf s) p.clauseDegree (tgt s p)
  rC := (packets (decompositionOf s)).coefficient * rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1

theorem half2 (K : ℕ) : 2 * K / 2 = K := Nat.mul_div_cancel_left K (by decide)

theorem v200 (q : ℕ) : NearCubicWires.BlockPlatform.UnaryCalc.value 0 200 q = 200 := by
  unfold NearCubicWires.BlockPlatform.UnaryCalc.value
  rw [pow_zero, Nat.mul_one]

theorem quarter (q : ℕ) : q / 2 / 2 = q / 4 := Nat.div_div_eq_div_mul q 2 2

section outs
variable (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L q : ℕ)

theorem oW_eq : r10 (mcOf selector s p packets L) q (2 * normalizedLiveCount q L) = wA q L := by
  show ((q - 2 * normalizedLiveCount q L / 2) / NearCubicWires.BlockPlatform.UnaryCalc.value 0 200 q -
      2 * normalizedLiveCount q L / 2) / (2 * normalizedLiveCount q L / 2 + 2) = wA q L
  rw [half2, v200]
  rfl

theorem oD_eq : r12 (mcOf selector s p packets L) q (2 * normalizedLiveCount q L) = uniformDeg q L := by
  show q / NearCubicWires.BlockPlatform.UnaryCalc.value 0 200 q / (2 * normalizedLiveCount q L / 2 + 2) = uniformDeg q L
  rw [half2, v200, Nat.div_div_eq_div_mul]
  rfl

theorem oX_eq (K2 : ℕ) : r4 (mcOf selector s p packets L) q K2 = q / 4 := quarter q

theorem oXK_eq : r5 (mcOf selector s p packets L) q (2 * normalizedLiveCount q L) = q - normalizedLiveCount q L := by
  show q - 2 * normalizedLiveCount q L / 2 = q - normalizedLiveCount q L
  rw [half2]

theorem oM_eq (K2 : ℕ) : r13 (mcOf selector s p packets L) q K2 = mC selector s p q := rfl

theorem oB_eq (K2 : ℕ) :
    r15 (mcOf selector s p packets L) q K2 = Nat.clog 2 (mC selector s p q + 1) + q / 4 := by
  show Nat.clog 2 (mC selector s p q + 1) + q / 2 / 2 = _
  rw [quarter]

theorem oH_eq (K2 : ℕ) : r18 (mcOf selector s p packets L) q K2 = yH selector s p L q := by
  show Nat.clog 2 (hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L *
    (q + 1) ^ hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L + 1) + q / 2 / 2 = _
  rw [quarter]
  rfl

theorem oC_eq : r26 (mcOf selector s p packets L) q (2 * normalizedLiveCount q L) =
    max (yA selector s p L q) (yB selector s p q) + 1 := by
  show max (Nat.clog 2 (cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) *
      (q + 1) ^ cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 1) +
      (q - 2 * normalizedLiveCount q L / 2))
    (Nat.clog 2 (cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) *
      (q + 1) ^ cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + 1) + q / 2 / 2) + 1 = _
  rw [half2, quarter]
  rfl

theorem oMV_eq (K2 : ℕ) : r27 (mcOf selector s p packets L) q K2 = mV selector s p q := rfl

theorem oBV_eq : r29 (mcOf selector s p packets L) q (2 * normalizedLiveCount q L) =
    Nat.clog 2 (mV selector s p q + 1) + (q - normalizedLiveCount q L) := by
  show Nat.clog 2 (mV selector s p q + 1) + (q - 2 * normalizedLiveCount q L / 2) = _
  rw [half2]

theorem oR_eq (K2 : ℕ) : r32 (mcOf selector s p packets L) q K2 = yR selector s p packets q := by
  show Nat.clog 2 (((packets (decompositionOf s)).coefficient * rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1) *
    (q + 1) ^ rowsE (decompositionOf s) p.clauseDegree (tgt s p) + 1) + q / 2 / 2 = _
  rw [quarter]
  rfl

end outs

/-! ## 3. Reading the register file -/

theorem outAt {NL R nR S : ℕ} {vs : List ℕ} {E : Fin NL → List Bool} (hI : Inv R nR vs S E) (i : ℕ) (hi : i < nR)
    (hiN : i < NL) (v : ℕ) (hv : vs.getD i 0 = v) :
    E ⟨i, hiN⟩ = ZeroPadding.pad R (List.replicate v true) := by
  rw [hI.1 ⟨i, hiN⟩ hi, hv]

/-- The entry file: `[q, K2]`, everything else blank. -/
theorem inv_entry {NL : ℕ} (R q K2 : ℕ) (vs : List ℕ) (hvs : vs = [q, K2]) (S : ℕ) (hS : 2 ≤ S) (h01 : 1 < NL)
    (E : Fin NL → List Bool) (h0 : E ⟨0, by omega⟩ = ZeroPadding.pad R (List.replicate q true))
    (h1 : E ⟨1, h01⟩ = ZeroPadding.pad R (List.replicate K2 true))
    (hz : ∀ x, x ≠ ⟨0, by omega⟩ → x ≠ ⟨1, h01⟩ → E x = List.replicate R false) (nR : ℕ) :
    Inv R nR vs S E := by
  subst hvs
  have blank : ∀ x : Fin NL, 2 ≤ x.val → E x = List.replicate R false := by
    intro x hx
    exact hz x (fun e => by rw [e] at hx; exact absurd (show 2 ≤ 0 from hx) (by decide))
      (fun e => by rw [e] at hx; exact absurd (show 2 ≤ 1 from hx) (by decide))
  refine ⟨fun x _ => ?_, fun x hx => blank x (le_trans hS hx)⟩
  rcases Nat.lt_or_ge x.val 2 with h | h
  · rcases Nat.lt_or_ge x.val 1 with h' | h'
    · have e : x = ⟨0, by omega⟩ := Fin.ext (show x.val = 0 by omega)
      rw [e, h0]
      rfl
    · have e : x = ⟨1, h01⟩ := Fin.ext (show x.val = 1 by omega)
      rw [e, h1]
      rfl
  · rw [blank x h, List.getD_eq_default _ _ (by simpa using h)]
    exact (NearCubicWires.SourceStart.Stages.pad_nil R).symm

/-! ## 4. The instance -/

section inst
variable (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ)

theorem kk_le (q : ℕ) : 2 * normalizedLiveCount q L ≤ 2 * q :=
  Nat.mul_le_mul_left 2 (normalizedLiveCount_le q L)

def metaVals2 : MetaVals2 selector s p packets L where
  NP := NL (mcOf selector s p packets L)
  states := _
  machine := metaM (mcOf selector s p packets L)
  cost := fun q => metaCost (mcOf selector s p packets L) q (2 * normalizedLiveCount q L)
  costC := Classical.choose (metaCost_poly (mcOf selector s p packets L))
  costE := Classical.choose (Classical.choose_spec (metaCost_poly (mcOf selector s p packets L)))
  cost_le := fun q => Classical.choose_spec (Classical.choose_spec (metaCost_poly (mcOf selector s p packets L))) q _
    (kk_le L q)
  iq := ⟨0, lt_NL _ 0 (by decide)⟩
  iK := ⟨1, lt_NL _ 1 (by decide)⟩
  oW := ⟨10, lt_NL _ 10 (by decide)⟩
  oD := ⟨12, lt_NL _ 12 (by decide)⟩
  oX := ⟨4, lt_NL _ 4 (by decide)⟩
  oXK := ⟨5, lt_NL _ 5 (by decide)⟩
  oM := ⟨13, lt_NL _ 13 (by decide)⟩
  oB := ⟨15, lt_NL _ 15 (by decide)⟩
  oH := ⟨18, lt_NL _ 18 (by decide)⟩
  oC := ⟨26, lt_NL _ 26 (by decide)⟩
  oMV := ⟨27, lt_NL _ 27 (by decide)⟩
  oBV := ⟨29, lt_NL _ 29 (by decide)⟩
  oR := ⟨32, lt_NL _ 32 (by decide)⟩
  nodup := by
    have h : ([0, 1, 10, 12, 4, 5, 13, 15, 18, 26, 27, 29, 32] : List ℕ).Nodup := by decide
    exact List.Nodup.of_map Fin.val h
  run := by
    intro q R E h0 h1 hz
    obtain ⟨E', hs, hI⟩ := meta_run (mcOf selector s p packets L) R q (2 * normalizedLiveCount q L) E
      (inv_entry R q (2 * normalizedLiveCount q L) _ rfl _ (le_trans (by decide) (Sof_ge _ 0)) _ E h0 h1 hz 33)
    refine ⟨E', hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (outAt hI 0 (by decide) _ q rfl).trans h0.symm
    · exact (outAt hI 1 (by decide) _ _ rfl).trans h1.symm
    · exact outAt hI 10 (by decide) _ _ (oW_eq selector s p packets L q)
    · exact outAt hI 12 (by decide) _ _ (oD_eq selector s p packets L q)
    · exact outAt hI 4 (by decide) _ _ (oX_eq selector s p packets L q _)
    · exact outAt hI 5 (by decide) _ _ (oXK_eq selector s p packets L q)
    · exact outAt hI 13 (by decide) _ _ (oM_eq selector s p packets L q _)
    · exact outAt hI 15 (by decide) _ _ (oB_eq selector s p packets L q _)
    · exact outAt hI 18 (by decide) _ _ (oH_eq selector s p packets L q _)
    · exact outAt hI 26 (by decide) _ _ (oC_eq selector s p packets L q)
    · exact outAt hI 27 (by decide) _ _ (oMV_eq selector s p packets L q _)
    · exact outAt hI 29 (by decide) _ _ (oBV_eq selector s p packets L q)
    · exact outAt hI 32 (by decide) _ _ (oR_eq selector s p packets L q _)

end inst

end
end NearCubicWires.SourceFactorSel.MetaPipe

