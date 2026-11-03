import Proof.SourceAssembly.SourceFactorSelWordsLocal
import Proof.Packets.BudgetCycParts
import Proof.SourceAssembly.SourceCacheBudget

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsCost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
open NearCubicWires.SourceFactorSel.Words
noncomputable section

/-! ## The base and the closure -/

/-- The request's child list (the cold cache's input 98). -/
abbrev gsOf (a : DecompositionAlgorithm) (r : Request) := (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs

/-- **The base**: the call's input, its child list (word and count), the meta word. -/
def Yb (a : DecompositionAlgorithm) (x : Request × List Bool) : ℕ :=
  (x.1.input a).length + (exactListWord (gsOf a x.1)).length + (gsOf a x.1).length + x.2.length + 1

/-- `f` is bounded by a fixed power of the base. -/
def PolB (a : DecompositionAlgorithm) (f : Request × List Bool → ℕ) : Prop := ∃ c d : ℕ, ∀ x, f x ≤ c * (Yb a x) ^ d

section closure
variable {a : DecompositionAlgorithm}

theorem Yb_pos (x : Request × List Bool) : 1 ≤ Yb a x := by unfold Yb; omega

theorem PolB.mono {f g : Request × List Bool → ℕ} (hg : PolB a g) (h : ∀ x, f x ≤ g x) : PolB a f := by
  obtain ⟨c, d, hc⟩ := hg
  exact ⟨c, d, fun x => (h x).trans (hc x)⟩

theorem PolB.const (k : ℕ) : PolB a (fun _ => k) := ⟨k, 0, fun x => by simp⟩

theorem PolB.ofY {f : Request × List Bool → ℕ} (h : ∀ x, f x ≤ Yb a x) : PolB a f :=
  ⟨1, 1, fun x => by simpa using h x⟩

theorem PolB.add {f g h : Request × List Bool → ℕ} (hf : PolB a f) (hg : PolB a g) (e : ∀ x, h x ≤ f x + g x) :
    PolB a h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 + c2, d1 + d2, fun x => ?_⟩
  have hs := Yb_pos (a := a) x
  have p1 : (Yb a x) ^ d1 ≤ (Yb a x) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have p2 : (Yb a x) ^ d2 ≤ (Yb a x) ^ (d1 + d2) := Nat.pow_le_pow_right hs (by omega)
  have q1 := (h1 x).trans (Nat.mul_le_mul_left c1 p1)
  have q2 := (h2 x).trans (Nat.mul_le_mul_left c2 p2)
  have e2 := e x
  rw [Nat.add_mul]
  omega

theorem PolB.mul {f g h : Request × List Bool → ℕ} (hf : PolB a f) (hg : PolB a g) (e : ∀ x, h x ≤ f x * g x) :
    PolB a h := by
  obtain ⟨c1, d1, h1⟩ := hf
  obtain ⟨c2, d2, h2⟩ := hg
  refine ⟨c1 * c2, d1 + d2, fun x => (e x).trans ?_⟩
  calc f x * g x ≤ (c1 * (Yb a x) ^ d1) * (c2 * (Yb a x) ^ d2) := Nat.mul_le_mul (h1 x) (h2 x)
    _ = c1 * c2 * (Yb a x) ^ (d1 + d2) := by rw [pow_add]; ring

theorem PolB.pow {f h : Request × List Bool → ℕ} (hf : PolB a f) (k : ℕ) (e : ∀ x, h x ≤ f x ^ k) : PolB a h := by
  obtain ⟨c, d, h1⟩ := hf
  refine ⟨c ^ k, d * k, fun x => (e x).trans ?_⟩
  calc f x ^ k ≤ (c * (Yb a x) ^ d) ^ k := Nat.pow_le_pow_left (h1 x) k
    _ = c ^ k * (Yb a x) ^ (d * k) := by rw [mul_pow, ← pow_mul]

/-- Linear combination of polynomial terms. -/
theorem PolB.add3 {f g h k : Request × List Bool → ℕ} (hf : PolB a f) (hg : PolB a g) (hh : PolB a h)
    (e : ∀ x, k x ≤ f x + g x + h x) : PolB a k :=
  PolB.add (PolB.add hf hg (fun _ => le_refl _)) hh e

end closure

/-! ## Two small facts (as P's `ColdBudgetPoly`, restated to keep this closure small) -/

theorem nbl_le (n : ℕ) : natBitLength n ≤ n + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 n
  omega

theorem flat_le {q : ℕ} (gs : List (ExactThresholdGate q)) (k : ℕ) :
    ((gs.take k).flatMap exactWord).length ≤ (exactListWord gs).length := by
  have h := congrArg (fun l => (List.flatMap exactWord l).length) (List.take_append_drop k gs)
  simp only [List.flatMap_append, List.length_append] at h
  simp only [exactListWord, List.length_append]
  omega

/-! ## The atoms -/

section atoms
variable (a : DecompositionAlgorithm)

theorem pIn : PolB a (fun x => (x.1.input a).length) := PolB.ofY (fun x => by unfold Yb; omega)
theorem pG : PolB a (fun x => (exactListWord (gsOf a x.1)).length) := PolB.ofY (fun x => by unfold Yb; omega)
theorem pNG : PolB a (fun x => (gsOf a x.1).length) := PolB.ofY (fun x => by unfold Yb; omega)
theorem pMB : PolB a (fun x => x.2.length) := PolB.ofY (fun x => by unfold Yb; omega)
theorem pIn1 : PolB a (fun x => (x.1.input a).length + 1) :=
  PolB.add (pIn a) (PolB.const 1) (fun _ => le_refl _)

/-- Every request word, `q`, `K` and the occurrence count are below the input length. -/
theorem sizes_le (r : Request) :
    r.q ≤ (r.input a).length ∧ r.nativeWord.length ≤ (r.input a).length ∧
    (r.supportWord a).length ≤ (r.input a).length ∧ (r.indexWord a).length ≤ (r.input a).length ∧
    (r.topWord a).length ≤ (r.input a).length ∧ (r.family a).occurrences.length ≤ (r.input a).length ∧
    (maskData a r).supportWord.length ≤ (r.input a).length ∧
    normalizedLiveCount r.q r.liveScale ≤ (r.input a).length := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := SourceBudget.words_le_input a r
  exact ⟨h1, h2, h3, h4, h5, h6, h7, (normalizedLiveCount_le _ _).trans h1⟩

/-- A linear function of the call's sizes. -/
theorem pLin (c : ℕ) (f : Request × List Bool → ℕ) (h : ∀ x, f x ≤ c * ((x.1.input a).length + 1)) : PolB a f :=
  PolB.mono (PolB.mul (PolB.const c) (pIn1 a) (fun _ => le_refl _)) h

end atoms

section stages
variable (a : DecompositionAlgorithm)

/-! ## The stages -/

theorem copiesCost_le (w : Fin 5 → List Bool) (B : ℕ) (h : ∀ i, (w i).length ≤ B) :
    SourceResident.copiesCost w ≤ 28 * B + 34 := by
  have h0 := h (SourceResident.srcIx ⟨0, by omega⟩)
  have h1 := h (SourceResident.srcIx ⟨1, by omega⟩)
  have h2 := h (SourceResident.srcIx ⟨2, by omega⟩)
  have h3 := h (SourceResident.srcIx ⟨3, by omega⟩)
  have h4 := h (SourceResident.srcIx ⟨4, by omega⟩)
  have h5 := h (SourceResident.srcIx ⟨5, by omega⟩)
  have h6 := h (SourceResident.srcIx ⟨6, by omega⟩)
  unfold SourceResident.copiesCost SourceResident.cc
  omega

theorem pCopies : PolB a (fun x => SourceResident.copiesCost (cw a x.1)) :=
  pLin a 34 _ (fun x => by
    obtain ⟨hq, hn, hs, _, ht, _, _, hK⟩ := sizes_le a x.1
    have hw : ∀ i, (cw a x.1 i).length ≤ (x.1.input a).length := by
      intro i
      fin_cases i
      · exact hn
      · exact hs
      · exact ht
      · show (List.replicate x.1.q true).length ≤ _; rw [List.length_replicate]; exact hq
      · show (List.replicate (normalizedLiveCount x.1.q x.1.liveScale) true).length ≤ _
        rw [List.length_replicate]; exact hK
    have := copiesCost_le (cw a x.1) _ hw
    omega)

theorem pOcc : PolB a (fun x => SourceResident.occCost (x.1.supportWord a).length (x.1.family a).occurrences.length) :=
  pLin a 4 _ (fun x => by
    obtain ⟨_, _, hs, _, _, hN, _, _⟩ := sizes_le a x.1
    unfold SourceResident.occCost
    omega)

/-- The seed loader's lead (`prefixFuel`) is linear. -/
theorem pPrefix : PolB a (fun x => SLoad.LeadDriver.prefixFuel a x.1) :=
  pLin a 64 _ (fun x => by
    obtain ⟨hq, _, hs, _, _, hN, _, hK⟩ := sizes_le a x.1
    simp only [SLoad.LeadDriver.prefixFuel, SLoad.RequestLead.prefixFuel, SLoad.Lead.cost]
    omega)

/-- The mask worker's budget. -/
theorem pMask (mask : MaskProducer) : PolB a (fun x => maskBudget mask.coefficient mask.degree (maskData a x.1)) := by
  have hb : PolB a (fun x => (maskData a x.1).q + (maskData a x.1).K + (maskData a x.1).m +
      (maskData a x.1).supportWord.length + 1) :=
    pLin a 5 _ (fun x => by
      obtain ⟨hq, _, _, _, _, hN, hms, hK⟩ := sizes_le a x.1
      show x.1.q + normalizedLiveCount x.1.q x.1.liveScale + (x.1.family a).occurrences.length +
        (maskData a x.1).supportWord.length + 1 ≤ _
      omega)
  exact PolB.mul (PolB.const mask.coefficient) (PolB.pow hb mask.degree (fun _ => le_refl _))
    (fun x => by unfold maskBudget; exact le_refl _)

theorem pLM (mask : MaskProducer) : PolB a (fun x => Item4.lmCost mask a x.1) :=
  PolB.add3 (pPrefix a) (pMask a mask) (pLin a 8 (fun x => 4 * x.1.q + 6) (fun x => by
      obtain ⟨hq, _⟩ := sizes_le a x.1
      omega))
    (fun x => by unfold Item4.lmCost; omega)

theorem pInputPass (mask : MaskProducer) : PolB a (fun x => SourceRequest.InputPass.cost mask a x.1) :=
  PolB.add3 (pPrefix a) (pMask a mask)
    (pLin a 64 (fun x => 2 * SLoad.RequestFrames.cost x.1.q x.1.nativeWord.length (x.1.supportWord a).length
      (x.1.indexWord a).length (x.1.topWord a).length + 4) (fun x => by
        obtain ⟨hq, hn, hs, hi, ht, _⟩ := sizes_le a x.1
        simp only [SLoad.RequestFrames.cost, SLoad.Frames.cost]
        omega))
    (fun x => by unfold SourceRequest.InputPass.cost; omega)

theorem pTK : PolB a (fun x => 2 * (2 * (maskData a x.1).K + 5) + 2) :=
  pLin a 12 _ (fun x => by
    obtain ⟨_, _, _, _, _, _, _, hK⟩ := sizes_le a x.1
    show 2 * (2 * normalizedLiveCount x.1.q x.1.liveScale + 5) + 2 ≤ _
    omega)

theorem pMeta : PolB a (fun x => (4 * x.2.length + 2) + 1 + (4 * (List.replicate x.2.length true).length + 2)) :=
  PolB.mono (PolB.add (PolB.mul (PolB.const 8) (pMB a) (fun _ => le_refl _)) (PolB.const 5) (fun _ => le_refl _))
    (fun x => by rw [List.length_replicate]; omega)

/-- The child-list measure (`BinaryCacheColdMeasure.budget`): quadratic in the child list. -/
theorem pMS : PolB a (fun x => P1Closure.BinaryCacheColdMeasure.budget (gsOf a x.1)) := by
  have hW : PolB a (fun x => natBitLength (gsOf a x.1).length) :=
    PolB.mono (PolB.add (pNG a) (PolB.const 1) (fun _ => le_refl _)) (fun x => nbl_le _)
  have hNW : PolB a (fun x => (gsOf a x.1).length * (8 * natBitLength (gsOf a x.1).length + 10)) :=
    PolB.mul (pNG a) (PolB.add (PolB.mul (PolB.const 8) hW (fun _ => le_refl _)) (PolB.const 10) (fun _ => le_refl _))
      (fun _ => le_refl _)
  have hqN : PolB a (fun x => (6 * x.1.q + 10) * (gsOf a x.1).length) :=
    PolB.mul (pLin a 16 (fun x => 6 * x.1.q + 10) (fun x => by obtain ⟨hq, _⟩ := sizes_le a x.1; omega)) (pNG a)
      (fun _ => le_refl _)
  have hsum := PolB.add (PolB.add (PolB.add (PolB.add hNW hqN (fun _ => le_refl _)) hW (fun _ => le_refl _)) (pNG a)
    (fun _ => le_refl _)) (PolB.add (pG a) (PolB.const 200) (fun _ => le_refl _)) (fun _ => le_refl _)
  refine PolB.mono (PolB.mul (PolB.const 64) hsum (fun _ => le_refl _)) (fun x => ?_)
  have hf := flat_le (gsOf a x.1) (gsOf a x.1).length
  simp only [P1Closure.BinaryCacheColdMeasure.budget, P1Closure.BinaryCacheColdMeasure.rawBudget,
    DecompositionSource.Count.budget, PCPPQueryNatural.budget, MatrixDimensionPrepare.budget,
    DecompositionCachedChild.budget]
  omega

section banks
variable {k : Nat} (SB : Item4.StartBank a k)

/-- The shared pool-entry loop and the cold runtime term of both accepted runs. -/
theorem pLoopCold (hSBs : PolB a (fun x => SB.B x.1 + SB.w x.1 + SB.Pc x.1)) : PolB a (fun x => (x.1.family a).occurrences.length *
      (409600 * (SB.B x.1 + x.1.q + SB.w x.1 + 1) ^ 2 + 4 * SB.B x.1 + 25) +
    Cold.runtimeCoefficient a * (SB.Pc x.1 + 2) ^ Cold.runtimeDegree a) := by
  have hN : PolB a (fun x => (x.1.family a).occurrences.length) :=
    pLin a 1 _ (fun x => by obtain ⟨_, _, _, _, _, hN, _⟩ := sizes_le a x.1; omega)
  have hbase : PolB a (fun x => SB.B x.1 + x.1.q + SB.w x.1 + 1) :=
    PolB.add hSBs (pLin a 2 (fun x => x.1.q + 1) (fun x => by obtain ⟨hq, _⟩ := sizes_le a x.1; omega))
      (fun x => show SB.B x.1 + x.1.q + SB.w x.1 + 1 ≤ (SB.B x.1 + SB.w x.1 + SB.Pc x.1) + (x.1.q + 1) by omega)
  have hsq : PolB a (fun x => 409600 * (SB.B x.1 + x.1.q + SB.w x.1 + 1) ^ 2 + 4 * SB.B x.1 + 25) :=
    PolB.add (PolB.mul (PolB.const 409600) (PolB.pow hbase 2 (fun _ => le_refl _)) (fun _ => le_refl _))
      (PolB.add (PolB.mul (PolB.const 4) hSBs (fun _ => le_refl _)) (PolB.const 25) (fun _ => le_refl _))
      (fun x => by nlinarith)
  have hP : PolB a (fun x => SB.Pc x.1 + 2) :=
    PolB.add hSBs (PolB.const 2) (fun x => show SB.Pc x.1 + 2 ≤ (SB.B x.1 + SB.w x.1 + SB.Pc x.1) + 2 by omega)
  exact PolB.add (PolB.mul hN hsq (fun _ => le_refl _))
    (PolB.mul (PolB.const (Cold.runtimeCoefficient a)) (PolB.pow hP (Cold.runtimeDegree a) (fun _ => le_refl _))
      (fun _ => le_refl _)) (fun _ => le_refl _)

/-- The index block's cost (P's bank + the accepted index run). -/
theorem pIdx (hSBc : PolB a (fun x => SB.cost x.1)) (hSBs : PolB a (fun x => SB.B x.1 + SB.w x.1 + SB.Pc x.1)) :
    PolB a (fun x => Item4.idxCost SB x.1) := by
  have hcap : PolB a (fun x => SourceEnvelope.capacity a (SB.Pc x.1)) :=
    PolB.mul (PolB.const (SourceEnvelope.coefficient a))
      (PolB.pow (PolB.add hSBs (PolB.const 1)
        (fun x => show SB.Pc x.1 + 1 ≤ (SB.B x.1 + SB.w x.1 + SB.Pc x.1) + 1 by omega)) (SourceEnvelope.degree a)
        (fun _ => le_refl _))
      (fun x => by unfold SourceEnvelope.capacity; exact le_refl _)
  have hlin : PolB a (fun x => 2 * PCJ6e421fabe2aa4155_SourceIndexExact.budget
      (counts a (CloseoutRowsUniversal.pool (Packets.live (x.1.family a)) (x.1.family a).occurrences)) +
      4 * (natListWord (counts a (CloseoutRowsUniversal.pool (Packets.live (x.1.family a)) (x.1.family a).occurrences))).length
      + 7) :=
    pLin a 64 _ (fun x => by
      obtain ⟨_, _, _, hi, _, hN, _⟩ := sizes_le a x.1
      have hidx : (x.1.indexWord a).length =
          (natListWord (counts a (CloseoutRowsUniversal.pool (Packets.live (x.1.family a)) (x.1.family a).occurrences))).length :=
        rfl
      have hlen : (counts a (CloseoutRowsUniversal.pool (Packets.live (x.1.family a)) (x.1.family a).occurrences)).length =
          2 * (x.1.family a).occurrences.length := by
        unfold counts; rw [List.length_map, CloseoutRowsUniversal.pool_length]
      have hst : (PCJ6e421fabe2aa4155_SourceNativeList.stream
          (counts a (CloseoutRowsUniversal.pool (Packets.live (x.1.family a)) (x.1.family a).occurrences))).length ≤
          (natListWord (counts a (CloseoutRowsUniversal.pool (Packets.live (x.1.family a)) (x.1.family a).occurrences))).length := by
        unfold natListWord PCJ6e421fabe2aa4155_SourceNativeList.stream
        rw [List.length_append]; omega
      have hnb := nbl_le
        (counts a (CloseoutRowsUniversal.pool (Packets.live (x.1.family a)) (x.1.family a).occurrences)).length
      unfold PCJ6e421fabe2aa4155_SourceIndexExact.budget
      omega)
  refine PolB.add (PolB.add hSBc (PolB.add (pLoopCold a SB hSBs) (PolB.mul (PolB.const 2) hcap (fun _ => le_refl _))
      (fun _ => le_refl _)) (fun _ => le_refl _))
    (PolB.add hlin (PolB.const 16) (fun _ => le_refl _)) (fun x => ?_)
  unfold Item4.idxCost PCJ6e421fabe2aa4155_SourcePoolIndex.budget
  rw [PCJ6e421fabe2aa4155_SourceCacheBudget.loop_eq]
  omega

/-- The pool block's cost (P's bank + the accepted cache run). -/
theorem pPool (hSBc : PolB a (fun x => SB.cost x.1)) (hSBs : PolB a (fun x => SB.B x.1 + SB.w x.1 + SB.Pc x.1)) :
    PolB a (fun x => Item4.poolCost SB x.1) := by
  refine PolB.add hSBc (PolB.add (pLoopCold a SB hSBs) (PolB.const 7) (fun _ => le_refl _)) (fun x => ?_)
  unfold Item4.poolCost
  rw [PCJ6e421fabe2aa4155_SourceCacheBudget.cache_eq]
  omega

theorem wordsCost_polyB (mask : MaskProducer) (hSBc : PolB a (fun x => SB.cost x.1))
    (hSBs : PolB a (fun x => SB.B x.1 + SB.w x.1 + SB.Pc x.1)) :
    PolB a (fun x => Words.wordsCost mask SB x.1 x.2) := by
  have h1 := PolB.add (pCopies a) (pOcc a) (fun _ => le_refl _)
  have h2 := PolB.add h1 (pLM a mask) (fun _ => le_refl _)
  have h3 := PolB.add h2 (pIdx a SB hSBc hSBs) (fun _ => le_refl _)
  have h4 := PolB.add h3 (pInputPass a mask) (fun _ => le_refl _)
  have h5 := PolB.add h4 (pTK a) (fun _ => le_refl _)
  have h6 := PolB.add h5 (pPool a SB hSBc hSBs) (fun _ => le_refl _)
  have h7 := PolB.add h6 (pMS a) (fun _ => le_refl _)
  have h8 := PolB.add h7 (pMeta a) (fun _ => le_refl _)
  refine PolB.add h8 (PolB.const 8) (fun x => ?_)
  unfold Words.wordsCost
  simp only [gsOf]
  omega

theorem wordsCost_poly (mask : MaskProducer) (hSBc : PolB a (fun x => SB.cost x.1))
    (hSBs : PolB a (fun x => SB.B x.1 + SB.w x.1 + SB.Pc x.1)) :
    ∃ wC wE : ℕ, ∀ (r : Request) (MB : List Bool), Words.wordsCost mask SB r MB ≤ wC * (Yb a (r, MB)) ^ wE := by
  obtain ⟨c, d, h⟩ := wordsCost_polyB a SB mask hSBc hSBs
  exact ⟨c, d, fun r MB => h (r, MB)⟩

end banks

end stages

end
end NearCubicWires.SourceFactorSel.WordsCost

