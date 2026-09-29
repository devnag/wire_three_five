import Proof.Wire_3_5.Primitive.SeedFix.W6B
import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Cost

/-! # W6, part 3: the front end, then the fill

P3:2543-2558: the numbers are read from the circuits' payloads (the top word) and the request. The numbers machine's
inner tapes are its word layout (192 streams, the cell, 80 registers) and, after them, the front end's scratch
(`TF3Cost.topFront3`, `TopFrontPort3`). First the front end runs on the raw tapes (its ports on the streams `sReq`,
`sCnt`, `sPay i`, `sNat i`), then the fill:
* `tfPort`, **`tfMap`** (injective), `fIn` (the raw streams: the request, the counts, the payloads, the native words);
* **`tf_dock`**: the docked front end from the raw inputs (payloads blank) to the raw streams with the payloads and the
  native words, its scratch `J` on the extra tapes, every head `0`;
* **`pre_run`**: the front end, then the fill (`fill6`, embedded): the word state `σF (fIn …) V` at capacity `2V + 2`.

Paper quantity of the main type: the circuits' payloads (the top word's parts) on the layout. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2InPorts tf2OutPorts TF2Ok)

variable (alg : DecompositionAlgorithm)

/-- The front end (`topFront3`). -/
noncomputable abbrev tf : PrimThrW.PortsE.TopFrontPort3 alg := PrimThrW.TF3Cost.topFront3 alg

/-- The layout's tapes. -/
abbrev T0 : ℕ := 191 + 2 + 80

/-- The inner tapes: the layout, then the front end's scratch. -/
noncomputable abbrev TI : ℕ := T0 + (tf alg).x

/-- The front end's ten ports on the layout's streams. -/
def tfPort (p : Fin 10) : Fin 192 :=
  if p.val = 0 then sReq else if p.val = 1 then sCnt else if p.val < 6 then ⟨22 + (p.val - 2), by omega⟩
  else ⟨26 + (p.val - 6), by omega⟩

theorem tfPort_val (p : Fin 10) :
    (tfPort p).val = if p.val = 0 then 0 else if p.val = 1 then 1 else 20 + p.val := by
  unfold tfPort sReq sCnt
  split_ifs <;> simp <;> omega

theorem tfPort_inj : Function.Injective tfPort := by
  intro a b h
  have e := congrArg Fin.val h
  rw [tfPort_val, tfPort_val] at e
  exact Fin.ext (by split_ifs at e <;> omega)

theorem sTape_lt (s : Fin 192) : (sTape (nr := 80) s).val < T0 := by
  have := s.isLt
  rw [sTape_val]; show _ < 191 + 2 + 80; split_ifs <;> omega

/-- The front end's tapes on the inner tapes. -/
noncomputable def tfMap (j : Fin (10 + (tf alg).x)) : Fin (TI alg) :=
  if h : j.val < 10 then Fin.castAdd (tf alg).x (sTape (nr := 80) (tfPort ⟨j.val, h⟩))
  else Fin.natAdd T0 ⟨j.val - 10, by omega⟩

theorem tfMap_inj : Function.Injective (tfMap alg) := by
  intro a b h
  unfold tfMap at h
  split_ifs at h with ha hb hb
  · have e := sTape_inj (Fin.castAdd_injective _ _ h)
    exact Fin.ext (by have := congrArg Fin.val (tfPort_inj e); simpa using this)
  · have e := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at e
    have := sTape_lt (tfPort ⟨a.val, ha⟩)
    unfold T0 at this
    omega
  · have e := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at e
    have := sTape_lt (tfPort ⟨b.val, hb⟩)
    unfold T0 at this
    omega
  · have e := congrArg Fin.val h
    simp only [Fin.val_natAdd] at e
    exact Fin.ext (by omega)

/-- **The raw streams**: the request, the count, `1^{ncar}`, `1^{cap_T}`, the payloads and the native words. -/
def fIn (w : List Bool) (ncar capT V : ℕ) (pay nat : Fin 4 → List Bool) : Fin 192 → List Bool := fun s =>
  if s.val = 0 then frame w else if s.val = 1 then List.replicate V true
  else if s.val = 2 then List.replicate ncar true else if s.val = 3 then List.replicate capT true
  else if h : 22 ≤ s.val ∧ s.val < 26 then pay ⟨s.val - 22, by omega⟩
  else if h : 26 ≤ s.val ∧ s.val < 30 then nat ⟨s.val - 26, by omega⟩ else []

/-- The payloads the front end leaves. -/
def payF {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (i : Fin 4) : List Bool :=
  if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []

/-- The native words the front end leaves. -/
def natF {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (i : Fin 4) : List Bool :=
  if h : i.val < a' then PCJd4d1d9d7d1fa4313_Production.thrWord (Cs ⟨i.val, h⟩) else []

theorem tfPort_out (w : List Bool) (V : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (ncar capT : ℕ) (p : Fin 10) :
    tf2OutPorts alg w V Cs p = fIn w ncar capT V (payF alg Cs) (natF Cs) (tfPort p) := by
  have hv := tfPort_val p
  unfold tf2OutPorts fIn
  fin_cases p <;> simp_all [payF, natF]

theorem tfPort_in (w : List Bool) (V ncar capT : ℕ) (p : Fin 10) :
    tf2InPorts w V p = fIn w ncar capT V (fun _ => []) (fun _ => []) (tfPort p) := by
  have hv := tfPort_val p
  unfold tf2InPorts fIn
  fin_cases p <;> simp_all

theorem fIn_other (w : List Bool) (ncar capT V : ℕ) (pay nat pay' nat' : Fin 4 → List Bool) (s : Fin 192)
    (hs : ∀ p, tfPort p ≠ s) : fIn w ncar capT V pay nat s = fIn w ncar capT V pay' nat' s := by
  have h22 : ¬ (22 ≤ s.val ∧ s.val < 30) := by
    rintro ⟨h1, h2⟩
    exact hs ⟨s.val - 20, by omega⟩ (Fin.ext (by rw [tfPort_val]; simp; split_ifs <;> omega))
  unfold fIn
  split_ifs <;> first | rfl | omega

theorem tfMap_lo (p : Fin 10) : tfMap alg (Fin.castAdd (tf alg).x p) = Fin.castAdd (tf alg).x (sTape (tfPort p)) := by
  unfold tfMap
  rw [dif_pos (by simp)]
  rfl

theorem tfMap_hi (e : Fin (tf alg).x) : tfMap alg (Fin.natAdd 10 e) = Fin.natAdd T0 e := by
  unfold tfMap
  rw [dif_neg (by simp)]
  congr 1
  exact Fin.ext (by simp)

theorem addCases_zero' {m k : ℕ} :
    (Fin.addCases (m := m) (n := k) (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0) : Fin (m + k) → ℕ) =
      fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- **The docked front end.** -/
theorem tf_dock (w : List Bool) (ncar capT V : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (J : Fin (tf alg).x → List Bool) (m : ℕ)
    (h : Step (tf alg).M m (fun _ => 0)
      (Fin.addCases (m := 10) (n := (tf alg).x) (motive := fun _ => List Bool) (tf2InPorts w V) (fun _ => []))
      (fun _ => 0)
      (Fin.addCases (m := 10) (n := (tf alg).x) (motive := fun _ => List Bool) (tf2OutPorts alg w V Cs) J)) :
    Step (RecoveryFocus.machine (tfMap alg) (tf alg).M) m (fun _ => 0)
      (Fin.addCases (rawB (fIn w ncar capT V (fun _ => []) (fun _ => []))) (fun _ => []))
      (fun _ => 0) (Fin.addCases (rawB (fIn w ncar capT V (payF alg Cs) (natF Cs))) J) := by
  have d := h.dock (tfMap alg) (tfMap_inj alg) (fun _ => 0)
    (Fin.addCases (rawB (fIn w ncar capT V (fun _ => []) (fun _ => []))) (fun _ => [])) (fun _ => rfl) (fun j => by
      refine Fin.addCases (fun p => ?_) (fun e => ?_) j
      · rw [tfMap_lo, Fin.addCases_left, Fin.addCases_left, rawB_s, tfPort_in w V ncar capT]
      · rw [tfMap_hi, Fin.addCases_right, Fin.addCases_right])
  have eH : dockH (tfMap alg) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, tfMap alg j = i
    · obtain ⟨j, rfl⟩ := hi; rw [dockH_slot _ (tfMap_inj alg)]
    · exact dockH_other _ _ _ _ (fun j hj => hi ⟨j, hj⟩)
  rw [eH] at d
  convert d using 1
  funext k
  refine Fin.addCases (fun j => ?_) (fun e => ?_) k
  · rw [Fin.addCases_left]
    rcases tape_cases j with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [rawB_s]
      by_cases hs : ∃ p, tfPort p = s
      · obtain ⟨p, rfl⟩ := hs
        rw [← tfMap_lo, install_slot _ (tfMap_inj alg), Fin.addCases_left, tfPort_out alg w V Cs ncar capT]
      · rw [install_other _ _ _ _ (fun j hj => by
          refine Fin.addCases (motive := fun j => tfMap alg j ≠ Fin.castAdd (tf alg).x (sTape s)) (fun p => ?_)
            (fun e => ?_) j hj
          · rw [tfMap_lo]; intro e; exact hs ⟨p, sTape_inj (Fin.castAdd_injective _ _ e)⟩
          · rw [tfMap_hi]; intro e
            have h1 := congrArg Fin.val e
            change T0 + _ = (sTape (nr := 80) s).val at h1
            have := sTape_lt s
            unfold T0 at this h1
            omega), Fin.addCases_left, rawB_s]
        exact fIn_other w ncar capT V _ _ _ _ s (fun p hp => hs ⟨p, hp⟩)
    · rw [rawB_c, install_other _ _ _ _ (fun j hj => by
        refine Fin.addCases (motive := fun j => tfMap alg j ≠ Fin.castAdd (tf alg).x cTape) (fun p => ?_)
          (fun e => ?_) j hj
        · rw [tfMap_lo]; intro e; exact sTape_ne_c _ (Fin.castAdd_injective _ _ e)
        · rw [tfMap_hi]; intro e
          have h1 := congrArg Fin.val e
          change T0 + _ = (cTape (ns := 191) (nr := 80)).val at h1
          rw [cTape_val] at h1
          unfold T0 at h1
          omega), Fin.addCases_left, rawB_c]
    · rw [rawB_r, install_other _ _ _ _ (fun j hj => by
        refine Fin.addCases (motive := fun j => tfMap alg j ≠ Fin.castAdd (tf alg).x (rTape r)) (fun p => ?_)
          (fun e => ?_) j hj
        · rw [tfMap_lo]; intro e; exact sTape_ne_r _ _ (Fin.castAdd_injective _ _ e)
        · rw [tfMap_hi]; intro e
          have h1 := congrArg Fin.val e
          change T0 + _ = (rTape (ns := 191) r).val at h1
          rw [rTape_val] at h1
          have := r.isLt
          unfold T0 at h1
          omega), Fin.addCases_left, rawB_r]
  · rw [Fin.addCases_right, ← tfMap_hi, install_slot _ (tfMap_inj alg), Fin.addCases_right]

/-- The state after the front end and the fill. -/
def σ1 (w : List Bool) (ncar capT V : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) : WL :=
  σF (fIn w ncar capT V (payF alg Cs) (natF Cs)) V

/-- The front end and the fill. -/
noncomputable def preM := Composition.machine (RecoveryFocus.machine (tfMap alg) (tf alg).M)
  (TapeEmbedding.machine (tf alg).x fill6.compile)

/-- **The front end, then the fill.** -/
theorem pre_run (w : List Bool) (ncar capT V : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (J : Fin (tf alg).x → List Bool) (m : ℕ)
    (h : Step (tf alg).M m (fun _ => 0)
      (Fin.addCases (m := 10) (n := (tf alg).x) (motive := fun _ => List Bool) (tf2InPorts w V) (fun _ => []))
      (fun _ => 0)
      (Fin.addCases (m := 10) (n := (tf alg).x) (motive := fun _ => List Bool) (tf2OutPorts alg w V Cs) J)) :
    Step (preM alg) (m + 1 + (11 * V + 20 + 1 + 1)) (fun _ => 0)
      (Fin.addCases (rawB (fIn w ncar capT V (fun _ => []) (fun _ => []))) (fun _ => []))
      (Fin.addCases (wenc (2 * V + 2) (σ1 alg w ncar capT V Cs)).H (fun _ => 0))
      (Fin.addCases (wenc (2 * V + 2) (σ1 alg w ncar capT V Cs)).A J) := by
  have d := tf_dock alg w ncar capT V Cs J m h
  have f := (Exec.step (fill6_exec (fIn w ncar capT V (payF alg Cs) (natF Cs)) V
    (by unfold fIn sCnt; simp) (by unfold fIn sAUX; simp))).embed (fun _ : Fin (tf alg).x => 0) J
  have e0 : (Fin.addCases (m := T0) (n := (tf alg).x) (motive := fun _ => ℕ)
      (⟨fun _ => 0, rawB (fIn w ncar capT V (payF alg Cs) (natF Cs))⟩ : Bank T0).H (fun _ => 0)) = fun _ => 0 :=
    addCases_zero'
  rw [e0] at f
  exact d.seq f

end NearCubicWires.WireExponent3_5.PrimT.W6
