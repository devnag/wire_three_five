import Proof.Wire_3_5.Recovery.CertScan
import Proof.Wire_3_5.Transfer.PadCast

/-! # The padded request's node producer (P3:3728-3729, 3761-3763; D1.6, Case 2 of the hybrid)

Realizes the first machine step of "after which each honest proof bit is computed by the deterministic PCPP algorithm"
(P3:3762-3763) for the hybrid slice: the PCPP algorithm runs on `S₂`'s PADDED request, the request of the native
circuit cast to the padded width `q ≥ R` (`unionRequest_pad`: `request a (castCircuit h C)`). Base's request
descriptor (`CloseoutCaseTwo.RequestDescriptor`) frames `PCPPNativeClauseDescriptorConsumer.machine a p …` of the
hierarchy node producer `p`, and the consumer's `descriptor_run` is generic in the producer and in the circuit: it reads
the producer's node stream, output index, size, and WIDTH tape `1^n`. The padded producer is base's producer followed by
a width rewrite `1^R ↦ 1^q` (erase the width tape with driver `1^q`, copy `1^q` onto exactly `q` cells); the cast
circuit has the same node stream, size and output (`castCircuit`, `stream_cast`), so the consumer then writes the
descriptor of the padded request.

Paper quantity: the padded request `request a (castCircuit h c)`; **`widthFix`** / **`widthFix_ready`**,
**`padProducer`**, **`padProducer_forward`** (the producer writes its node stream by forward append), and
**`padProducer_run`**: the padded producer leaves the cast circuit's node stream, output index, size and width `1^q`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## The cast circuit's descriptor data -/

theorem native_cast {R w : ℕ} (h : R ≤ w) (node : BooleanNode R) :
    PCPPRequestNodeSchema.native (castNode h node) = PCPPRequestNodeSchema.native node := by
  cases node <;> rfl

/-- **The cast circuit has the native circuit's node stream.** -/
theorem stream_cast {R w : ℕ} (h : R ≤ w) (c : BooleanCircuit R) :
    (castCircuit h c).nodes.flatMap PCPPRequestNodeSchema.native = c.nodes.flatMap PCPPRequestNodeSchema.native := by
  simp only [castCircuit, List.flatMap_map]
  congr 1
  funext node
  exact native_cast h node

/-! ## The width rewrite `1^R ↦ 1^q` -/

section Fix

def slotsFE : Fin 3 → Fin 6 := ![0, 1, 2]
def slotsFT : Fin 3 → Fin 6 := ![1, 3, 4]
def slotsFC : Fin 3 → Fin 6 := ![3, 0, 5]

/-- **The width rewrite**: erase tape 0 with driver `1^q` (tape 1), then copy `1^q` onto it. -/
noncomputable def widthFix :=
  Composition.machine (RecoveryFocus.machine slotsFE (RecoveryScratchErase.resetMachine 1))
  (Composition.machine (RecoveryFocus.machine slotsFT
    (DimensionTemplate.machine false))
    (RecoveryFocus.machine slotsFC (UWalkUnary.machine false false)))

def widthFixInput (R q : ℕ) : Fin 6 → List Bool :=
  ![List.replicate R true, List.replicate q true, [], [], [], []]

def widthFixCost (q : ℕ) : ℕ := (2 * q + 4) + 1 + ((2 * q + 8) + 1 + (2 * q + 6))

/-- **The width rewrite is ready**: the width tape ends as exactly `1^q`, the driver is kept. -/
theorem widthFix_ready (R q : ℕ) (h : R ≤ q) : ∃ out : Fin 6 → List Bool,
    ClockJoin.ReadyRun widthFix (widthFixCost q) (widthFixInput R q) out ∧
      out 0 = List.replicate q true ∧ out 1 = List.replicate q true := by
  set x := widthFixInput R q with hx
  have he := ready_of_root (RecoveryScratchErase.erase_ready q 0 ![List.replicate R true] (by
    intro i; fin_cases i; simpa using h))
  have h1 := he.focus slotsFE (by decide) x (by intro j; fin_cases j <;> rfl)
  set a1 := install slotsFE x (Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 1 => List.replicate q false)
    (fun _ : Fin 1 => List.replicate q true)) (fun _ : Fin 1 => List.replicate (max 0 (q + 1)) false)) with ha1
  have a1_1 : a1 1 = List.replicate q true := by
    rw [ha1, show (1 : Fin 6) = slotsFE 1 from rfl, install_slot _ (by decide)]; rfl
  have a1_0 : a1 0 = List.replicate q false := by
    rw [ha1, show (0 : Fin 6) = slotsFE 0 from rfl, install_slot _ (by decide)]; rfl
  have a1_hi : ∀ i : Fin 6, 3 ≤ i.val → a1 i = [] := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (intro e; have := congrArg Fin.val e; simp [slotsFE] at this; omega))]
    rcases i with ⟨v, hv⟩; simp only at hi; interval_cases v <;> rfl
  have h2 := (DimensionTemplate.ready false q).focus slotsFT (by decide) a1 (by
    intro j; fin_cases j
    · show a1 1 = _; rw [a1_1]; rfl
    · show a1 3 = _; rw [a1_hi _ (by decide)]; rfl
    · show a1 4 = _; rw [a1_hi _ (by decide)]; rfl)
  set a2 := install slotsFT a1 (DimensionTemplate.output false q) with ha2
  have hc := ready_pad _ _ _ _ ![0, q, 0] (UWalkUnary.ready false false (q + 2) q)
  have h3 := hc.focus slotsFC (by decide) a2 (by
    intro j; fin_cases j
    · show a2 3 = _
      rw [ha2, show (3 : Fin 6) = slotsFT 1 from rfl, install_slot _ (by decide)]
      simp [DimensionTemplate.output, UWalkUnary.input,
        RepairSource.CloseoutCapacity.Power.template_source]
    · show a2 0 = _
      rw [ha2, install_other _ _ _ _ (by decide), a1_0]
      simp [UWalkUnary.input, ZeroPadding.pad]
    · show a2 5 = _; rw [ha2, install_other _ _ _ _ (by decide), a1_hi _ (by decide)]; rfl)
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 h3), ?_, ?_⟩
  · rw [show (0 : Fin 6) = slotsFC 1 from rfl, install_slot _ (by decide)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead, ZeroPadding.pad]
  · rw [install_other _ _ _ _ (by decide), ha2, show (1 : Fin 6) = slotsFT 0 from rfl, install_slot _ (by decide)]
    rfl

end Fix

/-! ## The padded producer -/

noncomputable section Producer
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

/-- The width rewrite's tapes: base's width tape (72), then five extra tapes (the first holds `1^q`). -/
def padSlots (k : ℕ) (j : Fin 6) : Fin (PCPPNativeHierarchyNodes.tapes source k + 5) :=
  if h : j.val = 0 then (PCPPNativeHierarchyNodes.slots source k 72).castAdd 5
  else ⟨PCPPNativeHierarchyNodes.tapes source k + (j.val - 1), by have := j.isLt; omega⟩

theorem padSlots_inj (k : ℕ) : Function.Injective (padSlots source k) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  have h72 := (PCPPNativeHierarchyNodes.slots source k 72).isLt
  unfold padSlots at hv
  split_ifs at hv with ha hb hb <;> simp only [Fin.val_castAdd] at hv
  · exact Fin.ext (by omega)
  · omega
  · omega
  · exact Fin.ext (by omega)

/-- **The padded producer**: base's hierarchy node producer, then the width rewrite `1^R ↦ 1^q`. -/
noncomputable def padProducer (k CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (TapeEmbedding.machine 5 (PCPPNativeHierarchyNodes.machine source k CH Cpad code))
    (RecoveryFocus.machine (padSlots source k) widthFix)

/-- The padded producer's input: base's producer input and `1^q`. -/
def padInput (k : ℕ) (X : Fin (PCPPNativeHierarchyNodes.tapes source k) → List Bool) (q : ℕ) :
    Fin (PCPPNativeHierarchyNodes.tapes source k + 5) → List Bool :=
  Fin.addCases X ![List.replicate q true, [], [], [], []]

/-- The node stream's tape in the padded producer. -/
def padTarget (k : ℕ) : Fin (PCPPNativeHierarchyNodes.tapes source k + 5) :=
  (PCPPNativeHierarchyNodes.slots source k 177).castAdd 5

/-- **The padded producer writes its node stream by forward append.** -/
theorem padProducer_forward (k CH Cpad : ℕ) (code : List Bool) :
    CursorRestore.NoLeft (padProducer source k CH Cpad code) (padTarget source k) := by
  apply CursorRestore.composition_forward
  · exact EquationRowCuts.embedded_forward 5 _ _ (PCPPNativeHierarchyNodes.forward source k CH Cpad code)
  · apply EquationRowCuts.unselected_forward
    intro j
    by_cases hj : j.val = 0
    · have e : padSlots source k j = (PCPPNativeHierarchyNodes.slots source k 72).castAdd 5 := by
        unfold padSlots; rw [dif_pos hj]
      rw [e, padTarget]
      intro heq
      have := PCPPNativeHierarchyNodes.slots_injective source k (Fin.castAdd_injective _ _ heq)
      exact absurd (congrArg Fin.val this) (by decide)
    · intro heq
      have hv := congrArg Fin.val heq
      have h177 := (PCPPNativeHierarchyNodes.slots source k 177).isLt
      simp only [padSlots, dif_neg hj, padTarget, Fin.val_castAdd, Fin.val_mk] at hv
      omega

theorem padSlots_away (k : ℕ) (m : Fin 438) (hm : m ≠ 72) :
    ∀ j, padSlots source k j ≠ (PCPPNativeHierarchyNodes.slots source k m).castAdd 5 := by
  intro j
  by_cases hj : j.val = 0
  · have e : padSlots source k j = (PCPPNativeHierarchyNodes.slots source k 72).castAdd 5 := by
      unfold padSlots; rw [dif_pos hj]
    rw [e]
    intro heq
    exact hm (PCPPNativeHierarchyNodes.slots_injective source k (Fin.castAdd_injective _ _ heq)).symm
  · intro heq
    have hv := congrArg Fin.val heq
    have hm' := (PCPPNativeHierarchyNodes.slots source k m).isLt
    simp only [padSlots, dif_neg hj, Fin.val_castAdd] at hv
    omega

/-- **The padded producer is ready**: from base's producer input and `1^q` (`q ≥ R`) it leaves the node stream of the
cast circuit (head at its end), its output index and size, and the width `1^q`. -/
theorem padProducer_run {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
    (oracle : BooleanCircuit
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q) :
    ∃ result, run (padProducer source k H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle + 1 + widthFixCost q)
      (padInput source k (SourceHandoff.sourceTapes (PCPPNativeInputFields.word (HierarchySourceInput.hierarchyInput H r)
        (PCPPNative.descriptor oracle))) q) = some result ∧
      result.final.tapes (padTarget source k) = (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k H.coefficient
        Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)).nodes.flatMap PCPPRequestNodeSchema.native ∧
      result.final.heads (padTarget source k) = ((castCircuit hq (PCPPNativeHierarchyNodes.circuit source k
        H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)).nodes.flatMap
        PCPPRequestNodeSchema.native).length ∧
      result.final.tapes ((PCPPNativeHierarchyNodes.slots source k 89).castAdd 5) =
        List.replicate (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad
          (VerifierEncoding.code H.verifier) r.2 hpad oracle)).output.val true ∧
      result.final.tapes ((PCPPNativeHierarchyNodes.slots source k 91).castAdd 5) =
        List.replicate (castCircuit hq (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad
          (VerifierEncoding.code H.verifier) r.2 hpad oracle)).size true ∧
      result.final.tapes ((PCPPNativeHierarchyNodes.slots source k 72).castAdd 5) = List.replicate q true := by
  set P := PCPPNativeHierarchyNodes.machine source k H.coefficient Cpad (VerifierEncoding.code H.verifier) with hP
  obtain ⟨res, hres, -, t177, h177, -, t89, -, t91, h72, t72⟩ :=
    PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  set extra : Fin 5 → List Bool := ![List.replicate q true, [], [], [], []] with hextra
  have hE := TapeEmbedding.run_embed P (fun _ : Fin 5 => 0) extra _ _ res hres
  have hcfg : ∀ Y, TapeEmbedding.config (fun _ : Fin 5 => 0) extra (initialConfiguration P Y) =
      initialConfiguration (TapeEmbedding.machine 5 P) (padInput source k Y q) := by
    intro Y
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [TapeEmbedding.config, initialConfiguration]
    · rfl
  rw [hcfg] at hE
  set emb := TapeEmbedding.receipt (fun _ : Fin 5 => 0) extra res with hemb
  -- the width rewrite, docked at the producer's final configuration
  obtain ⟨wo, ⟨wrec, hwrun, hwt, -, -⟩, wo0, -⟩ := widthFix_ready _ q hq
  have hslot : ∀ j : Fin 6, j.val ≠ 0 → padSlots source k j = (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin 5).natAdd
      (PCPPNativeHierarchyNodes.tapes source k) := by
    intro j hj; apply Fin.ext; simp [padSlots, hj]
  have hslot0 : padSlots source k 0 = (PCPPNativeHierarchyNodes.slots source k 72).castAdd 5 := by
    unfold padSlots; rw [dif_pos (show (0 : Fin 6).val = 0 from rfl)]
  obtain ⟨result, hdock, -, -, -, dt, doff⟩ := RecoveryFocus.dock (padSlots source k) (padSlots_inj source k)
    widthFix (widthFixCost q) emb.final.heads emb.final.tapes
    (initialConfiguration widthFix (widthFixInput (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) r.2) q))
    (by
      intro j
      by_cases hj : j.val = 0
      · have : j = 0 := Fin.ext hj
        subst this
        rw [hslot0]
        exact (TapeEmbedding.receipt_heads_old (fun _ : Fin 5 => 0) extra res
          (PCPPNativeHierarchyNodes.slots source k 72)).trans h72
      · rw [hslot j hj]
        exact TapeEmbedding.receipt_heads_new (fun _ : Fin 5 => 0) extra res _)
    (by
      intro j
      by_cases hj : j.val = 0
      · have : j = 0 := Fin.ext hj
        subst this
        rw [hslot0]
        exact (TapeEmbedding.receipt_tapes_old (fun _ : Fin 5 => 0) extra res
          (PCPPNativeHierarchyNodes.slots source k 72)).trans t72
      · rw [hslot j hj]
        refine (TapeEmbedding.receipt_tapes_new (fun _ : Fin 5 => 0) extra res _).trans ?_
        rcases j with ⟨v, hv⟩
        simp only at hj
        interval_cases v <;> first | omega | rfl)
    wrec hwrun
  have hjoin := Composition.run_join (TapeEmbedding.machine 5 P) (RecoveryFocus.machine (padSlots source k) widthFix)
    _ _ _ emb result hE hdock
  refine ⟨_, hjoin, ?_, ?_, ?_, ?_, ?_⟩
  · exact (doff _ (padSlots_away source k 177 (by decide))).2.trans
      ((TapeEmbedding.receipt_tapes_old (fun _ : Fin 5 => 0) extra res _).trans (t177.trans (stream_cast hq _).symm))
  · exact (doff _ (padSlots_away source k 177 (by decide))).1.trans
      ((TapeEmbedding.receipt_heads_old (fun _ : Fin 5 => 0) extra res _).trans
        (h177.trans (congrArg List.length (stream_cast hq _).symm)))
  · exact (doff _ (padSlots_away source k 89 (by decide))).2.trans
      ((TapeEmbedding.receipt_tapes_old (fun _ : Fin 5 => 0) extra res _).trans t89)
  · exact (doff _ (padSlots_away source k 91 (by decide))).2.trans
      ((TapeEmbedding.receipt_tapes_old (fun _ : Fin 5 => 0) extra res _).trans
        (t91.trans (by rw [castCircuit_size])))
  · rw [← hslot0]
    exact (dt 0).trans (congrFun hwt 0 |>.trans wo0)

end Producer

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad
