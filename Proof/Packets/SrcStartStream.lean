import Proof.Packets.SrcStartRounds
import Proof.PCP.PCPPQueryField
import Proof.Circuits.DecompositionCountPosition
import Proof.Hierarchy.HierarchyFixedWord
import Proof.SourceAssembly.PoolDonorCompatible

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Stream
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.CompilerSemantics
open NearCubicWires.SourceStart.Rounds
open NearCubicWires.P1Closure PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. The padding, the tag bit, the payload bounds -/

/-- The absent circuit's payload `segment [] [] = natWord 0 ++ frame []`. -/
def W0 : List Bool := natWord 0 ++ frame []
/-- Four absent-circuit frames. -/
def P4 : List Bool := frame W0 ++ (frame W0 ++ (frame W0 ++ frame W0))

theorem segment_nil (q : ℕ) : segment ([] : List (SupportedNormalizedGate q)) [] = W0 := by
  rw [Circuit.segment_split]
  simp [W0, Circuit.bottoms, CopyFrames.frames]

theorem fr_nil (q : ℕ) : fr (([] : List (SupportedNormalizedGate q)), ([] : List Bool)) = frame W0 := by
  simp only [fr, segment_nil]

theorem bitLength_zero : natBitLength 0 = 1 := by simp [natBitLength]
theorem bitLength_one : natBitLength 1 = 1 := by simp [natBitLength]
theorem bitLength_two : natBitLength 2 = 2 := by
  have h : Nat.log 2 2 = 1 := Nat.log_eq_one_iff'.mpr ⟨le_refl 2, by norm_num⟩
  simp [natBitLength, h]

theorem tag_bit (n : ℕ) (hn : natBitLength n = 1) (tail : List Bool) :
    readTapeBit (natWord n ++ tail) 1 = false := by
  unfold readTapeBit natWord NearCubicWires.WilliamsPublishedForm.framedNatBits
  rw [hn]
  rfl

theorem tag_bit_two (tail : List Bool) : readTapeBit (natWord 2 ++ tail) 1 = true := by
  unfold readTapeBit natWord NearCubicWires.WilliamsPublishedForm.framedNatBits
  rw [bitLength_two]
  rfl

theorem W0_length : W0.length = 4 := by simp [W0, bitLength_zero]
theorem P4_length : P4.length = 36 := by simp [P4, frame_length, W0_length]

theorem frames_cost (bs : List (List Bool)) :
    (CopyFrames.frames bs).length = (bs.map CopyFrames.cost1).sum ∧ bs.length ≤ (bs.map CopyFrames.cost1).sum := by
  induction bs with
  | nil => simp [CopyFrames.frames]
  | cons b bs ih =>
    simp only [CopyFrames.frames_cons, List.length_append, frame_length, List.map_cons, List.sum_cons,
      List.length_cons, CopyFrames.cost1]
    omega

/-- A round costs at most quadratically in its payload. -/
theorem roundCost_le {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t : List Bool) :
    Rounds.roundCost gs t ≤ 64*((segment gs t).length+1)^2 := by
  have hs := Circuit.segment_split gs t
  have hf := frames_cost (Circuit.bottoms gs)
  have hb : (Circuit.bottoms gs).length = gs.length := by simp [Circuit.bottoms]
  have hn := DecompositionSource.natWord_length gs.length
  have hl : natBitLength gs.length ≤ gs.length+1 := Nat.add_le_add_right (Nat.log_le_self 2 gs.length) 1
  unfold Rounds.roundCost Circuit.circCost Circuit.capCost CopyFrames.copyCost PCPPQueryNatural.budget
    MatrixDimensionPrepare.budget
  rw [hs]
  simp only [List.length_append, frame_length] at hn ⊢
  rw [hb] at hf
  generalize hS : (natWord gs.length).length + (2 * t.length + 1) + (CopyFrames.frames (Circuit.bottoms gs)).length = S
  have hnS : gs.length ≤ S := by omega
  have hbS : natBitLength gs.length ≤ S + 1 := by omega
  have h1 : gs.length * (8 * natBitLength gs.length + 10) ≤ S * (8 * (S + 1) + 10) :=
    Nat.mul_le_mul hnS (by omega)
  have h2 : S * (8 * (S + 1) + 10) + 20 * (S + 1) + 40 ≤ 64 * (S + 1) ^ 2 := by nlinarith
  have hsum : ((Circuit.bottoms gs).map CopyFrames.cost1).sum ≤ S := by omega
  nlinarith

/-! ## 2. The front: unframe field 0, append the padding, reset every head -/

def preCore := Composition.machine GeneratedAmplifier.Copy.machine
  (RecoveryFocus.machine (![1] : Fin 1 → Fin 2) (HierarchyFixedWord.raw P4))
def preM := MaskedReset.machine preCore (fun _ => true)
def preCost (nw : List Bool) : ℕ := 2*((2*nw.length+1)+1+P4.length)+2

theorem pre_step (nw : List Bool) : ∃ k,
    Step preM (preCost nw) (fun _ => 0) ![frame nw, [], []] (fun _ => 0)
      ![frame nw, nw ++ P4, List.replicate k false] := by
  have u := Circuit.unframe_step [] nw [] []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at u
  have ap := Circuit.append_step nw P4
  have d := ap.dock (![1] : Fin 1 → Fin 2) (by decide) ![2*nw.length+1, nw.length] ![frame nw, nw]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  have c := u.seq d
  obtain ⟨k, m⟩ := NearCubicWires.PacketsGlue.RequestMeta.step_mask0 c (fun _ => true)
    (by intro i _; fin_cases i <;> rfl)
  have e0 : install (![1] : Fin 1 → Fin 2) ![frame nw, nw] (fun _ => nw ++ P4) 0 = frame nw :=
    install_other _ _ _ 0 (by intro j; fin_cases j; decide)
  have e1 : install (![1] : Fin 1 → Fin 2) ![frame nw, nw] (fun _ => nw ++ P4) 1 = nw ++ P4 :=
    install_slot _ (by decide) _ _ 0
  refine ⟨k, (m.congr_in ?_ ?_).congr ?_ ?_⟩
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · exact e0
    · exact e1
    · rfl

/-! ## 3. Skipping the five header naturals -/

theorem skip_step (pre tail backing : List Bool) (n : Nat) :
    Step (PCPPQueryField.machine false) (2*natBitLength n+3)
      ![pre.length,0,0] ![pre++natWord n++tail,backing,[]]
      ![pre.length+2*natBitLength n+1,0,0]
      ![pre++natWord n++tail,StablePartition.Workspace.overlay (UnaryTemplate.tape (natBitLength n)) backing,[]] := by
  obtain ⟨r,hr,hf,_⟩ := PCPPQueryField.nat_run false pre tail backing [] n
  refine Step.of_run hr ?_ ?_
  · rw [hf]
    rfl
  · rw [hf]
    rfl

abbrev sk := PCPPQueryField.machine false
def sk5 := Composition.machine (Composition.machine (Composition.machine (Composition.machine sk sk) sk) sk) sk

/-- One skip, on a work word `W = (P ++ natWord n) ++ R`, with explicit head positions. -/
theorem skip_at (P R backing W : List Bool) (n h0 h1 : ℕ) (hW : W = P ++ natWord n ++ R) (hh0 : h0 = P.length)
    (hh1 : h1 = h0+2*natBitLength n+1) : ∃ bk : List Bool,
    Step sk (2*natBitLength n+3) ![h0, 0, 0] ![W, backing, []] ![h1, 0, 0] ![W, bk, []] := by
  subst hW hh0 hh1
  exact ⟨_, skip_step P R backing n⟩

def hdr5 (n1 n2 n3 n4 n5 : ℕ) : List Bool := natWord n1 ++ natWord n2 ++ natWord n3 ++ natWord n4 ++ natWord n5
def sk5Cost (n1 n2 n3 n4 n5 : ℕ) : ℕ :=
  (2*natBitLength n1+3)+1+(2*natBitLength n2+3)+1+(2*natBitLength n3+3)+1+(2*natBitLength n4+3)+1+
    (2*natBitLength n5+3)

theorem sk5_step (n1 n2 n3 n4 n5 : ℕ) (tail backing : List Bool) : ∃ bk : List Bool,
    Step sk5 (sk5Cost n1 n2 n3 n4 n5) ![0, 0, 0]
      ![natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++ tail)))), backing, []]
      ![(hdr5 n1 n2 n3 n4 n5).length, 0, 0]
      ![natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++ tail)))), bk, []] := by
  set W := natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++ tail)))) with hWd
  have e1 := DecompositionSource.natWord_length n1
  have e2 := DecompositionSource.natWord_length n2
  have e3 := DecompositionSource.natWord_length n3
  have e4 := DecompositionSource.natWord_length n4
  have e5 := DecompositionSource.natWord_length n5
  have l5 : (hdr5 n1 n2 n3 n4 n5).length = (2*natBitLength n1+1)+(2*natBitLength n2+1)+(2*natBitLength n3+1)+
      (2*natBitLength n4+1)+(2*natBitLength n5+1) := by simp only [hdr5, List.length_append]; omega
  obtain ⟨b1, s1⟩ := skip_at [] (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++ tail)))) backing W n1
    0 (2*natBitLength n1+1) (by simp [hWd]) rfl (by omega)
  obtain ⟨b2, s2⟩ := skip_at (natWord n1) (natWord n3 ++ (natWord n4 ++ (natWord n5 ++ tail))) b1 W n2
    (2*natBitLength n1+1) ((2*natBitLength n1+1)+(2*natBitLength n2+1)) (by simp [hWd, List.append_assoc])
    (by omega) (by omega)
  obtain ⟨b3, s3⟩ := skip_at (natWord n1 ++ natWord n2) (natWord n4 ++ (natWord n5 ++ tail)) b2 W n3
    ((2*natBitLength n1+1)+(2*natBitLength n2+1)) ((2*natBitLength n1+1)+(2*natBitLength n2+1)+(2*natBitLength n3+1))
    (by simp [hWd, List.append_assoc]) (by simp only [List.length_append]; omega) (by omega)
  obtain ⟨b4, s4⟩ := skip_at (natWord n1 ++ natWord n2 ++ natWord n3) (natWord n5 ++ tail) b3 W n4
    ((2*natBitLength n1+1)+(2*natBitLength n2+1)+(2*natBitLength n3+1))
    ((2*natBitLength n1+1)+(2*natBitLength n2+1)+(2*natBitLength n3+1)+(2*natBitLength n4+1))
    (by simp [hWd, List.append_assoc]) (by simp only [List.length_append]; omega) (by omega)
  obtain ⟨b5, s5⟩ := skip_at (natWord n1 ++ natWord n2 ++ natWord n3 ++ natWord n4) tail b4 W n5
    ((2*natBitLength n1+1)+(2*natBitLength n2+1)+(2*natBitLength n3+1)+(2*natBitLength n4+1))
    ((2*natBitLength n1+1)+(2*natBitLength n2+1)+(2*natBitLength n3+1)+(2*natBitLength n4+1)+(2*natBitLength n5+1))
    (by simp [hWd, List.append_assoc]) (by simp only [List.length_append]; omega) (by omega)
  refine ⟨b5, ?_⟩
  rw [l5]
  exact (((s1.seq s2).seq s3).seq s4).seq s5

/-! ## 4. The main branch (52 tapes: 0 work, 1 stream, 2 backing, 3 skip scratch, 4–51 the rounds' private tapes) -/

def mvL := DecompositionCountPosition.move (fun i : Fin 52 => if i.val = 0 then HeadMove.left else HeadMove.stay)
def skSlots : Fin 3 → Fin 52 := ![0, 2, 3]
theorem skSlots_inj : Function.Injective skSlots := by decide

theorem TT4 : TT 4 = 50 := rfl

def rdSlots (j : Fin (TT 4)) : Fin 52 :=
  ⟨if j.val < 2 then j.val else j.val + 2, by have h : j.val < 50 := j.isLt; split_ifs <;> omega⟩
theorem rd_val (j : Fin (TT 4)) : (rdSlots j).val = if j.val < 2 then j.val else j.val + 2 := rfl
theorem rdSlots_inj : Function.Injective rdSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [rdSlots] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def mainM := Composition.machine (Composition.machine mvL (RecoveryFocus.machine skSlots sk5))
  (RecoveryFocus.machine rdSlots (iter roundM 4))

def mInH : Fin 52 → ℕ := fun i => if i.val = 0 then 1 else 0
def mInT (T : List Bool) : Fin 52 → List Bool := fun i => if i.val = 0 then T else []

theorem move_step {t : ℕ} (dirs : Fin t → HeadMove) (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (DecompositionCountPosition.move dirs) 1 H A (fun i => (dirs i).apply (H i)) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run dirs H A
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

def mainCost {q : ℕ} (n1 n2 n3 n4 n5 : ℕ) (ps : List (List (SupportedNormalizedGate q) × List Bool)) : ℕ :=
  1+1+sk5Cost n1 n2 n3 n4 n5+1+iterCost ps

/-- **The main branch**: header skipped, four rounds, the stream on tape 1. -/
theorem main_step {q : ℕ} (n1 n2 n3 n4 n5 : ℕ) (p0 p1 p2 p3 : List (SupportedNormalizedGate q) × List Bool)
    (rest : List Bool) :
    ∃ (H : Fin 52 → ℕ) (A : Fin 52 → List Bool),
      Step mainM (mainCost n1 n2 n3 n4 n5 [p0, p1, p2, p3]) mInH
        (mInT (natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++
          (([p0, p1, p2, p3].map fr).flatten ++ rest))))))) H A ∧
      A 1 = bf ([p0, p1, p2, p3].flatMap Prod.fst) := by
  set T := natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++
    (([p0, p1, p2, p3].map fr).flatten ++ rest))))) with hT
  -- step back to cell 0
  have s1 := move_step (fun i : Fin 52 => if i.val = 0 then HeadMove.left else HeadMove.stay) mInH (mInT T)
  have e1 : (fun i : Fin 52 => ((fun i : Fin 52 => if i.val = 0 then HeadMove.left else HeadMove.stay) i).apply (mInH i)) =
      fun _ => 0 := by
    funext i
    by_cases h : i.val = 0 <;> simp [mInH, h, HeadMove.apply]
  rw [e1] at s1
  -- skip the header
  obtain ⟨bk, s2⟩ := sk5_step n1 n2 n3 n4 n5 (([p0, p1, p2, p3].map fr).flatten ++ rest) []
  have d2 := s2.dock skSlots skSlots_inj (fun _ => 0) (mInT T) (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl)
  -- the rounds
  obtain ⟨H3, A3, s3, -, -, a31, -⟩ := rounds_step [p0, p1, p2, p3] (hdr5 n1 n2 n3 n4 n5) rest []
  have off2 : ∀ i : Fin 52, i.val ≠ 0 → i.val ≠ 2 → i.val ≠ 3 → ∀ j, skSlots j ≠ i := by
    intro i h0 h2 h3 j hj
    subst hj
    fin_cases j <;> simp_all [skSlots]
  have d3 := s3.dock rdSlots rdSlots_inj
    (dockH skSlots (fun _ => 0) ![(hdr5 n1 n2 n3 n4 n5).length, 0, 0])
    (install skSlots (mInT T) ![T, bk, []])
    (by
      intro j
      by_cases j0 : j.val = 0
      · have e : rdSlots j = skSlots 0 := Fin.ext (by rw [rd_val]; simp [skSlots, j0])
        rw [e, dockH_slot _ skSlots_inj]
        simp [inH, j0]
      · have hne : ∀ k, skSlots k ≠ rdSlots j := off2 _ (by rw [rd_val]; split_ifs <;> omega)
          (by rw [rd_val]; split_ifs <;> omega) (by rw [rd_val]; split_ifs <;> omega)
        rw [dockH_other _ _ _ _ hne]
        simp [inH, j0])
    (by
      intro j
      by_cases j0 : j.val = 0
      · have e : rdSlots j = skSlots 0 := Fin.ext (by rw [rd_val]; simp [skSlots, j0])
        rw [e, install_slot _ skSlots_inj]
        simp [inT, j0, hT, hdr5, List.append_assoc]
      · have hne : ∀ k, skSlots k ≠ rdSlots j := off2 _ (by rw [rd_val]; split_ifs <;> omega)
          (by rw [rd_val]; split_ifs <;> omega) (by rw [rd_val]; split_ifs <;> omega)
        rw [install_other _ _ _ _ hne]
        simp only [mInT, inT, j0, if_false]
        have hj : (rdSlots j).val ≠ 0 := by rw [rd_val]; split_ifs <;> omega
        simp [hj])
  refine ⟨_, _, (s1.seq d2).seq d3, ?_⟩
  have e : (1 : Fin 52) = rdSlots ⟨1, by rw [TT4]; omega⟩ := rfl
  rw [e, install_slot _ rdSlots_inj]
  simpa using a31

/-! ## 5. The whole extractor (54 tapes: 0 field, 1 stream, 2 work, 3 front log, 4–53 the main branch's 2–51) -/

def preSlots : Fin 3 → Fin 54 := ![0, 2, 3]
theorem preSlots_inj : Function.Injective preSlots := by decide
def mvR := DecompositionCountPosition.move (fun i : Fin 54 => if i.val = 2 then HeadMove.right else HeadMove.stay)
def mSlots (i : Fin 52) : Fin 54 :=
  ⟨if i.val = 0 then 2 else if i.val = 1 then 1 else i.val + 2, by have := i.isLt; split_ifs <;> omega⟩
theorem m_val (i : Fin 52) : (mSlots i).val = if i.val = 0 then 2 else if i.val = 1 then 1 else i.val + 2 := rfl
theorem mSlots_inj : Function.Injective mSlots := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [mSlots] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **The extractor** (one fixed machine). -/
def xM := Composition.machine (Composition.machine (RecoveryFocus.machine preSlots preM) mvR)
  (CloseoutRowsOriginalSwitch.machine (CloseoutRowsOriginalSwitch.stop 54) (RecoveryFocus.machine mSlots mainM) 2)

def xIn (w : List Bool) : Fin 54 → List Bool := fun i => if i.val = 0 then w else []

/-- The bank after the front and the one-cell step. -/
theorem front_step (nw : List Bool) : ∃ k,
    Step (Composition.machine (RecoveryFocus.machine preSlots preM) mvR) (preCost nw+1+1) (fun _ => 0) (xIn (frame nw))
      (fun i => if i.val = 2 then 1 else 0)
      (install preSlots (xIn (frame nw)) ![frame nw, nw ++ P4, List.replicate k false]) := by
  obtain ⟨k, s⟩ := pre_step nw
  have d := s.dock preSlots preSlots_inj (fun _ => 0) (xIn (frame nw)) (fun _ => rfl)
    (by intro j; fin_cases j <;> rfl)
  have hz : dockH preSlots (fun _ : Fin 54 => 0) (fun _ : Fin 3 => 0) = fun _ => 0 :=
    ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)
  rw [hz] at d
  have m := move_step (fun i : Fin 54 => if i.val = 2 then HeadMove.right else HeadMove.stay) (fun _ => 0)
    (install preSlots (xIn (frame nw)) ![frame nw, nw ++ P4, List.replicate k false])
  refine ⟨k, (d.seq m).congr ?_ rfl⟩
  funext i
  by_cases h : i.val = 2 <;> simp [h, HeadMove.apply]

theorem front_work (nw : List Bool) (k : ℕ) :
    install preSlots (xIn (frame nw)) ![frame nw, nw ++ P4, List.replicate k false] 2 = nw ++ P4 :=
  install_slot preSlots preSlots_inj _ _ 1

theorem front_stream (nw : List Bool) (k : ℕ) :
    install preSlots (xIn (frame nw)) ![frame nw, nw ++ P4, List.replicate k false] 1 = [] :=
  (install_other preSlots _ _ 1 (by intro j; fin_cases j <;> decide)).trans rfl

def xBound (m : ℕ) : ℕ := 400*(m+30)^2

/-- **Terminal-shaped `nativeWord`** (tag bit `true`): the extractor stops, the stream is `[]`. -/
theorem x_stop (nw : List Bool) (hb : readTapeBit (nw ++ P4) 1 = true) :
    ∃ (n : ℕ) (H : Fin 54 → ℕ) (A : Fin 54 → List Bool),
      Step xM n (fun _ => 0) (xIn (frame nw)) H A ∧ A 1 = [] ∧ n ≤ xBound nw.length := by
  obtain ⟨k, f⟩ := front_step nw
  have st := CloseoutRowsOriginalSwitch.true_run (CloseoutRowsOriginalSwitch.stop 54) (RecoveryFocus.machine mSlots mainM)
    (2 : Fin 54) (Rounds.stop_step (fun i : Fin 54 => if i.val = 2 then 1 else 0)
      (install preSlots (xIn (frame nw)) ![frame nw, nw ++ P4, List.replicate k false]))
    (by rw [front_work]; simpa using hb)
  refine ⟨_, _, _, f.seq st, front_stream nw k, ?_⟩
  unfold preCost xBound
  rw [P4_length]
  nlinarith

/-- **Header-and-payload `nativeWord`** (tag bit `false`): the stream is the payloads' bottom frames. -/
theorem x_main {q : ℕ} (n1 n2 n3 n4 n5 : ℕ) (p0 p1 p2 p3 : List (SupportedNormalizedGate q) × List Bool)
    (rest nw : List Bool)
    (hnw : nw ++ P4 = natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++
      (([p0, p1, p2, p3].map fr).flatten ++ rest))))))
    (hb : readTapeBit (nw ++ P4) 1 = false) :
    ∃ (n : ℕ) (H : Fin 54 → ℕ) (A : Fin 54 → List Bool),
      Step xM n (fun _ => 0) (xIn (frame nw)) H A ∧ A 1 = bf ([p0, p1, p2, p3].flatMap Prod.fst) ∧
      n ≤ preCost nw+1+1+1+(mainCost n1 n2 n3 n4 n5 [p0, p1, p2, p3]+2) := by
  obtain ⟨k, f⟩ := front_step nw
  obtain ⟨H, A, s, a1⟩ := main_step n1 n2 n3 n4 n5 p0 p1 p2 p3 rest
  rw [← hnw] at s
  set B := install preSlots (xIn (frame nw)) ![frame nw, nw ++ P4, List.replicate k false] with hB
  have d := s.dock mSlots mSlots_inj (fun i : Fin 54 => if i.val = 2 then 1 else 0) B
    (by
      intro j
      simp only [mSlots, mInH]
      split_ifs <;> first | rfl | omega)
    (by
      intro j
      by_cases j0 : j.val = 0
      · have e : mSlots j = 2 := Fin.ext (by rw [m_val]; simp [j0])
        rw [e, hB, front_work]
        simp [mInT, j0]
      · have hne : ∀ i, preSlots i ≠ mSlots j := by
          intro i hi
          have hv := congrArg Fin.val hi
          fin_cases i <;> simp [preSlots, mSlots] at hv <;> split_ifs at hv <;> omega
        rw [hB, install_other _ _ _ _ hne]
        simp only [mInT, j0, if_false, xIn]
        have hj : (mSlots j).val ≠ 0 := by rw [m_val]; split_ifs <;> omega
        simp [hj])
  have sw := CloseoutRowsOriginalSwitch.false_run (CloseoutRowsOriginalSwitch.stop 54) (RecoveryFocus.machine mSlots mainM)
    (2 : Fin 54) d (by rw [hB, front_work]; simpa using hb)
  refine ⟨_, _, _, f.seq sw, ?_, le_rfl⟩
  have e : (1 : Fin 54) = mSlots 1 := rfl
  rw [e, install_slot _ mSlots_inj]
  exact a1

/-! ## 1. At most four payloads, padded to exactly four -/

theorem pad4 {q : ℕ} (LP : List (List (SupportedNormalizedGate q) × List Bool)) (hL : LP.length ≤ 4) :
    ∃ (p0 p1 p2 p3 : List (SupportedNormalizedGate q) × List Bool) (rest : List Bool),
      (LP.map fr).flatten ++ P4 = ([p0, p1, p2, p3].map fr).flatten ++ rest ∧
      [p0, p1, p2, p3].flatMap Prod.fst = LP.flatMap Prod.fst := by
  have d := fr_nil q
  match LP, hL with
  | [], _ => exact ⟨([], []), ([], []), ([], []), ([], []), [], by simp [P4, d], by simp⟩
  | [x0], _ => exact ⟨x0, ([], []), ([], []), ([], []), frame W0, by simp [P4, d], by simp⟩
  | [x0, x1], _ => exact ⟨x0, x1, ([], []), ([], []), frame W0 ++ frame W0, by simp [P4, d], by simp⟩
  | [x0, x1, x2], _ => exact ⟨x0, x1, x2, ([], []), frame W0 ++ (frame W0 ++ frame W0), by simp [P4, d], by simp⟩
  | [x0, x1, x2, x3], _ => exact ⟨x0, x1, x2, x3, P4, by simp, by simp⟩
  | _ :: _ :: _ :: _ :: _ :: _, h => exact absurd h (by simp)

/-! ## 2. The cost bound of the main branch -/

theorem fr_length {q : ℕ} (p : List (SupportedNormalizedGate q) × List Bool) :
    (fr p).length = 2*(segment p.1 p.2).length+1 := by simp [fr, frame_length]

theorem main_bound {q : ℕ} (n1 n2 n3 n4 n5 : ℕ) (p0 p1 p2 p3 : List (SupportedNormalizedGate q) × List Bool)
    (rest nw : List Bool)
    (hnw : nw ++ P4 = natWord n1 ++ (natWord n2 ++ (natWord n3 ++ (natWord n4 ++ (natWord n5 ++
      (([p0, p1, p2, p3].map fr).flatten ++ rest)))))) :
    preCost nw+1+1+1+(mainCost n1 n2 n3 n4 n5 [p0, p1, p2, p3]+2) ≤ xBound nw.length := by
  have hl := congrArg List.length hnw
  simp only [List.length_append, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    fr_length, P4_length, DecompositionSource.natWord_length] at hl
  have r0 := roundCost_le p0.1 p0.2
  have r1 := roundCost_le p1.1 p1.2
  have r2 := roundCost_le p2.1 p2.2
  have r3 := roundCost_le p3.1 p3.2
  unfold preCost mainCost sk5Cost xBound
  simp only [iterCost, P4_length]
  generalize hS : (2 * (segment p0.1 p0.2).length + 1) + (2 * (segment p1.1 p1.2).length + 1) +
    (2 * (segment p2.1 p2.2).length + 1) + (2 * (segment p3.1 p3.2).length + 1) = S at hl
  have hsq : ((segment p0.1 p0.2).length + 1) ^ 2 + ((segment p1.1 p1.2).length + 1) ^ 2 +
      ((segment p2.1 p2.2).length + 1) ^ 2 + ((segment p3.1 p3.2).length + 1) ^ 2 ≤ (nw.length + 30) ^ 2 := by
    have hle : (segment p0.1 p0.2).length + 1 + ((segment p1.1 p1.2).length + 1) + ((segment p2.1 p2.2).length + 1) +
        ((segment p3.1 p3.2).length + 1) ≤ nw.length + 30 := by omega
    nlinarith
  have hb1 : natBitLength n1 ≤ nw.length + 30 := by omega
  have hb2 : natBitLength n2 ≤ nw.length + 30 := by omega
  have hb3 : natBitLength n3 ≤ nw.length + 30 := by omega
  have hb4 : natBitLength n4 ≤ nw.length + 30 := by omega
  have hb5 : natBitLength n5 ≤ nw.length + 30 := by omega
  nlinarith

/-! ## 3. The extractor on every request -/

theorem flat_map_fr {q : ℕ} {C : Type} (cs : List C) (occF : C → List (SupportedNormalizedGate q)) (topF : C → List Bool) :
    ((cs.map (fun c => (occF c, topF c))).map fr).flatten = cs.flatMap (fun c => frame (segment (occF c) (topF c))) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih, fr]

theorem flat_fst {q : ℕ} {C : Type} (cs : List C) (occF : C → List (SupportedNormalizedGate q)) (topF : C → List Bool) :
    (cs.map (fun c => (occF c, topF c))).flatMap Prod.fst = cs.flatMap occF := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, List.flatMap_cons, ih]

/-- The THR/SYM shape: tag `k ∈ {0,1}`, four header naturals, the circuit payloads. -/
theorem x_mode {q : ℕ} {C : Type} (k qv L tg : ℕ) (hk : natBitLength k = 1) (cs : List C) (h4 : cs.length ≤ 4)
    (occF : C → List (SupportedNormalizedGate q)) (topF : C → List Bool) :
    ∃ (n : ℕ) (H : Fin 54 → ℕ) (A : Fin 54 → List Bool),
      Step xM n (fun _ => 0)
        (xIn (frame (natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
          cs.flatMap (fun c => frame (segment (occF c) (topF c)))))) H A ∧
      A 1 = bf (cs.flatMap occF) ∧
      n ≤ xBound (natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
          cs.flatMap (fun c => frame (segment (occF c) (topF c)))).length := by
  obtain ⟨p0, p1, p2, p3, rest, hp, hf⟩ :=
    pad4 (cs.map (fun c => (occF c, topF c))) (by simp [h4])
  rw [flat_map_fr] at hp
  rw [flat_fst] at hf
  have hnw : (natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
      cs.flatMap (fun c => frame (segment (occF c) (topF c)))) ++ P4 =
      natWord k ++ (natWord qv ++ (natWord L ++ (natWord tg ++ (natWord cs.length ++
        (([p0, p1, p2, p3].map fr).flatten ++ rest))))) := by
    simp only [List.append_assoc, hp]
  have hb : readTapeBit ((natWord k ++ natWord qv ++ natWord L ++ natWord tg ++ natWord cs.length ++
      cs.flatMap (fun c => frame (segment (occF c) (topF c)))) ++ P4) 1 = false := by
    rw [hnw]
    exact tag_bit k hk _
  obtain ⟨n, H, A, s, a1, hn⟩ := x_main k qv L tg cs.length p0 p1 p2 p3 rest _ hnw hb
  exact ⟨n, H, A, s, by rw [a1, hf], hn.trans (main_bound k qv L tg cs.length p0 p1 p2 p3 rest _ hnw)⟩

/-- **The extractor on every request.** -/
theorem x_request (a : DecompositionAlgorithm) (r : Request) :
    ∃ (n : ℕ) (H : Fin 54 → ℕ) (A : Fin 54 → List Bool),
      Step xM n (fun _ => 0) (xIn (frame r.nativeWord)) H A ∧
      A 1 = PoolEntryLoop.stream (r.family a).occurrences ∧ n ≤ xBound r.nativeWord.length := by
  cases r with
  | terminal =>
    obtain ⟨n, H, A, s, a1, hn⟩ := x_stop (natWord 2) (tag_bit_two P4)
    exact ⟨n, H, A, s, a1, hn⟩
  | sym r four L target =>
    obtain ⟨n, H, A, s, a1, hn⟩ := x_mode 0 r.q L target bitLength_zero r.circuits four
      symmetricCircuitOccurrences (fun c => List.ofFn c.top)
    have hw : Request.nativeWord (.sym r four L target) = natWord 0 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => frame (segment (symmetricCircuitOccurrences c) (List.ofFn c.top))) := by
      simp only [Request.nativeWord, Circuit.symWord_segment]
    rw [hw]
    exact ⟨n, H, A, s, a1, hn⟩
  | thr r four L target =>
    obtain ⟨n, H, A, s, a1, hn⟩ := x_mode 1 r.q L target bitLength_one r.circuits four
      thresholdCircuitOccurrences (fun c => thresholdWord (nonStrictAsStrict (retainedTopGate c)))
    have hw : Request.nativeWord (.thr r four L target) = natWord 1 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => frame (segment (thresholdCircuitOccurrences c)
            (thresholdWord (nonStrictAsStrict (retainedTopGate c))))) := by
      simp only [Request.nativeWord, Circuit.thrWord_segment]
    rw [hw]
    exact ⟨n, H, A, s, a1, hn⟩

end
end NearCubicWires.SourceStart.Stream
