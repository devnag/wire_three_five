import Proof.Packets.SrcStartCircuit
import Proof.Packets.PacketsMetaField

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Rounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.CompilerSemantics
noncomputable section

/-! ## 1. The halting machine as a `Step` -/

theorem stop_step {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (CloseoutRowsOriginalSwitch.stop t) 0 H A H A :=
  ⟨_, rfl, rfl, rfl, le_rfl⟩

/-! ## 2. One round -/

/-- The payload tape's head returns to `0` (tape 1 of the unframer), the cursor (tape 0) keeps its advance. -/
def zSel : Fin 2 → Bool := ![false, true]
def unZ := MaskedReset.machine GeneratedAmplifier.Copy.machine zSel

/-- Round layout (14 tapes): 0 the cursor tape, 1 the stream, 2 the payload, 3 the reset log, 4–13 `circ`'s scratch. -/
def zSlots : Fin 3 → Fin 14 := ![0, 2, 3]
def cSlots (i : Fin 12) : Fin 14 :=
  ⟨if i.val = 0 then 2 else if i.val = 1 then 1 else i.val + 2, by have := i.isLt; split_ifs <;> omega⟩

theorem zSlots_inj : Function.Injective zSlots := by decide
theorem cSlots_inj : Function.Injective cSlots := by decide

/-- **The round machine** (one fixed machine). -/
def roundM := Composition.machine (RecoveryFocus.machine zSlots unZ) (RecoveryFocus.machine cSlots Circuit.circ)

/-- The two-port bank of `n` tapes: the cursor tape, the stream, all else blank. -/
def inT (n : ℕ) (T S : List Bool) : Fin n → List Bool := fun i => if i.val = 0 then T else if i.val = 1 then S else []
def inH (n : ℕ) (p s : ℕ) : Fin n → ℕ := fun i => if i.val = 0 then p else if i.val = 1 then s else 0

def roundCost {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t : List Bool) : ℕ :=
  (2*(2*(segment gs t).length+1)+2)+1+Circuit.circCost gs t

/-- The bottom frames of a list of gates. -/
abbrev bf {q : ℕ} (gs : List (SupportedNormalizedGate q)) : List Bool :=
  gs.flatMap (fun g => frame (CloseoutRowsCircuitBottom.nativeWord g))

theorem z_off (i : Fin 14) (h0 : i.val ≠ 0) (h2 : i.val ≠ 2) (h3 : i.val ≠ 3) : ∀ j, zSlots j ≠ i := by
  intro j hj
  subst hj
  fin_cases j <;> simp_all [zSlots]

theorem c_off (i : Fin 14) (h1 : i.val ≠ 1) (h2 : i.val < 2 ∨ i.val = 3) : ∀ j, cSlots j ≠ i := by
  intro j hj
  have hv := congrArg Fin.val hj
  simp only [cSlots] at hv
  split_ifs at hv <;> omega

def zInH (pre : List Bool) : Fin 3 → ℕ := ![pre.length, 0, 0]
def zInT (T : List Bool) : Fin 3 → List Bool := ![T, [], []]
def zOutH (pre bits : List Bool) : Fin 3 → ℕ := ![pre.length+2*bits.length+1, 0, 0]
def zOutT (T bits : List Bool) (k : ℕ) : Fin 3 → List Bool := ![T, bits, List.replicate k false]

/-- The unframer with the payload head reset. -/
theorem unZ_step (pre bits tail : List Bool) : ∃ k,
    Step unZ (2*(2*bits.length+1)+2) (zInH pre) (zInT (pre++frame bits++tail))
      (zOutH pre bits) (zOutT (pre++frame bits++tail) bits k) := by
  have u := Circuit.unframe_step pre bits tail []
  simp only [List.nil_append, List.length_nil] at u
  obtain ⟨k, m⟩ := NearCubicWires.PacketsGlue.RequestMeta.step_mask0 u zSel
    (by intro i hi; fin_cases i <;> simp_all [zSel])
  refine ⟨k, (m.congr_in ?_ ?_).congr ?_ ?_⟩
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

/-- **One round**: the circuit frame `frame (segment gs t)` under the cursor is consumed; its bottom frames are appended
to the stream. -/
theorem round_step {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t pre tail S : List Bool) :
    ∃ (H : Fin 14 → ℕ) (A : Fin 14 → List Bool),
      Step roundM (roundCost gs t) (inH 14 pre.length S.length) (inT 14 (pre++frame (segment gs t)++tail) S) H A ∧
      A 0 = pre++frame (segment gs t)++tail ∧ H 0 = pre.length+(frame (segment gs t)).length ∧
      A 1 = S++bf gs ∧ H 1 = (S++bf gs).length := by
  obtain ⟨k, m⟩ := unZ_step pre (segment gs t) tail
  have d1 := m.dock zSlots zSlots_inj (inH 14 pre.length S.length) (inT 14 (pre++frame (segment gs t)++tail) S)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  have a10 : install zSlots (inT 14 (pre++frame (segment gs t)++tail) S)
      (zOutT (pre++frame (segment gs t)++tail) (segment gs t) k) 0 = pre++frame (segment gs t)++tail :=
    install_slot zSlots zSlots_inj _ _ 0
  have h10 : dockH zSlots (inH 14 pre.length S.length) (zOutH pre (segment gs t)) 0 =
      pre.length+2*(segment gs t).length+1 := dockH_slot zSlots zSlots_inj _ _ 0
  have a12 : install zSlots (inT 14 (pre++frame (segment gs t)++tail) S)
      (zOutT (pre++frame (segment gs t)++tail) (segment gs t) k) 2 = segment gs t :=
    install_slot zSlots zSlots_inj _ _ 1
  have h12 : dockH zSlots (inH 14 pre.length S.length) (zOutH pre (segment gs t)) 2 = 0 :=
    dockH_slot zSlots zSlots_inj _ _ 1
  have a11 : install zSlots (inT 14 (pre++frame (segment gs t)++tail) S)
      (zOutT (pre++frame (segment gs t)++tail) (segment gs t) k) 1 = S :=
    install_other zSlots _ _ 1 (z_off 1 (by decide) (by decide) (by decide))
  have h11 : dockH zSlots (inH 14 pre.length S.length) (zOutH pre (segment gs t)) 1 = S.length :=
    dockH_other zSlots _ _ 1 (z_off 1 (by decide) (by decide) (by decide))
  have aoff : ∀ i : Fin 14, 4 ≤ i.val → install zSlots (inT 14 (pre++frame (segment gs t)++tail) S)
      (zOutT (pre++frame (segment gs t)++tail) (segment gs t) k) i = [] := by
    intro i hi
    rw [install_other zSlots _ _ i (z_off i (by omega) (by omega) (by omega))]
    simp only [inT]
    rw [if_neg (by omega), if_neg (by omega)]
  have hoff : ∀ i : Fin 14, 4 ≤ i.val → dockH zSlots (inH 14 pre.length S.length) (zOutH pre (segment gs t)) i = 0 := by
    intro i hi
    rw [dockH_other zSlots _ _ i (z_off i (by omega) (by omega) (by omega))]
    simp only [inH]
    rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨Hc, Ac, hc, c0, c1, ch1⟩ := Circuit.circ_step gs t [] S
  have d2 := hc.dock cSlots cSlots_inj (dockH zSlots (inH 14 pre.length S.length) (zOutH pre (segment gs t)))
    (install zSlots (inT 14 (pre++frame (segment gs t)++tail) S) (zOutT (pre++frame (segment gs t)++tail) (segment gs t) k))
    (by
      intro j
      by_cases j0 : j.val = 0
      · have e : cSlots j = 2 := Fin.ext (by simp [cSlots, j0])
        rw [e, h12]; simp [Circuit.inHeads, j0]
      by_cases j1 : j.val = 1
      · have e : cSlots j = 1 := Fin.ext (by simp [cSlots, j1])
        rw [e, h11]; simp [Circuit.inHeads, j1]
      · rw [hoff _ (by simp only [cSlots, j0, j1, if_false]; omega)]; simp [Circuit.inHeads, j1])
    (by
      intro j
      by_cases j0 : j.val = 0
      · have e : cSlots j = 2 := Fin.ext (by simp [cSlots, j0])
        rw [e, a12]; simp [Circuit.inBank, j0]
      by_cases j1 : j.val = 1
      · have e : cSlots j = 1 := Fin.ext (by simp [cSlots, j1])
        rw [e, a11]; simp [Circuit.inBank, j1]
      · rw [aoff _ (by simp only [cSlots, j0, j1, if_false]; omega)]; simp [Circuit.inBank, j0, j1])
  refine ⟨_, _, d1.seq d2, ?_, ?_, ?_, ?_⟩
  · rw [install_other cSlots _ _ 0 (c_off 0 (by decide) (by decide))]
    exact a10
  · rw [dockH_other cSlots _ _ 0 (c_off 0 (by decide) (by decide)), h10, frame_length]
    omega
  · have e : (1 : Fin 14) = cSlots 1 := rfl
    rw [e, install_slot cSlots cSlots_inj]
    exact c1
  · have e : (1 : Fin 14) = cSlots 1 := rfl
    rw [e, dockH_slot cSlots cSlots_inj]
    exact ch1

/-! ## 3. `n` rounds on fresh private tapes -/

def TT : ℕ → ℕ
  | 0 => 2
  | n+1 => TT n + 12

def SS (s : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => s + SS s n

theorem two_le_TT : ∀ n, 2 ≤ TT n
  | 0 => le_rfl
  | n+1 => by have := two_le_TT n; change 2 ≤ TT n + 12; omega

/-- The next round's slots: its cursor and stream are tapes 0 and 1, its private tapes are the 12 new ones. -/
def rSlots (n : ℕ) (i : Fin 14) : Fin (TT n + 12) :=
  ⟨if i.val < 2 then i.val else TT n + (i.val - 2), by have := i.isLt; have := two_le_TT n; split_ifs <;> omega⟩

theorem rSlots_inj (n : ℕ) : Function.Injective (rSlots n) := by
  intro i j h
  have hv := congrArg Fin.val h
  have := two_le_TT n
  simp only [rSlots] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **`n` rounds** (one fixed machine per `n`): the first round, then the remaining `n-1` on the old tapes. -/
def iter {s : ℕ} (R : Machine 14 s) : (n : ℕ) → Machine (TT n) (SS s n)
  | 0 => CloseoutRowsOriginalSwitch.stop 2
  | n+1 => Composition.machine (RecoveryFocus.machine (rSlots n) R) (TapeEmbedding.machine 12 (iter R n))

/-- A circuit payload `segment gs t`, framed. -/
abbrev fr {q : ℕ} (p : List (SupportedNormalizedGate q) × List Bool) : List Bool := frame (segment p.1 p.2)

def iterCost {q : ℕ} : List (List (SupportedNormalizedGate q) × List Bool) → ℕ
  | [] => 0
  | p :: ps => roundCost p.1 p.2+1+iterCost ps

theorem inT_split (n : ℕ) (T S : List Bool) (E : Fin 12 → List Bool) :
    Fin.addCases (motive := fun _ => List Bool) (inT (TT n) T S) E =
      install (rSlots n) (inT (TT n + 12) T S) (fun j => if j.val < 2 then inT 14 T S j else E ⟨j.val - 2, by omega⟩) := by
  have h2 := two_le_TT n
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.addCases_left]
    by_cases hi : i.val < 2
    · have e : Fin.castAdd 12 i = rSlots n ⟨i.val, by omega⟩ := Fin.ext (by simp [rSlots, hi])
      rw [e, install_slot _ (rSlots_inj n)]
      simp only [hi, if_true, inT]
    · rw [install_other _ _ _ _ (by
        intro j hj
        have hv := congrArg Fin.val hj
        simp only [rSlots, Fin.val_castAdd] at hv
        split_ifs at hv <;> omega)]
      simp only [inT, Fin.val_castAdd]
      rfl
  · rw [Fin.addCases_right]
    have e : Fin.natAdd (TT n) i = rSlots n ⟨i.val + 2, by omega⟩ := Fin.ext (by simp [rSlots])
    rw [e, install_slot _ (rSlots_inj n)]
    simp

/-- **`n` rounds**: for consecutive framed payloads after the cursor, the stream receives all their bottom frames. -/
theorem iter_step {q : ℕ} (s : ℕ) (R : Machine 14 s)
    (hR : ∀ (gs : List (SupportedNormalizedGate q)) (t pre tail S : List Bool),
      ∃ (H : Fin 14 → ℕ) (A : Fin 14 → List Bool),
        Step R (roundCost gs t) (inH 14 pre.length S.length) (inT 14 (pre++frame (segment gs t)++tail) S) H A ∧
        A 0 = pre++frame (segment gs t)++tail ∧ H 0 = pre.length+(frame (segment gs t)).length ∧
        A 1 = S++bf gs ∧ H 1 = (S++bf gs).length) :
    ∀ (ps : List (List (SupportedNormalizedGate q) × List Bool)) (pre rest S : List Bool),
      ∃ (H : Fin (TT ps.length) → ℕ) (A : Fin (TT ps.length) → List Bool),
        Step (iter R ps.length) (iterCost ps) (inH _ pre.length S.length)
          (inT _ (pre++(ps.map fr).flatten++rest) S) H A ∧
        A ⟨0, by have := two_le_TT ps.length; omega⟩ = pre++(ps.map fr).flatten++rest ∧
        H ⟨0, by have := two_le_TT ps.length; omega⟩ = pre.length+((ps.map fr).flatten).length ∧
        A ⟨1, by have := two_le_TT ps.length; omega⟩ = S++bf (ps.flatMap Prod.fst) ∧
        H ⟨1, by have := two_le_TT ps.length; omega⟩ = (S++bf (ps.flatMap Prod.fst)).length
  | [], pre, rest, S => by
    refine ⟨_, _, stop_step _ _, ?_, ?_, ?_, ?_⟩ <;> simp [inT, inH]
  | p :: ps, pre, rest, S => by
    have h2 := two_le_TT ps.length
    obtain ⟨H1, A1, s1, a0, h0, a1, h1⟩ := hR p.1 p.2 pre ((ps.map fr).flatten++rest) S
    obtain ⟨H2, A2, s2, b0, g0, b1, g1⟩ := iter_step s R hR ps (pre++fr p) rest (S++bf p.1)
    -- the round, docked at the new tapes
    have d1 := s1.dock (rSlots ps.length) (rSlots_inj ps.length) (inH (TT ps.length + 12) pre.length S.length)
      (inT (TT ps.length + 12) (pre++((p :: ps).map fr).flatten++rest) S)
      (by intro j; simp only [inH, rSlots]; split_ifs <;> omega)
      (by
        intro j
        simp only [inT, rSlots, List.map_cons, List.flatten_cons, List.append_assoc]
        split_ifs <;> first | rfl | omega)
    -- the ambient after the round is the embedded start of the remaining rounds
    have eA : install (rSlots ps.length) (inT (TT ps.length + 12) (pre++((p :: ps).map fr).flatten++rest) S) A1 =
        Fin.addCases (motive := fun _ => List Bool)
          (inT (TT ps.length) (pre++fr p++(ps.map fr).flatten++rest) (S++bf p.1))
          (fun j : Fin 12 => A1 ⟨j.val+2, by omega⟩) := by
      rw [inT_split]
      funext i
      by_cases hi : ∃ j, rSlots ps.length j = i
      · obtain ⟨j, rfl⟩ := hi
        rw [install_slot _ (rSlots_inj _), install_slot _ (rSlots_inj _)]
        by_cases j0 : j.val = 0
        · have e : j = 0 := Fin.ext j0
          subst e
          simp only [inT]
          rw [a0]
          simp [List.append_assoc]
        by_cases j1 : j.val = 1
        · have e : j = 1 := Fin.ext j1
          subst e
          simp only [inT]
          rw [a1]
          simp
        · have hj : ¬ j.val < 2 := by omega
          simp only [hj, if_false]
          congr 1
          apply Fin.ext
          show j.val = j.val - 2 + 2
          omega
      · simp only [not_exists] at hi
        rw [install_other _ _ _ _ hi, install_other _ _ _ _ hi]
        have i0 : i.val ≠ 0 := fun h => hi 0 (Fin.ext (by simp [rSlots, h]))
        have i1 : i.val ≠ 1 := fun h => hi 1 (Fin.ext (by simp [rSlots, h]))
        simp only [inT, i0, i1, if_false]
    have eH : dockH (rSlots ps.length) (inH (TT ps.length + 12) pre.length S.length) H1 =
        Fin.addCases (motive := fun _ => ℕ)
          (inH (TT ps.length) (pre++fr p).length (S++bf p.1).length)
          (fun j : Fin 12 => H1 ⟨j.val+2, by omega⟩) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.addCases_left]
        by_cases hi : i.val < 2
        · have e : Fin.castAdd 12 i = rSlots ps.length ⟨i.val, by omega⟩ := Fin.ext (by simp [rSlots, hi])
          rw [e, dockH_slot _ (rSlots_inj _)]
          by_cases i0 : i.val = 0
          · have e2 : (⟨i.val, by omega⟩ : Fin 14) = 0 := Fin.ext i0
            rw [e2, h0]
            simp only [inH, i0, if_true, List.length_append]
          · have i1 : i.val = 1 := by omega
            have e2 : (⟨i.val, by omega⟩ : Fin 14) = 1 := Fin.ext i1
            rw [e2, h1]
            simp only [inH, i1, show (1:ℕ) ≠ 0 from by omega, if_false, if_true]
        · rw [dockH_other _ _ _ _ (by
            intro j hj
            have hv := congrArg Fin.val hj
            simp only [rSlots, Fin.val_castAdd] at hv
            split_ifs at hv <;> omega)]
          simp only [inH, Fin.val_castAdd]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [Fin.addCases_right]
        have e : Fin.natAdd (TT ps.length) i = rSlots ps.length ⟨i.val + 2, by omega⟩ := Fin.ext (by simp [rSlots])
        rw [e, dockH_slot _ (rSlots_inj _)]
    rw [eA, eH] at d1
    have d2 := s2.embed (fun j : Fin 12 => H1 ⟨j.val+2, by omega⟩) (fun j : Fin 12 => A1 ⟨j.val+2, by omega⟩)
    have whole := d1.seq d2
    refine ⟨_, _, whole, ?_, ?_, ?_, ?_⟩
    · have e : (⟨0, by omega⟩ : Fin (TT ps.length + 12)) = Fin.castAdd 12 ⟨0, by omega⟩ := rfl
      change Fin.addCases (motive := fun _ => List Bool) A2 _ ⟨0, by omega⟩ = _
      rw [e, Fin.addCases_left, b0]
      simp [List.append_assoc]
    · have e : (⟨0, by omega⟩ : Fin (TT ps.length + 12)) = Fin.castAdd 12 ⟨0, by omega⟩ := rfl
      change Fin.addCases (motive := fun _ => ℕ) H2 _ ⟨0, by omega⟩ = _
      rw [e, Fin.addCases_left, g0]
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      omega
    · have e : (⟨1, by omega⟩ : Fin (TT ps.length + 12)) = Fin.castAdd 12 ⟨1, by omega⟩ := rfl
      change Fin.addCases (motive := fun _ => List Bool) A2 _ ⟨1, by omega⟩ = _
      rw [e, Fin.addCases_left, b1]
      simp only [bf, List.flatMap_cons, List.flatMap_append, List.append_assoc]
    · have e : (⟨1, by omega⟩ : Fin (TT ps.length + 12)) = Fin.castAdd 12 ⟨1, by omega⟩ := rfl
      change Fin.addCases (motive := fun _ => ℕ) H2 _ ⟨1, by omega⟩ = _
      rw [e, Fin.addCases_left, g1]
      simp only [bf, List.flatMap_cons, List.flatMap_append, List.append_assoc]

/-- **The rounds at the round machine.** -/
theorem rounds_step {q : ℕ} (ps : List (List (SupportedNormalizedGate q) × List Bool)) (pre rest S : List Bool) :
    ∃ (H : Fin (TT ps.length) → ℕ) (A : Fin (TT ps.length) → List Bool),
      Step (iter roundM ps.length) (iterCost ps) (inH _ pre.length S.length)
        (inT _ (pre++(ps.map fr).flatten++rest) S) H A ∧
      A ⟨0, by have := two_le_TT ps.length; omega⟩ = pre++(ps.map fr).flatten++rest ∧
      H ⟨0, by have := two_le_TT ps.length; omega⟩ = pre.length+((ps.map fr).flatten).length ∧
      A ⟨1, by have := two_le_TT ps.length; omega⟩ = S++bf (ps.flatMap Prod.fst) ∧
      H ⟨1, by have := two_le_TT ps.length; omega⟩ = (S++bf (ps.flatMap Prod.fst)).length :=
  iter_step _ roundM (fun gs t pre tail S => round_step gs t pre tail S) ps pre rest S

end
end NearCubicWires.SourceStart.Rounds
