import Proof.Wire_3_5.Stage35.FoldRun
import Proof.Wire_3_5.Recovery.CaseTwoExec

/-!
# The Case-2 execution over a Case-2 source block

Paper v2, §H.6 stage 2 ("In the yes case (Case 2, Hard proof table), prefix self-reduction recovers `Γ*_pf`. Each
honest proof bit is then computed by the deterministic PCPP algorithm") with the XOR power `f^{⊕t(q)}` of §H.5 Case 2
and the length schedule of §H.6 ("For source lengths `N_a = 2^a`, put `m_a = t(q(N_a)) q_0(N_a)`"): from the five cold
words of the recovery's Case-2 port (the block's word `w0`, the framed canonical description of `B*_pf`, the framed
address `x`, `1^R`, `1^B`) one fixed machine
1. turns the canonical description into the descriptor frame (`CloseoutCaseTwo.Cold` converter);
2. recomputes the slice parameters from `x` (this proof's parameter core: the index `S`, the schedule `t`; the widths
   `1^{q(2^S)}` and the block width `1^w`, `w = q + 1 + ⌈D log₂(q+2)⌉`), the copy count `t + 1` as a template word,
   and the bank capacity `1^C` (`CloseoutCapacity`);
3. initializes the fold's bank and runs the uniform fold over `t + 1` blocks of `x` (`Stage35.Fold`);
4. frames the accumulator bit.
This is the earlier hybrid Case-2 execution of this proof with the padded source block replaced by any `SBlock`
(the near-cubic-wires Case-2 source block interface) and its frames by the converter.
-/

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Stage35.Exec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open W3.NearCubicWires.RepairSource.Outer3.Case2
open Stage35.Fold
open NearCubicWires.RecoveryPipeline (padCore)

theorem wtapes_ge9 {a : PointwisePCPPAlgorithm} (S : SBlock a) (D : ℕ) : 9 ≤ S.wtapes D := by
  unfold SBlock.wtapes Occurrence.tapes OccurrenceAddress.tapes OccurrenceBit.tapes
  omega

noncomputable section
variable {a : PointwisePCPPAlgorithm} (S : SBlock a) (k D : ℕ)

/-! ## The layout -/

/-- The parameter core's tapes. -/
abbrev ptD : ℕ := prefixTapes D
/-- The widths' tapes. -/
abbrev pwD : ℕ := CaseTwoParamWidth.pw D
/-- The fold worker's tapes. -/
abbrev twF : ℕ := Fold.tw S D

/-- Block bases: frames `[0,140)`, parameter core `140 + ·`, widths `b2 + ·`, template `b3 + ·`, capacity `b4 + ·`,
fold `b5 + ·`, logs and output `b6 + ·`. -/
abbrev b2 : ℕ := 140 + ptD D
abbrev b3 : ℕ := b2 D + pwD D
abbrev b4 : ℕ := b3 D + 3
abbrev b5 : ℕ := b4 D + 26
abbrev b6 : ℕ := b5 D + twF S D + 3
/-- The machine's tape count. -/
abbrev G : ℕ := b6 S D + 5

theorem ptD_ge : 160 ≤ ptD D := by
  have := scanTapes_eq D; unfold ptD prefixTapes; omega

/-- Every layout equation and bound, for `omega`. -/
theorem layout_all : 160 ≤ ptD D ∧ pwD D = 28 + (26 + 2 * D) + 5 ∧
    twF S D = S.wtapes D + 1 + 1 + 9 ∧ 9 ≤ S.wtapes D ∧
    xt S D = S.wtapes D + 1 + 1 ∧
    b2 D = 140 + ptD D ∧ b3 D = b2 D + pwD D ∧ b4 D = b3 D + 3 ∧ b5 D = b4 D + 26 ∧
    b6 S D = b5 D + twF S D + 3 ∧ G S D = b6 S D + 5 :=
  ⟨ptD_ge D, rfl, rfl, wtapes_ge9 S D, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A position of the machine. -/
def gp (m : ℕ) (h : m < G S D) : Fin (G S D) := ⟨m, h⟩

/-! ## The stages' slots -/

/-- Close a value goal of the layout (needs the layout facts in context). -/
macro "ex_tac" : tactic => `(tactic| (first | omega | (simp only [Fin.val_mk] at * <;> omega)))

def pfSlot (i : Fin 135) : Fin (G S D) := ⟨i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega⟩
def pcSlot (i : Fin (ptD D)) : Fin (G S D) :=
  ⟨if i.val = 0 then 2 else 140 + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
def pwSlot (i : Fin (pwD D)) : Fin (G S D) :=
  ⟨if i.val = 0 then 176 else b2 D + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
def tmpSlot (i : Fin 3) : Fin (G S D) :=
  ⟨if i.val = 0 then 145 else b3 D + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
def capSlot (i : Fin 26) : Fin (G S D) :=
  ⟨if i.val = 0 then 2 else b4 D + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
/-- The fold's tapes: its hierarchy and descriptor ports on the frames (138, 132), its address port on `x` (2), its
driver on the capacity (`b4 + 24`), its counter on the template (`b3 + 1`), everything else in its own block. -/
def fSlot (j : Fin (twF S D + 2 + 1)) : Fin (G S D) :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 132 else if j.val = xt S D then 2
    else if j.val = twF S D then b4 D + 24 else if j.val = twF S D + 2 then b3 D + 1
    else b5 D + j.val, by have := j.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
def copyQSlot (i : Fin 3) : Fin (G S D) :=
  ⟨if i.val = 0 then b2 D + 26 else if i.val = 1 then b5 D + (xt S D + 3) else b6 S D,
    by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
def copyWSlot (i : Fin 3) : Fin (G S D) :=
  ⟨if i.val = 0 then b2 D + (28 + (26 + 2 * D) + 3) else if i.val = 1 then b5 D + (xt S D + 2)
    else b6 S D + 1, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
def accSlot (i : Fin 2) : Fin (G S D) :=
  ⟨if i.val = 0 then b5 D + (S.wtapes D + 1) else b6 S D + 2,
    by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩
def outSlot (i : Fin 3) : Fin (G S D) :=
  ⟨if i.val = 0 then b5 D + (S.wtapes D + 1) else b6 S D + 2 + i.val,
    by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; split_ifs <;> omega⟩

/-- The erase's backing: the fold's scratch, then its offset and width ports. -/
def comb (j : Fin (ks S D + 2)) : Fin (twF S D) :=
  if h : j.val < ks S D then scratch S D ⟨j.val, h⟩
  else ee S D ⟨j.val - ks S D + 1, by have := j.isLt; omega⟩

/-- The erase's slots in the machine. -/
def eraseG (j : Fin (ks S D + 2 + 1 + 1)) : Fin (G S D) :=
  fSlot S D ((eraseSlots (comb S D) j).castAdd 1)

/-- Injectivity of a slot map from its values. -/
theorem inj_of_val {m t : ℕ} (f : Fin m → Fin t) (h : ∀ i j, (f i).val = (f j).val → i.val = j.val) :
    Function.Injective f := fun i j hij => Fin.ext (h i j (congrArg Fin.val hij))

theorem comb_injective : Function.Injective (comb S D) := by
  intro i j h
  have hil := i.isLt
  have hjl := j.isLt
  by_cases hi : i.val < ks S D <;> by_cases hj : j.val < ks S D
  · have h' := h
    simp only [comb, dif_pos hi, dif_pos hj] at h'
    exact Fin.ext (by simpa using congrArg Fin.val (scratch_injective S D h'))
  · exfalso
    have h' := h
    simp only [comb, dif_pos hi, dif_neg hj] at h'
    exact ee_not_scratch' S D _ (by show j.val - ks S D + 1 < 4; omega) ⟨⟨i.val, hi⟩, h'⟩
  · exfalso
    have h' := h
    simp only [comb, dif_neg hi, dif_pos hj] at h'
    exact ee_not_scratch' S D _ (by show i.val - ks S D + 1 < 4; omega) ⟨⟨j.val, hj⟩, h'.symm⟩
  · have h' := congrArg Fin.val h
    simp only [comb, dif_neg hi, dif_neg hj, ee_val] at h'
    exact Fin.ext (by omega)

/-! ## Injectivity -/

theorem pfSlot_inj : Function.Injective (pfSlot S D) :=
  inj_of_val _ (by intro i j h; exact h)
theorem pcSlot_inj : Function.Injective (pcSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [pcSlot] at h; split_ifs at h <;> omega)
theorem pwSlot_inj : Function.Injective (pwSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [pwSlot] at h; split_ifs at h <;> omega)
theorem tmpSlot_inj : Function.Injective (tmpSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [tmpSlot] at h; split_ifs at h <;> omega)
theorem capSlot_inj : Function.Injective (capSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [capSlot] at h; split_ifs at h <;> omega)
theorem fSlot_inj : Function.Injective (fSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [fSlot] at h; split_ifs at h <;> omega)
theorem copyQSlot_inj : Function.Injective (copyQSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [copyQSlot] at h; split_ifs at h <;> omega)
theorem copyWSlot_inj : Function.Injective (copyWSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [copyWSlot] at h; split_ifs at h <;> omega)
theorem accSlot_inj : Function.Injective (accSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [accSlot] at h; split_ifs at h <;> omega)
theorem outSlot_inj : Function.Injective (outSlot S D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [outSlot] at h; split_ifs at h <;> omega)
theorem eraseG_inj : Function.Injective (eraseG S D) := fun _ _ h =>
  eraseSlots_injective _ (comb_injective S D) (Fin.castAdd_injective _ _ (fSlot_inj S D h))

/-! ## The machine -/

section Machine
variable (A u v e1 e2 e3 e4 : ℕ)

/-- The preparation: frames, the parameter core, the widths, the counter template, the bank capacity. -/
def pre :=
  Composition.machine (RecoveryFocus.machine (pfSlot S D) Cold.machine)
  (Composition.machine (RecoveryFocus.machine (pcSlot S D) (CaseTwoParamScan.paramCore k A u v D e1 e2 e3))
  (Composition.machine (RecoveryFocus.machine (pwSlot S D) (CaseTwoParamWidth.paramWidth k A D))
  (Composition.machine (RecoveryFocus.machine (tmpSlot S D)
    (RepairSource.ProjectionNormalization.DimensionTemplate.machine true))
    (RecoveryFocus.machine (capSlot S D) (RepairSource.CloseoutCapacity.machine e4 e4)))))

/-- The fold's bank initialization: `1^q`, the erase, `1^w`, the accumulator. -/
def init :=
  Composition.machine (RecoveryFocus.machine (copyQSlot S D) PCPUnaryCopy.machine)
  (Composition.machine (RecoveryFocus.machine (eraseG S D)
    (RecoveryScratchErase.resetMachine (ks S D + 2)))
  (Composition.machine (RecoveryFocus.machine (copyWSlot S D) PCPUnaryCopy.machine)
    (RecoveryFocus.machine (accSlot S D) (HierarchyFixedWord.machine [false]))))

/-- The fold and the framed output bit. -/
def post :=
  Composition.machine (RecoveryFocus.machine (fSlot S D) (foldMachine S D))
    (RecoveryFocus.machine (outSlot S D) RecoveryCaseOneBooleanOutput.machine)

/-- **The hybrid Case-2 execution.** -/
def htwo := Composition.machine (pre S k D A u v e1 e2 e3 e4)
  (Composition.machine (init S D) (post S D))

/-- The input: base's five cold words (hierarchy, description, address, `1^R`, `1^B`) on the frames' block. -/
def htwoIn (hier desc addr : List Bool) (R B : ℕ) : Fin (G S D) → List Bool := fun i =>
  if h : i.val < 135 then Cold.input hier desc addr R B ⟨i.val, h⟩ else []

end Machine

/-! ## The preparation -/

section Pre
variable (A u v e1 e2 e3 e4 : ℕ)

/-- The preparation's cost. -/
def preCost {R : ℕ} (B : ℕ) (c : BooleanCircuit R) (bits : List Bool) : ℕ :=
  Cold.budget B c + 1 + (CaseTwoParamScan.paramCost k A u v D e1 e2 e3 bits + 1 +
    (CaseTwoParamWidth.pwCost k A D (CertPrefix.prefixS k A u v D bits.length) + 1 +
      ((2 * candT k A u v (CertPrefix.prefixS k A u v D bits.length) ((v - u) ^ 16) (v ^ 16) bits.length + 8) + 1 +
        RepairSource.CloseoutCapacity.budget e4 e4 bits)))

/-- **The preparation is ready**: the frames (hierarchy, descriptor, address), `1^q` and `1^w` at the index
`S = prefixS … n`, the copy count `t + 1` as a template word, the capacity `1^{C}`, and the fold's block still empty. -/
theorem pre_run (hD : 1 ≤ D) {R B : ℕ} (c : BooleanCircuit R) (hc : c.size ≤ B) (w bits : List Bool)
    (hn : bits.length ≤ pcap e1 bits.length)
    (hvals : ∀ a', a' ≤ bits.length → ∀ i, i ≤ bits.length →
      candA0 k A u v a' * ((v - u) ^ 16) ^ i ≤ pcap e1 bits.length ∧
      candB0 v * (v ^ 16) ^ i ≤ pcap e1 bits.length ∧ 1 + i ≤ pcap e1 bits.length)
    (hT : max (pcap e1 bits.length + 1) (max ((v - u) ^ 16 + 1) (v ^ 16 + 1)) ≤ pcap e2 bits.length)
    (hTc : roundCostBound ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length) + 1 ≤ pcap e2 bits.length)
    (hTs : pcap e2 bits.length + 1 + bits.length + bits.length + 1 ≤ pcap e3 bits.length)
    (hTs' : scanRoundBound k A v D bits.length bits.length ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length)
      (pcap e2 bits.length) bits.length + 1 ≤ pcap e3 bits.length) :
    ∃ out : Fin (G S D) → List Bool,
      ClockJoin.ReadyRun (pre S k D A u v e1 e2 e3 e4) (preCost k D A u v e1 e2 e3 e4 B c bits)
        (htwoIn S D w
          (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B c))
          (RepairOrdinary.frame bits) R B) out ∧
      out (gp S D 0 (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega)) = w ∧
      out (gp S D 132 (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega)) =
        RepairOrdinary.frame (PCPPNative.descriptor c) ∧
      out (gp S D 2 (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega)) =
        RepairOrdinary.frame bits ∧
      out (gp S D (b2 D + 26) (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega)) =
        List.replicate (widthAt k A (CertPrefix.prefixS k A u v D bits.length)) true ∧
      out (gp S D (b2 D + (28 + (26 + 2 * D) + 3))
          (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega)) =
        List.replicate (widthAt k A (CertPrefix.prefixS k A u v D bits.length) + 1 +
          CloseoutLanguage.clauseWidth D (widthAt k A (CertPrefix.prefixS k A u v D bits.length))) true ∧
      out (gp S D (b3 D + 1) (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega)) =
        UnaryTemplate.tape
          (candT k A u v (CertPrefix.prefixS k A u v D bits.length) ((v - u) ^ 16) (v ^ 16) bits.length + 1) ∧
      out (gp S D (b4 D + 24) (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all S D; omega)) =
        List.replicate (RepairSource.CloseoutCapacity.capacity e4 e4 bits.length) true ∧
      (∀ p : Fin (G S D), b5 D ≤ p.val → out p = []) := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D
  set Sx := CertPrefix.prefixS k A u v D bits.length with hS
  set t := candT k A u v Sx ((v - u) ^ 16) (v ^ 16) bits.length with ht
  set x := htwoIn S D w
    (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B c)) (RepairOrdinary.frame bits) R B
    with hx
  have x_hi : ∀ p : Fin (G S D), 135 ≤ p.val → x p = [] := by
    intro p hp; rw [hx]; simp only [htwoIn]; rw [dif_neg (by omega)]
  -- the frames: the canonical description of the proof circuit becomes its descriptor frame (tape 132)
  obtain ⟨o1, r1, o1d, o1h, -, o1a⟩ := Cold.converter_run (R := R) c hc w (RepairOrdinary.frame bits)
  have g1 := r1.focus (pfSlot S D) (pfSlot_inj S D) x (by
    intro i; rw [hx]; simp only [htwoIn, pfSlot]; rw [dif_pos i.isLt])
  set a1 := install (pfSlot S D) x o1 with ha1
  have a1_lo : ∀ p : Fin (G S D), (h : p.val < 135) → a1 p = o1 ⟨p.val, h⟩ := by
    intro p h; rw [ha1]; exact install_slot _ (pfSlot_inj S D) x o1 ⟨p.val, h⟩
  have a1_hi : ∀ p : Fin (G S D), 135 ≤ p.val → a1 p = [] := by
    intro p hp
    rw [ha1, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [pfSlot]; omega), x_hi p hp]
  -- the parameter core
  obtain ⟨o2, r2, o20, o22, o236, o25⟩ := CaseTwoParamScan.paramCore_run k A u v D e1 e2 e3 hD bits hn hvals hT hTc hTs hTs'
  have g2 := r2.focus (pcSlot S D) (pcSlot_inj S D) a1 (by
    intro i
    by_cases h0 : i.val = 0
    · rw [a1_lo _ (by simp only [pcSlot, h0, if_true]; omega)]
      simp only [pcSlot, h0, if_true, prefixInput, if_true]
      exact o1a
    · rw [a1_hi _ (by simp only [pcSlot, h0, if_false]; omega)]
      simp only [prefixInput, h0, if_false])
  set a2 := install (pcSlot S D) a1 o2 with ha2
  have a2_off : ∀ p : Fin (G S D), p.val ≠ 2 → (p.val < 141 ∨ 140 + ptD D ≤ p.val) → a2 p = a1 p := by
    intro p h1 h2
    rw [ha2, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [pcSlot]; split_ifs <;> omega)]
  have a2_at : ∀ (m : ℕ) (hm : m < ptD D) (hm0 : m ≠ 0) (p : Fin (G S D)), p.val = 140 + m →
      a2 p = o2 ⟨m, hm⟩ := by
    intro m hm hm0 p hp
    rw [show p = pcSlot S D ⟨m, hm⟩ from Fin.ext (by simp only [pcSlot, Fin.val_mk, if_neg hm0]; omega), ha2,
      install_slot _ (pcSlot_inj S D)]
  have a2_2 : a2 (gp S D 2 (by omega)) = RepairOrdinary.frame bits := by
    rw [show gp S D 2 _ = pcSlot S D ⟨0, by omega⟩ from Fin.ext rfl, ha2,
      install_slot _ (pcSlot_inj S D)]
    exact o20
  -- the widths
  obtain ⟨o3, r3, o30, o326, o3w⟩ := CaseTwoParamWidth.paramWidth_run k A D Sx hD
  have p3 := ready_pad _ _ _ _ (fun i : Fin (pwD D) => if i.val = 0 then pcap e3 bits.length else 0) r3
  have g3 := p3.focus (pwSlot S D) (pwSlot_inj S D) a2 (by
    intro i
    by_cases h0 : i.val = 0
    · rw [show pwSlot S D i = gp S D 176 (by omega) from Fin.ext (by simp [pwSlot, gp, h0] <;> omega),
        a2_at 36 (by omega) (by omega) _ (by simp [gp] <;> omega)]
      simp only [h0, if_true, CaseTwoParamWidth.pwInput]
      exact o236
    · rw [a2_off _ (by simp only [pwSlot, h0, if_false]; omega) (Or.inr (by simp only [pwSlot, h0, if_false]; omega)),
        a1_hi _ (by simp only [pwSlot, h0, if_false]; omega)]
      simp [CaseTwoParamWidth.pwInput, h0])
  set a3 := install (pwSlot S D) a2
    (fun i => ZeroPadding.pad (if i.val = 0 then pcap e3 bits.length else 0) (o3 i)) with ha3
  have a3_off : ∀ p : Fin (G S D), p.val ≠ 176 → (p.val < b2 D + 1 ∨ b3 D ≤ p.val) → a3 p = a2 p := by
    intro p h1 h2
    rw [ha3, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [pwSlot]; split_ifs <;> omega)]
  have a3_at : ∀ (m : ℕ) (hm : m < pwD D) (hm0 : m ≠ 0) (p : Fin (G S D)), p.val = b2 D + m →
      a3 p = o3 ⟨m, hm⟩ := by
    intro m hm hm0 p hp
    rw [show p = pwSlot S D ⟨m, hm⟩ from Fin.ext (by simp only [pwSlot, Fin.val_mk, if_neg hm0]; omega), ha3,
      install_slot _ (pwSlot_inj S D)]
    simp only [Fin.val_mk, if_neg hm0, ZeroPadding.pad_zero]
  -- the copy count's template
  have p4 := ready_pad _ _ _ _ ![pcap e1 bits.length, 0, 0]
    (RepairSource.ProjectionNormalization.DimensionTemplate.ready true t)
  have g4 := p4.focus (tmpSlot S D) (tmpSlot_inj S D) a3 (by
    intro i; fin_cases i
    · show a3 (tmpSlot S D 0) = _
      rw [a3_off _ (by simp [tmpSlot] <;> omega) (Or.inl (by simp [tmpSlot] <;> omega)),
        a2_at 5 (by omega) (by omega) _ (by simp [tmpSlot] <;> omega)]
      simp only [RepairSource.ProjectionNormalization.DimensionTemplate.input]
      exact o25
    · show a3 (tmpSlot S D 1) = _
      rw [a3_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)),
        a2_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)), a1_hi _ (by simp [tmpSlot] <;> omega)]
      rfl
    · show a3 (tmpSlot S D 2) = _
      rw [a3_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)),
        a2_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)), a1_hi _ (by simp [tmpSlot] <;> omega)]
      rfl)
  set a4 := install (tmpSlot S D) a3 (fun i => ZeroPadding.pad (![pcap e1 bits.length, 0, 0] i)
    (RepairSource.ProjectionNormalization.DimensionTemplate.output true t i)) with ha4
  have a4_off : ∀ p : Fin (G S D), p.val ≠ 145 → p.val ≠ b3 D + 1 → p.val ≠ b3 D + 2 → a4 p = a3 p := by
    intro p h1 h2 h3
    rw [ha4, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [tmpSlot] <;> omega)]
  -- the capacity
  obtain ⟨o5, r5, o524, -, o50⟩ := RepairSource.CloseoutCapacity.capacity_run e4 e4 bits
  have g5 := r5.focus (capSlot S D) (capSlot_inj S D) a4 (by
    intro i
    by_cases h0 : i.val = 0
    · rw [a4_off _ (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega),
        a3_off _ (by simp [capSlot, h0] <;> omega) (Or.inl (by simp [capSlot, h0] <;> omega)),
        show capSlot S D i = gp S D 2 (by omega) from Fin.ext (by simp [capSlot, gp, h0] <;> omega), a2_2]
      simp [RepairSource.CloseoutCapacity.input, h0]
    · have hi := i.isLt
      rw [a4_off _ (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega),
        a3_off _ (by simp [capSlot, h0] <;> omega) (Or.inr (by simp [capSlot, h0] <;> omega)),
        a2_off _ (by simp [capSlot, h0] <;> omega) (Or.inr (by simp [capSlot, h0] <;> omega)),
        a1_hi _ (by simp [capSlot, h0] <;> omega)]
      simp [RepairSource.CloseoutCapacity.input, h0])
  set a5 := install (capSlot S D) a4 o5 with ha5
  have a5_off : ∀ p : Fin (G S D), p.val ≠ 2 → (p.val < b4 D + 1 ∨ b4 D + 26 ≤ p.val) → a5 p = a4 p := by
    intro p h1 h2
    rw [ha5, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [capSlot]; split_ifs <;> omega)]
  refine ⟨a5, ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2 (ClockJoin.join _ _ _ _ _ _ _ g3
    (ClockJoin.join _ _ _ _ _ _ _ g4 g5))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a4_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega)
      (by simp [gp] <;> omega), a3_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)),
      a2_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a1_lo _ (by simp [gp] <;> omega)]
    exact o1h
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a4_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega)
      (by simp [gp] <;> omega), a3_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)),
      a2_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a1_lo _ (by simp [gp] <;> omega)]
    exact o1d
  · rw [show gp S D 2 _ = capSlot S D 0 from Fin.ext rfl, ha5, install_slot _ (capSlot_inj S D)]
    exact o50
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a4_off _ (by simp [gp] <;> omega)
      (by simp [gp] <;> omega) (by simp [gp] <;> omega), a3_at 26 (by omega) (by omega) _ (by simp [gp] <;> omega)]
    exact o326
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a4_off _ (by simp [gp] <;> omega)
      (by simp [gp] <;> omega) (by simp [gp] <;> omega), a3_at (28 + (26 + 2 * D) + 3) (by omega) (by omega) _ (by simp [gp] <;> omega)]
    exact o3w
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)),
      show gp S D (b3 D + 1) _ = tmpSlot S D 1 from Fin.ext (by simp [gp, tmpSlot] <;> omega), ha4,
      install_slot _ (tmpSlot_inj S D)]
    simp [RepairSource.ProjectionNormalization.DimensionTemplate.output]
  · rw [show gp S D (b4 D + 24) _ = capSlot S D 24 from Fin.ext (by simp [gp, capSlot] <;> omega), ha5,
      install_slot _ (capSlot_inj S D)]
    exact o524
  · intro p hp
    rw [a5_off _ (by omega) (Or.inr (by omega)), a4_off _ (by omega) (by omega) (by omega),
      a3_off _ (by omega) (Or.inr (by omega)), a2_off _ (by omega) (Or.inr (by omega)), a1_hi _ (by omega)]

end Pre

/-! ## The fold's bank initialization -/

section Init

theorem fSlot_val (j : Fin (twF S D + 2 + 1)) : (fSlot S D j).val =
    if j.val = 0 then 0 else if j.val = 1 then 132 else if j.val = xt S D then 2
    else if j.val = twF S D then b4 D + 24 else if j.val = twF S D + 2 then b3 D + 1
    else b5 D + j.val := rfl

/-- The fold's own positions: every fold tape other than its aliased ports sits at `b5 + j`. -/
theorem fSlot_own (j : Fin (twF S D + 2 + 1)) (h0 : j.val ≠ 0) (h1 : j.val ≠ 1)
    (hx : j.val ≠ xt S D) (hd : j.val ≠ twF S D) (hc : j.val ≠ twF S D + 2) :
    (fSlot S D j).val = b5 D + j.val := by
  rw [fSlot_val, if_neg h0, if_neg h1, if_neg hx, if_neg hd, if_neg hc]

/-- The erase's backing positions are the fold's own. -/
theorem comb_own (i : Fin (ks S D + 2)) :
    (fSlot S D (((comb S D i).castAdd 2).castAdd 1)).val = b5 D + (comb S D i).val := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D
  have hc := (comb S D i).isLt
  have hr : (comb S D i).val = (comb S D i).val := rfl
  apply fSlot_own
  all_goals simp only [Fin.val_castAdd]
  all_goals
    unfold comb
    split_ifs with h
    · have := (scratch_iff S D (scratch S D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
      omega
    · simp only [ee_val, Fin.val_mk]; omega

variable (q w C : ℕ)

/-- The initialization's cost. -/
def initCost : ℕ := (2 * q + 4) + 1 + ((2 * C + 4) + 1 + ((2 * w + 4) + 1 + 4))

/-- **The fold's bank is initialized**: `1^q` on its width port, `0^C` on the offset and every scratch tape, `0^C` then
`1^w` on the block-width port, `0^{C+1}` on the capacity tape, `[false]` on the accumulator; every position below the
fold's block is kept. -/
theorem init_run (X : Fin (G S D) → List Bool)
    (hq : X (gp S D (b2 D + 26) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) = List.replicate q true)
    (hw : X (gp S D (b2 D + (28 + (26 + 2 * D) + 3)) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) = List.replicate w true)
    (hC : X (gp S D (b4 D + 24) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) = List.replicate C true)
    (hfresh : ∀ p : Fin (G S D), b5 D ≤ p.val → X p = []) :
    ∃ Y : Fin (G S D) → List Bool,
      ClockJoin.ReadyRun (init S D) (initCost q w C) X Y ∧
      (∀ p : Fin (G S D), p.val < b5 D → Y p = X p) ∧
      (∀ i : Fin (ks S D), Y (fSlot S D
        (((scratch S D i).castAdd 2).castAdd 1)) = List.replicate C false) ∧
      Y (fSlot S D (((ee S D 1).castAdd 2).castAdd 1)) = List.replicate C false ∧
      Y (fSlot S D (((ee S D 2).castAdd 2).castAdd 1)) = ZeroPadding.pad C (List.replicate w true) ∧
      Y (fSlot S D (((ee S D 3).castAdd 2).castAdd 1)) = List.replicate q true ∧
      Y (fSlot S D (((xe S D (xacc S D)).castAdd 2).castAdd 1)) = [false] ∧
      Y (fSlot S D ⟨twF S D + 1, by omega⟩) = List.replicate (C + 1) false ∧
      (∀ p : Fin (G S D), b6 S D + 3 ≤ p.val → Y p = X p) := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D
  -- `1^q` onto the width port
  have g6 := (ready_of_root (PCPUnaryCopy.copy_ready q 0 0 0)).focus (copyQSlot S D)
    (copyQSlot_inj S D) X (by
      intro j; fin_cases j
      · show X (gp S D (b2 D + 26) _) = _; rw [hq]; simp
      · show X (copyQSlot S D 1) = _; rw [hfresh _ (by simp [copyQSlot] <;> omega)]; rfl
      · show X (copyQSlot S D 2) = _; rw [hfresh _ (by simp [copyQSlot] <;> omega)]; rfl)
  set y1 := install (copyQSlot S D) X ![ZeroPadding.pad 0 (List.replicate q true),
    ZeroPadding.pad 0 (List.replicate q true), List.replicate (max 0 (q + 1)) false] with hy1
  have y1_off : ∀ p : Fin (G S D), p.val ≠ b2 D + 26 → p.val ≠ b5 D + (xt S D + 3) →
      p.val ≠ b6 S D → y1 p = X p := by
    intro p h1 h2 h3
    rw [hy1, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [copyQSlot] <;> omega)]
  -- the erase
  have g7 := (ready_of_root (RecoveryScratchErase.erase_ready C 0 (fun _ : Fin (ks S D + 2) => [])
    (by intro i; simp))).focus (eraseG S D) (eraseG_inj S D) y1 (by
      intro j
      refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
      · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
        · simp only [Fin.addCases_left]
          rw [show eraseG S D (Fin.castAdd 1 (Fin.castAdd 1 i)) =
              fSlot S D (((comb S D i).castAdd 2).castAdd 1) by
                unfold eraseG; rw [eraseSlots_scratch]]
          have hv := comb_own S D i
          have hc := (comb S D i).isLt
          rw [y1_off _ (by omega) (by
                have := comb_own S D i
                unfold comb at this ⊢
                split_ifs at this ⊢ with h
                · have := (scratch_iff S D (scratch S D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
                  omega
                · simp only [ee_val, Fin.val_mk] at this ⊢; omega) (by omega),
            hfresh _ (by omega)]
        · have hl : l' = 0 := Subsingleton.elim _ _
          subst hl
          simp only [Fin.addCases_left, Fin.addCases_right]
          rw [show eraseG S D (Fin.castAdd 1 (Fin.natAdd (ks S D + 2) (0 : Fin 1))) =
              gp S D (b4 D + 24) (by omega) by
                apply Fin.ext; unfold eraseG; rw [eraseSlots_driver, fSlot_val]
                simp only [Fin.val_castAdd, Fin.val_natAdd]
                rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; rfl,
            y1_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega) (by simp [gp] <;> omega), hC]
      · have hl : l = 0 := Subsingleton.elim _ _
        subst hl
        simp only [Fin.addCases_right]
        rw [show eraseG S D (Fin.natAdd (ks S D + 2 + 1) (0 : Fin 1)) =
            gp S D (b5 D + (twF S D + 1)) (by omega) by
              apply Fin.ext; unfold eraseG; rw [eraseSlots_capacity, fSlot_val]
              simp only [Fin.val_castAdd, Fin.val_natAdd]
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
              rfl,
          y1_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega) (by simp [gp] <;> omega),
          hfresh _ (by simp [gp] <;> omega)]
        rfl)
  set eo : Fin (ks S D + 2 + 1 + 1) → List Bool :=
    Fin.addCases (Fin.addCases (fun _ : Fin (ks S D + 2) => List.replicate C false)
      (fun _ : Fin 1 => List.replicate C true)) (fun _ : Fin 1 => List.replicate (max 0 (C + 1)) false) with heo
  set y2 := install (eraseG S D) y1 eo with hy2
  have y2_comb : ∀ i : Fin (ks S D + 2),
      y2 (fSlot S D (((comb S D i).castAdd 2).castAdd 1)) = List.replicate C false := by
    intro i
    rw [show fSlot S D (((comb S D i).castAdd 2).castAdd 1) =
        eraseG S D (Fin.castAdd 1 (Fin.castAdd 1 i)) by unfold eraseG; rw [eraseSlots_scratch],
      hy2, install_slot _ (eraseG_inj S D)]
    simp [heo]
  have y2_cap : y2 (fSlot S D ⟨twF S D + 1, by omega⟩) = List.replicate (C + 1) false := by
    rw [show fSlot S D ⟨twF S D + 1, by omega⟩ =
        eraseG S D (Fin.natAdd (ks S D + 2 + 1) (0 : Fin 1)) by
          unfold eraseG; rw [eraseSlots_capacity]; rfl,
      hy2, install_slot _ (eraseG_inj S D)]
    simp [heo]
  have y2_drv : y2 (gp S D (b4 D + 24) (by omega)) = List.replicate C true := by
    rw [show gp S D (b4 D + 24) (by omega) =
        eraseG S D (Fin.castAdd 1 (Fin.natAdd (ks S D + 2) (0 : Fin 1))) by
          apply Fin.ext; unfold eraseG; rw [eraseSlots_driver, fSlot_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; rfl,
      hy2, install_slot _ (eraseG_inj S D)]
    simp [heo]
  have y2_off : ∀ p : Fin (G S D), p.val < b5 D → p.val ≠ b4 D + 24 → y2 p = y1 p := by
    intro p h1 h2
    rw [hy2, install_off_val _ _ _ _ (by
      intro j
      refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
      · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
        · unfold eraseG; rw [eraseSlots_scratch, comb_own]; omega
        · have hl : l' = 0 := Subsingleton.elim _ _
          subst hl
          unfold eraseG; rw [eraseSlots_driver, fSlot_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; omega
      · have hl : l = 0 := Subsingleton.elim _ _
        subst hl
        unfold eraseG; rw [eraseSlots_capacity, fSlot_val]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        simp <;> omega)]
  -- `1^w` onto the block-width port
  have hE2 : fSlot S D (((ee S D 2).castAdd 2).castAdd 1) =
      fSlot S D (((comb S D ⟨ks S D + 1, by omega⟩).castAdd 2).castAdd 1) := by
    congr 3; unfold comb; rw [dif_neg (by simp)]; apply Fin.ext; simp [ee_val]
  have hE2v : (fSlot S D (((ee S D 2).castAdd 2).castAdd 1)).val = b5 D + (xt S D + 2) := by
    rw [hE2, comb_own]; unfold comb; rw [dif_neg (by simp)]; simp [ee_val]
  have g8 := (ready_of_root (PCPUnaryCopy.copy_ready w 0 C 0)).focus (copyWSlot S D)
    (copyWSlot_inj S D) y2 (by
      intro j; fin_cases j
      · show y2 (gp S D (b2 D + (28 + (26 + 2 * D) + 3)) _) = _
        rw [y2_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega),
          y1_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega) (by simp [gp] <;> omega), hw]
        simp
      · show y2 (copyWSlot S D 1) = _
        rw [show copyWSlot S D 1 = fSlot S D (((ee S D 2).castAdd 2).castAdd 1) from
          Fin.ext (by rw [hE2v]; simp [copyWSlot]), hE2, y2_comb]
        rfl
      · show y2 (copyWSlot S D 2) = _
        rw [hy2, install_off_val _ _ _ _ (by
            intro j
            refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
            · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
              · unfold eraseG; rw [eraseSlots_scratch, comb_own]; simp [copyWSlot]
                have := (comb S D i).isLt; omega
              · have hl : l' = 0 := Subsingleton.elim _ _
                subst hl
                unfold eraseG; rw [eraseSlots_driver, fSlot_val]
                simp only [Fin.val_castAdd, Fin.val_natAdd]
                rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; simp [copyWSlot]; omega
            · have hl : l = 0 := Subsingleton.elim _ _
              subst hl
              unfold eraseG; rw [eraseSlots_capacity, fSlot_val]
              simp only [Fin.val_castAdd, Fin.val_natAdd]
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
              simp [copyWSlot]; omega),
          y1_off _ (by simp [copyWSlot] <;> omega) (by simp [copyWSlot] <;> omega) (by simp [copyWSlot] <;> omega),
          hfresh _ (by simp [copyWSlot] <;> omega)]
        rfl)
  set y3 := install (copyWSlot S D) y2 ![ZeroPadding.pad 0 (List.replicate w true),
    ZeroPadding.pad C (List.replicate w true), List.replicate (max 0 (w + 1)) false] with hy3
  have y3_off : ∀ p : Fin (G S D), p.val ≠ b2 D + (28 + (26 + 2 * D) + 3) →
      p.val ≠ b5 D + (xt S D + 2) → p.val ≠ b6 S D + 1 → y3 p = y2 p := by
    intro p h1 h2 h3
    rw [hy3, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [copyWSlot] <;> omega)]
  -- the accumulator `[false]`
  have hacc_own : (fSlot S D (((xe S D (xacc S D)).castAdd 2).castAdd 1)).val =
      b5 D + (S.wtapes D + 1) := by
    rw [fSlot_own _ _ _ (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes]) (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega) (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega)
      (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega) (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega)]
    simp [xe, xacc, SBlock.accumulator, SBlock.xtapes]
  have y2_acc : ∀ p : Fin (G S D), (p.val = b5 D + (S.wtapes D + 1) ∨ p.val = b6 S D + 2) →
      y2 p = [] := by
    intro p hp
    rw [hy2, install_off_val _ _ _ _ (by
        intro j
        refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
        · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
          · unfold eraseG; rw [eraseSlots_scratch, comb_own]
            unfold comb
            split_ifs with h
            · have := (scratch_iff S D (scratch S D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
              omega
            · simp only [ee_val, Fin.val_mk]; have := i.isLt; omega
          · have hl : l' = 0 := Subsingleton.elim _ _
            subst hl
            unfold eraseG; rw [eraseSlots_driver, fSlot_val]
            simp only [Fin.val_castAdd, Fin.val_natAdd]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; omega
        · have hl : l = 0 := Subsingleton.elim _ _
          subst hl
          unfold eraseG; rw [eraseSlots_capacity, fSlot_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp <;> omega),
      y1_off _ (by omega) (by omega) (by omega), hfresh _ (by omega)]
  have g9 := (UWalkNumbers.fixed_ready [false]).focus (accSlot S D) (accSlot_inj S D) y3 (by
    intro j; fin_cases j
    · show y3 (accSlot S D 0) = []
      rw [y3_off _ (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega),
        y2_acc _ (Or.inl (by simp [accSlot]))]
    · show y3 (accSlot S D 1) = []
      rw [y3_off _ (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega),
        y2_acc _ (Or.inr (by simp [accSlot]))])
  set y4 := install (accSlot S D) y3 ![[false], List.replicate [false].length false] with hy4
  have y4_off : ∀ p : Fin (G S D), p.val ≠ b5 D + (S.wtapes D + 1) → p.val ≠ b6 S D + 2 →
      y4 p = y3 p := by
    intro p h1 h2
    rw [hy4, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [accSlot] <;> omega)]
  have hE1 : fSlot S D (((ee S D 1).castAdd 2).castAdd 1) =
      fSlot S D (((comb S D ⟨ks S D, by omega⟩).castAdd 2).castAdd 1) := by
    congr 3; unfold comb; rw [dif_neg (by simp)]; apply Fin.ext; simp [ee_val]
  have hE1v : (fSlot S D (((ee S D 1).castAdd 2).castAdd 1)).val = b5 D + (xt S D + 1) := by
    rw [hE1, comb_own]; unfold comb; rw [dif_neg (by simp)]; simp [ee_val]
  have hE3v : (fSlot S D (((ee S D 3).castAdd 2).castAdd 1)).val = b5 D + (xt S D + 3) := by
    rw [fSlot_own _ _ _ (by simp [ee_val]) (by simp [ee_val]) (by simp [ee_val]) (by simp [ee_val] <;> omega)
      (by simp [ee_val] <;> omega)]
    simp [ee_val]
  refine ⟨y4, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g6 (ClockJoin.join _ _ _ _ _ _ _ g7
    (ClockJoin.join _ _ _ _ _ _ _ g8 g9))) (by simp [initCost]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [y4_off _ (by omega) (by omega)]
    by_cases hw1 : p.val = b2 D + (28 + (26 + 2 * D) + 3)
    · rw [show p = copyWSlot S D 0 from Fin.ext (by simp [copyWSlot]; omega), hy3,
        install_slot _ (copyWSlot_inj S D),
        show copyWSlot S D 0 = gp S D (b2 D + (28 + (26 + 2 * D) + 3)) (by omega) from
          Fin.ext (by simp [copyWSlot, gp]), hw]
      simp
    rw [y3_off _ hw1 (by omega) (by omega)]
    by_cases hd : p.val = b4 D + 24
    · rw [show p = gp S D (b4 D + 24) (by omega) from Fin.ext (by simp [gp]; omega), y2_drv, hC]
    rw [y2_off _ hp hd]
    by_cases hq1 : p.val = b2 D + 26
    · rw [show p = copyQSlot S D 0 from Fin.ext (by simp [copyQSlot]; omega), hy1,
        install_slot _ (copyQSlot_inj S D),
        show copyQSlot S D 0 = gp S D (b2 D + 26) (by omega) from Fin.ext (by simp [copyQSlot, gp]), hq]
      simp
    rw [y1_off _ hq1 (by omega) (by omega)]
  · intro i
    have hcomb : scratch S D i = comb S D ⟨i.val, by omega⟩ := by
      unfold comb; rw [dif_pos i.isLt]
    have hs := (scratch_iff S D (scratch S D i)).1 ⟨_, rfl⟩
    rw [hcomb] at hs ⊢
    have hv := comb_own S D ⟨i.val, by omega⟩
    have hcl := (comb S D ⟨i.val, by omega⟩).isLt
    rw [y4_off _ (by omega) (by omega), y3_off _ (by omega) (by omega) (by omega), y2_comb]
  · rw [y4_off _ (by rw [hE1v]; omega) (by rw [hE1v]; omega), y3_off _ (by rw [hE1v]; omega) (by rw [hE1v]; omega)
      (by rw [hE1v]; omega), hE1, y2_comb]
  · rw [y4_off _ (by rw [hE2v]; omega) (by rw [hE2v]; omega),
      show fSlot S D (((ee S D 2).castAdd 2).castAdd 1) = copyWSlot S D 1 from
        Fin.ext (by rw [hE2v]; simp [copyWSlot]), hy3, install_slot _ (copyWSlot_inj S D)]
    rfl
  · rw [y4_off _ (by rw [hE3v]; omega) (by rw [hE3v]; omega), y3_off _ (by rw [hE3v]; omega) (by rw [hE3v]; omega)
      (by rw [hE3v]; omega)]
    rw [hy2, install_off_val _ _ _ _ (by
        intro j
        rw [hE3v]
        refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
        · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
          · unfold eraseG; rw [eraseSlots_scratch, comb_own]
            unfold comb
            split_ifs with h
            · have := (scratch_iff S D (scratch S D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
              omega
            · simp only [ee_val, Fin.val_mk]; have := i.isLt; omega
          · have hl : l' = 0 := Subsingleton.elim _ _
            subst hl
            unfold eraseG; rw [eraseSlots_driver, fSlot_val]
            simp only [Fin.val_castAdd, Fin.val_natAdd]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; omega
        · have hl : l = 0 := Subsingleton.elim _ _
          subst hl
          unfold eraseG; rw [eraseSlots_capacity, fSlot_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp <;> omega),
      show fSlot S D (((ee S D 3).castAdd 2).castAdd 1) = copyQSlot S D 1 from
        Fin.ext (by rw [hE3v]; simp [copyQSlot]), hy1, install_slot _ (copyQSlot_inj S D)]
    simp
  · rw [show fSlot S D (((xe S D (xacc S D)).castAdd 2).castAdd 1) = accSlot S D 0 from
      Fin.ext (by rw [hacc_own]; simp [accSlot]), hy4, install_slot _ (accSlot_inj S D)]
    rfl
  · have hcv : (fSlot S D ⟨twF S D + 1, by omega⟩).val = b5 D + (twF S D + 1) := by
      rw [fSlot_val]; simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [y4_off _ (by rw [hcv]; omega) (by rw [hcv]; omega), y3_off _ (by rw [hcv]; omega) (by rw [hcv]; omega)
      (by rw [hcv]; omega), y2_cap]
  · intro p hp
    rw [y4_off _ (by omega) (by omega), y3_off _ (by omega) (by omega) (by omega)]
    rw [hy2, install_off_val _ _ _ _ (by
        intro j
        refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
        · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
          · unfold eraseG; rw [eraseSlots_scratch, comb_own]
            have := (comb S D i).isLt; omega
          · have hl : l' = 0 := Subsingleton.elim _ _
            subst hl
            unfold eraseG; rw [eraseSlots_driver, fSlot_val]
            simp only [Fin.val_castAdd, Fin.val_natAdd]
            rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; omega
        · have hl : l = 0 := Subsingleton.elim _ _
          subst hl
          unfold eraseG; rw [eraseSlots_capacity, fSlot_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          simp <;> omega),
      y1_off _ (by omega) (by omega) (by omega)]

end Init

/-! ## The fold and the framed bit -/

section Post
variable (ins : S.ι)

/-- **The fold and the framed output are ready**: on the initialized bank the fold computes the padded XOR power of
the padded request's unsigned honest table at `x`, and the output tape receives its framed bit. -/
theorem post_run (hD : 1 ≤ D) {N : ℕ} (point : BitInput N)
    (hcb : (a.output (S.req ins)).clauseBits ≤
      capOf S D ins)
    (c C : ℕ) (hfit : c * widthOf S D ins ≤ N)
    (htotal : foldNeed S D ins point c ≤ C) (Z : Fin (G S D) → List Bool)
    (z0 : Z (gp S D 0 (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) =
      S.w0 ins)
    (z132 : Z (gp S D 132 (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) = RepairOrdinary.frame (S.d ins))
    (z2 : Z (gp S D 2 (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) = RepairOrdinary.frame (List.ofFn point))
    (zcnt : Z (gp S D (b3 D + 1) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) = UnaryTemplate.tape c)
    (zdrv : Z (gp S D (b4 D + 24) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D; omega)) = List.replicate C true)
    (zscr : ∀ i : Fin (ks S D), Z (fSlot S D
        (((scratch S D i).castAdd 2).castAdd 1)) = List.replicate C false)
    (zE1 : Z (fSlot S D (((ee S D 1).castAdd 2).castAdd 1)) = List.replicate C false)
    (zE2 : Z (fSlot S D (((ee S D 2).castAdd 2).castAdd 1)) =
      ZeroPadding.pad C (List.replicate (widthOf S D ins) true))
    (zE3 : Z (fSlot S D (((ee S D 3).castAdd 2).castAdd 1)) = List.replicate (S.req ins).arity true)
    (zacc : Z (fSlot S D (((xe S D (xacc S D)).castAdd 2).castAdd 1)) = [false])
    (zcap : Z (fSlot S D ⟨twF S D + 1, by omega⟩) = List.replicate (C + 1) false)
    (zout : ∀ p : Fin (G S D), b6 S D + 3 ≤ p.val → Z p = []) :
    ∃ out : Fin (G S D) → List Bool,
      ClockJoin.ReadyRun (post S D)
        (foldBudget S D ins point c C + 1 + 8) Z out ∧
      out (outSlot S D 1) = RepairOrdinary.frame (padCore (xorPower (CloseoutLanguage.paddedUnsigned
        (a.output (S.req ins)) hcb) c) hfit point).toNat.bits := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D
  have hf := fold_run S D ins hD point hcb c C (C + 1) hfit htotal le_rfl
  set capF : Fin (twF S D + 2 + 1) → ℕ := fun j => if j.val = twF S D + 2 then c + 2 else 0
    with hcapF
  have hp := ready_pad _ _ _ _ capF hf
  have g10 := hp.focus (fSlot S D) (fSlot_inj S D) Z (by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
    · have hc0 : capF (Fin.castAdd 1 j') = 0 := by
        simp only [hcapF, Fin.val_castAdd]; rw [if_neg (by have := j'.isLt; omega)]
      rw [hc0, ZeroPadding.pad_zero, Fin.addCases_left]
      refine Fin.addCases (fun j'' => ?_) (fun l' => ?_) j'
      · simp only [roundTapes, Fin.addCases_left]
        have hjl := j''.isLt
        by_cases hs : ∃ i, scratch S D i = j''
        · obtain ⟨i, rfl⟩ := hs
          have hsv := (scratch_iff S D (scratch S D i)).1 ⟨_, rfl⟩
          rw [padScratch_scr _ _ _ _ ⟨i, rfl⟩,
            roundIn_other S D ins point 0 C false _ (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega), zscr i]
          simp [ZeroPadding.pad]
        · rw [padScratch_port _ _ _ _ hs]
          have hsv : ¬ ((2 ≤ j''.val ∧ j''.val ≤ S.wtapes D) ∨ xt S D + 4 ≤ j''.val) :=
            fun h => hs ((scratch_iff S D j'').2 h)
          by_cases h0 : j''.val = 0
          · rw [show fSlot S D ((j''.castAdd 2).castAdd 1) = gp S D 0 (by omega) from
              Fin.ext (by rw [fSlot_val]; simp [h0, gp]), z0, roundIn_val, h0, bankN_w0]
          by_cases h1 : j''.val = 1
          · rw [show fSlot S D ((j''.castAdd 2).castAdd 1) = gp S D 132 (by omega) from
              Fin.ext (by rw [fSlot_val]; simp [h1, gp]), z132, roundIn_val, h1, bankN_desc]
          by_cases hacc : j''.val = S.wtapes D + 1
          · rw [show j'' = xe S D (xacc S D) from Fin.ext hacc, zacc,
              roundIn_val, show (xe S D (xacc S D)).val = S.wtapes D + 1 from rfl, bankN_acc]
          have hport : j''.val = xt S D ∨ j''.val = xt S D + 1 ∨ j''.val = xt S D + 2 ∨
              j''.val = xt S D + 3 := by omega
          rcases hport with he | he | he | he
          · rw [show fSlot S D ((j''.castAdd 2).castAdd 1) = gp S D 2 (by omega) from
              Fin.ext (by rw [fSlot_val]; simp [gp, he, SBlock.xtapes] <;> omega), z2,
              show j'' = ee S D 0 from Fin.ext (by simp [ee_val, he]), roundIn_e0]
          · rw [show j'' = ee S D 1 from Fin.ext (by simp [ee_val, he]), zE1, roundIn_e1]
            simp [ZeroPadding.pad]
          · rw [show j'' = ee S D 2 from Fin.ext (by simp [ee_val, he]), zE2, roundIn_e2]
          · rw [show j'' = ee S D 3 from Fin.ext (by simp [ee_val, he]), zE3, roundIn_e3]
      · have hl := l'.isLt
        simp only [roundTapes, Fin.addCases_right]
        by_cases hl0 : l'.val = 0
        · have : l' = 0 := Fin.ext hl0
          subst this
          rw [show fSlot S D ((Fin.natAdd (twF S D) (0 : Fin 2)).castAdd 1) =
              gp S D (b4 D + 24) (by omega) from Fin.ext (by
                rw [fSlot_val]; simp only [Fin.val_castAdd, Fin.val_natAdd]
                rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; rfl), zdrv]
          rfl
        · have : l' = 1 := Fin.ext (by omega)
          subst this
          rw [show fSlot S D ((Fin.natAdd (twF S D) (1 : Fin 2)).castAdd 1) =
              fSlot S D ⟨twF S D + 1, by omega⟩ from Fin.ext (by
                rw [fSlot_val, fSlot_val]; simp), zcap]
          rfl
    · have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      have hcn : capF (Fin.natAdd (twF S D + 2) (0 : Fin 1)) = c + 2 := by
        simp only [hcapF, Fin.val_natAdd]; rw [if_pos (by simp)]
      rw [hcn, Fin.addCases_right,
        show fSlot S D (Fin.natAdd (twF S D + 2) (0 : Fin 1)) = gp S D (b3 D + 1) (by omega)
          from Fin.ext (by
            rw [fSlot_val]; simp only [Fin.val_natAdd]
            rw [if_neg (by simp <;> omega), if_neg (by simp <;> omega), if_neg (by simp <;> omega),
              if_neg (by simp <;> omega), if_pos (by simp)]; rfl), zcnt]
      exact (RepairSource.CloseoutCapacity.Power.template_source c).symm)
  set bit := padCore (xorPower (CloseoutLanguage.paddedUnsigned
    (a.output (S.req ins)) hcb) c) hfit point with hbit
  set Z1 := install (fSlot S D) Z (fun j => ZeroPadding.pad (capF j)
    (Fin.addCases (roundTapes (padScratch (scratch S D) C
      (roundIn S D ins point c C bit)) C (C + 1))
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c) j)) with hZ1
  have hacc_own : (fSlot S D (((xe S D (xacc S D)).castAdd 2).castAdd 1)).val =
      b5 D + (S.wtapes D + 1) := by
    rw [fSlot_own _ _ _ (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes]) (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega) (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega)
      (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega) (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes] <;> omega)]
    simp [xe, xacc, SBlock.accumulator, SBlock.xtapes]
  have z1acc : Z1 (outSlot S D 0) = [bit] := by
    rw [show outSlot S D 0 = fSlot S D (((xe S D (xacc S D)).castAdd 2).castAdd 1)
      from Fin.ext (by rw [hacc_own]; simp [outSlot]), hZ1, install_slot _ (fSlot_inj S D)]
    have hc0 : capF (((xe S D (xacc S D)).castAdd 2).castAdd 1) = 0 := by
      simp only [hcapF, Fin.val_castAdd]; rw [if_neg (by simp [xe, xacc, SBlock.accumulator, SBlock.xtapes]; omega)]
    rw [hc0, ZeroPadding.pad_zero, Fin.addCases_left]
    simp only [roundTapes, Fin.addCases_left]
    have hns : ¬ ∃ i, scratch S D i = xe S D (xacc S D) := by
      rw [scratch_iff]; simp [xe, xacc, SBlock.accumulator, SBlock.xtapes]
    rw [padScratch_port _ _ _ _ hns, roundIn_val,
      show (xe S D (xacc S D)).val = S.wtapes D + 1 from rfl, bankN_acc]
  have z1far : ∀ p : Fin (G S D), b6 S D + 3 ≤ p.val → Z1 p = [] := by
    intro p hp
    rw [hZ1, install_off_val _ _ _ _ (by
      intro j; have := j.isLt; rw [fSlot_val]; split_ifs <;> omega), zout p hp]
  obtain ⟨o11, r11, o111⟩ := RecoveryCaseOneBooleanOutput.ready bit
  have g11 := r11.focus (outSlot S D) (outSlot_inj S D) Z1 (by
    intro j; fin_cases j
    · exact z1acc
    · exact z1far _ (by simp [outSlot])
    · exact z1far _ (by simp [outSlot]))
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ g10 g11, ?_⟩
  rw [install_slot _ (outSlot_inj S D)]
  exact o111

end Post

/-! ## The whole execution -/

section Whole
variable (ins : S.ι)

/-- The fold's block width at the request's arity `q`. -/
theorem widthOf_eq {q : ℕ} (harity : (S.req ins).arity = q) :
    widthOf S D ins = q + 1 + CloseoutLanguage.clauseWidth D q := by
  unfold widthOf capOf
  rw [harity]
  omega

/-- The execution's cost. -/
def htwoCost (A u v e1 e2 e3 e4 B q : ℕ) {R : ℕ} (c : BooleanCircuit R) {N : ℕ} (point : BitInput N) (cc : ℕ) : ℕ :=
  preCost k D A u v e1 e2 e3 e4 B c (List.ofFn point) + 1 +
    (initCost q (q + 1 + CloseoutLanguage.clauseWidth D q) (RepairSource.CloseoutCapacity.capacity e4 e4 N) + 1 +
      (foldBudget S D ins point cc (RepairSource.CloseoutCapacity.capacity e4 e4 N) + 1 + 8))

/-- **The Case-2 execution is ready**: from the five cold words (the block's word `w0`, the canonical description of
the proof circuit `c`, the framed address `x`, `1^R`, `1^B`) the machine writes the framed bit
`padCore (xorPower (paddedUnsigned (a.output (S.req ins)) hcb) (t+1)) hfit x` at the width
`q = q(2^S)`, `S = prefixS … |x|`, `t = candT … S … |x|`, given the parameter core's capacities, the fit of the
`t + 1` blocks, and the fold's capacity bound `foldNeed ≤ C`. -/
theorem htwo_run (A u v e1 e2 e3 e4 : ℕ) (hD : 1 ≤ D) {R B : ℕ} (c : BooleanCircuit R) (hc : c.size ≤ B)
    (hd : S.d ins = PCPPNative.descriptor c) {N : ℕ} (point : BitInput N) {q : ℕ}
    (harity : (S.req ins).arity = q) (hqS : q = widthAt k A (CertPrefix.prefixS k A u v D N))
    (hcb : (a.output (S.req ins)).clauseBits ≤ capOf S D ins)
    (hfit : (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) * widthOf S D ins ≤ N)
    (htotal : foldNeed S D ins point
      (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) ≤
        RepairSource.CloseoutCapacity.capacity e4 e4 N)
    (hn : N ≤ pcap e1 N)
    (hvals : ∀ a', a' ≤ N → ∀ i, i ≤ N →
      candA0 k A u v a' * ((v - u) ^ 16) ^ i ≤ pcap e1 N ∧ candB0 v * (v ^ 16) ^ i ≤ pcap e1 N ∧ 1 + i ≤ pcap e1 N)
    (hT : max (pcap e1 N + 1) (max ((v - u) ^ 16 + 1) (v ^ 16 + 1)) ≤ pcap e2 N)
    (hTc : roundCostBound ((v - u) ^ 16) (v ^ 16) (pcap e1 N) + 1 ≤ pcap e2 N)
    (hTs : pcap e2 N + 1 + N + N + 1 ≤ pcap e3 N)
    (hTs' : scanRoundBound k A v D N N ((v - u) ^ 16) (v ^ 16) (pcap e1 N) (pcap e2 N) N + 1 ≤ pcap e3 N) :
    ∃ out : Fin (G S D) → List Bool,
      ClockJoin.ReadyRun (htwo S k D A u v e1 e2 e3 e4)
        (htwoCost S k D ins A u v e1 e2 e3 e4 B q c point
          (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1))
        (htwoIn S D (S.w0 ins) (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B c))
          (RepairOrdinary.frame (List.ofFn point)) R B) out ∧
      out (outSlot S D 1) = RepairOrdinary.frame (padCore (xorPower (CloseoutLanguage.paddedUnsigned
        (a.output (S.req ins)) hcb)
          (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1)) hfit point).toNat.bits := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all S D
  have hlen : (List.ofFn point).length = N := List.length_ofFn
  obtain ⟨X, hX, x0, x132, x2, xq, xw, xcnt, xdrv, xfresh⟩ := pre_run S k D A u v e1 e2 e3 e4 hD c hc
    (S.w0 ins) (List.ofFn point) (by rw [hlen]; exact hn) (by rw [hlen]; exact hvals)
    (by rw [hlen]; exact hT) (by rw [hlen]; exact hTc) (by rw [hlen]; exact hTs) (by rw [hlen]; exact hTs')
  rw [hlen] at xq xw xcnt xdrv
  rw [← hqS] at xq xw
  obtain ⟨Y, hY, ylow, yscr, yE1, yE2, yE3, yacc, ycap, yfar⟩ := init_run S D q
    (q + 1 + CloseoutLanguage.clauseWidth D q) (RepairSource.CloseoutCapacity.capacity e4 e4 N) X xq xw xdrv xfresh
  obtain ⟨Z, hZ, zo⟩ := post_run S D ins hD point hcb _ _ hfit htotal Y
    (by rw [ylow _ (by simp [gp] <;> omega)]; exact x0)
    (by rw [ylow _ (by simp [gp] <;> omega), hd]; exact x132)
    (by rw [ylow _ (by simp [gp] <;> omega)]; exact x2) (by rw [ylow _ (by simp [gp] <;> omega)]; exact xcnt)
    (by rw [ylow _ (by simp [gp] <;> omega)]; exact xdrv) yscr yE1 (by rw [yE2, widthOf_eq S D ins harity])
    (by rw [yE3, harity]) yacc ycap (fun p hp => (yfar p hp).trans (xfresh p (by omega)))
  refine ⟨Z, ?_, zo⟩
  unfold htwo htwoCost
  exact ClockJoin.join _ _ _ _ _ _ _ hX (ClockJoin.join _ _ _ _ _ _ _ hY hZ)

end Whole

end

end Stage35.Exec
