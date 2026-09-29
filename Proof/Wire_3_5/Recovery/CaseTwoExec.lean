import Proof.Wire_3_5.Recovery.CaseTwoFoldRun
import Proof.Wire_3_5.Recovery.CaseTwoParamScan
import Proof.Wire_3_5.Recovery.CaseTwoParamWidth

/-! # The hybrid Case-2 execution (P3:3729-3733, 3758-3763; D1.6 A3c)

Realizes the Case-2 half of "The resulting slice is computable in `E^NP` [...] In the yes case, prefix self-reduction
recovers the first eligible description, after which each honest proof bit is computed by the deterministic PCPP
algorithm" (P3:3758-3763) for the hybrid slice, with the growing XOR schedule (P3:3729-3733, 3818-3822): from the five
cold words of base's Case-2 dispatch (the hierarchy word, the recovered oracle description, the framed address `x`,
`1^R`, `1^B`) one fixed machine
1. prepares the frames (base `CloseoutCaseTwo.PreparedFrames`: the oracle's descriptor from its canonical description);
2. recomputes the slice parameters from `x` (A3a: the index `S`, the schedule `t`; A3b: `1^{q(2^S)}` and the block
   width `1^w`, `w = q + 1 + ⌈D log₂(q+2)⌉`), the copy count `t + 1` as a counter word (base `DimensionTemplate`), and the
   bank capacity `1^{C}` (base `CloseoutCapacity`);
3. initializes the fold's bank (the width `1^q`, base `RecoveryScratchErase` on the scratch, the offset and the width,
   the width `1^w` (base `PCPUnaryCopy`), the accumulator `[false]`);
4. runs A2's uniform fold over `t + 1` blocks of `x`;
5. frames the accumulator bit (base `RecoveryCaseOneBooleanOutput`).

This module fixes the machine's tape layout (`G` tapes: the frames' 140, then the blocks of each stage). -/

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoExec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun
open NearCubicWires.RepairSource.ProjectionNormalization (HierarchySourceInput.hierarchyInput)
open NearCubicWires.RecoveryPipeline (padCore)

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm) (k D : ℕ)

/-! ## The layout -/

/-- The parameter core's tapes. -/
abbrev ptD : ℕ := prefixTapes D
/-- The widths' tapes. -/
abbrev pwD : ℕ := CaseTwoParamWidth.pw D
/-- The fold worker's tapes. -/
abbrev twF : ℕ := CaseTwoFold.tw source a k D

/-- Block bases: frames `[0,140)`, parameter core `140 + ·`, widths `b2 + ·`, template `b3 + ·`, capacity `b4 + ·`,
fold `b5 + ·`, logs and output `b6 + ·`. -/
abbrev b2 : ℕ := 140 + ptD D
abbrev b3 : ℕ := b2 D + pwD D
abbrev b4 : ℕ := b3 D + 3
abbrev b5 : ℕ := b4 D + 26
abbrev b6 : ℕ := b5 D + twF source a k D + 3
/-- The machine's tape count. -/
abbrev G : ℕ := b6 source a k D + 5

theorem ptD_ge : 160 ≤ ptD D := by
  have := scanTapes_eq D; unfold ptD prefixTapes; omega

/-- Every layout equation and bound, for `omega`. -/
theorem layout_all : 160 ≤ ptD D ∧ pwD D = 28 + (26 + 2 * D) + 5 ∧
    twF source a k D = wtapes source a k D + 1 + 1 + 9 ∧ 9 ≤ wtapes source a k D ∧
    xt source a k D = wtapes source a k D + 1 + 1 ∧
    b2 D = 140 + ptD D ∧ b3 D = b2 D + pwD D ∧ b4 D = b3 D + 3 ∧ b5 D = b4 D + 26 ∧
    b6 source a k D = b5 D + twF source a k D + 3 ∧ G source a k D = b6 source a k D + 5 :=
  ⟨ptD_ge D, rfl, rfl, wtapes_ge source a k D, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A position of the machine. -/
def gp (m : ℕ) (h : m < G source a k D) : Fin (G source a k D) := ⟨m, h⟩

/-! ## The stages' slots -/

/-- Close a value goal of the layout (needs the layout facts in context). -/
macro "ex_tac" : tactic => `(tactic| (first | omega | (simp only [Fin.val_mk] at * <;> omega)))

def pfSlot (i : Fin 140) : Fin (G source a k D) := ⟨i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega⟩
def pcSlot (i : Fin (ptD D)) : Fin (G source a k D) :=
  ⟨if i.val = 0 then 2 else 140 + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
def pwSlot (i : Fin (pwD D)) : Fin (G source a k D) :=
  ⟨if i.val = 0 then 176 else b2 D + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
def tmpSlot (i : Fin 3) : Fin (G source a k D) :=
  ⟨if i.val = 0 then 145 else b3 D + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
def capSlot (i : Fin 26) : Fin (G source a k D) :=
  ⟨if i.val = 0 then 2 else b4 D + i.val, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
/-- The fold's tapes: its hierarchy and descriptor ports on the frames (138, 132), its address port on `x` (2), its
driver on the capacity (`b4 + 24`), its counter on the template (`b3 + 1`), everything else in its own block. -/
def fSlot (j : Fin (twF source a k D + 2 + 1)) : Fin (G source a k D) :=
  ⟨if j.val = 0 then 138 else if j.val = 1 then 132 else if j.val = xt source a k D then 2
    else if j.val = twF source a k D then b4 D + 24 else if j.val = twF source a k D + 2 then b3 D + 1
    else b5 D + j.val, by have := j.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
def copyQSlot (i : Fin 3) : Fin (G source a k D) :=
  ⟨if i.val = 0 then b2 D + 26 else if i.val = 1 then b5 D + (xt source a k D + 3) else b6 source a k D,
    by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
def copyWSlot (i : Fin 3) : Fin (G source a k D) :=
  ⟨if i.val = 0 then b2 D + (28 + (26 + 2 * D) + 3) else if i.val = 1 then b5 D + (xt source a k D + 2)
    else b6 source a k D + 1, by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
def accSlot (i : Fin 2) : Fin (G source a k D) :=
  ⟨if i.val = 0 then b5 D + (wtapes source a k D + 1) else b6 source a k D + 2,
    by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩
def outSlot (i : Fin 3) : Fin (G source a k D) :=
  ⟨if i.val = 0 then b5 D + (wtapes source a k D + 1) else b6 source a k D + 2 + i.val,
    by have := i.isLt; obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; split_ifs <;> omega⟩

/-- The erase's backing: the fold's scratch, then its offset and width ports. -/
def comb (j : Fin (ks source a k D + 2)) : Fin (twF source a k D) :=
  if h : j.val < ks source a k D then scratch source a k D ⟨j.val, h⟩
  else ee source a k D ⟨j.val - ks source a k D + 1, by have := j.isLt; omega⟩

/-- The erase's slots in the machine. -/
def eraseG (j : Fin (ks source a k D + 2 + 1 + 1)) : Fin (G source a k D) :=
  fSlot source a k D ((eraseSlots (comb source a k D) j).castAdd 1)

/-- Injectivity of a slot map from its values. -/
theorem inj_of_val {m t : ℕ} (f : Fin m → Fin t) (h : ∀ i j, (f i).val = (f j).val → i.val = j.val) :
    Function.Injective f := fun i j hij => Fin.ext (h i j (congrArg Fin.val hij))

theorem comb_injective : Function.Injective (comb source a k D) := by
  intro i j h
  have hil := i.isLt
  have hjl := j.isLt
  by_cases hi : i.val < ks source a k D <;> by_cases hj : j.val < ks source a k D
  · have h' := h
    simp only [comb, dif_pos hi, dif_pos hj] at h'
    exact Fin.ext (by simpa using congrArg Fin.val (scratch_injective source a k D h'))
  · exfalso
    have h' := h
    simp only [comb, dif_pos hi, dif_neg hj] at h'
    exact ee_not_scratch' source a k D _ (by show j.val - ks source a k D + 1 < 4; omega) ⟨⟨i.val, hi⟩, h'⟩
  · exfalso
    have h' := h
    simp only [comb, dif_neg hi, dif_pos hj] at h'
    exact ee_not_scratch' source a k D _ (by show i.val - ks source a k D + 1 < 4; omega) ⟨⟨j.val, hj⟩, h'.symm⟩
  · have h' := congrArg Fin.val h
    simp only [comb, dif_neg hi, dif_neg hj, ee_val] at h'
    exact Fin.ext (by omega)

/-! ## Injectivity -/

theorem pfSlot_inj : Function.Injective (pfSlot source a k D) :=
  inj_of_val _ (by intro i j h; exact h)
theorem pcSlot_inj : Function.Injective (pcSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [pcSlot] at h; split_ifs at h <;> omega)
theorem pwSlot_inj : Function.Injective (pwSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [pwSlot] at h; split_ifs at h <;> omega)
theorem tmpSlot_inj : Function.Injective (tmpSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [tmpSlot] at h; split_ifs at h <;> omega)
theorem capSlot_inj : Function.Injective (capSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [capSlot] at h; split_ifs at h <;> omega)
theorem fSlot_inj : Function.Injective (fSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [fSlot] at h; split_ifs at h <;> omega)
theorem copyQSlot_inj : Function.Injective (copyQSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [copyQSlot] at h; split_ifs at h <;> omega)
theorem copyWSlot_inj : Function.Injective (copyWSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [copyWSlot] at h; split_ifs at h <;> omega)
theorem accSlot_inj : Function.Injective (accSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [accSlot] at h; split_ifs at h <;> omega)
theorem outSlot_inj : Function.Injective (outSlot source a k D) :=
  inj_of_val _ (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; intro i j h; have hi := i.isLt; have hj := j.isLt; simp only [outSlot] at h; split_ifs at h <;> omega)
theorem eraseG_inj : Function.Injective (eraseG source a k D) := fun _ _ h =>
  eraseSlots_injective _ (comb_injective source a k D) (Fin.castAdd_injective _ _ (fSlot_inj source a k D h))

/-! ## The machine -/

section Machine
variable (A u v e1 e2 e3 e4 CH Cpad : ℕ) (code : List Bool)

/-- The preparation: frames, the parameter core, the widths, the counter template, the bank capacity. -/
def pre :=
  Composition.machine (RecoveryFocus.machine (pfSlot source a k D) PreparedFrames.machine)
  (Composition.machine (RecoveryFocus.machine (pcSlot source a k D) (CaseTwoParamScan.paramCore k A u v D e1 e2 e3))
  (Composition.machine (RecoveryFocus.machine (pwSlot source a k D) (CaseTwoParamWidth.paramWidth k A D))
  (Composition.machine (RecoveryFocus.machine (tmpSlot source a k D)
    (RepairSource.ProjectionNormalization.DimensionTemplate.machine true))
    (RecoveryFocus.machine (capSlot source a k D) (RepairSource.CloseoutCapacity.machine e4 e4)))))

/-- The fold's bank initialization: `1^q`, the erase, `1^w`, the accumulator. -/
def init :=
  Composition.machine (RecoveryFocus.machine (copyQSlot source a k D) PCPUnaryCopy.machine)
  (Composition.machine (RecoveryFocus.machine (eraseG source a k D)
    (RecoveryScratchErase.resetMachine (ks source a k D + 2)))
  (Composition.machine (RecoveryFocus.machine (copyWSlot source a k D) PCPUnaryCopy.machine)
    (RecoveryFocus.machine (accSlot source a k D) (HierarchyFixedWord.machine [false]))))

/-- The fold and the framed output bit. -/
def post :=
  Composition.machine (RecoveryFocus.machine (fSlot source a k D) (foldMachine source a k D CH Cpad code))
    (RecoveryFocus.machine (outSlot source a k D) RecoveryCaseOneBooleanOutput.machine)

/-- **The hybrid Case-2 execution.** -/
def htwo := Composition.machine (pre source a k D A u v e1 e2 e3 e4)
  (Composition.machine (init source a k D) (post source a k D CH Cpad code))

/-- The input: base's five cold words (hierarchy, description, address, `1^R`, `1^B`) on the frames' block. -/
def htwoIn (hier desc addr : List Bool) (R B : ℕ) : Fin (G source a k D) → List Bool := fun i =>
  if h : i.val < 140 then PreparedFrames.input hier desc addr R B ⟨i.val, h⟩ else []

end Machine

/-! ## The preparation -/

section Pre
variable (A u v e1 e2 e3 e4 : ℕ)

/-- The preparation's cost. -/
def preCost {R : ℕ} (B : ℕ) (c : BooleanCircuit R) (left right bits : List Bool) : ℕ :=
  PreparedFrames.budget B c left right + 1 + (CaseTwoParamScan.paramCost k A u v D e1 e2 e3 bits + 1 +
    (CaseTwoParamWidth.pwCost k A D (CertPrefix.prefixS k A u v D bits.length) + 1 +
      ((2 * candT k A u v (CertPrefix.prefixS k A u v D bits.length) ((v - u) ^ 16) (v ^ 16) bits.length + 8) + 1 +
        RepairSource.CloseoutCapacity.budget e4 e4 bits)))

/-- **The preparation is ready**: the frames (hierarchy, descriptor, address), `1^q` and `1^w` at the index
`S = prefixS … n`, the copy count `t + 1` as a template word, the capacity `1^{C}`, and the fold's block still empty. -/
theorem pre_run (hD : 1 ≤ D) {R B : ℕ} (c : BooleanCircuit R) (hc : c.size ≤ B) (left right bits : List Bool)
    (hn : bits.length ≤ pcap e1 bits.length)
    (hvals : ∀ a', a' ≤ bits.length → ∀ i, i ≤ bits.length →
      candA0 k A u v a' * ((v - u) ^ 16) ^ i ≤ pcap e1 bits.length ∧
      candB0 v * (v ^ 16) ^ i ≤ pcap e1 bits.length ∧ 1 + i ≤ pcap e1 bits.length)
    (hT : max (pcap e1 bits.length + 1) (max ((v - u) ^ 16 + 1) (v ^ 16 + 1)) ≤ pcap e2 bits.length)
    (hTc : roundCostBound ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length) + 1 ≤ pcap e2 bits.length)
    (hTs : pcap e2 bits.length + 1 + bits.length + bits.length + 1 ≤ pcap e3 bits.length)
    (hTs' : scanRoundBound k A v D bits.length bits.length ((v - u) ^ 16) (v ^ 16) (pcap e1 bits.length)
      (pcap e2 bits.length) bits.length + 1 ≤ pcap e3 bits.length) :
    ∃ out : Fin (G source a k D) → List Bool,
      ClockJoin.ReadyRun (pre source a k D A u v e1 e2 e3 e4) (preCost k D A u v e1 e2 e3 e4 B c left right bits)
        (htwoIn source a k D (RepairOrdinary.frame left ++ RepairOrdinary.frame right)
          (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B c))
          (RepairOrdinary.frame bits) R B) out ∧
      out (gp source a k D 138 (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega)) =
        RepairOrdinary.frame (RepairOrdinary.frame left ++ RepairOrdinary.frame right) ∧
      out (gp source a k D 132 (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega)) =
        RepairOrdinary.frame (PCPPNative.descriptor c) ∧
      out (gp source a k D 2 (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega)) =
        RepairOrdinary.frame bits ∧
      out (gp source a k D (b2 D + 26) (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega)) =
        List.replicate (widthAt k A (CertPrefix.prefixS k A u v D bits.length)) true ∧
      out (gp source a k D (b2 D + (28 + (26 + 2 * D) + 3))
          (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega)) =
        List.replicate (widthAt k A (CertPrefix.prefixS k A u v D bits.length) + 1 +
          CloseoutLanguage.clauseWidth D (widthAt k A (CertPrefix.prefixS k A u v D bits.length))) true ∧
      out (gp source a k D (b3 D + 1) (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega)) =
        UnaryTemplate.tape
          (candT k A u v (CertPrefix.prefixS k A u v D bits.length) ((v - u) ^ 16) (v ^ 16) bits.length + 1) ∧
      out (gp source a k D (b4 D + 24) (by obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := layout_all source a k D; omega)) =
        List.replicate (RepairSource.CloseoutCapacity.capacity e4 e4 bits.length) true ∧
      (∀ p : Fin (G source a k D), b5 D ≤ p.val → out p = []) := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D
  set S := CertPrefix.prefixS k A u v D bits.length with hS
  set t := candT k A u v S ((v - u) ^ 16) (v ^ 16) bits.length with ht
  set x := htwoIn source a k D (RepairOrdinary.frame left ++ RepairOrdinary.frame right)
    (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B c)) (RepairOrdinary.frame bits) R B
    with hx
  have x_hi : ∀ p : Fin (G source a k D), 140 ≤ p.val → x p = [] := by
    intro p hp; rw [hx]; simp only [htwoIn]; rw [dif_neg (by omega)]
  -- the frames
  obtain ⟨o1, r1, o1h, o1d, -, -, o1a⟩ := PreparedFrames.frames_run c hc left right (RepairOrdinary.frame bits)
  have g1 := r1.focus (pfSlot source a k D) (pfSlot_inj source a k D) x (by
    intro i; rw [hx]; simp only [htwoIn, pfSlot]; rw [dif_pos i.isLt])
  set a1 := install (pfSlot source a k D) x o1 with ha1
  have a1_lo : ∀ p : Fin (G source a k D), (h : p.val < 140) → a1 p = o1 ⟨p.val, h⟩ := by
    intro p h; rw [ha1]; exact install_slot _ (pfSlot_inj source a k D) x o1 ⟨p.val, h⟩
  have a1_hi : ∀ p : Fin (G source a k D), 140 ≤ p.val → a1 p = [] := by
    intro p hp
    rw [ha1, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [pfSlot]; omega), x_hi p hp]
  -- the parameter core
  obtain ⟨o2, r2, o20, o22, o236, o25⟩ := CaseTwoParamScan.paramCore_run k A u v D e1 e2 e3 hD bits hn hvals hT hTc hTs hTs'
  have g2 := r2.focus (pcSlot source a k D) (pcSlot_inj source a k D) a1 (by
    intro i
    by_cases h0 : i.val = 0
    · rw [a1_lo _ (by simp only [pcSlot, h0, if_true]; omega)]
      simp only [pcSlot, h0, if_true, prefixInput, if_true]
      exact o1a
    · rw [a1_hi _ (by simp only [pcSlot, h0, if_false]; omega)]
      simp only [prefixInput, h0, if_false])
  set a2 := install (pcSlot source a k D) a1 o2 with ha2
  have a2_off : ∀ p : Fin (G source a k D), p.val ≠ 2 → (p.val < 141 ∨ 140 + ptD D ≤ p.val) → a2 p = a1 p := by
    intro p h1 h2
    rw [ha2, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [pcSlot]; split_ifs <;> omega)]
  have a2_at : ∀ (m : ℕ) (hm : m < ptD D) (hm0 : m ≠ 0) (p : Fin (G source a k D)), p.val = 140 + m →
      a2 p = o2 ⟨m, hm⟩ := by
    intro m hm hm0 p hp
    rw [show p = pcSlot source a k D ⟨m, hm⟩ from Fin.ext (by simp only [pcSlot, Fin.val_mk, if_neg hm0]; omega), ha2,
      install_slot _ (pcSlot_inj source a k D)]
  have a2_2 : a2 (gp source a k D 2 (by omega)) = RepairOrdinary.frame bits := by
    rw [show gp source a k D 2 _ = pcSlot source a k D ⟨0, by omega⟩ from Fin.ext rfl, ha2,
      install_slot _ (pcSlot_inj source a k D)]
    exact o20
  -- the widths
  obtain ⟨o3, r3, o30, o326, o3w⟩ := CaseTwoParamWidth.paramWidth_run k A D S hD
  have p3 := ready_pad _ _ _ _ (fun i : Fin (pwD D) => if i.val = 0 then pcap e3 bits.length else 0) r3
  have g3 := p3.focus (pwSlot source a k D) (pwSlot_inj source a k D) a2 (by
    intro i
    by_cases h0 : i.val = 0
    · rw [show pwSlot source a k D i = gp source a k D 176 (by omega) from Fin.ext (by simp [pwSlot, gp, h0] <;> omega),
        a2_at 36 (by omega) (by omega) _ (by simp [gp] <;> omega)]
      simp only [h0, if_true, CaseTwoParamWidth.pwInput]
      exact o236
    · rw [a2_off _ (by simp only [pwSlot, h0, if_false]; omega) (Or.inr (by simp only [pwSlot, h0, if_false]; omega)),
        a1_hi _ (by simp only [pwSlot, h0, if_false]; omega)]
      simp [CaseTwoParamWidth.pwInput, h0])
  set a3 := install (pwSlot source a k D) a2
    (fun i => ZeroPadding.pad (if i.val = 0 then pcap e3 bits.length else 0) (o3 i)) with ha3
  have a3_off : ∀ p : Fin (G source a k D), p.val ≠ 176 → (p.val < b2 D + 1 ∨ b3 D ≤ p.val) → a3 p = a2 p := by
    intro p h1 h2
    rw [ha3, install_off_val _ _ _ _ (by intro j; have := j.isLt; simp only [pwSlot]; split_ifs <;> omega)]
  have a3_at : ∀ (m : ℕ) (hm : m < pwD D) (hm0 : m ≠ 0) (p : Fin (G source a k D)), p.val = b2 D + m →
      a3 p = o3 ⟨m, hm⟩ := by
    intro m hm hm0 p hp
    rw [show p = pwSlot source a k D ⟨m, hm⟩ from Fin.ext (by simp only [pwSlot, Fin.val_mk, if_neg hm0]; omega), ha3,
      install_slot _ (pwSlot_inj source a k D)]
    simp only [Fin.val_mk, if_neg hm0, ZeroPadding.pad_zero]
  -- the copy count's template
  have p4 := ready_pad _ _ _ _ ![pcap e1 bits.length, 0, 0]
    (RepairSource.ProjectionNormalization.DimensionTemplate.ready true t)
  have g4 := p4.focus (tmpSlot source a k D) (tmpSlot_inj source a k D) a3 (by
    intro i; fin_cases i
    · show a3 (tmpSlot source a k D 0) = _
      rw [a3_off _ (by simp [tmpSlot] <;> omega) (Or.inl (by simp [tmpSlot] <;> omega)),
        a2_at 5 (by omega) (by omega) _ (by simp [tmpSlot] <;> omega)]
      simp only [RepairSource.ProjectionNormalization.DimensionTemplate.input]
      exact o25
    · show a3 (tmpSlot source a k D 1) = _
      rw [a3_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)),
        a2_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)), a1_hi _ (by simp [tmpSlot] <;> omega)]
      rfl
    · show a3 (tmpSlot source a k D 2) = _
      rw [a3_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)),
        a2_off _ (by simp [tmpSlot] <;> omega) (Or.inr (by simp [tmpSlot] <;> omega)), a1_hi _ (by simp [tmpSlot] <;> omega)]
      rfl)
  set a4 := install (tmpSlot source a k D) a3 (fun i => ZeroPadding.pad (![pcap e1 bits.length, 0, 0] i)
    (RepairSource.ProjectionNormalization.DimensionTemplate.output true t i)) with ha4
  have a4_off : ∀ p : Fin (G source a k D), p.val ≠ 145 → p.val ≠ b3 D + 1 → p.val ≠ b3 D + 2 → a4 p = a3 p := by
    intro p h1 h2 h3
    rw [ha4, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [tmpSlot] <;> omega)]
  -- the capacity
  obtain ⟨o5, r5, o524, -, o50⟩ := RepairSource.CloseoutCapacity.capacity_run e4 e4 bits
  have g5 := r5.focus (capSlot source a k D) (capSlot_inj source a k D) a4 (by
    intro i
    by_cases h0 : i.val = 0
    · rw [a4_off _ (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega),
        a3_off _ (by simp [capSlot, h0] <;> omega) (Or.inl (by simp [capSlot, h0] <;> omega)),
        show capSlot source a k D i = gp source a k D 2 (by omega) from Fin.ext (by simp [capSlot, gp, h0] <;> omega), a2_2]
      simp [RepairSource.CloseoutCapacity.input, h0]
    · have hi := i.isLt
      rw [a4_off _ (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega) (by simp [capSlot, h0] <;> omega),
        a3_off _ (by simp [capSlot, h0] <;> omega) (Or.inr (by simp [capSlot, h0] <;> omega)),
        a2_off _ (by simp [capSlot, h0] <;> omega) (Or.inr (by simp [capSlot, h0] <;> omega)),
        a1_hi _ (by simp [capSlot, h0] <;> omega)]
      simp [RepairSource.CloseoutCapacity.input, h0])
  set a5 := install (capSlot source a k D) a4 o5 with ha5
  have a5_off : ∀ p : Fin (G source a k D), p.val ≠ 2 → (p.val < b4 D + 1 ∨ b4 D + 26 ≤ p.val) → a5 p = a4 p := by
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
  · rw [show gp source a k D 2 _ = capSlot source a k D 0 from Fin.ext rfl, ha5, install_slot _ (capSlot_inj source a k D)]
    exact o50
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a4_off _ (by simp [gp] <;> omega)
      (by simp [gp] <;> omega) (by simp [gp] <;> omega), a3_at 26 (by omega) (by omega) _ (by simp [gp] <;> omega)]
    exact o326
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)), a4_off _ (by simp [gp] <;> omega)
      (by simp [gp] <;> omega) (by simp [gp] <;> omega), a3_at (28 + (26 + 2 * D) + 3) (by omega) (by omega) _ (by simp [gp] <;> omega)]
    exact o3w
  · rw [a5_off _ (by simp [gp] <;> omega) (Or.inl (by simp [gp] <;> omega)),
      show gp source a k D (b3 D + 1) _ = tmpSlot source a k D 1 from Fin.ext (by simp [gp, tmpSlot] <;> omega), ha4,
      install_slot _ (tmpSlot_inj source a k D)]
    simp [RepairSource.ProjectionNormalization.DimensionTemplate.output]
  · rw [show gp source a k D (b4 D + 24) _ = capSlot source a k D 24 from Fin.ext (by simp [gp, capSlot] <;> omega), ha5,
      install_slot _ (capSlot_inj source a k D)]
    exact o524
  · intro p hp
    rw [a5_off _ (by omega) (Or.inr (by omega)), a4_off _ (by omega) (by omega) (by omega),
      a3_off _ (by omega) (Or.inr (by omega)), a2_off _ (by omega) (Or.inr (by omega)), a1_hi _ (by omega)]

end Pre

/-! ## The fold's bank initialization -/

section Init

theorem fSlot_val (j : Fin (twF source a k D + 2 + 1)) : (fSlot source a k D j).val =
    if j.val = 0 then 138 else if j.val = 1 then 132 else if j.val = xt source a k D then 2
    else if j.val = twF source a k D then b4 D + 24 else if j.val = twF source a k D + 2 then b3 D + 1
    else b5 D + j.val := rfl

/-- The fold's own positions: every fold tape other than its aliased ports sits at `b5 + j`. -/
theorem fSlot_own (j : Fin (twF source a k D + 2 + 1)) (h0 : j.val ≠ 0) (h1 : j.val ≠ 1)
    (hx : j.val ≠ xt source a k D) (hd : j.val ≠ twF source a k D) (hc : j.val ≠ twF source a k D + 2) :
    (fSlot source a k D j).val = b5 D + j.val := by
  rw [fSlot_val, if_neg h0, if_neg h1, if_neg hx, if_neg hd, if_neg hc]

/-- The erase's backing positions are the fold's own. -/
theorem comb_own (i : Fin (ks source a k D + 2)) :
    (fSlot source a k D (((comb source a k D i).castAdd 2).castAdd 1)).val = b5 D + (comb source a k D i).val := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D
  have hc := (comb source a k D i).isLt
  have hr : (comb source a k D i).val = (comb source a k D i).val := rfl
  apply fSlot_own
  all_goals simp only [Fin.val_castAdd]
  all_goals
    unfold comb
    split_ifs with h
    · have := (scratch_iff source a k D (scratch source a k D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
      omega
    · simp only [ee_val, Fin.val_mk]; omega

variable (q w C : ℕ)

/-- The initialization's cost. -/
def initCost : ℕ := (2 * q + 4) + 1 + ((2 * C + 4) + 1 + ((2 * w + 4) + 1 + 4))

/-- **The fold's bank is initialized**: `1^q` on its width port, `0^C` on the offset and every scratch tape, `0^C` then
`1^w` on the block-width port, `0^{C+1}` on the capacity tape, `[false]` on the accumulator; every position below the
fold's block is kept. -/
theorem init_run (X : Fin (G source a k D) → List Bool)
    (hq : X (gp source a k D (b2 D + 26) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) = List.replicate q true)
    (hw : X (gp source a k D (b2 D + (28 + (26 + 2 * D) + 3)) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) = List.replicate w true)
    (hC : X (gp source a k D (b4 D + 24) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) = List.replicate C true)
    (hfresh : ∀ p : Fin (G source a k D), b5 D ≤ p.val → X p = []) :
    ∃ Y : Fin (G source a k D) → List Bool,
      ClockJoin.ReadyRun (init source a k D) (initCost q w C) X Y ∧
      (∀ p : Fin (G source a k D), p.val < b5 D → Y p = X p) ∧
      (∀ i : Fin (ks source a k D), Y (fSlot source a k D
        (((scratch source a k D i).castAdd 2).castAdd 1)) = List.replicate C false) ∧
      Y (fSlot source a k D (((ee source a k D 1).castAdd 2).castAdd 1)) = List.replicate C false ∧
      Y (fSlot source a k D (((ee source a k D 2).castAdd 2).castAdd 1)) = ZeroPadding.pad C (List.replicate w true) ∧
      Y (fSlot source a k D (((ee source a k D 3).castAdd 2).castAdd 1)) = List.replicate q true ∧
      Y (fSlot source a k D (((xe source a k D (xacc source a k D)).castAdd 2).castAdd 1)) = [false] ∧
      Y (fSlot source a k D ⟨twF source a k D + 1, by omega⟩) = List.replicate (C + 1) false ∧
      (∀ p : Fin (G source a k D), b6 source a k D + 3 ≤ p.val → Y p = X p) := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D
  -- `1^q` onto the width port
  have g6 := (ready_of_root (PCPUnaryCopy.copy_ready q 0 0 0)).focus (copyQSlot source a k D)
    (copyQSlot_inj source a k D) X (by
      intro j; fin_cases j
      · show X (gp source a k D (b2 D + 26) _) = _; rw [hq]; simp
      · show X (copyQSlot source a k D 1) = _; rw [hfresh _ (by simp [copyQSlot] <;> omega)]; rfl
      · show X (copyQSlot source a k D 2) = _; rw [hfresh _ (by simp [copyQSlot] <;> omega)]; rfl)
  set y1 := install (copyQSlot source a k D) X ![ZeroPadding.pad 0 (List.replicate q true),
    ZeroPadding.pad 0 (List.replicate q true), List.replicate (max 0 (q + 1)) false] with hy1
  have y1_off : ∀ p : Fin (G source a k D), p.val ≠ b2 D + 26 → p.val ≠ b5 D + (xt source a k D + 3) →
      p.val ≠ b6 source a k D → y1 p = X p := by
    intro p h1 h2 h3
    rw [hy1, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [copyQSlot] <;> omega)]
  -- the erase
  have g7 := (ready_of_root (RecoveryScratchErase.erase_ready C 0 (fun _ : Fin (ks source a k D + 2) => [])
    (by intro i; simp))).focus (eraseG source a k D) (eraseG_inj source a k D) y1 (by
      intro j
      refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
      · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
        · simp only [Fin.addCases_left]
          rw [show eraseG source a k D (Fin.castAdd 1 (Fin.castAdd 1 i)) =
              fSlot source a k D (((comb source a k D i).castAdd 2).castAdd 1) by
                unfold eraseG; rw [eraseSlots_scratch]]
          have hv := comb_own source a k D i
          have hc := (comb source a k D i).isLt
          rw [y1_off _ (by omega) (by
                have := comb_own source a k D i
                unfold comb at this ⊢
                split_ifs at this ⊢ with h
                · have := (scratch_iff source a k D (scratch source a k D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
                  omega
                · simp only [ee_val, Fin.val_mk] at this ⊢; omega) (by omega),
            hfresh _ (by omega)]
        · have hl : l' = 0 := Subsingleton.elim _ _
          subst hl
          simp only [Fin.addCases_left, Fin.addCases_right]
          rw [show eraseG source a k D (Fin.castAdd 1 (Fin.natAdd (ks source a k D + 2) (0 : Fin 1))) =
              gp source a k D (b4 D + 24) (by omega) by
                apply Fin.ext; unfold eraseG; rw [eraseSlots_driver, fSlot_val]
                simp only [Fin.val_castAdd, Fin.val_natAdd]
                rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; rfl,
            y1_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega) (by simp [gp] <;> omega), hC]
      · have hl : l = 0 := Subsingleton.elim _ _
        subst hl
        simp only [Fin.addCases_right]
        rw [show eraseG source a k D (Fin.natAdd (ks source a k D + 2 + 1) (0 : Fin 1)) =
            gp source a k D (b5 D + (twF source a k D + 1)) (by omega) by
              apply Fin.ext; unfold eraseG; rw [eraseSlots_capacity, fSlot_val]
              simp only [Fin.val_castAdd, Fin.val_natAdd]
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
              rfl,
          y1_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega) (by simp [gp] <;> omega),
          hfresh _ (by simp [gp] <;> omega)]
        rfl)
  set eo : Fin (ks source a k D + 2 + 1 + 1) → List Bool :=
    Fin.addCases (Fin.addCases (fun _ : Fin (ks source a k D + 2) => List.replicate C false)
      (fun _ : Fin 1 => List.replicate C true)) (fun _ : Fin 1 => List.replicate (max 0 (C + 1)) false) with heo
  set y2 := install (eraseG source a k D) y1 eo with hy2
  have y2_comb : ∀ i : Fin (ks source a k D + 2),
      y2 (fSlot source a k D (((comb source a k D i).castAdd 2).castAdd 1)) = List.replicate C false := by
    intro i
    rw [show fSlot source a k D (((comb source a k D i).castAdd 2).castAdd 1) =
        eraseG source a k D (Fin.castAdd 1 (Fin.castAdd 1 i)) by unfold eraseG; rw [eraseSlots_scratch],
      hy2, install_slot _ (eraseG_inj source a k D)]
    simp [heo]
  have y2_cap : y2 (fSlot source a k D ⟨twF source a k D + 1, by omega⟩) = List.replicate (C + 1) false := by
    rw [show fSlot source a k D ⟨twF source a k D + 1, by omega⟩ =
        eraseG source a k D (Fin.natAdd (ks source a k D + 2 + 1) (0 : Fin 1)) by
          unfold eraseG; rw [eraseSlots_capacity]; rfl,
      hy2, install_slot _ (eraseG_inj source a k D)]
    simp [heo]
  have y2_drv : y2 (gp source a k D (b4 D + 24) (by omega)) = List.replicate C true := by
    rw [show gp source a k D (b4 D + 24) (by omega) =
        eraseG source a k D (Fin.castAdd 1 (Fin.natAdd (ks source a k D + 2) (0 : Fin 1))) by
          apply Fin.ext; unfold eraseG; rw [eraseSlots_driver, fSlot_val]
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; rfl,
      hy2, install_slot _ (eraseG_inj source a k D)]
    simp [heo]
  have y2_off : ∀ p : Fin (G source a k D), p.val < b5 D → p.val ≠ b4 D + 24 → y2 p = y1 p := by
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
  have hE2 : fSlot source a k D (((ee source a k D 2).castAdd 2).castAdd 1) =
      fSlot source a k D (((comb source a k D ⟨ks source a k D + 1, by omega⟩).castAdd 2).castAdd 1) := by
    congr 3; unfold comb; rw [dif_neg (by simp)]; apply Fin.ext; simp [ee_val]
  have hE2v : (fSlot source a k D (((ee source a k D 2).castAdd 2).castAdd 1)).val = b5 D + (xt source a k D + 2) := by
    rw [hE2, comb_own]; unfold comb; rw [dif_neg (by simp)]; simp [ee_val]
  have g8 := (ready_of_root (PCPUnaryCopy.copy_ready w 0 C 0)).focus (copyWSlot source a k D)
    (copyWSlot_inj source a k D) y2 (by
      intro j; fin_cases j
      · show y2 (gp source a k D (b2 D + (28 + (26 + 2 * D) + 3)) _) = _
        rw [y2_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega),
          y1_off _ (by simp [gp] <;> omega) (by simp [gp] <;> omega) (by simp [gp] <;> omega), hw]
        simp
      · show y2 (copyWSlot source a k D 1) = _
        rw [show copyWSlot source a k D 1 = fSlot source a k D (((ee source a k D 2).castAdd 2).castAdd 1) from
          Fin.ext (by rw [hE2v]; simp [copyWSlot]), hE2, y2_comb]
        rfl
      · show y2 (copyWSlot source a k D 2) = _
        rw [hy2, install_off_val _ _ _ _ (by
            intro j
            refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
            · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
              · unfold eraseG; rw [eraseSlots_scratch, comb_own]; simp [copyWSlot]
                have := (comb source a k D i).isLt; omega
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
  set y3 := install (copyWSlot source a k D) y2 ![ZeroPadding.pad 0 (List.replicate w true),
    ZeroPadding.pad C (List.replicate w true), List.replicate (max 0 (w + 1)) false] with hy3
  have y3_off : ∀ p : Fin (G source a k D), p.val ≠ b2 D + (28 + (26 + 2 * D) + 3) →
      p.val ≠ b5 D + (xt source a k D + 2) → p.val ≠ b6 source a k D + 1 → y3 p = y2 p := by
    intro p h1 h2 h3
    rw [hy3, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [copyWSlot] <;> omega)]
  -- the accumulator `[false]`
  have hacc_own : (fSlot source a k D (((xe source a k D (xacc source a k D)).castAdd 2).castAdd 1)).val =
      b5 D + (wtapes source a k D + 1) := by
    rw [fSlot_own _ _ _ _ _ (by simp [xe, xacc]) (by simp [xe, xacc] <;> omega) (by simp [xe, xacc] <;> omega)
      (by simp [xe, xacc] <;> omega) (by simp [xe, xacc] <;> omega)]
    simp [xe, xacc]
  have y2_acc : ∀ p : Fin (G source a k D), (p.val = b5 D + (wtapes source a k D + 1) ∨ p.val = b6 source a k D + 2) →
      y2 p = [] := by
    intro p hp
    rw [hy2, install_off_val _ _ _ _ (by
        intro j
        refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
        · refine Fin.addCases (fun i => ?_) (fun l' => ?_) j'
          · unfold eraseG; rw [eraseSlots_scratch, comb_own]
            unfold comb
            split_ifs with h
            · have := (scratch_iff source a k D (scratch source a k D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
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
  have g9 := (UWalkNumbers.fixed_ready [false]).focus (accSlot source a k D) (accSlot_inj source a k D) y3 (by
    intro j; fin_cases j
    · show y3 (accSlot source a k D 0) = []
      rw [y3_off _ (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega),
        y2_acc _ (Or.inl (by simp [accSlot]))]
    · show y3 (accSlot source a k D 1) = []
      rw [y3_off _ (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega) (by simp [accSlot] <;> omega),
        y2_acc _ (Or.inr (by simp [accSlot]))])
  set y4 := install (accSlot source a k D) y3 ![[false], List.replicate [false].length false] with hy4
  have y4_off : ∀ p : Fin (G source a k D), p.val ≠ b5 D + (wtapes source a k D + 1) → p.val ≠ b6 source a k D + 2 →
      y4 p = y3 p := by
    intro p h1 h2
    rw [hy4, install_off_val _ _ _ _ (by intro j; fin_cases j <;> simp [accSlot] <;> omega)]
  have hE1 : fSlot source a k D (((ee source a k D 1).castAdd 2).castAdd 1) =
      fSlot source a k D (((comb source a k D ⟨ks source a k D, by omega⟩).castAdd 2).castAdd 1) := by
    congr 3; unfold comb; rw [dif_neg (by simp)]; apply Fin.ext; simp [ee_val]
  have hE1v : (fSlot source a k D (((ee source a k D 1).castAdd 2).castAdd 1)).val = b5 D + (xt source a k D + 1) := by
    rw [hE1, comb_own]; unfold comb; rw [dif_neg (by simp)]; simp [ee_val]
  have hE3v : (fSlot source a k D (((ee source a k D 3).castAdd 2).castAdd 1)).val = b5 D + (xt source a k D + 3) := by
    rw [fSlot_own _ _ _ _ _ (by simp [ee_val]) (by simp [ee_val]) (by simp [ee_val]) (by simp [ee_val] <;> omega)
      (by simp [ee_val] <;> omega)]
    simp [ee_val]
  refine ⟨y4, ClockJoin.enlarge _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _ g6 (ClockJoin.join _ _ _ _ _ _ _ g7
    (ClockJoin.join _ _ _ _ _ _ _ g8 g9))) (by simp [initCost]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [y4_off _ (by omega) (by omega)]
    by_cases hw1 : p.val = b2 D + (28 + (26 + 2 * D) + 3)
    · rw [show p = copyWSlot source a k D 0 from Fin.ext (by simp [copyWSlot]; omega), hy3,
        install_slot _ (copyWSlot_inj source a k D),
        show copyWSlot source a k D 0 = gp source a k D (b2 D + (28 + (26 + 2 * D) + 3)) (by omega) from
          Fin.ext (by simp [copyWSlot, gp]), hw]
      simp
    rw [y3_off _ hw1 (by omega) (by omega)]
    by_cases hd : p.val = b4 D + 24
    · rw [show p = gp source a k D (b4 D + 24) (by omega) from Fin.ext (by simp [gp]; omega), y2_drv, hC]
    rw [y2_off _ hp hd]
    by_cases hq1 : p.val = b2 D + 26
    · rw [show p = copyQSlot source a k D 0 from Fin.ext (by simp [copyQSlot]; omega), hy1,
        install_slot _ (copyQSlot_inj source a k D),
        show copyQSlot source a k D 0 = gp source a k D (b2 D + 26) (by omega) from Fin.ext (by simp [copyQSlot, gp]), hq]
      simp
    rw [y1_off _ hq1 (by omega) (by omega)]
  · intro i
    have hcomb : scratch source a k D i = comb source a k D ⟨i.val, by omega⟩ := by
      unfold comb; rw [dif_pos i.isLt]
    have hs := (scratch_iff source a k D (scratch source a k D i)).1 ⟨_, rfl⟩
    rw [hcomb] at hs ⊢
    have hv := comb_own source a k D ⟨i.val, by omega⟩
    have hcl := (comb source a k D ⟨i.val, by omega⟩).isLt
    rw [y4_off _ (by omega) (by omega), y3_off _ (by omega) (by omega) (by omega), y2_comb]
  · rw [y4_off _ (by rw [hE1v]; omega) (by rw [hE1v]; omega), y3_off _ (by rw [hE1v]; omega) (by rw [hE1v]; omega)
      (by rw [hE1v]; omega), hE1, y2_comb]
  · rw [y4_off _ (by rw [hE2v]; omega) (by rw [hE2v]; omega),
      show fSlot source a k D (((ee source a k D 2).castAdd 2).castAdd 1) = copyWSlot source a k D 1 from
        Fin.ext (by rw [hE2v]; simp [copyWSlot]), hy3, install_slot _ (copyWSlot_inj source a k D)]
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
            · have := (scratch_iff source a k D (scratch source a k D ⟨i.val, h⟩)).1 ⟨_, rfl⟩
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
      show fSlot source a k D (((ee source a k D 3).castAdd 2).castAdd 1) = copyQSlot source a k D 1 from
        Fin.ext (by rw [hE3v]; simp [copyQSlot]), hy1, install_slot _ (copyQSlot_inj source a k D)]
    simp
  · rw [show fSlot source a k D (((xe source a k D (xacc source a k D)).castAdd 2).castAdd 1) = accSlot source a k D 0 from
      Fin.ext (by rw [hacc_own]; simp [accSlot]), hy4, install_slot _ (accSlot_inj source a k D)]
    rfl
  · have hcv : (fSlot source a k D ⟨twF source a k D + 1, by omega⟩).val = b5 D + (twF source a k D + 1) := by
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
            have := (comb source a k D i).isLt; omega
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
variable {k} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
  (oracle : BooleanCircuit
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
  (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)

/-- **The fold and the framed output are ready**: on the initialized bank the fold computes the padded XOR power of
the padded request's unsigned honest table at `x`, and the output tape receives its framed bit. -/
theorem post_run (hcoeff : H.coefficient ≤ Cpad) (hD : 1 ≤ D) {N : ℕ} (point : BitInput N)
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    (c C : ℕ) (hfit : c * widthOf source a H Cpad hpad r oracle q hq D ≤ N)
    (htotal : foldNeed source a H Cpad hpad r oracle q hq D point c ≤ C) (Z : Fin (G source a k D) → List Bool)
    (z138 : Z (gp source a k D 138 (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) =
      RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r))
    (z132 : Z (gp source a k D 132 (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) = RepairOrdinary.frame (PCPPNative.descriptor oracle))
    (z2 : Z (gp source a k D 2 (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) = RepairOrdinary.frame (List.ofFn point))
    (zcnt : Z (gp source a k D (b3 D + 1) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) = UnaryTemplate.tape c)
    (zdrv : Z (gp source a k D (b4 D + 24) (by obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D; omega)) = List.replicate C true)
    (zscr : ∀ i : Fin (ks source a k D), Z (fSlot source a k D
        (((scratch source a k D i).castAdd 2).castAdd 1)) = List.replicate C false)
    (zE1 : Z (fSlot source a k D (((ee source a k D 1).castAdd 2).castAdd 1)) = List.replicate C false)
    (zE2 : Z (fSlot source a k D (((ee source a k D 2).castAdd 2).castAdd 1)) =
      ZeroPadding.pad C (List.replicate (widthOf source a H Cpad hpad r oracle q hq D) true))
    (zE3 : Z (fSlot source a k D (((ee source a k D 3).castAdd 2).castAdd 1)) = List.replicate q true)
    (zacc : Z (fSlot source a k D (((xe source a k D (xacc source a k D)).castAdd 2).castAdd 1)) = [false])
    (zcap : Z (fSlot source a k D ⟨twF source a k D + 1, by omega⟩) = List.replicate (C + 1) false)
    (zout : ∀ p : Fin (G source a k D), b6 source a k D + 3 ≤ p.val → Z p = []) :
    ∃ out : Fin (G source a k D) → List Bool,
      ClockJoin.ReadyRun (post source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (foldBudget source a H Cpad hpad r oracle q hq D point c C + 1 + 8) Z out ∧
      out (outSlot source a k D 1) = RepairOrdinary.frame (padCore (xorPower (CloseoutLanguage.paddedUnsigned
        (a.output (wrequest source a H Cpad hpad r oracle q hq)) hcb) c) hfit point).toNat.bits := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D
  have hf := fold_run source a H Cpad hpad r oracle q hq D hcoeff hD point hcb c C (C + 1) hfit htotal le_rfl
  set capF : Fin (twF source a k D + 2 + 1) → ℕ := fun j => if j.val = twF source a k D + 2 then c + 2 else 0
    with hcapF
  have hp := ready_pad _ _ _ _ capF hf
  have g10 := hp.focus (fSlot source a k D) (fSlot_inj source a k D) Z (by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
    · have hc0 : capF (Fin.castAdd 1 j') = 0 := by
        simp only [hcapF, Fin.val_castAdd]; rw [if_neg (by have := j'.isLt; omega)]
      rw [hc0, ZeroPadding.pad_zero, Fin.addCases_left]
      refine Fin.addCases (fun j'' => ?_) (fun l' => ?_) j'
      · simp only [roundTapes, Fin.addCases_left]
        have hjl := j''.isLt
        by_cases hs : ∃ i, scratch source a k D i = j''
        · obtain ⟨i, rfl⟩ := hs
          have hsv := (scratch_iff source a k D (scratch source a k D i)).1 ⟨_, rfl⟩
          rw [padScratch_scr _ _ _ _ ⟨i, rfl⟩,
            roundIn_other source a H Cpad hpad r oracle q hq D point 0 C false _ (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega), zscr i]
          simp [ZeroPadding.pad]
        · rw [padScratch_port _ _ _ _ hs]
          have hsv : ¬ ((2 ≤ j''.val ∧ j''.val ≤ wtapes source a k D) ∨ xt source a k D + 4 ≤ j''.val) :=
            fun h => hs ((scratch_iff source a k D j'').2 h)
          by_cases h0 : j''.val = 0
          · rw [show fSlot source a k D ((j''.castAdd 2).castAdd 1) = gp source a k D 138 (by omega) from
              Fin.ext (by rw [fSlot_val]; simp [h0, gp]), z138, roundIn_val, h0, bankN_hier]
          by_cases h1 : j''.val = 1
          · rw [show fSlot source a k D ((j''.castAdd 2).castAdd 1) = gp source a k D 132 (by omega) from
              Fin.ext (by rw [fSlot_val]; simp [h1, gp]), z132, roundIn_val, h1, bankN_desc]
          by_cases hacc : j''.val = wtapes source a k D + 1
          · rw [show j'' = xe source a k D (xacc source a k D) from Fin.ext (by simp [xe, xacc, hacc]), zacc,
              roundIn_val, show (xe source a k D (xacc source a k D)).val = wtapes source a k D + 1 from rfl, bankN_acc]
          have hport : j''.val = xt source a k D ∨ j''.val = xt source a k D + 1 ∨ j''.val = xt source a k D + 2 ∨
              j''.val = xt source a k D + 3 := by omega
          rcases hport with he | he | he | he
          · rw [show fSlot source a k D ((j''.castAdd 2).castAdd 1) = gp source a k D 2 (by omega) from
              Fin.ext (by rw [fSlot_val]; simp [gp, he] <;> omega), z2,
              show j'' = ee source a k D 0 from Fin.ext (by simp [ee_val, he]), roundIn_e0]
          · rw [show j'' = ee source a k D 1 from Fin.ext (by simp [ee_val, he]), zE1, roundIn_e1]
            simp [ZeroPadding.pad]
          · rw [show j'' = ee source a k D 2 from Fin.ext (by simp [ee_val, he]), zE2, roundIn_e2]
          · rw [show j'' = ee source a k D 3 from Fin.ext (by simp [ee_val, he]), zE3, roundIn_e3]
      · have hl := l'.isLt
        simp only [roundTapes, Fin.addCases_right]
        by_cases hl0 : l'.val = 0
        · have : l' = 0 := Fin.ext hl0
          subst this
          rw [show fSlot source a k D ((Fin.natAdd (twF source a k D) (0 : Fin 2)).castAdd 1) =
              gp source a k D (b4 D + 24) (by omega) from Fin.ext (by
                rw [fSlot_val]; simp only [Fin.val_castAdd, Fin.val_natAdd]
                rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by simp)]; rfl), zdrv]
          rfl
        · have : l' = 1 := Fin.ext (by omega)
          subst this
          rw [show fSlot source a k D ((Fin.natAdd (twF source a k D) (1 : Fin 2)).castAdd 1) =
              fSlot source a k D ⟨twF source a k D + 1, by omega⟩ from Fin.ext (by
                rw [fSlot_val, fSlot_val]; simp), zcap]
          rfl
    · have hl : l = 0 := Subsingleton.elim _ _
      subst hl
      have hcn : capF (Fin.natAdd (twF source a k D + 2) (0 : Fin 1)) = c + 2 := by
        simp only [hcapF, Fin.val_natAdd]; rw [if_pos (by simp)]
      rw [hcn, Fin.addCases_right,
        show fSlot source a k D (Fin.natAdd (twF source a k D + 2) (0 : Fin 1)) = gp source a k D (b3 D + 1) (by omega)
          from Fin.ext (by
            rw [fSlot_val]; simp only [Fin.val_natAdd]
            rw [if_neg (by simp <;> omega), if_neg (by simp <;> omega), if_neg (by simp <;> omega),
              if_neg (by simp <;> omega), if_pos (by simp)]; rfl), zcnt]
      exact (RepairSource.CloseoutCapacity.Power.template_source c).symm)
  set bit := padCore (xorPower (CloseoutLanguage.paddedUnsigned
    (a.output (wrequest source a H Cpad hpad r oracle q hq)) hcb) c) hfit point with hbit
  set Z1 := install (fSlot source a k D) Z (fun j => ZeroPadding.pad (capF j)
    (Fin.addCases (roundTapes (padScratch (scratch source a k D) C
      (roundIn source a H Cpad hpad r oracle q hq D point c C bit)) C (C + 1))
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c) j)) with hZ1
  have hacc_own : (fSlot source a k D (((xe source a k D (xacc source a k D)).castAdd 2).castAdd 1)).val =
      b5 D + (wtapes source a k D + 1) := by
    rw [fSlot_own _ _ _ _ _ (by simp [xe, xacc]) (by simp [xe, xacc] <;> omega) (by simp [xe, xacc] <;> omega)
      (by simp [xe, xacc] <;> omega) (by simp [xe, xacc] <;> omega)]
    simp [xe, xacc]
  have z1acc : Z1 (outSlot source a k D 0) = [bit] := by
    rw [show outSlot source a k D 0 = fSlot source a k D (((xe source a k D (xacc source a k D)).castAdd 2).castAdd 1)
      from Fin.ext (by rw [hacc_own]; simp [outSlot]), hZ1, install_slot _ (fSlot_inj source a k D)]
    have hc0 : capF (((xe source a k D (xacc source a k D)).castAdd 2).castAdd 1) = 0 := by
      simp only [hcapF, Fin.val_castAdd]; rw [if_neg (by simp [xe, xacc]; omega)]
    rw [hc0, ZeroPadding.pad_zero, Fin.addCases_left]
    simp only [roundTapes, Fin.addCases_left]
    have hns : ¬ ∃ i, scratch source a k D i = xe source a k D (xacc source a k D) := by
      rw [scratch_iff]; simp [xe, xacc]; omega
    rw [padScratch_port _ _ _ _ hns, roundIn_val,
      show (xe source a k D (xacc source a k D)).val = wtapes source a k D + 1 from rfl, bankN_acc]
  have z1far : ∀ p : Fin (G source a k D), b6 source a k D + 3 ≤ p.val → Z1 p = [] := by
    intro p hp
    rw [hZ1, install_off_val _ _ _ _ (by
      intro j; have := j.isLt; rw [fSlot_val]; split_ifs <;> omega), zout p hp]
  obtain ⟨o11, r11, o111⟩ := RecoveryCaseOneBooleanOutput.ready bit
  have g11 := r11.focus (outSlot source a k D) (outSlot_inj source a k D) Z1 (by
    intro j; fin_cases j
    · exact z1acc
    · exact z1far _ (by simp [outSlot])
    · exact z1far _ (by simp [outSlot]))
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ g10 g11, ?_⟩
  rw [install_slot _ (outSlot_inj source a k D)]
  exact o111

end Post

/-! ## The whole execution -/

section Whole
variable {k} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
  (oracle : BooleanCircuit
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
  (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)

theorem wrequest_arity : (wrequest source a H Cpad hpad r oracle q hq).arity = max q a.minimumArity := rfl

/-- The fold's block width at a width above the PCPP's minimum arity. -/
theorem widthOf_eq (hmin : a.minimumArity ≤ q) :
    widthOf source a H Cpad hpad r oracle q hq D = q + 1 + CloseoutLanguage.clauseWidth D q := by
  unfold widthOf capOf
  rw [wrequest_arity, max_eq_left hmin]
  omega

/-- The execution's cost. -/
def htwoCost (A u v e1 e2 e3 e4 B : ℕ) {N : ℕ} (point : BitInput N) (c : ℕ) : ℕ :=
  preCost k D A u v e1 e2 e3 e4 B oracle (List.ofFn r.2) (H.time r.1).bits (List.ofFn point) + 1 +
    (initCost q (q + 1 + CloseoutLanguage.clauseWidth D q) (RepairSource.CloseoutCapacity.capacity e4 e4 N) + 1 +
      (foldBudget source a H Cpad hpad r oracle q hq D point c (RepairSource.CloseoutCapacity.capacity e4 e4 N) + 1 + 8))

/-- **The hybrid Case-2 execution is ready**: from base's five cold words (the hierarchy input, the canonical
description of the oracle, the framed address `x`, `1^R`, `1^B`) the machine writes the framed bit
`padCore (xorPower (paddedUnsigned (a.output req) hcb) (t+1)) hfit x` of the padded request `req` at the width
`q = q(2^S)`, `S = prefixS … |x|`, `t = candT … S … |x|`, given the parameter core's capacities, the fit of the
`t + 1` blocks, and the fold's capacity bound `foldNeed ≤ C`. -/
theorem htwo_run (A u v e1 e2 e3 e4 : ℕ) (hcoeff : H.coefficient ≤ Cpad) (hD : 1 ≤ D) {B : ℕ}
    (hc : oracle.size ≤ B) {N : ℕ} (point : BitInput N)
    (hqS : q = widthAt k A (CertPrefix.prefixS k A u v D N)) (hmin : a.minimumArity ≤ q)
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    (hfit : (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) *
      widthOf source a H Cpad hpad r oracle q hq D ≤ N)
    (htotal : foldNeed source a H Cpad hpad r oracle q hq D point
      (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1) ≤
        RepairSource.CloseoutCapacity.capacity e4 e4 N)
    (hn : N ≤ pcap e1 N)
    (hvals : ∀ a', a' ≤ N → ∀ i, i ≤ N →
      candA0 k A u v a' * ((v - u) ^ 16) ^ i ≤ pcap e1 N ∧ candB0 v * (v ^ 16) ^ i ≤ pcap e1 N ∧ 1 + i ≤ pcap e1 N)
    (hT : max (pcap e1 N + 1) (max ((v - u) ^ 16 + 1) (v ^ 16 + 1)) ≤ pcap e2 N)
    (hTc : roundCostBound ((v - u) ^ 16) (v ^ 16) (pcap e1 N) + 1 ≤ pcap e2 N)
    (hTs : pcap e2 N + 1 + N + N + 1 ≤ pcap e3 N)
    (hTs' : scanRoundBound k A v D N N ((v - u) ^ 16) (v ^ 16) (pcap e1 N) (pcap e2 N) N + 1 ≤ pcap e3 N) :
    ∃ out : Fin (G source a k D) → List Bool,
      ClockJoin.ReadyRun (htwo source a k D A u v e1 e2 e3 e4 H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (htwoCost source a D H Cpad hpad r oracle q hq A u v e1 e2 e3 e4 B point
          (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1))
        (htwoIn source a k D (HierarchySourceInput.hierarchyInput H r)
          (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription B oracle))
          (RepairOrdinary.frame (List.ofFn point))
          (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) B) out ∧
      out (outSlot source a k D 1) = RepairOrdinary.frame (padCore (xorPower (CloseoutLanguage.paddedUnsigned
        (a.output (wrequest source a H Cpad hpad r oracle q hq)) hcb)
          (candT k A u v (CertPrefix.prefixS k A u v D N) ((v - u) ^ 16) (v ^ 16) N + 1)) hfit point).toNat.bits := by
  obtain ⟨hpt, hpw, htw, hwt, hxt, hb2, hb3, hb4, hb5, hb6, hG⟩ := layout_all source a k D
  have hlen : (List.ofFn point).length = N := List.length_ofFn
  obtain ⟨X, hX, x138, x132, x2, xq, xw, xcnt, xdrv, xfresh⟩ := pre_run source a k D A u v e1 e2 e3 e4 hD oracle hc
    (List.ofFn r.2) (H.time r.1).bits (List.ofFn point) (by rw [hlen]; exact hn) (by rw [hlen]; exact hvals)
    (by rw [hlen]; exact hT) (by rw [hlen]; exact hTc) (by rw [hlen]; exact hTs) (by rw [hlen]; exact hTs')
  rw [hlen] at xq xw xcnt xdrv
  rw [← hqS] at xq xw
  obtain ⟨Y, hY, ylow, yscr, yE1, yE2, yE3, yacc, ycap, yfar⟩ := init_run source a k D q
    (q + 1 + CloseoutLanguage.clauseWidth D q) (RepairSource.CloseoutCapacity.capacity e4 e4 N) X xq xw xdrv xfresh
  obtain ⟨Z, hZ, zo⟩ := post_run source a D H Cpad hpad r oracle q hq hcoeff hD point hcb _ _ hfit htotal Y
    (by rw [ylow _ (by simp [gp] <;> omega)]; exact x138) (by rw [ylow _ (by simp [gp] <;> omega)]; exact x132)
    (by rw [ylow _ (by simp [gp] <;> omega)]; exact x2) (by rw [ylow _ (by simp [gp] <;> omega)]; exact xcnt)
    (by rw [ylow _ (by simp [gp] <;> omega)]; exact xdrv) yscr yE1 (by rw [yE2, widthOf_eq source a D H Cpad hpad r oracle q hq hmin])
    yE3 yacc ycap (fun p hp => (yfar p hp).trans (xfresh p (by omega)))
  refine ⟨Z, ?_, zo⟩
  have e : HierarchySourceInput.hierarchyInput H r =
      RepairOrdinary.frame (List.ofFn r.2) ++ RepairOrdinary.frame (H.time r.1).bits := rfl
  rw [e]
  unfold htwo htwoCost
  exact ClockJoin.join _ _ _ _ _ _ _ hX (ClockJoin.join _ _ _ _ _ _ _ hY hZ)

end Whole

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoExec
