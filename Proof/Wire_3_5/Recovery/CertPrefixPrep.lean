import Proof.Wire_3_5.Recovery.CertPrefixBounds

/-! # The prefix's preparation from the input word (P3:3758-3759; D1.6, the prefix stage)

Realizes the first step of the `E^NP` program on an input `x` of length `n`: everything the scan needs is computed from
the framed word alone. Base's `HierarchyAllocation` (at `1·n + 0`) gives `1^n` and the word `0 1^n` (twice: the scan's
counter and the schedule loop's counter, `c = n`); base's `CloseoutCapacity.machine` gives the drivers `1^{C_i}` of the
three capacities (`pcap e_i n`, `Proof.Wire_3_5.Recovery.CertPrefixBounds`); base's `HierarchyFixedWord` writes the words
`0 1^p`, `0 1^w`; base's `RecoveryScratchErase` turns the empty banks into `false`-padded ones (`C₁` for the scan
index, `C₂` for the schedule round's scratch, `C₃` for the scan round's scratch) and produces the capacity tapes.

Paper quantity: the prefix's initial configuration; **`prepMachine`** on `prefixTapes D` tapes and **`prep_run`**: from
`frame x` on tape 0 it halts with `frame x` kept and the scan block (tapes `1 … scanTapes D + 3`) holding exactly the
scan loop's input at `S = 0` (`scanLoopInput`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutSchedule (Clause.tapes)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-- Evaluate an erase machine's tapes by value. -/
theorem erase_tapes_val {t : ℕ} (backing : Fin t → List Bool) (X Y : List Bool) (j : Fin (t + 1 + 1)) :
    Fin.addCases (motive := fun _ => List Bool) (Fin.addCases (motive := fun _ => List Bool) backing
      (fun _ : Fin 1 => X)) (fun _ : Fin 1 => Y) j =
      if h : j.val < t then backing ⟨j.val, h⟩ else if j.val = t then X else Y := by
  refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun l => ?_) j'
    · simp
    · have := l.isLt; simp
  · have := l.isLt; simp

/-- An install leaves every position outside its slots' values unchanged. -/
theorem install_off_val {t u : ℕ} (slot : Fin t → Fin u) (amb : Fin u → List Bool) (out : Fin t → List Bool)
    (p : Fin u) (h : ∀ j, (slot j).val ≠ p.val) : install slot amb out p = amb p :=
  install_other _ _ _ _ (fun j => fin_ne (h j))

section Prep
variable (D : ℕ)

theorem scanTapes_eq : scanTapes D = Clause.tapes D + 119 := by unfold scanTapes candTapes; omega

/-- The prefix's tape count: the input, the scan block, and 120 work tapes. -/
def prefixTapes : ℕ := scanTapes D + 124

/-- The first allocation: `1^n` onto the scan's `n` port (2), the word `0 1^n` onto the scan's counter. -/
def slA1 (i : Fin 10) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 0 else if i.val = 3 then scanTapes D + 3 else if i.val = 8 then 2 else scanTapes D + 4 + i.val,
    by have := i.isLt; unfold prefixTapes; split_ifs <;> omega⟩
/-- The second allocation: the word `0 1^n` onto the schedule loop's counter (35). -/
def slA2 (i : Fin 10) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 0 else if i.val = 3 then 35 else scanTapes D + 14 + i.val,
    by have := i.isLt; unfold prefixTapes; split_ifs <;> omega⟩
/-- The capacity producers: `1^{C₁}` onto 8, `1^{C₂}` onto 33, `1^{C₃}` onto `scanTapes D + 1`. -/
def slC1 (i : Fin 26) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 0 else if i.val = 24 then 8 else scanTapes D + 24 + i.val,
    by have := i.isLt; unfold prefixTapes; split_ifs <;> omega⟩
def slC2 (i : Fin 26) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 0 else if i.val = 24 then 33 else scanTapes D + 50 + i.val,
    by have := i.isLt; unfold prefixTapes; split_ifs <;> omega⟩
def slC3 (i : Fin 26) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 0 else if i.val = 24 then scanTapes D + 1 else scanTapes D + 76 + i.val,
    by have := i.isLt; unfold prefixTapes; split_ifs <;> omega⟩
/-- The fixed words `0 1^p` (onto 6) and `0 1^w` (onto 7). -/
def slP (i : Fin 2) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 6 else scanTapes D + 102, by unfold prefixTapes; split_ifs <;> omega⟩
def slW (i : Fin 2) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 7 else scanTapes D + 103, by unfold prefixTapes; split_ifs <;> omega⟩
/-- The erases: the scan index (1) with driver 8 and capacity tape 9; the schedule round's scratch (10–32) with
driver 33 and capacity tape 34; the scan round's scratch (36–`scanTapes D`) with its driver and capacity tape. -/
def slE1 (i : Fin (1 + 1 + 1)) : Fin (prefixTapes D) :=
  ⟨if i.val = 0 then 1 else if i.val = 1 then 8 else 9, by unfold prefixTapes; split_ifs <;> omega⟩
def slE2 (i : Fin (23 + 1 + 1)) : Fin (prefixTapes D) :=
  ⟨if i.val < 23 then 10 + i.val else if i.val = 23 then 33 else 34,
    by have := i.isLt; unfold prefixTapes; split_ifs <;> omega⟩
def slE3 (i : Fin (Clause.tapes D + 84 + 1 + 1)) : Fin (prefixTapes D) :=
  ⟨if i.val < Clause.tapes D + 84 then 36 + i.val else if i.val = Clause.tapes D + 84 then scanTapes D + 1
    else scanTapes D + 2, by have := i.isLt; have := scanTapes_eq D; unfold prefixTapes; split_ifs <;> omega⟩
/-- The scan block. -/
def slS (i : Fin (scanTapes D + 2 + 1)) : Fin (prefixTapes D) :=
  ⟨1 + i.val, by have := i.isLt; unfold prefixTapes; omega⟩

/-- Injectivity of a slot map of the prefix from its values. -/
macro "cert_prefix_inj" : tactic => `(tactic| (intro a b h; have hv := congrArg Fin.val h; simp only [slA1, slA2, slC1, slC2, slC3, slP, slW, slE1, slE2, slE3, slS, Fin.val_mk, scanTapes_eq] at hv; apply Fin.ext; split_ifs at hv <;> omega))

theorem slA1_inj : Function.Injective (slA1 D) := by cert_prefix_inj
theorem slA2_inj : Function.Injective (slA2 D) := by cert_prefix_inj
theorem slC1_inj : Function.Injective (slC1 D) := by cert_prefix_inj
theorem slC2_inj : Function.Injective (slC2 D) := by cert_prefix_inj
theorem slC3_inj : Function.Injective (slC3 D) := by cert_prefix_inj
theorem slP_inj : Function.Injective (slP D) := by cert_prefix_inj
theorem slW_inj : Function.Injective (slW D) := by cert_prefix_inj
theorem slE1_inj : Function.Injective (slE1 D) := by cert_prefix_inj
theorem slE2_inj : Function.Injective (slE2 D) := by cert_prefix_inj
theorem slE3_inj : Function.Injective (slE3 D) := by cert_prefix_inj
theorem slS_inj : Function.Injective (slS D) := by
  intro a b h; have hv := congrArg Fin.val h; simp only [slS, Fin.val_mk] at hv; exact Fin.ext (by omega)

/-- **The preparation, part A**: the allocations and the capacity producers. -/
noncomputable def prepA (e1 e2 e3 : ℕ) :=
  Composition.machine (RecoveryFocus.machine (slA1 D) (HierarchyAllocation.machine 1 0))
  (Composition.machine (RecoveryFocus.machine (slA2 D) (HierarchyAllocation.machine 1 0))
  (Composition.machine (RecoveryFocus.machine (slC1 D) (RepairSource.CloseoutCapacity.machine e1 e1))
  (Composition.machine (RecoveryFocus.machine (slC2 D) (RepairSource.CloseoutCapacity.machine e2 e2))
    (RecoveryFocus.machine (slC3 D) (RepairSource.CloseoutCapacity.machine e3 e3)))))

/-- **The preparation, part B**: the fixed words and the erases. -/
noncomputable def prepB (p w : ℕ) :=
  Composition.machine (RecoveryFocus.machine (slP D) (HierarchyFixedWord.machine (CompareMachine.word p)))
  (Composition.machine (RecoveryFocus.machine (slW D) (HierarchyFixedWord.machine (CompareMachine.word w)))
  (Composition.machine (RecoveryFocus.machine (slE1 D) (RecoveryScratchErase.resetMachine 1))
  (Composition.machine (RecoveryFocus.machine (slE2 D) (RecoveryScratchErase.resetMachine 23))
    (RecoveryFocus.machine (slE3 D) (RecoveryScratchErase.resetMachine (Clause.tapes D + 84))))))

/-- **The preparation**. -/
noncomputable def prepMachine (p w e1 e2 e3 : ℕ) := Composition.machine (prepA D e1 e2 e3) (prepB D p w)

/-- The prefix's input: `frame x` on tape 0. -/
def prefixInput (bits : List Bool) : Fin (prefixTapes D) → List Bool := fun i => if i.val = 0 then frame bits else []

/-- The scan loop's input at `S = 0` with the capacities `C₁, C₂, C₃` (`scanLoop_ready` at `nr = c = n`). -/
noncomputable def scanLoopInput (n p w C1 C2 C3 : ℕ) : Fin (scanTapes D + 2 + 1) → List Bool :=
  Fin.addCases (roundTapes (padScratch (scanScratch D) C3 (scanInput D 0 n [] [] [] p w C1 (C1 + 1) C2 (C2 + 1) n))
    C3 (C3 + 1)) (fun _ => CompareMachine.word n)

/-- The preparation's costs. -/
def prepCostA (e1 e2 e3 : ℕ) (bits : List Bool) : ℕ :=
  HierarchyAllocation.budget 1 0 bits + 1 + (HierarchyAllocation.budget 1 0 bits + 1 +
  (RepairSource.CloseoutCapacity.budget e1 e1 bits + 1 + (RepairSource.CloseoutCapacity.budget e2 e2 bits + 1 +
  RepairSource.CloseoutCapacity.budget e3 e3 bits)))
def prepCostB (p w C1 C2 C3 : ℕ) : ℕ :=
  (2 * (CompareMachine.word p).length + 2) + 1 + ((2 * (CompareMachine.word w).length + 2) + 1 +
  ((2 * C1 + 4) + 1 + ((2 * C2 + 4) + 1 + (2 * C3 + 4))))

end Prep

/-! ## Which positions each stage leaves alone -/

section Off
variable (D : ℕ)

macro "cert_prefix_off" : tactic => `(tactic| (intro j; have := j.isLt; simp only [slA1, slA2, slC1, slC2, slC3, slP, slW, slE1, slE2, slE3, Fin.val_mk, scanTapes_eq] at *; split_ifs <;> omega))

theorem slA1_off (p : Fin (prefixTapes D)) (h : p.val ≠ 0 ∧ p.val ≠ 2 ∧ (p.val < scanTapes D + 3 ∨ scanTapes D + 13 < p.val)) :
    ∀ j, (slA1 D j).val ≠ p.val := by cert_prefix_off
theorem slA2_off (p : Fin (prefixTapes D)) (h : p.val ≠ 0 ∧ p.val ≠ 35 ∧ (p.val < scanTapes D + 15 ∨ scanTapes D + 23 < p.val)) :
    ∀ j, (slA2 D j).val ≠ p.val := by cert_prefix_off
theorem slC1_off (p : Fin (prefixTapes D)) (h : p.val ≠ 0 ∧ p.val ≠ 8 ∧ (p.val < scanTapes D + 25 ∨ scanTapes D + 49 < p.val)) :
    ∀ j, (slC1 D j).val ≠ p.val := by cert_prefix_off
theorem slC2_off (p : Fin (prefixTapes D)) (h : p.val ≠ 0 ∧ p.val ≠ 33 ∧ (p.val < scanTapes D + 51 ∨ scanTapes D + 75 < p.val)) :
    ∀ j, (slC2 D j).val ≠ p.val := by cert_prefix_off
theorem slC3_off (p : Fin (prefixTapes D)) (h : p.val ≠ 0 ∧ p.val ≠ scanTapes D + 1 ∧ (p.val < scanTapes D + 77 ∨ scanTapes D + 101 < p.val)) :
    ∀ j, (slC3 D j).val ≠ p.val := by cert_prefix_off
theorem slP_off (p : Fin (prefixTapes D)) (h : p.val ≠ 6 ∧ p.val ≠ scanTapes D + 102) :
    ∀ j, (slP D j).val ≠ p.val := by cert_prefix_off
theorem slW_off (p : Fin (prefixTapes D)) (h : p.val ≠ 7 ∧ p.val ≠ scanTapes D + 103) :
    ∀ j, (slW D j).val ≠ p.val := by cert_prefix_off
theorem slE1_off (p : Fin (prefixTapes D)) (h : p.val ≠ 1 ∧ p.val ≠ 8 ∧ p.val ≠ 9) :
    ∀ j, (slE1 D j).val ≠ p.val := by cert_prefix_off
theorem slE2_off (p : Fin (prefixTapes D)) (h : p.val < 10 ∨ 35 ≤ p.val) :
    ∀ j, (slE2 D j).val ≠ p.val := by cert_prefix_off
theorem slE3_off (p : Fin (prefixTapes D)) (h : p.val < 36 ∨ scanTapes D + 3 ≤ p.val) :
    ∀ j, (slE3 D j).val ≠ p.val := by cert_prefix_off

end Off

/-! ## The preparation's run -/

/-- Evaluate a loop's tapes (a round's tapes and the counter) by value. -/
theorem loopIn_val {tw : ℕ} (X : Fin tw → List Bool) (T cap : ℕ) (wd : List Bool) (i : Fin (tw + 2 + 1)) :
    Fin.addCases (motive := fun _ => List Bool) (roundTapes X T cap) (fun _ : Fin 1 => wd) i =
      if h : i.val < tw then X ⟨i.val, h⟩ else if i.val = tw then List.replicate T true
      else if i.val = tw + 1 then List.replicate cap false else wd := by
  refine Fin.addCases (fun i' => ?_) (fun l => ?_) i
  · simp only [Fin.addCases_left, roundTapes]
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i'
    · simp
    · fin_cases l <;> simp
  · fin_cases l; simp

macro "cert_prefix_vtac" : tactic => `(tactic| (first | omega | (simp <;> omega) | simp))

section Run
variable (D : ℕ)

theorem scratchCap_scan (T : ℕ) (i : Fin (scanTapes D)) :
    scratchCap (scanScratch D) T i = if 35 ≤ i.val then T else 0 := by
  unfold scratchCap
  by_cases h : 35 ≤ i.val
  · rw [if_pos ⟨⟨i.val - 35, by have := i.isLt; have := scanTapes_eq D; omega⟩,
      Fin.ext (by simp [scanScratch]; omega)⟩, if_pos h]
  · rw [if_neg (by rintro ⟨j, hj⟩; have := congrArg Fin.val hj; simp [scanScratch] at this; omega), if_neg h]

theorem scanInput_mid (S n : ℕ) (Ap Bp Ep : List Bool) (p w total capT T capF c v : ℕ) (h : v < scanTapes D)
    (h2 : 2 ≤ v) (h35 : v < 35) :
    scanInput D S n Ap Bp Ep p w total capT T capF c ⟨v, h⟩ =
      innerTapes Ap Bp Ep p w total capT T capF c ⟨v - 2, by omega⟩ := by
  simp only [scanInput]; rw [if_neg (by omega), if_neg (by omega), dif_pos ⟨h2, h35⟩]

/-- The scan loop's input by value (positions below 35 of the round, the scratch, the drivers, the counter). -/
theorem scanLoopInput_low (n p w C1 C2 C3 : ℕ) (i : Fin (scanTapes D + 2 + 1)) (hi : i.val < 35) :
    scanLoopInput D n p w C1 C2 C3 i =
      scanInput D 0 n [] [] [] p w C1 (C1 + 1) C2 (C2 + 1) n ⟨i.val, by have := scanTapes_eq D; omega⟩ := by
  unfold scanLoopInput
  rw [loopIn_val, dif_pos (by have := scanTapes_eq D; omega)]
  simp only [padScratch]
  rw [scratchCap_scan, if_neg (by simp; omega)]
  simp [ZeroPadding.pad]

theorem scanLoopInput_scratch (n p w C1 C2 C3 : ℕ) (i : Fin (scanTapes D + 2 + 1)) (hi : 35 ≤ i.val)
    (hi' : i.val < scanTapes D) : scanLoopInput D n p w C1 C2 C3 i = List.replicate C3 false := by
  unfold scanLoopInput
  rw [loopIn_val, dif_pos hi']
  simp only [padScratch]
  rw [scratchCap_scan, if_pos (by simp; omega), scanInput_fresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp; omega)]
  simp [ZeroPadding.pad]

theorem scanLoopInput_top (n p w C1 C2 C3 : ℕ) (i : Fin (scanTapes D + 2 + 1)) (hi : scanTapes D ≤ i.val) :
    scanLoopInput D n p w C1 C2 C3 i = if i.val = scanTapes D then List.replicate C3 true
      else if i.val = scanTapes D + 1 then List.replicate (C3 + 1) false else CompareMachine.word n := by
  unfold scanLoopInput
  rw [loopIn_val, dif_neg (by omega)]

end Run

/-! ## The two parts of the preparation -/

section Parts
variable (D : ℕ)

/-- A fixed position of the prefix. -/
def ppos (m : ℕ) (h : m < prefixTapes D) : Fin (prefixTapes D) := ⟨m, h⟩

macro "cert_prefix_ptac" : tactic => `(tactic| (first | (simp only [ppos, Fin.val_mk]; omega) | simp [ppos] | (simp [ppos] <;> omega)))

theorem alloc_out0 (bits : List Bool) : HierarchyAllocation.output 1 0 bits 0 = frame bits := by
  simp [HierarchyAllocation.output, HierarchyAllocation.afterConstant, HierarchyAllocation.afterProduct,
    HierarchyAllocation.afterEll, HierarchyAllocation.afterDegree, HierarchyAllocation.input]
theorem alloc_out3 (bits : List Bool) : HierarchyAllocation.output 1 0 bits 3 = CompareMachine.word bits.length := by
  simp [HierarchyAllocation.output, HierarchyAllocation.afterConstant, HierarchyAllocation.afterProduct,
    HierarchyAllocation.afterEll, CompareMachine.word]
theorem alloc_out8 (bits : List Bool) : HierarchyAllocation.output 1 0 bits 8 = List.replicate bits.length true := by
  simp [HierarchyAllocation.output]

/-- The state after part A. -/
def specA (bits : List Bool) (C1 C2 C3 : ℕ) (a : Fin (prefixTapes D) → List Bool) : Prop :=
  a (ppos D 0 (by unfold prefixTapes; omega)) = frame bits ∧
  a (ppos D 2 (by unfold prefixTapes; omega)) = List.replicate bits.length true ∧
  a (ppos D 35 (by unfold prefixTapes; omega)) = CompareMachine.word bits.length ∧
  a (ppos D (scanTapes D + 3) (by unfold prefixTapes; omega)) = CompareMachine.word bits.length ∧
  a (ppos D 8 (by unfold prefixTapes; omega)) = List.replicate C1 true ∧
  a (ppos D 33 (by unfold prefixTapes; omega)) = List.replicate C2 true ∧
  a (ppos D (scanTapes D + 1) (by unfold prefixTapes; omega)) = List.replicate C3 true ∧
  (∀ q : Fin (prefixTapes D), q.val ≠ 0 → q.val ≠ 2 → q.val ≠ 8 → q.val ≠ 33 → q.val ≠ 35 →
    q.val ≠ scanTapes D + 1 → (q.val < scanTapes D + 3 ∨ scanTapes D + 101 < q.val) → a q = [])

/-- **Part A is ready.** -/
theorem partA_run (e1 e2 e3 : ℕ) (bits : List Bool) : ∃ out : Fin (prefixTapes D) → List Bool,
    ClockJoin.ReadyRun (prepA D e1 e2 e3) (prepCostA e1 e2 e3 bits) (prefixInput D bits) out ∧
    specA D bits (pcap e1 bits.length) (pcap e2 bits.length) (pcap e3 bits.length) out := by
  set x := prefixInput D bits with hx
  have hST := scanTapes_eq D
  set z : Fin (prefixTapes D) := ppos D 0 (by unfold prefixTapes; omega) with hz
  have hx0 : ∀ q : Fin (prefixTapes D), q.val ≠ 0 → x q = [] := fun q h => by simp [hx, prefixInput, h]
  have hxz : x z = frame bits := by simp [hx, prefixInput, hz, ppos]
  have g1 := (HierarchyAllocation.allocation_ready 1 0 bits).focus (slA1 D) (slA1_inj D) x (by
    intro j
    by_cases hj : j.val = 0
    · rw [show slA1 D j = z from Fin.ext (by simp [slA1, hj, hz, ppos]), hxz]
      simp [HierarchyAllocation.input, hj]
    · rw [hx0 _ (by simp only [slA1, Fin.val_mk]; split_ifs <;> omega)]
      simp [HierarchyAllocation.input, hj])
  set a1 := install (slA1 D) x (HierarchyAllocation.output 1 0 bits) with ha1
  have b1 : ∀ q : Fin (prefixTapes D), q.val ≠ 0 ∧ q.val ≠ 2 ∧ (q.val < scanTapes D + 3 ∨ scanTapes D + 13 < q.val) →
      a1 q = x q := fun q h => install_off_val _ _ _ _ (slA1_off D q h)
  have a1z : a1 z = frame bits := by
    rw [ha1, show z = slA1 D 0 from Fin.ext (by simp [slA1, hz, ppos]), install_slot _ (slA1_inj D), alloc_out0]
  have g2 := (HierarchyAllocation.allocation_ready 1 0 bits).focus (slA2 D) (slA2_inj D) a1 (by
    intro j
    by_cases hj : j.val = 0
    · rw [show slA2 D j = z from Fin.ext (by simp [slA2, hj, hz, ppos]), a1z]
      simp [HierarchyAllocation.input, hj]
    · rw [b1 _ (by simp only [slA2, Fin.val_mk]; split_ifs <;> omega),
        hx0 _ (by simp only [slA2, Fin.val_mk]; split_ifs <;> omega)]
      simp [HierarchyAllocation.input, hj])
  set a2 := install (slA2 D) a1 (HierarchyAllocation.output 1 0 bits) with ha2
  have b2 : ∀ q : Fin (prefixTapes D), q.val ≠ 0 ∧ q.val ≠ 35 ∧ (q.val < scanTapes D + 15 ∨ scanTapes D + 23 < q.val) →
      a2 q = a1 q := fun q h => install_off_val _ _ _ _ (slA2_off D q h)
  have a2z : a2 z = frame bits := by
    rw [ha2, show z = slA2 D 0 from Fin.ext (by simp [slA2, hz, ppos]), install_slot _ (slA2_inj D), alloc_out0]
  obtain ⟨o3, r3, o3d, -, o3z⟩ := RepairSource.CloseoutCapacity.capacity_run e1 e1 bits
  have g3 := r3.focus (slC1 D) (slC1_inj D) a2 (by
    intro j
    by_cases hj : j.val = 0
    · rw [show slC1 D j = z from Fin.ext (by simp [slC1, hj, hz, ppos]), a2z]
      simp [RepairSource.CloseoutCapacity.input, hj]
    · rw [b2 _ (by simp only [slC1, Fin.val_mk]; split_ifs <;> omega),
        b1 _ (by simp only [slC1, Fin.val_mk]; split_ifs <;> omega),
        hx0 _ (by simp only [slC1, Fin.val_mk]; split_ifs <;> omega)]
      simp [RepairSource.CloseoutCapacity.input, hj])
  set a3 := install (slC1 D) a2 o3 with ha3
  have b3 : ∀ q : Fin (prefixTapes D), q.val ≠ 0 ∧ q.val ≠ 8 ∧ (q.val < scanTapes D + 25 ∨ scanTapes D + 49 < q.val) →
      a3 q = a2 q := fun q h => install_off_val _ _ _ _ (slC1_off D q h)
  have a3z : a3 z = frame bits := by
    rw [ha3, show z = slC1 D 0 from Fin.ext (by simp [slC1, hz, ppos]), install_slot _ (slC1_inj D), o3z]
  obtain ⟨o4, r4, o4d, -, o4z⟩ := RepairSource.CloseoutCapacity.capacity_run e2 e2 bits
  have g4 := r4.focus (slC2 D) (slC2_inj D) a3 (by
    intro j
    by_cases hj : j.val = 0
    · rw [show slC2 D j = z from Fin.ext (by simp [slC2, hj, hz, ppos]), a3z]
      simp [RepairSource.CloseoutCapacity.input, hj]
    · rw [b3 _ (by simp only [slC2, Fin.val_mk]; split_ifs <;> omega),
        b2 _ (by simp only [slC2, Fin.val_mk]; split_ifs <;> omega),
        b1 _ (by simp only [slC2, Fin.val_mk]; split_ifs <;> omega),
        hx0 _ (by simp only [slC2, Fin.val_mk]; split_ifs <;> omega)]
      simp [RepairSource.CloseoutCapacity.input, hj])
  set a4 := install (slC2 D) a3 o4 with ha4
  have b4 : ∀ q : Fin (prefixTapes D), q.val ≠ 0 ∧ q.val ≠ 33 ∧ (q.val < scanTapes D + 51 ∨ scanTapes D + 75 < q.val) →
      a4 q = a3 q := fun q h => install_off_val _ _ _ _ (slC2_off D q h)
  have a4z : a4 z = frame bits := by
    rw [ha4, show z = slC2 D 0 from Fin.ext (by simp [slC2, hz, ppos]), install_slot _ (slC2_inj D), o4z]
  obtain ⟨o5, r5, o5d, -, o5z⟩ := RepairSource.CloseoutCapacity.capacity_run e3 e3 bits
  have g5 := r5.focus (slC3 D) (slC3_inj D) a4 (by
    intro j
    by_cases hj : j.val = 0
    · rw [show slC3 D j = z from Fin.ext (by simp [slC3, hj, hz, ppos]), a4z]
      simp [RepairSource.CloseoutCapacity.input, hj]
    · rw [b4 _ (by simp only [slC3, Fin.val_mk]; split_ifs <;> omega),
        b3 _ (by simp only [slC3, Fin.val_mk]; split_ifs <;> omega),
        b2 _ (by simp only [slC3, Fin.val_mk]; split_ifs <;> omega),
        b1 _ (by simp only [slC3, Fin.val_mk]; split_ifs <;> omega),
        hx0 _ (by simp only [slC3, Fin.val_mk]; split_ifs <;> omega)]
      simp [RepairSource.CloseoutCapacity.input, hj])
  set a5 := install (slC3 D) a4 o5 with ha5
  have b5 : ∀ q : Fin (prefixTapes D), q.val ≠ 0 ∧ q.val ≠ scanTapes D + 1 ∧
      (q.val < scanTapes D + 77 ∨ scanTapes D + 101 < q.val) → a5 q = a4 q :=
    fun q h => install_off_val _ _ _ _ (slC3_off D q h)
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2 (ClockJoin.join _ _ _ _ _ _ _ g3
    (ClockJoin.join _ _ _ _ _ _ _ g4 g5))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha5, show ppos D 0 _ = slC3 D 0 from Fin.ext (by simp [slC3, ppos]), install_slot _ (slC3_inj D), o5z]
  · rw [b5 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b4 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b3 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b2 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, ha1,
      show ppos D 2 _ = slA1 D 8 from Fin.ext (by simp [slA1, ppos]), install_slot _ (slA1_inj D), alloc_out8]
  · rw [b5 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b4 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b3 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, ha2,
      show ppos D 35 _ = slA2 D 3 from Fin.ext (by simp [slA2, ppos]), install_slot _ (slA2_inj D), alloc_out3]
  · rw [b5 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b4 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b3 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b2 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, ha1,
      show ppos D (scanTapes D + 3) _ = slA1 D 3 from Fin.ext (by simp [slA1, ppos]), install_slot _ (slA1_inj D),
      alloc_out3]
  · rw [b5 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b4 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, ha3,
      show ppos D 8 _ = slC1 D 24 from Fin.ext (by simp [slC1, ppos]), install_slot _ (slC1_inj D), o3d]
    rfl
  · rw [b5 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, ha4,
      show ppos D 33 _ = slC2 D 24 from Fin.ext (by simp [slC2, ppos]), install_slot _ (slC2_inj D), o4d]
    rfl
  · rw [ha5, show ppos D (scanTapes D + 1) _ = slC3 D 24 from Fin.ext (by simp [slC3, ppos]),
      install_slot _ (slC3_inj D), o5d]
    rfl
  · intro q h0 h2 h8 h33 h35 h1 hr
    rw [b5 q ⟨h0, h1, by omega⟩, b4 q ⟨h0, h33, by omega⟩, b3 q ⟨h0, h8, by omega⟩, b2 q ⟨h0, h35, by omega⟩,
      b1 q ⟨h0, h2, by omega⟩, hx0 q h0]

end Parts

section PartB
variable (D : ℕ)

/-- The state after part B (the scan block by values, the frame, and the empty top). -/
def specB (bits : List Bool) (p w C1 C2 C3 : ℕ) (a : Fin (prefixTapes D) → List Bool) : Prop :=
  a (ppos D 0 (by unfold prefixTapes; omega)) = frame bits ∧
  a (ppos D 1 (by unfold prefixTapes; omega)) = List.replicate C1 false ∧
  a (ppos D 2 (by unfold prefixTapes; omega)) = List.replicate bits.length true ∧
  (∀ q : Fin (prefixTapes D), 3 ≤ q.val → q.val ≤ 5 → a q = []) ∧
  a (ppos D 6 (by unfold prefixTapes; omega)) = CompareMachine.word p ∧
  a (ppos D 7 (by unfold prefixTapes; omega)) = CompareMachine.word w ∧
  a (ppos D 8 (by unfold prefixTapes; omega)) = List.replicate C1 true ∧
  a (ppos D 9 (by unfold prefixTapes; omega)) = List.replicate (max 0 (C1 + 1)) false ∧
  (∀ q : Fin (prefixTapes D), 10 ≤ q.val → q.val ≤ 32 → a q = List.replicate C2 false) ∧
  a (ppos D 33 (by unfold prefixTapes; omega)) = List.replicate C2 true ∧
  a (ppos D 34 (by unfold prefixTapes; omega)) = List.replicate (max 0 (C2 + 1)) false ∧
  a (ppos D 35 (by unfold prefixTapes; omega)) = CompareMachine.word bits.length ∧
  (∀ q : Fin (prefixTapes D), 36 ≤ q.val → q.val ≤ scanTapes D → a q = List.replicate C3 false) ∧
  a (ppos D (scanTapes D + 1) (by unfold prefixTapes; omega)) = List.replicate C3 true ∧
  a (ppos D (scanTapes D + 2) (by unfold prefixTapes; omega)) = List.replicate (max 0 (C3 + 1)) false ∧
  a (ppos D (scanTapes D + 3) (by unfold prefixTapes; omega)) = CompareMachine.word bits.length ∧
  (∀ q : Fin (prefixTapes D), scanTapes D + 104 ≤ q.val → a q = [])

/-- **Part B is ready** from the state after part A. -/
theorem partB_run (p w : ℕ) (bits : List Bool) (C1 C2 C3 : ℕ) (a : Fin (prefixTapes D) → List Bool)
    (hA : specA D bits C1 C2 C3 a) : ∃ out : Fin (prefixTapes D) → List Bool,
    ClockJoin.ReadyRun (prepB D p w) (prepCostB p w C1 C2 C3) a out ∧ specB D bits p w C1 C2 C3 out := by
  obtain ⟨az, a2, a35, aS3, a8, a33, aS1, afresh⟩ := hA
  have hST := scanTapes_eq D
  -- the fixed words
  have g6 := (UWalkNumbers.fixed_ready (CompareMachine.word p)).focus (slP D) (slP_inj D) a (by
    intro j
    have hv : (slP D j).val = 6 ∨ (slP D j).val = scanTapes D + 102 := by
      simp only [slP, Fin.val_mk]; split_ifs <;> omega
    rw [afresh _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)])
  set a6 := install (slP D) a ![CompareMachine.word p, List.replicate (CompareMachine.word p).length false]
    with ha6
  have b6 : ∀ q : Fin (prefixTapes D), q.val ≠ 6 ∧ q.val ≠ scanTapes D + 102 → a6 q = a q :=
    fun q h => install_off_val _ _ _ _ (slP_off D q h)
  have g7 := (UWalkNumbers.fixed_ready (CompareMachine.word w)).focus (slW D) (slW_inj D) a6 (by
    intro j
    have hv : (slW D j).val = 7 ∨ (slW D j).val = scanTapes D + 103 := by
      simp only [slW, Fin.val_mk]; split_ifs <;> omega
    rw [b6 _ (by omega), afresh _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)])
  set a7 := install (slW D) a6 ![CompareMachine.word w, List.replicate (CompareMachine.word w).length false]
    with ha7
  have b7 : ∀ q : Fin (prefixTapes D), q.val ≠ 7 ∧ q.val ≠ scanTapes D + 103 → a7 q = a6 q :=
    fun q h => install_off_val _ _ _ _ (slW_off D q h)
  have fresh7 : ∀ q : Fin (prefixTapes D), q.val ≠ 0 → q.val ≠ 2 → q.val ≠ 6 → q.val ≠ 7 → q.val ≠ 8 →
      q.val ≠ 33 → q.val ≠ 35 → q.val ≠ scanTapes D + 1 → (q.val < scanTapes D + 3 ∨ scanTapes D + 103 < q.val) →
      a7 q = [] := by
    intro q h0 h2 h6 h7 h8 h33 h35 h1 hr
    rw [b7 q ⟨h7, by omega⟩, b6 q ⟨h6, by omega⟩, afresh q h0 h2 h8 h33 h35 h1 (by omega)]
  have a7_8 : a7 (ppos D 8 (by unfold prefixTapes; omega)) = List.replicate C1 true := by
    rw [b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, b6 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, a8]
  have a7_33 : a7 (ppos D 33 (by unfold prefixTapes; omega)) = List.replicate C2 true := by
    rw [b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, b6 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, a33]
  have a7_S1 : a7 (ppos D (scanTapes D + 1) (by unfold prefixTapes; omega)) = List.replicate C3 true := by
    rw [b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, b6 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, aS1]
  -- the erases
  have he1 := ready_of_root (RecoveryScratchErase.erase_ready C1 0 (fun _ : Fin 1 => []) (by simp))
  have g8 := he1.focus (slE1 D) (slE1_inj D) a7 (by
    intro j
    rw [erase_tapes_val]
    have hj := j.isLt
    by_cases h1 : j.val = 1
    · rw [dif_neg (by omega), if_pos h1, show slE1 D j = ppos D 8 (by unfold prefixTapes; omega) from
        Fin.ext (by simp [slE1, h1, ppos]), a7_8]
    · have hv : (slE1 D j).val = 1 ∨ (slE1 D j).val = 9 := by simp only [slE1, Fin.val_mk]; split_ifs <;> omega
      rw [fresh7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
      split_ifs <;> rfl)
  set a8' := install (slE1 D) a7 (Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 1 => List.replicate C1 false)
    (fun _ : Fin 1 => List.replicate C1 true))
    (fun _ : Fin 1 => List.replicate (max 0 (C1 + 1)) false)) with ha8
  have b8 : ∀ q : Fin (prefixTapes D), q.val ≠ 1 ∧ q.val ≠ 8 ∧ q.val ≠ 9 → a8' q = a7 q :=
    fun q h => install_off_val _ _ _ _ (slE1_off D q h)
  have he2 := ready_of_root (RecoveryScratchErase.erase_ready C2 0 (fun _ : Fin 23 => []) (by simp))
  have g9 := he2.focus (slE2 D) (slE2_inj D) a8' (by
    intro j
    rw [erase_tapes_val]
    have hj := j.isLt
    by_cases h1 : j.val = 23
    · rw [dif_neg (by omega), if_pos h1, b8 _ (by simp [slE2, h1]),
        show slE2 D j = ppos D 33 (by unfold prefixTapes; omega) from Fin.ext (by simp [slE2, h1, ppos]), a7_33]
    · have hv : (10 ≤ (slE2 D j).val ∧ (slE2 D j).val ≤ 32) ∨ (slE2 D j).val = 34 := by
        simp only [slE2, Fin.val_mk]; split_ifs <;> omega
      rw [b8 _ (by omega), fresh7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)]
      split_ifs <;> rfl)
  set a9 := install (slE2 D) a8' (Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 23 => List.replicate C2 false)
    (fun _ : Fin 1 => List.replicate C2 true))
    (fun _ : Fin 1 => List.replicate (max 0 (C2 + 1)) false)) with ha9
  have b9 : ∀ q : Fin (prefixTapes D), q.val < 10 ∨ 35 ≤ q.val → a9 q = a8' q :=
    fun q h => install_off_val _ _ _ _ (slE2_off D q h)
  have he3 := ready_of_root (RecoveryScratchErase.erase_ready C3 0
    (fun _ : Fin (Clause.tapes D + 84) => []) (by simp))
  have g10 := he3.focus (slE3 D) (slE3_inj D) a9 (by
    intro j
    rw [erase_tapes_val]
    have hj := j.isLt
    by_cases h1 : j.val = Clause.tapes D + 84
    · rw [dif_neg (by omega), if_pos h1, b9 _ (by simp only [slE3, Fin.val_mk]; split_ifs <;> omega),
        b8 _ (by simp only [slE3, Fin.val_mk]; split_ifs <;> omega),
        show slE3 D j = ppos D (scanTapes D + 1) (by unfold prefixTapes; omega) from
          Fin.ext (by simp only [slE3, ppos, Fin.val_mk]; split_ifs <;> omega), a7_S1]
    · have hv : (36 ≤ (slE3 D j).val ∧ (slE3 D j).val ≤ scanTapes D) ∨ (slE3 D j).val = scanTapes D + 2 := by
        simp only [slE3, Fin.val_mk]; split_ifs <;> omega
      rw [b9 _ (by omega), b8 _ (by omega), fresh7 _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]
      split_ifs <;> rfl)
  have b10 : ∀ q : Fin (prefixTapes D), q.val < 36 ∨ scanTapes D + 3 ≤ q.val →
      install (slE3 D) a9 (Fin.addCases (motive := fun _ => List Bool)
        (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin (Clause.tapes D + 84) => List.replicate C3 false)
        (fun _ : Fin 1 => List.replicate C3 true))
        (fun _ : Fin 1 => List.replicate (max 0 (C3 + 1)) false)) q = a9 q :=
    fun q h => install_off_val _ _ _ _ (slE3_off D q h)
  -- the slots written by the erases
  have e1v : ∀ j : Fin (1 + 1 + 1), a8' (slE1 D j) = if j.val = 0 then List.replicate C1 false
      else if j.val = 1 then List.replicate C1 true else List.replicate (max 0 (C1 + 1)) false := by
    intro j; rw [ha8, install_slot _ (slE1_inj D), erase_tapes_val]
    have := j.isLt; split_ifs <;> first | rfl | omega
  have e2v : ∀ j : Fin (23 + 1 + 1), a9 (slE2 D j) = if j.val < 23 then List.replicate C2 false
      else if j.val = 23 then List.replicate C2 true else List.replicate (max 0 (C2 + 1)) false := by
    intro j; rw [ha9, install_slot _ (slE2_inj D), erase_tapes_val]
    split_ifs <;> rfl
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ g6 (ClockJoin.join _ _ _ _ _ _ _ g7 (ClockJoin.join _ _ _ _ _ _ _ g8
    (ClockJoin.join _ _ _ _ _ _ _ g9 g10))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), b8 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b6 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, az]
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), show ppos D 1 _ = slE1 D 0 from Fin.ext (by simp [slE1, ppos]), e1v]
    rfl
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), b8 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b6 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, a2]
  · intro q h3 h5
    rw [b10 _ (by omega), b9 _ (by omega), b8 _ ⟨by omega, by omega, by omega⟩,
      fresh7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), b8 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, ha6,
      show ppos D 6 _ = slP D 0 from Fin.ext (by simp [slP, ppos]), install_slot _ (slP_inj D)]
    rfl
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), b8 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, ha7,
      show ppos D 7 _ = slW D 0 from Fin.ext (by simp [slW, ppos]), install_slot _ (slW_inj D)]
    rfl
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), show ppos D 8 _ = slE1 D 1 from Fin.ext (by simp [slE1, ppos]), e1v]
    rfl
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), show ppos D 9 _ = slE1 D 2 from Fin.ext (by simp [slE1, ppos]), e1v]
    rfl
  · intro q h10 h32
    rw [b10 _ (by omega), show q = slE2 D ⟨q.val - 10, by omega⟩ from Fin.ext (by
      simp only [slE2, Fin.val_mk]; split_ifs <;> omega), e2v]
    rw [if_pos (by simp; omega)]
  · rw [b10 _ (by cert_prefix_ptac), show ppos D 33 _ = slE2 D 23 from Fin.ext (by simp [slE2, ppos]), e2v]
    rfl
  · rw [b10 _ (by cert_prefix_ptac), show ppos D 34 _ = slE2 D 24 from Fin.ext (by simp [slE2, ppos]), e2v]
    rfl
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), b8 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b6 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, a35]
  · intro q h36 hST'
    rw [show q = slE3 D ⟨q.val - 36, by omega⟩ from Fin.ext (by
      simp only [slE3, Fin.val_mk]; split_ifs <;> omega), install_slot _ (slE3_inj D), erase_tapes_val]
    rw [dif_pos (by simp; omega)]
  · rw [show ppos D (scanTapes D + 1) _ = slE3 D ⟨Clause.tapes D + 84, by omega⟩ from Fin.ext (by
      simp only [slE3, ppos, Fin.val_mk]; split_ifs <;> omega), install_slot _ (slE3_inj D), erase_tapes_val]
    simp
  · rw [show ppos D (scanTapes D + 2) _ = slE3 D ⟨Clause.tapes D + 85, by omega⟩ from Fin.ext (by
      simp only [slE3, ppos, Fin.val_mk]; split_ifs <;> omega), install_slot _ (slE3_inj D), erase_tapes_val]
    simp
  · rw [b10 _ (by cert_prefix_ptac), b9 _ (by cert_prefix_ptac), b8 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac, by cert_prefix_ptac⟩, b7 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩,
      b6 _ ⟨by cert_prefix_ptac, by cert_prefix_ptac⟩, aS3]
  · intro q hq
    rw [b10 _ (by omega), b9 _ (by omega), b8 _ ⟨by omega, by omega, by omega⟩,
      fresh7 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

end PartB

section Block
variable (D : ℕ)

/-- **After the preparation the scan block holds the scan loop's input at `S = 0`.** -/
theorem block_eq (bits : List Bool) (p w C1 C2 C3 : ℕ) (a : Fin (prefixTapes D) → List Bool)
    (hB : specB D bits p w C1 C2 C3 a) (i : Fin (scanTapes D + 2 + 1)) :
    a (slS D i) = scanLoopInput D bits.length p w C1 C2 C3 i := by
  obtain ⟨-, b1, b2, b345, b6, b7, b8, b9, bmid, b33, b34, b35, bscr, bS1, bS2, bS3, -⟩ := hB
  have hi := i.isLt
  have hST := scanTapes_eq D
  have hq : (slS D i).val = 1 + i.val := rfl
  by_cases hlo : i.val < 35
  · rw [scanLoopInput_low D _ _ _ _ _ _ i hlo]
    by_cases h0 : i.val = 0
    · rw [show slS D i = ppos D 1 (by unfold prefixTapes; omega) from Fin.ext (by simp [slS, ppos, h0]), b1]
      simp [scanInput, h0, ZeroPadding.pad]
    · by_cases h1 : i.val = 1
      · rw [show slS D i = ppos D 2 (by unfold prefixTapes; omega) from Fin.ext (by simp [slS, ppos, h1]), b2]
        simp [scanInput, h1]
      · rw [scanInput_mid D _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
        by_cases h4 : i.val ≤ 4
        · rw [b345 _ (by omega) (by omega)]
          rcases (show i.val = 2 ∨ i.val = 3 ∨ i.val = 4 by omega) with h | h | h <;> simp [innerTapes, h]
        · by_cases h5 : i.val = 5
          · rw [show slS D i = ppos D 6 (by unfold prefixTapes; omega) from Fin.ext (by simp [slS, ppos, h5]), b6]
            simp [innerTapes, h5]
          · by_cases h6 : i.val = 6
            · rw [show slS D i = ppos D 7 (by unfold prefixTapes; omega) from Fin.ext (by simp [slS, ppos, h6]), b7]
              simp [innerTapes, h6]
            · by_cases h7 : i.val = 7
              · rw [show slS D i = ppos D 8 (by unfold prefixTapes; omega) from Fin.ext (by simp [slS, ppos, h7]), b8]
                simp [innerTapes, h7]
              · by_cases h8 : i.val = 8
                · rw [show slS D i = ppos D 9 (by unfold prefixTapes; omega) from
                    Fin.ext (by simp [slS, ppos, h8]), b9]
                  simp [innerTapes, h8]
                · by_cases h32 : i.val = 32
                  · rw [show slS D i = ppos D 33 (by unfold prefixTapes; omega) from
                      Fin.ext (by simp [slS, ppos, h32]), b33]
                    simp [innerTapes, h32]
                  · by_cases h33 : i.val = 33
                    · rw [show slS D i = ppos D 34 (by unfold prefixTapes; omega) from
                        Fin.ext (by simp [slS, ppos, h33]), b34]
                      simp [innerTapes, h33]
                    · by_cases h34 : i.val = 34
                      · rw [show slS D i = ppos D 35 (by unfold prefixTapes; omega) from
                          Fin.ext (by simp [slS, ppos, h34]), b35]
                        simp [innerTapes, h34]
                      · rw [bmid _ (by omega) (by omega)]
                        simp only [innerTapes]
                        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
                          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  · by_cases htop : scanTapes D ≤ i.val
    · rw [scanLoopInput_top D _ _ _ _ _ _ i htop]
      by_cases e0 : i.val = scanTapes D
      · rw [if_pos e0, show slS D i = ppos D (scanTapes D + 1) (by unfold prefixTapes; omega) from
          Fin.ext (by simp [slS, ppos, e0]; omega), bS1]
      · by_cases e1 : i.val = scanTapes D + 1
        · rw [if_neg e0, if_pos e1, show slS D i = ppos D (scanTapes D + 2) (by unfold prefixTapes; omega) from
            Fin.ext (by simp [slS, ppos, e1]; omega), bS2]
          simp
        · rw [if_neg e0, if_neg e1, show slS D i = ppos D (scanTapes D + 3) (by unfold prefixTapes; omega) from
            Fin.ext (by simp only [slS, ppos, Fin.val_mk]; omega), bS3]
    · rw [scanLoopInput_scratch D _ _ _ _ _ _ i (by omega) (by omega), bscr _ (by omega) (by omega)]

/-- **The preparation is ready.** -/
theorem prep_run (p w e1 e2 e3 : ℕ) (bits : List Bool) : ∃ out : Fin (prefixTapes D) → List Bool,
    ClockJoin.ReadyRun (prepMachine D p w e1 e2 e3)
      (prepCostA e1 e2 e3 bits + 1 + prepCostB p w (pcap e1 bits.length) (pcap e2 bits.length) (pcap e3 bits.length))
      (prefixInput D bits) out ∧
    specB D bits p w (pcap e1 bits.length) (pcap e2 bits.length) (pcap e3 bits.length) out := by
  obtain ⟨a, ha, hA⟩ := partA_run D e1 e2 e3 bits
  obtain ⟨out, hb, hB⟩ := partB_run D p w bits _ _ _ a hA
  exact ⟨out, ClockJoin.join _ _ _ _ _ _ _ ha hb, hB⟩

end Block

end NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep
