import Proof.Wire_3_5.UnionMachine.CWParDock

/-! # C6 front, U5, the code writers: the parity atoms' tops and tags

The two class modes' parity atoms (P3:3092-3094; `unionParityAtom`) differ in their family tag and top:
* `SYM∘THR` (**`topSym_step`**, 136 tapes): the top table's code `encodeBoolList (c ↦ [c odd])` (base serializer on
  `CWParTop.topS`'s fields) and the tag `encodeNat 0 = 0`;
* `THR∘THR` (**`topThr_step`**, 497 tapes): the top gate's code `cons ALT (cons 9 (cons ALLT 0))` — the weights
  `+1, -1, …` and the all-ones support as base serializer codes (`CWParTop.topT`), `encodeInt 1 = 9` — and the tag
  `encodeNat 1 = 3`.
Both read the count word `false :: 1^k` on tape `0` and keep it.

Paper quantity of the main types: the codes of the parity atoms' tops and tags. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParTops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParGen
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTop NearCubicWires.WireExponent3_5.UnionMachine.CWParStages
open NearCubicWires.WireExponent3_5.UnionMachine.CWParDock
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (cons)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serM serCost)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## `SYM∘THR` -/

/-- The top table's code. -/
def topSv (k : ℕ) : ℕ := PCPTraversal.code ((oddL (k + 1)).map fun b => [b])

def tsSl : Fin 6 → Fin 136 := ![0, 1, 2, 3, 4, 5]
def ssSl (j : Fin 129) : Fin 136 :=
  ⟨if j.val = 0 then 2 else if j.val = 2 then 3 else if j.val = 1 then 6 else j.val + 4, by split_ifs <;> omega⟩
def scSl : Fin 4 → Fin 136 := ![81, 1, 133, 134]

theorem tsSl_inj : Function.Injective tsSl := by decide
theorem scSl_inj : Function.Injective scSl := by decide
theorem ssSl_inj : Function.Injective ssSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ssSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem tsSl_val (j : Fin 6) : (tsSl j).val = j.val := by fin_cases j <;> rfl
theorem scSl_val (j : Fin 4) : (scSl j).val = [81, 1, 133, 134].getD j.val 0 := by fin_cases j <;> rfl

/-- **The `SYM∘THR` top machine.** -/
noncomputable def topSymM :=
  Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (1 : Fin 136)) NearCubicWires.WireExponent3_5.PrimT.cellM)
    (Composition.machine (RecoveryFocus.machine tsSl (Rewind.machine topS.toProg.compile))
      (Composition.machine (RecoveryFocus.machine ssSl serM)
        (Composition.machine (RecoveryFocus.machine scSl (Rewind.machine cpW.toProg.compile))
          (RecoveryFocus.machine (fun _ : Fin 1 => (135 : Fin 136)) NearCubicWires.WireExponent3_5.PrimT.cellM))))

def topSymIn (k : ℕ) : Fin 136 → List Bool := fun t => if t.val = 0 then CompareMachine.word k else []

noncomputable def topSymCost (k : ℕ) : ℕ :=
  1 + 1 + ((2 * (k * 24 + 30) + 2) + 1 + (serCost ((oddL (k + 1)).map fun b => [b]) + 1 +
    ((2 * (14 * (topSv k).bits.length + 5) + 2) + 1 + 1)))

theorem topSym_step (k : ℕ) : ∃ out : Fin 136 → List Bool,
    Step topSymM (topSymCost k) (fun _ => 0) (topSymIn k) (fun _ => 0) out ∧
      out 0 = CompareMachine.word k ∧ out 133 = frame (topSv k).bits ∧ out 135 = frame (0 : ℕ).bits := by
  set B0 := topSymIn k with hB0
  have f0 : ∀ t : Fin 136, 1 ≤ t.val → B0 t = [] := fun t ht => by simp only [hB0, topSymIn]; rw [if_neg (by omega)]
  have d1 := cell_dock (1 : Fin 136) B0 (f0 1 (by decide))
  set B1 := install (fun _ : Fin 1 => (1 : Fin 136)) B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 136, t.val ≠ 1 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b11 : B1 1 = [false] := install_slot (fun _ : Fin 1 => (1 : Fin 136)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  obtain ⟨o2, s2, g0, g1, g2, g3⟩ := topSStage k
  have d2 := s2.dock tsSl tsSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [topIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, topSymIn]
    · show B1 1 = _; rw [b11]; rfl
    all_goals (show B1 _ = _; rw [b1 _ (by decide), f0 _ (by decide)]; rfl))
  rw [zeroH] at d2
  set B2 := install tsSl B1 o2 with hB2
  have b2h : ∀ j, B2 (tsSl j) = o2 j := fun j => install_slot _ tsSl_inj _ _ _
  have b2 : ∀ t : Fin 136, 6 ≤ t.val → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by have hv := congrArg Fin.val e; rw [tsSl_val] at hv; have := j.isLt; omega)
  obtain ⟨o3, d3, z0, -, z77⟩ := ser_dock ssSl ssSl_inj ((oddL (k + 1)).map fun b => [b]) B2
    (by show B2 2 = _; rw [show (2 : Fin 136) = tsSl 2 from rfl, b2h, g2, sgl_eq])
    (by show B2 3 = _; rw [show (3 : Fin 136) = tsSl 3 from rfl, b2h, g3, List.length_map, oddL, List.length_map,
      List.length_range])
    (by intro j h0 h2; have hj := j.isLt
        rw [b2 _ (by simp only [ssSl]; split_ifs <;> omega), b1 _ (by simp only [ssSl]; split_ifs <;> omega),
          f0 _ (by simp only [ssSl]; split_ifs <;> omega)])
  set B3 := install ssSl B2 o3 with hB3
  have b3h : ∀ j, B3 (ssSl j) = o3 j := fun j => install_slot _ ssSl_inj _ _ _
  have b3 : ∀ t : Fin 136, (t.val < 2 ∨ t.val = 4 ∨ t.val = 5 ∨ 133 ≤ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [ssSl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  obtain ⟨o4, d4, -, k1, k2⟩ := cp_dock scSl scSl_inj (topSv k).bits _ B3
    (by show B3 81 = _; rw [show (81 : Fin 136) = ssSl 77 from rfl, b3h, z77]; rfl)
    (by show B3 1 = _; rw [b3 _ (by decide), show (1 : Fin 136) = tsSl 1 from rfl, b2h, g1])
    (by show B3 133 = _; rw [b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), f0 _ (by decide)])
    (by show B3 134 = _; rw [b3 _ (by decide), b2 _ (by decide), b1 _ (by decide), f0 _ (by decide)])
  set B4 := install scSl B3 o4 with hB4
  have b4h : ∀ j, B4 (scSl j) = o4 j := fun j => install_slot _ scSl_inj _ _ _
  have b4 : ∀ t : Fin 136, (∀ j, (scSl j).val ≠ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have d5 := cell_dock (135 : Fin 136) B4 (by
    rw [b4 _ (by intro j; rw [scSl_val]; fin_cases j <;> decide), b3 _ (by decide), b2 _ (by decide),
      b1 _ (by decide), f0 _ (by decide)])
  set B5 := install (fun _ : Fin 1 => (135 : Fin 136)) B4 (fun _ => [false]) with hB5
  have b5 : ∀ t : Fin 136, t.val ≠ 135 → B5 t = B4 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have run := d1.seq (d2.seq (d3.seq (d4.seq d5)))
  have run' : Step topSymM _ (fun _ => 0) B0 (fun _ => 0) B5 := run
  refine ⟨B5, run'.enlarge (by unfold topSymCost; exact le_refl _), ?_, ?_, ?_⟩
  · rw [b5 _ (by decide), b4 _ (by intro j; rw [scSl_val]; fin_cases j <;> decide), b3 _ (by decide),
      show (0 : Fin 136) = tsSl 0 from rfl, b2h, g0]
  · rw [b5 _ (by decide), show (133 : Fin 136) = scSl 2 from rfl, b4h, k2]
  · exact install_slot (fun _ : Fin 1 => (135 : Fin 136)) (fun a b _ => Subsingleton.elim a b) _ _ 0

/-! ## `THR∘THR` -/

/-- The top gate's weights' fields. -/
def altGs (k : ℕ) : List (List Bool) := (List.range k).map fun i => if Even i then w9 else w10

/-- The weights' code, the support's code, and the top gate's code. -/
def altV (k : ℕ) : ℕ := PCPTraversal.code (altGs k)
def alltV (k : ℕ) : ℕ := PCPTraversal.code (List.replicate k [true])
def topTv (k : ℕ) : ℕ := cons (altV k) (cons 9 (cons (alltV k) 0))

def ttSl : Fin 6 → Fin 497 := ![0, 1, 2, 3, 4, 5]
def sAl (j : Fin 129) : Fin 497 :=
  ⟨if j.val = 0 then 2 else if j.val = 2 then 0 else if j.val = 1 then 6 else j.val + 4, by split_ifs <;> omega⟩
def cpA : Fin 4 → Fin 497 := ![81, 1, 133, 134]
def sLl (j : Fin 129) : Fin 497 :=
  ⟨if j.val = 0 then 3 else if j.val = 2 then 0 else if j.val = 1 then 135 else j.val + 133, by split_ifs <;> omega⟩
def cpL : Fin 4 → Fin 497 := ![210, 1, 262, 263]
/-- A tagged cons on `a`, `r`, fresh tapes from `base`. -/
def cS (a r base : ℕ) (ha : a < 497) (hr : r < 497) (hb : base + 74 < 497) (j : Fin 76) : Fin 497 :=
  ⟨if j.val = 2 then a else if j.val = 3 then r else if j.val < 2 then j.val + base else j.val + base - 2,
    by split_ifs <;> omega⟩
def cAl : Fin 76 → Fin 497 := cS 262 264 265 (by decide) (by decide) (by decide)
def cp1l : Fin 4 → Fin 497 := ![327, 1, 339, 340]
def k9l : Fin 3 → Fin 497 := ![341, 1, 342]
def cBl : Fin 76 → Fin 497 := cS 341 339 343 (by decide) (by decide) (by decide)
def cp2l : Fin 4 → Fin 497 := ![405, 1, 417, 418]
def cCl : Fin 76 → Fin 497 := cS 133 417 419 (by decide) (by decide) (by decide)
def cp3l : Fin 4 → Fin 497 := ![481, 1, 493, 494]
def ktl : Fin 3 → Fin 497 := ![495, 1, 496]

theorem cS_val (a r base : ℕ) (ha : a < 497) (hr : r < 497) (hb : base + 74 < 497) (j : Fin 76) :
    (cS a r base ha hr hb j).val =
      if j.val = 2 then a else if j.val = 3 then r else if j.val < 2 then j.val + base else j.val + base - 2 := rfl

theorem cS_inj (a r base : ℕ) (ha : a < 497) (hr : r < 497) (hb : base + 74 < 497) (hra : a ≠ r)
    (hlo : a < base ∧ r < base) : Function.Injective (cS a r base ha hr hb) := by
  intro x y h; have hv := congrArg Fin.val h; rw [cS_val, cS_val] at hv
  have := x.isLt; have := y.isLt
  apply Fin.ext; split_ifs at hv <;> omega

theorem ttSl_inj : Function.Injective ttSl := by decide
theorem cpA_inj : Function.Injective cpA := by decide
theorem cpL_inj : Function.Injective cpL := by decide
theorem cp1l_inj : Function.Injective cp1l := by decide
theorem cp2l_inj : Function.Injective cp2l := by decide
theorem cp3l_inj : Function.Injective cp3l := by decide
theorem k9l_inj : Function.Injective k9l := by decide
theorem ktl_inj : Function.Injective ktl := by decide
theorem sAl_inj : Function.Injective sAl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [sAl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem sLl_inj : Function.Injective sLl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [sLl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem cAl_inj : Function.Injective cAl := cS_inj _ _ _ _ _ _ (by decide) ⟨by decide, by decide⟩
theorem cBl_inj : Function.Injective cBl := cS_inj _ _ _ _ _ _ (by decide) ⟨by decide, by decide⟩
theorem cCl_inj : Function.Injective cCl := cS_inj _ _ _ _ _ _ (by decide) ⟨by decide, by decide⟩

theorem ttSl_val (j : Fin 6) : (ttSl j).val = j.val := by fin_cases j <;> rfl
theorem cpA_val (j : Fin 4) : (cpA j).val = [81, 1, 133, 134].getD j.val 0 := by fin_cases j <;> rfl
theorem cpL_val (j : Fin 4) : (cpL j).val = [210, 1, 262, 263].getD j.val 0 := by fin_cases j <;> rfl
theorem cp1l_val (j : Fin 4) : (cp1l j).val = [327, 1, 339, 340].getD j.val 0 := by fin_cases j <;> rfl
theorem cp2l_val (j : Fin 4) : (cp2l j).val = [405, 1, 417, 418].getD j.val 0 := by fin_cases j <;> rfl
theorem cp3l_val (j : Fin 4) : (cp3l j).val = [481, 1, 493, 494].getD j.val 0 := by fin_cases j <;> rfl
theorem k9l_val (j : Fin 3) : (k9l j).val = [341, 1, 342].getD j.val 0 := by fin_cases j <;> rfl
theorem ktl_val (j : Fin 3) : (ktl j).val = [495, 1, 496].getD j.val 0 := by fin_cases j <;> rfl

/-- **The `THR∘THR` top machine.** -/
noncomputable def topThrM :=
  Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (1 : Fin 497)) NearCubicWires.WireExponent3_5.PrimT.cellM)
  (Composition.machine (RecoveryFocus.machine ttSl (Rewind.machine topT.toProg.compile))
  (Composition.machine (RecoveryFocus.machine sAl serM)
  (Composition.machine (RecoveryFocus.machine cpA (Rewind.machine cpW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine sLl serM)
  (Composition.machine (RecoveryFocus.machine cpL (Rewind.machine cpW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (264 : Fin 497)) NearCubicWires.WireExponent3_5.PrimT.cellM)
  (Composition.machine (RecoveryFocus.machine cAl PCPPRequestTaggedCons.machine)
  (Composition.machine (RecoveryFocus.machine cp1l (Rewind.machine cpW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine k9l (Rewind.machine (constW w9).toProg.compile))
  (Composition.machine (RecoveryFocus.machine cBl PCPPRequestTaggedCons.machine)
  (Composition.machine (RecoveryFocus.machine cp2l (Rewind.machine cpW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine cCl PCPPRequestTaggedCons.machine)
  (Composition.machine (RecoveryFocus.machine cp3l (Rewind.machine cpW.toProg.compile))
  (RecoveryFocus.machine ktl (Rewind.machine (constW [true, true]).toProg.compile)))))))))))))))

def topThrIn (k : ℕ) : Fin 497 → List Bool := fun t => if t.val = 0 then CompareMachine.word k else []

theorem bits9 : (9 : ℕ).bits = w9 := by decide
theorem bits3 : (3 : ℕ).bits = [true, true] := by decide

noncomputable def topThrCost (k : ℕ) : ℕ :=
  1 + 1 + ((2 * (k * 60 + 10) + 2) + 1 + (serCost (altGs k) + 1 + ((2 * (14 * (altV k).bits.length + 5) + 2) + 1 + (
    serCost (List.replicate k [true]) + 1 + ((2 * (14 * (alltV k).bits.length + 5) + 2) + 1 + (1 + 1 + (
    PCPPRequestTaggedCons.budget (alltV k) 0 + 1 + ((2 * (14 * (cons (alltV k) 0).bits.length + 5) + 2) + 1 + (
    (2 * (4 * (frame w9).length) + 2) + 1 + (PCPPRequestTaggedCons.budget 9 (cons (alltV k) 0) + 1 + (
    (2 * (14 * (cons 9 (cons (alltV k) 0)).bits.length + 5) + 2) + 1 + (
    PCPPRequestTaggedCons.budget (altV k) (cons 9 (cons (alltV k) 0)) + 1 + (
    (2 * (14 * (topTv k).bits.length + 5) + 2) + 1 + ((2 * (4 * (frame [true, true]).length) + 2)))))))))))))))

theorem topThr_step (k : ℕ) : ∃ out : Fin 497 → List Bool,
    Step topThrM (topThrCost k) (fun _ => 0) (topThrIn k) (fun _ => 0) out ∧
      out 0 = CompareMachine.word k ∧ out 493 = frame (topTv k).bits ∧ out 495 = frame (3 : ℕ).bits := by
  set B0 := topThrIn k with hB0
  have f0 : ∀ t : Fin 497, 1 ≤ t.val → B0 t = [] := fun t ht => by simp only [hB0, topThrIn]; rw [if_neg (by omega)]
  -- 1: the cell
  have d1 := cell_dock (1 : Fin 497) B0 (f0 1 (by decide))
  set B1 := install (fun _ : Fin 1 => (1 : Fin 497)) B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 497, t.val ≠ 1 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b11 : B1 1 = [false] := install_slot (fun _ : Fin 1 => (1 : Fin 497)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  have f1 : ∀ t : Fin 497, 2 ≤ t.val → B1 t = [] := fun t ht => by rw [b1 _ (by omega), f0 _ (by omega)]
  -- 2: the top's fields
  obtain ⟨o2, s2, g0, g1, g2, g3⟩ := topTStage k
  have d2 := s2.dock ttSl ttSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [topIn_val]
    fin_cases j
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, topThrIn]
    · show B1 1 = _; rw [b11]; rfl
    all_goals (show B1 _ = _; rw [f1 _ (by decide)]; rfl))
  rw [zeroH] at d2
  set B2 := install ttSl B1 o2 with hB2
  have b2h : ∀ j, B2 (ttSl j) = o2 j := fun j => install_slot _ ttSl_inj _ _ _
  have b2 : ∀ t : Fin 497, 6 ≤ t.val → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by have hv := congrArg Fin.val e; rw [ttSl_val] at hv; have := j.isLt; omega)
  have f2 : ∀ t : Fin 497, 6 ≤ t.val → B2 t = [] := fun t ht => by rw [b2 _ ht, f1 _ (by omega)]
  have h20 : B2 0 = CompareMachine.word k := by rw [show (0 : Fin 497) = ttSl 0 from rfl, b2h, g0]
  have h21 : B2 1 = [false] := by rw [show (1 : Fin 497) = ttSl 1 from rfl, b2h, g1]
  -- 3: the weights' code
  obtain ⟨o3, d3, z0, z2, z77⟩ := ser_dock sAl sAl_inj (altGs k) B2
    (by show B2 2 = _; rw [show (2 : Fin 497) = ttSl 2 from rfl, b2h, g2]; rfl)
    (by show B2 0 = _; rw [h20, altGs, List.length_map, List.length_range])
    (by intro j h0 h2; have hj := j.isLt; rw [f2 _ (by simp only [sAl]; split_ifs <;> omega)])
  set B3 := install sAl B2 o3 with hB3
  have b3h : ∀ j, B3 (sAl j) = o3 j := fun j => install_slot _ sAl_inj _ _ _
  have b3 : ∀ t : Fin 497, (t.val = 1 ∨ (2 < t.val ∧ t.val < 6) ∨ 133 ≤ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [sAl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have f3 : ∀ t : Fin 497, 133 ≤ t.val → B3 t = [] := fun t ht => by rw [b3 _ (by omega), f2 _ (by omega)]
  have h30 : B3 0 = CompareMachine.word k := by
    rw [show (0 : Fin 497) = sAl 2 from rfl, b3h, z2, altGs, List.length_map, List.length_range]
  -- 4: copy it exact
  obtain ⟨o4, d4, -, k1, k2⟩ := cp_dock cpA cpA_inj (altV k).bits _ B3
    (by show B3 81 = _; rw [show (81 : Fin 497) = sAl 77 from rfl, b3h, z77]; rfl)
    (by show B3 1 = _; rw [b3 _ (by decide), h21])
    (by show B3 133 = _; rw [f3 _ (by decide)]) (by show B3 134 = _; rw [f3 _ (by decide)])
  set B4 := install cpA B3 o4 with hB4
  have b4h : ∀ j, B4 (cpA j) = o4 j := fun j => install_slot _ cpA_inj _ _ _
  have b4 : ∀ t : Fin 497, (∀ j, (cpA j).val ≠ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f4 : ∀ t : Fin 497, 135 ≤ t.val → B4 t = [] := fun t ht => by
    rw [b4 _ (by intro j; rw [cpA_val]; fin_cases j <;> simp <;> omega), f3 _ (by omega)]
  have h41 : B4 1 = [false] := by rw [show (1 : Fin 497) = cpA 1 from rfl, b4h, k1]
  have h4A : B4 133 = frame (altV k).bits := by rw [show (133 : Fin 497) = cpA 2 from rfl, b4h, k2]
  -- 5: the support's code
  obtain ⟨o5, d5, y0, y2, y77⟩ := ser_dock sLl sLl_inj (List.replicate k [true]) B4
    (by show B4 3 = _
        rw [b4 _ (by intro j; rw [cpA_val]; fin_cases j <;> decide), b3 _ (by decide),
          show (3 : Fin 497) = ttSl 3 from rfl, b2h, g3, sgl_eq, List.map_replicate])
    (by show B4 0 = _
        rw [b4 _ (by intro j; rw [cpA_val]; fin_cases j <;> decide), h30, List.length_replicate])
    (by intro j h0 h2; have hj := j.isLt; rw [f4 _ (by simp only [sLl]; split_ifs <;> omega)])
  set B5 := install sLl B4 o5 with hB5
  have b5h : ∀ j, B5 (sLl j) = o5 j := fun j => install_slot _ sLl_inj _ _ _
  have b5 : ∀ t : Fin 497, (t.val = 1 ∨ t.val = 2 ∨ (3 < t.val ∧ t.val < 135) ∨ 262 ≤ t.val) → B5 t = B4 t :=
    fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [sLl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have f5 : ∀ t : Fin 497, 262 ≤ t.val → B5 t = [] := fun t ht => by rw [b5 _ (by omega), f4 _ (by omega)]
  have h50 : B5 0 = CompareMachine.word k := by
    rw [show (0 : Fin 497) = sLl 2 from rfl, b5h, y2, List.length_replicate]
  -- 6: copy it exact
  obtain ⟨o6, d6, -, m1, m2⟩ := cp_dock cpL cpL_inj (alltV k).bits _ B5
    (by show B5 210 = _; rw [show (210 : Fin 497) = sLl 77 from rfl, b5h, y77]; rfl)
    (by show B5 1 = _; rw [b5 _ (by decide), h41])
    (by show B5 262 = _; rw [f5 _ (by decide)]) (by show B5 263 = _; rw [f5 _ (by decide)])
  set B6 := install cpL B5 o6 with hB6
  have b6h : ∀ j, B6 (cpL j) = o6 j := fun j => install_slot _ cpL_inj _ _ _
  have b6 : ∀ t : Fin 497, (∀ j, (cpL j).val ≠ t.val) → B6 t = B5 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f6 : ∀ t : Fin 497, 264 ≤ t.val → B6 t = [] := fun t ht => by
    rw [b6 _ (by intro j; rw [cpL_val]; fin_cases j <;> simp <;> omega), f5 _ (by omega)]
  have h61 : B6 1 = [false] := by rw [show (1 : Fin 497) = cpL 1 from rfl, b6h, m1]
  have h6L : B6 262 = frame (alltV k).bits := by rw [show (262 : Fin 497) = cpL 2 from rfl, b6h, m2]
  -- 7: the constant `frame 0.bits`
  have d7 := cell_dock (264 : Fin 497) B6 (f6 264 (by decide))
  set B7 := install (fun _ : Fin 1 => (264 : Fin 497)) B6 (fun _ => [false]) with hB7
  have b7 : ∀ t : Fin 497, t.val ≠ 264 → B7 t = B6 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have h7z : B7 264 = [false] := install_slot (fun _ : Fin 1 => (264 : Fin 497)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  have f7 : ∀ t : Fin 497, 265 ≤ t.val → B7 t = [] := fun t ht => by rw [b7 _ (by omega), f6 _ (by omega)]
  -- 8: `cons ALLT 0`
  obtain ⟨o8, d8, pd8, q8⟩ := cons_dock cAl cAl_inj (alltV k) 0 B7
    (by show B7 262 = _; rw [b7 _ (by decide), h6L]) (by show B7 264 = _; rw [h7z]; rfl)
    (by intro j h2 h3; have hj := j.isLt
        rw [f7 _ (by rw [show cAl = cS 262 264 265 _ _ _ from rfl, cS_val]; split_ifs <;> omega)])
  set B8 := install cAl B7 o8 with hB8
  have b8h : ∀ j, B8 (cAl j) = o8 j := fun j => install_slot _ cAl_inj _ _ _
  have b8 : ∀ t : Fin 497, (t.val < 262 ∨ t.val = 263 ∨ 339 ≤ t.val) → B8 t = B7 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; rw [show cAl = cS 262 264 265 _ _ _ from rfl, cS_val] at hv
      have hj := j.isLt; split_ifs at hv <;> omega)
  have f8 : ∀ t : Fin 497, 339 ≤ t.val → B8 t = [] := fun t ht => by rw [b8 _ (by omega), f7 _ (by omega)]
  -- 9: copy it exact
  obtain ⟨o9, d9, -, n1, n2⟩ := cp_dock cp1l cp1l_inj (cons (alltV k) 0).bits _ B8
    (by show B8 327 = _; rw [show (327 : Fin 497) = cAl 64 from rfl, b8h, q8])
    (by show B8 1 = _; rw [b8 _ (by decide), b7 _ (by decide), h61])
    (by show B8 339 = _; rw [f8 _ (by decide)]) (by show B8 340 = _; rw [f8 _ (by decide)])
  set B9 := install cp1l B8 o9 with hB9
  have b9h : ∀ j, B9 (cp1l j) = o9 j := fun j => install_slot _ cp1l_inj _ _ _
  have b9 : ∀ t : Fin 497, (∀ j, (cp1l j).val ≠ t.val) → B9 t = B8 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f9 : ∀ t : Fin 497, 341 ≤ t.val → B9 t = [] := fun t ht => by
    rw [b9 _ (by intro j; rw [cp1l_val]; fin_cases j <;> simp <;> omega), f8 _ (by omega)]
  have h91 : B9 1 = [false] := by rw [show (1 : Fin 497) = cp1l 1 from rfl, b9h, n1]
  -- 10: the constant `frame 9.bits`
  obtain ⟨o10, d10, c0, c1⟩ := const_dock k9l k9l_inj w9 B9
    (by show B9 341 = _; rw [f9 _ (by decide)]) (by show B9 1 = _; rw [h91])
    (by show B9 342 = _; rw [f9 _ (by decide)])
  set B10 := install k9l B9 o10 with hB10
  have b10h : ∀ j, B10 (k9l j) = o10 j := fun j => install_slot _ k9l_inj _ _ _
  have b10 : ∀ t : Fin 497, (∀ j, (k9l j).val ≠ t.val) → B10 t = B9 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f10 : ∀ t : Fin 497, 343 ≤ t.val → B10 t = [] := fun t ht => by
    rw [b10 _ (by intro j; rw [k9l_val]; fin_cases j <;> simp <;> omega), f9 _ (by omega)]
  have h101 : B10 1 = [false] := by rw [show (1 : Fin 497) = k9l 1 from rfl, b10h, c1]
  -- 11: `cons 9 ·`
  obtain ⟨o11, d11, pd11, q11⟩ := cons_dock cBl cBl_inj 9 (cons (alltV k) 0) B10
    (by show B10 341 = _; rw [show (341 : Fin 497) = k9l 0 from rfl, b10h, c0, bits9])
    (by show B10 339 = _; rw [b10 _ (by intro j; rw [k9l_val]; fin_cases j <;> decide),
      show (339 : Fin 497) = cp1l 2 from rfl, b9h, n2])
    (by intro j h2 h3; have hj := j.isLt
        rw [f10 _ (by rw [show cBl = cS 341 339 343 _ _ _ from rfl, cS_val]; split_ifs <;> omega)])
  set B11 := install cBl B10 o11 with hB11
  have b11h : ∀ j, B11 (cBl j) = o11 j := fun j => install_slot _ cBl_inj _ _ _
  have b11 : ∀ t : Fin 497, (t.val < 339 ∨ t.val = 340 ∨ t.val = 342 ∨ 417 ≤ t.val) → B11 t = B10 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; rw [show cBl = cS 341 339 343 _ _ _ from rfl, cS_val] at hv
      have hj := j.isLt; split_ifs at hv <;> omega)
  have f11 : ∀ t : Fin 497, 417 ≤ t.val → B11 t = [] := fun t ht => by rw [b11 _ (by omega), f10 _ (by omega)]
  -- 12: copy it exact
  obtain ⟨o12, d12, -, u1, u2⟩ := cp_dock cp2l cp2l_inj (cons 9 (cons (alltV k) 0)).bits _ B11
    (by show B11 405 = _; rw [show (405 : Fin 497) = cBl 64 from rfl, b11h, q11])
    (by show B11 1 = _; rw [b11 _ (by decide), h101])
    (by show B11 417 = _; rw [f11 _ (by decide)]) (by show B11 418 = _; rw [f11 _ (by decide)])
  set B12 := install cp2l B11 o12 with hB12
  have b12h : ∀ j, B12 (cp2l j) = o12 j := fun j => install_slot _ cp2l_inj _ _ _
  have b12 : ∀ t : Fin 497, (∀ j, (cp2l j).val ≠ t.val) → B12 t = B11 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f12 : ∀ t : Fin 497, 419 ≤ t.val → B12 t = [] := fun t ht => by
    rw [b12 _ (by intro j; rw [cp2l_val]; fin_cases j <;> simp <;> omega), f11 _ (by omega)]
  have h121 : B12 1 = [false] := by rw [show (1 : Fin 497) = cp2l 1 from rfl, b12h, u1]
  -- 13: `cons ALT ·`
  obtain ⟨o13, d13, pd13, q13⟩ := cons_dock cCl cCl_inj (altV k) (cons 9 (cons (alltV k) 0)) B12
    (by show B12 133 = _
        rw [b12 _ (by intro j; rw [cp2l_val]; fin_cases j <;> decide), b11 _ (by decide),
          b10 _ (by intro j; rw [k9l_val]; fin_cases j <;> decide), b9 _ (by intro j; rw [cp1l_val]; fin_cases j <;> decide),
          b8 _ (by decide), b7 _ (by decide), b6 _ (by intro j; rw [cpL_val]; fin_cases j <;> decide),
          b5 _ (by decide), h4A])
    (by show B12 417 = _; rw [show (417 : Fin 497) = cp2l 2 from rfl, b12h, u2])
    (by intro j h2 h3; have hj := j.isLt
        rw [f12 _ (by rw [show cCl = cS 133 417 419 _ _ _ from rfl, cS_val]; split_ifs <;> omega)])
  set B13 := install cCl B12 o13 with hB13
  have b13h : ∀ j, B13 (cCl j) = o13 j := fun j => install_slot _ cCl_inj _ _ _
  have b13 : ∀ t : Fin 497, (t.val < 133 ∨ (133 < t.val ∧ t.val < 417) ∨ t.val = 418 ∨ 493 ≤ t.val) →
      B13 t = B12 t := fun t ht => install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; rw [show cCl = cS 133 417 419 _ _ _ from rfl, cS_val] at hv
      have hj := j.isLt; split_ifs at hv <;> omega)
  -- 14: copy it exact
  obtain ⟨o14, d14, -, v1, v2⟩ := cp_dock cp3l cp3l_inj (topTv k).bits _ B13
    (by show B13 481 = _; rw [show (481 : Fin 497) = cCl 64 from rfl, b13h, q13]; rfl)
    (by show B13 1 = _; rw [b13 _ (by decide), h121])
    (by show B13 493 = _; rw [b13 _ (by decide), f12 _ (by decide)])
    (by show B13 494 = _; rw [b13 _ (by decide), f12 _ (by decide)])
  set B14 := install cp3l B13 o14 with hB14
  have b14h : ∀ j, B14 (cp3l j) = o14 j := fun j => install_slot _ cp3l_inj _ _ _
  have b14 : ∀ t : Fin 497, (∀ j, (cp3l j).val ≠ t.val) → B14 t = B13 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  -- 15: the tag `frame 3.bits`
  obtain ⟨o15, d15, e0, -⟩ := const_dock ktl ktl_inj [true, true] B14
    (by show B14 495 = _; rw [b14 _ (by intro j; rw [cp3l_val]; fin_cases j <;> decide), b13 _ (by decide),
      f12 _ (by decide)])
    (by show B14 1 = _; rw [show (1 : Fin 497) = cp3l 1 from rfl, b14h, v1])
    (by show B14 496 = _; rw [b14 _ (by intro j; rw [cp3l_val]; fin_cases j <;> decide), b13 _ (by decide),
      f12 _ (by decide)])
  set B15 := install ktl B14 o15 with hB15
  have b15h : ∀ j, B15 (ktl j) = o15 j := fun j => install_slot _ ktl_inj _ _ _
  have b15 : ∀ t : Fin 497, (∀ j, (ktl j).val ≠ t.val) → B15 t = B14 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq (d10.seq (d11.seq (d12.seq
    (d13.seq (d14.seq d15)))))))))))))
  have run' : Step topThrM _ (fun _ => 0) B0 (fun _ => 0) B15 := run
  refine ⟨B15, run'.enlarge (by unfold topThrCost; exact le_refl _), ?_, ?_, ?_⟩
  · rw [b15 _ (by intro j; rw [ktl_val]; fin_cases j <;> decide),
      b14 _ (by intro j; rw [cp3l_val]; fin_cases j <;> decide), b13 _ (by decide),
      b12 _ (by intro j; rw [cp2l_val]; fin_cases j <;> decide), b11 _ (by decide),
      b10 _ (by intro j; rw [k9l_val]; fin_cases j <;> decide), b9 _ (by intro j; rw [cp1l_val]; fin_cases j <;> decide),
      b8 _ (by decide), b7 _ (by decide), b6 _ (by intro j; rw [cpL_val]; fin_cases j <;> decide), h50]
  · rw [b15 _ (by intro j; rw [ktl_val]; fin_cases j <;> decide), show (493 : Fin 497) = cp3l 2 from rfl, b14h, v2]
  · rw [show (495 : Fin 497) = ktl 0 from rfl, b15h, e0, bits3]

end NearCubicWires.WireExponent3_5.UnionMachine.CWParTops
