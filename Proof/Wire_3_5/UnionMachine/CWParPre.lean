import Proof.Wire_3_5.UnionMachine.CWParRound

/-! # C6 front, U5, the code writers: the parity writer's prefix — the shared codes

Every bottom of the encoding parity (P3:3092-3094) carries the same weight list and support list; this machine
(`preM`, 344 tapes) writes them once from the bitmap `frame (bitmap S)` on tape `0`:
* the cell; the base fields' pass (`CWParGen.genB`): the weights' and the support's fields, the counts `q` and `k`;
* base's serializer twice, each copied exact: `frame WLv.bits` (the weight list's code) on `134`;
* base's tagged cons `P3 = cons SBv 0` on the support list's code, copied exact: `frame P3v.bits` on `340`;
* the length ruler `1^q` on `342` (`CWWords.lenStage`); the count words `false :: 1^q` on `4`, `false :: 1^k` on `5`.

Paper quantity of the main type (**`pre_step`**): the parity bottoms' shared weight-list and support-list codes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParPre
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParGen
open NearCubicWires.WireExponent3_5.UnionMachine.CWParStages NearCubicWires.WireExponent3_5.UnionMachine.CWParRound
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (lenW lenIn lenIn_val lenStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serM serIn serCost serStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain (serIn_val)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## The shared codes -/

/-- The weights' fields, as the serializer's field list. -/
def wlGs (l : List Bool) : List (List Bool) := l.map fun b => if b then w9 else [false]

/-- The support's fields. -/
def sbGs (l : List Bool) : List (List Bool) := l.map fun b => [b]

/-- The weight list's code. -/
def WLv (l : List Bool) : ℕ := PCPTraversal.code (wlGs l)

/-- The support list's code. -/
def SBv (l : List Bool) : ℕ := PCPTraversal.code (sbGs l)

/-- `cons SBv 0`. -/
def P3v (l : List Bool) : ℕ := cons (SBv l) 0

theorem wlF_gs (l : List Bool) : wlF l = (wlGs l).flatMap frame := rfl

theorem sgl_gs (l : List Bool) : sgl l = (sbGs l).flatMap frame := sgl_eq l

/-! ## The layout -/

def genSl : Fin 7 → Fin 344 := ![0, 1, 2, 3, 4, 5, 6]
def ser1Sl (j : Fin 129) : Fin 344 :=
  ⟨if j.val = 0 then 2 else if j.val = 2 then 4 else if j.val = 1 then 7 else j.val + 5, by split_ifs <;> omega⟩
def cp1Sl : Fin 4 → Fin 344 := ![82, 1, 134, 135]
def ser2Sl (j : Fin 129) : Fin 344 :=
  ⟨if j.val = 0 then 3 else if j.val = 2 then 4 else if j.val = 1 then 136 else j.val + 134, by split_ifs <;> omega⟩
def cp2Sl : Fin 4 → Fin 344 := ![211, 1, 263, 264]
def zSl : Fin 1 → Fin 344 := fun _ => 265
def consSl (j : Fin 76) : Fin 344 :=
  ⟨if j.val = 2 then 263 else if j.val = 3 then 265 else if j.val < 2 then j.val + 266 else j.val + 264,
    by split_ifs <;> omega⟩
def cp3Sl : Fin 4 → Fin 344 := ![328, 1, 340, 341]
def lenSl : Fin 4 → Fin 344 := ![0, 1, 342, 343]

theorem genSl_inj : Function.Injective genSl := by decide
theorem cp1Sl_inj : Function.Injective cp1Sl := by decide
theorem cp2Sl_inj : Function.Injective cp2Sl := by decide
theorem cp3Sl_inj : Function.Injective cp3Sl := by decide
theorem lenSl_inj : Function.Injective lenSl := by decide
theorem zSl_inj : Function.Injective zSl := fun a b _ => Subsingleton.elim a b
theorem ser1Sl_inj : Function.Injective ser1Sl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ser1Sl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem ser2Sl_inj : Function.Injective ser2Sl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ser2Sl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem consSl_inj : Function.Injective consSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [consSl] at hv; apply Fin.ext; split_ifs at hv <;> omega

theorem genSl_val (j : Fin 7) : (genSl j).val = j.val := by fin_cases j <;> rfl
theorem cp1Sl_val (j : Fin 4) : (cp1Sl j).val = [82, 1, 134, 135].getD j.val 0 := by fin_cases j <;> rfl
theorem cp2Sl_val (j : Fin 4) : (cp2Sl j).val = [211, 1, 263, 264].getD j.val 0 := by fin_cases j <;> rfl
theorem cp3Sl_val (j : Fin 4) : (cp3Sl j).val = [328, 1, 340, 341].getD j.val 0 := by fin_cases j <;> rfl
theorem lenSl_val (j : Fin 4) : (lenSl j).val = [0, 1, 342, 343].getD j.val 0 := by fin_cases j <;> rfl

noncomputable def cellR := RecoveryFocus.machine (fun _ : Fin 1 => (1 : Fin 344)) NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def genR := RecoveryFocus.machine genSl (Rewind.machine genB.toProg.compile)
noncomputable def ser1R := RecoveryFocus.machine ser1Sl serM
noncomputable def cp1R := RecoveryFocus.machine cp1Sl (Rewind.machine cpW.toProg.compile)
noncomputable def ser2R := RecoveryFocus.machine ser2Sl serM
noncomputable def cp2R := RecoveryFocus.machine cp2Sl (Rewind.machine cpW.toProg.compile)
noncomputable def zR := RecoveryFocus.machine zSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def consR := RecoveryFocus.machine consSl PCPPRequestTaggedCons.machine
noncomputable def cp3R := RecoveryFocus.machine cp3Sl (Rewind.machine cpW.toProg.compile)
noncomputable def lenR := RecoveryFocus.machine lenSl (Rewind.machine lenW.toProg.compile)

/-- **The parity writer's prefix machine.** -/
noncomputable def preM :=
  Composition.machine cellR (Composition.machine genR (Composition.machine ser1R (Composition.machine cp1R
    (Composition.machine ser2R (Composition.machine cp2R (Composition.machine zR (Composition.machine consR
      (Composition.machine cp3R lenR))))))))

/-- The prefix's entry: the bitmap framed on tape `0`. -/
def preIn (l : List Bool) : Fin 344 → List Bool := fun t => if t.val = 0 then frame l else []

theorem zeroH (t : ℕ) (sl : Fin t → Fin 344) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- The prefix's fuel. -/
noncomputable def preCost (l : List Bool) : ℕ :=
  1 + 1 + ((2 * (72 * l.length + 9) + 2) + 1 + (serCost (wlGs l) + 1 + ((2 * (14 * (WLv l).bits.length + 5) + 2) + 1 + (
    serCost (sbGs l) + 1 + ((2 * (14 * (SBv l).bits.length + 5) + 2) + 1 + (1 + 1 + (
    PCPPRequestTaggedCons.budget (SBv l) 0 + 1 + ((2 * (14 * (P3v l).bits.length + 5) + 2) + 1 + (
    (2 * (l.length * 9 + 1) + 2))))))))))

/-- **The parity writer's prefix**: from the bitmap, the shared codes and the counts. -/
theorem pre_step (l : List Bool) :
    ∃ out : Fin 344 → List Bool, Step preM (preCost l) (fun _ => 0) (preIn l) (fun _ => 0) out ∧
      out 0 = frame l ∧ out 134 = frame (WLv l).bits ∧ out 340 = frame (P3v l).bits ∧
      out 4 = CompareMachine.word l.length ∧ out 5 = CompareMachine.word (l.count true) ∧
      out 342 = List.replicate l.length true := by
  set B0 := preIn l with hB0
  have f0 : ∀ t : Fin 344, 1 ≤ t.val → B0 t = [] := by intro t ht; simp only [hB0, preIn]; rw [if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock (fun _ : Fin 1 => (1 : Fin 344))
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0) B0 (fun _ => rfl) (fun _ => f0 1 (by decide))
  rw [zeroH] at d1
  set B1 := install (fun _ : Fin 1 => (1 : Fin 344)) B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 344, t.val ≠ 1 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b11 : B1 1 = [false] := install_slot (fun _ : Fin 1 => (1 : Fin 344)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  have f1 : ∀ t : Fin 344, 2 ≤ t.val → B1 t = [] := fun t ht => by rw [b1 _ (by omega), f0 _ (by omega)]
  -- 2: the base fields
  obtain ⟨o2, s2, g0, g1, g2, g3, g4, g5⟩ := genBStage l
  have d2 := s2.dock genSl genSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro k; rw [genBIn_val]
    fin_cases k
    · show B1 0 = _; rw [b1 _ (by decide)]; simp [hB0, preIn]
    · show B1 1 = _; rw [b11]; rfl
    all_goals (show B1 _ = _; rw [f1 _ (by decide)]; rfl))
  rw [zeroH] at d2
  set B2 := install genSl B1 o2 with hB2
  have b2h : ∀ k, B2 (genSl k) = o2 k := fun k => install_slot _ genSl_inj _ _ _
  have b2 : ∀ t : Fin 344, 7 ≤ t.val → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun k e => by have hv := congrArg Fin.val e; rw [genSl_val] at hv; have := k.isLt; omega)
  have f2 : ∀ t : Fin 344, 7 ≤ t.val → B2 t = [] := fun t ht => by rw [b2 _ ht, f1 _ (by omega)]
  -- 3: the weight list's code
  obtain ⟨o3, s3, z0, z2, z77⟩ := serStage (wlGs l)
  have d3 := s3.dock ser1Sl ser1Sl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro k; rw [serIn_val]
    by_cases h0 : k.val = 0
    · rw [if_pos h0, show ser1Sl k = genSl 2 from Fin.ext (by simp [ser1Sl, h0]; rfl), b2h, g2, wlF_gs]
    · rw [if_neg h0]
      by_cases h2 : k.val = 2
      · rw [if_pos h2, show ser1Sl k = genSl 4 from Fin.ext (by simp [ser1Sl, h2]; rfl), b2h, g4, wlGs,
          List.length_map]
      · have hk := k.isLt
        rw [if_neg h2, f2 _ (by simp only [ser1Sl]; split_ifs <;> omega)])
  rw [zeroH] at d3
  set B3 := install ser1Sl B2 o3 with hB3
  have b3h : ∀ k, B3 (ser1Sl k) = o3 k := fun k => install_slot _ ser1Sl_inj _ _ _
  have b3 : ∀ t : Fin 344, (t.val < 2 ∨ t.val = 3 ∨ t.val = 5 ∨ t.val = 6 ∨ 134 ≤ t.val) → B3 t = B2 t :=
    fun t ht => install_other _ _ _ _ (fun k e => by
      have hv := congrArg Fin.val e; simp only [ser1Sl] at hv; have hk := k.isLt; split_ifs at hv <;> omega)
  have f3 : ∀ t : Fin 344, 134 ≤ t.val → B3 t = [] := fun t ht => by rw [b3 _ (by omega), f2 _ (by omega)]
  have h382 : B3 82 = frame (WLv l).bits ++ List.replicate
      (PCPPairReusable.capacity (PCPSerializerMass.mass (wlGs l)) - (frame (WLv l).bits).length) false := by
    rw [show (82 : Fin 344) = ser1Sl 77 from rfl, b3h, z77]; rfl
  have h34 : B3 4 = CompareMachine.word l.length := by
    rw [show (4 : Fin 344) = ser1Sl 2 from rfl, b3h, z2, wlGs, List.length_map]
  have h31 : B3 1 = [false] := by rw [b3 _ (by decide), show (1 : Fin 344) = genSl 1 from rfl, b2h, g1]
  -- 4: copy it exact
  obtain ⟨o4, s4, -, k1, k2⟩ := cpStage (WLv l).bits (List.replicate
    (PCPPairReusable.capacity (PCPSerializerMass.mass (wlGs l)) - (frame (WLv l).bits).length) false)
  have d4 := s4.dock cp1Sl cp1Sl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B3 82 = _; rw [h382]; rfl
    · show B3 1 = _; rw [h31]; rfl
    · show B3 134 = _; rw [f3 _ (by decide)]; rfl
    · show B3 135 = _; rw [f3 _ (by decide)]; rfl)
  rw [zeroH] at d4
  set B4 := install cp1Sl B3 o4 with hB4
  have b4h : ∀ k, B4 (cp1Sl k) = o4 k := fun k => install_slot _ cp1Sl_inj _ _ _
  have b4 : ∀ t : Fin 344, (∀ k, (cp1Sl k).val ≠ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have f4 : ∀ t : Fin 344, 136 ≤ t.val → B4 t = [] := fun t ht => by
    rw [b4 _ (by intro k; rw [cp1Sl_val]; fin_cases k <;> simp <;> omega), f3 _ (by omega)]
  have h41 : B4 1 = [false] := by rw [show (1 : Fin 344) = cp1Sl 1 from rfl, b4h, k1]
  -- 5: the support list's code
  obtain ⟨o5, s5, y0, y2, y77⟩ := serStage (sbGs l)
  have d5 := s5.dock ser2Sl ser2Sl_inj (fun _ => 0) B4 (fun _ => rfl) (by
    intro k; rw [serIn_val]
    by_cases h0 : k.val = 0
    · rw [if_pos h0, show ser2Sl k = genSl 3 from Fin.ext (by simp [ser2Sl, h0]; rfl),
        b4 _ (by intro k'; rw [cp1Sl_val]; fin_cases k' <;> decide), b3 _ (by decide), b2h, g3, sgl_gs]
    · rw [if_neg h0]
      by_cases h2 : k.val = 2
      · rw [if_pos h2, show ser2Sl k = (4 : Fin 344) from Fin.ext (by simp [ser2Sl, h2]),
          b4 _ (by intro k'; rw [cp1Sl_val]; fin_cases k' <;> decide), h34, sbGs, List.length_map]
      · have hk := k.isLt
        rw [if_neg h2, f4 _ (by simp only [ser2Sl]; split_ifs <;> omega)])
  rw [zeroH] at d5
  set B5 := install ser2Sl B4 o5 with hB5
  have b5h : ∀ k, B5 (ser2Sl k) = o5 k := fun k => install_slot _ ser2Sl_inj _ _ _
  have b5 : ∀ t : Fin 344, (t.val < 3 ∨ (4 < t.val ∧ t.val < 136) ∨ 263 ≤ t.val) → B5 t = B4 t :=
    fun t ht => install_other _ _ _ _ (fun k e => by
      have hv := congrArg Fin.val e; simp only [ser2Sl] at hv; have hk := k.isLt; split_ifs at hv <;> omega)
  have f5 : ∀ t : Fin 344, 263 ≤ t.val → B5 t = [] := fun t ht => by rw [b5 _ (by omega), f4 _ (by omega)]
  have h5211 : B5 211 = frame (SBv l).bits ++ List.replicate
      (PCPPairReusable.capacity (PCPSerializerMass.mass (sbGs l)) - (frame (SBv l).bits).length) false := by
    rw [show (211 : Fin 344) = ser2Sl 77 from rfl, b5h, y77]; rfl
  have h54 : B5 4 = CompareMachine.word l.length := by
    rw [show (4 : Fin 344) = ser2Sl 2 from rfl, b5h, y2, sbGs, List.length_map]
  -- 6: copy it exact
  obtain ⟨o6, s6, -, m1, m2⟩ := cpStage (SBv l).bits (List.replicate
    (PCPPairReusable.capacity (PCPSerializerMass.mass (sbGs l)) - (frame (SBv l).bits).length) false)
  have d6 := s6.dock cp2Sl cp2Sl_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B5 211 = _; rw [h5211]; rfl
    · show B5 1 = _; rw [b5 _ (by decide), h41]; rfl
    · show B5 263 = _; rw [f5 _ (by decide)]; rfl
    · show B5 264 = _; rw [f5 _ (by decide)]; rfl)
  rw [zeroH] at d6
  set B6 := install cp2Sl B5 o6 with hB6
  have b6h : ∀ k, B6 (cp2Sl k) = o6 k := fun k => install_slot _ cp2Sl_inj _ _ _
  have b6 : ∀ t : Fin 344, (∀ k, (cp2Sl k).val ≠ t.val) → B6 t = B5 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have f6 : ∀ t : Fin 344, 265 ≤ t.val → B6 t = [] := fun t ht => by
    rw [b6 _ (by intro k; rw [cp2Sl_val]; fin_cases k <;> simp <;> omega), f5 _ (by omega)]
  have h61 : B6 1 = [false] := by rw [show (1 : Fin 344) = cp2Sl 1 from rfl, b6h, m1]
  have h6S : B6 263 = frame (SBv l).bits := by rw [show (263 : Fin 344) = cp2Sl 2 from rfl, b6h, m2]
  -- 7: the constant `frame 0.bits`
  have d7 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock zSl zSl_inj (fun _ => 0) B6 (fun _ => rfl)
    (fun _ => f6 265 (by decide))
  rw [zeroH] at d7
  set B7 := install zSl B6 (fun _ => [false]) with hB7
  have b7 : ∀ t : Fin 344, t.val ≠ 265 → B7 t = B6 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have h7z : B7 265 = [false] := install_slot zSl zSl_inj _ _ 0
  have f7 : ∀ t : Fin 344, 266 ≤ t.val → B7 t = [] := fun t ht => by rw [b7 _ (by omega), f6 _ (by omega)]
  -- 8: `P3 = cons SBv 0`
  obtain ⟨o8, r8, ⟨pd8, q64⟩, -⟩ := PCPPRequestTaggedCons.cons_run (SBv l) 0
  have d8 := (FrontLoopKit.step_of_ready r8).dock consSl consSl_inj (fun _ => 0) B7 (fun _ => rfl) (by
    intro k
    show B7 (consSl k) = PCPPRequestTaggedCons.input (SBv l) 0 k
    unfold PCPPRequestTaggedCons.input PCPPRequestPair.input PCPPairCanonical.input
    by_cases h2 : k.val = 2
    · rw [dif_pos (by omega)]; simp only [h2, if_true]
      rw [show consSl k = (263 : Fin 344) from Fin.ext (by simp [consSl, h2]), b7 _ (by decide), h6S]
    · by_cases h3 : k.val = 3
      · rw [dif_pos (by omega)]; simp only [h3, if_true, show (3 : ℕ) ≠ 2 by decide, if_false]
        rw [show consSl k = (265 : Fin 344) from Fin.ext (by simp [consSl, h3]), h7z]; rfl
      · have hk := k.isLt
        rw [f7 _ (by simp only [consSl]; split_ifs <;> omega)]
        split_ifs <;> simp_all)
  rw [zeroH] at d8
  set B8 := install consSl B7 o8 with hB8
  have b8h : ∀ k, B8 (consSl k) = o8 k := fun k => install_slot _ consSl_inj _ _ _
  have b8 : ∀ t : Fin 344, (t.val < 263 ∨ t.val = 264 ∨ 340 ≤ t.val) → B8 t = B7 t := fun t ht =>
    install_other _ _ _ _ (fun k e => by
      have hv := congrArg Fin.val e; simp only [consSl] at hv; have hk := k.isLt; split_ifs at hv <;> omega)
  have f8 : ∀ t : Fin 344, 340 ≤ t.val → B8 t = [] := fun t ht => by rw [b8 _ (by omega), f7 _ (by omega)]
  have h8P : B8 328 = frame (P3v l).bits ++ List.replicate pd8 false := by
    rw [show (328 : Fin 344) = consSl 64 from rfl, b8h, q64]; rfl
  -- 9: copy it exact
  obtain ⟨o9, s9, -, n1, n2⟩ := cpStage (P3v l).bits (List.replicate pd8 false)
  have d9 := s9.dock cp3Sl cp3Sl_inj (fun _ => 0) B8 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B8 328 = _; rw [h8P]; rfl
    · show B8 1 = _; rw [b8 _ (by decide), b7 _ (by decide), h61]; rfl
    · show B8 340 = _; rw [f8 _ (by decide)]; rfl
    · show B8 341 = _; rw [f8 _ (by decide)]; rfl)
  rw [zeroH] at d9
  set B9 := install cp3Sl B8 o9 with hB9
  have b9h : ∀ k, B9 (cp3Sl k) = o9 k := fun k => install_slot _ cp3Sl_inj _ _ _
  have b9 : ∀ t : Fin 344, (∀ k, (cp3Sl k).val ≠ t.val) → B9 t = B8 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have h91 : B9 1 = [false] := by rw [show (1 : Fin 344) = cp3Sl 1 from rfl, b9h, n1]
  have h90 : B9 0 = frame l := by
    rw [b9 _ (by intro k; rw [cp3Sl_val]; fin_cases k <;> decide), b8 _ (by decide), b7 _ (by decide),
      b6 _ (by intro k; rw [cp2Sl_val]; fin_cases k <;> decide), b5 _ (by decide),
      b4 _ (by intro k; rw [cp1Sl_val]; fin_cases k <;> decide), b3 _ (by decide),
      show (0 : Fin 344) = genSl 0 from rfl, b2h, g0]
  -- 10: the length ruler `1^q`
  obtain ⟨o10, s10, l0, -, l2⟩ := lenStage l
  have d10 := s10.dock lenSl lenSl_inj (fun _ => 0) B9 (fun _ => rfl) (by
    intro k; rw [lenIn_val]
    fin_cases k
    · show B9 0 = _; rw [h90]; rfl
    · show B9 1 = _; rw [h91]; rfl
    · show B9 342 = _; rw [b9 _ (by intro k'; rw [cp3Sl_val]; fin_cases k' <;> decide), f8 _ (by decide)]; rfl
    · show B9 343 = _; rw [b9 _ (by intro k'; rw [cp3Sl_val]; fin_cases k' <;> decide), f8 _ (by decide)]; rfl)
  rw [zeroH] at d10
  set B10 := install lenSl B9 o10 with hB10
  have b10h : ∀ k, B10 (lenSl k) = o10 k := fun k => install_slot _ lenSl_inj _ _ _
  have b10 : ∀ t : Fin 344, (∀ k, (lenSl k).val ≠ t.val) → B10 t = B9 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq d10))))))))
  have run' : Step preM _ (fun _ => 0) B0 (fun _ => 0) B10 := run
  refine ⟨B10, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact run'.enlarge (by unfold preCost; exact le_refl _)
  · rw [show (0 : Fin 344) = lenSl 0 from rfl, b10h, l0]
  · rw [b10 _ (by intro k; rw [lenSl_val]; fin_cases k <;> decide),
      b9 _ (by intro k; rw [cp3Sl_val]; fin_cases k <;> decide), b8 _ (by decide), b7 _ (by decide),
      b6 _ (by intro k; rw [cp2Sl_val]; fin_cases k <;> decide), b5 _ (by decide),
      show (134 : Fin 344) = cp1Sl 2 from rfl, b4h, k2]
  · rw [b10 _ (by intro k; rw [lenSl_val]; fin_cases k <;> decide), show (340 : Fin 344) = cp3Sl 2 from rfl, b9h, n2]
  · rw [b10 _ (by intro k; rw [lenSl_val]; fin_cases k <;> decide),
      b9 _ (by intro k; rw [cp3Sl_val]; fin_cases k <;> decide), b8 _ (by decide), b7 _ (by decide),
      b6 _ (by intro k; rw [cp2Sl_val]; fin_cases k <;> decide), h54]
  · rw [b10 _ (by intro k; rw [lenSl_val]; fin_cases k <;> decide),
      b9 _ (by intro k; rw [cp3Sl_val]; fin_cases k <;> decide), b8 _ (by decide), b7 _ (by decide),
      b6 _ (by intro k; rw [cp2Sl_val]; fin_cases k <;> decide), b5 _ (by decide),
      b4 _ (by intro k; rw [cp1Sl_val]; fin_cases k <;> decide), b3 _ (by decide),
      show (5 : Fin 344) = genSl 5 from rfl, b2h, g5]
  · rw [show (342 : Fin 344) = lenSl 2 from rfl, b10h, l2]

end NearCubicWires.WireExponent3_5.UnionMachine.CWParPre
