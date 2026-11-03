import Proof.Wire_3_5.UnionMachine.CWParStages
import Proof.PCP.PCPPRequestTaggedCons
import Proof.Wire_3_5.UnionMachine.CWMain

/-! # C6 front, U5, the code writers: the parity's bottoms, one per round

The encoding parity's bottom `j` is base's `thresholdParityBottomGate S j` (weights `[i ∈ S]`, threshold `j+1`, support
`S`), coded `encodeTaggedList [WL, encodeInt (j+1), SB] = cons WL (cons (pair 0 (encodeNat (j+1))) P3)` with
`P3 = cons SB 0`, `cons a r = Nat.pair 1 (Nat.pair a r)`. One ROUND handles bottom `j` on `331` tapes:
* `0` the weights' code `frame WL.bits`, `1` `frame P3.bits`, `2` the codes' accumulator, `3` the counter's fields
  `sgl j.bits`, `4` its count word, `5` the cell;
* the increment (`CWParStages.incStage`): the counter becomes `j + 1`;
* base's serializer on the counter's fields: `encodeNat (j+1)`; base's pair node `pair 0 ·`: `encodeInt (j+1)`;
* base's tagged cons twice (`PCPPRequestTaggedCons`): the bottom's code; the append to the accumulator.
Base's machines leave their inputs unspecified, so each reads a fresh copy (`cpStage`).

Paper quantity of the main type (**`roundP_run`**): the code of the parity's `j`-th bottom, appended. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParStages
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (appendBW appendBCost appendBIn appendBIn_val appendBStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serM serIn serCost serStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain (serIn_val)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## The bottom's code -/

/-- `Nat.pair 1 (Nat.pair a r)`: one cell of a tagged list. -/
def cons (a r : ℕ) : ℕ := Nat.pair 1 (Nat.pair a r)

/-- The code of the parity's bottom `j`, from the weights' code `wl` and `p3 = cons SB 0`. -/
def codeB (wl p3 j : ℕ) : ℕ := cons wl (cons (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))) p3)

/-- The counter's fields as the serializer's field list. -/
def gsOf (n : ℕ) : List (List Bool) := n.bits.map fun b => [b]

/-- **The serializer's code of the counter's fields is `encodeNat`.** -/
theorem code_gsOf (n : ℕ) : PCPTraversal.code (gsOf n) = CanonicalBinary.encodeNat n := by
  show CanonicalBinary.encodeBalancedList ((gsOf n).map RadixSemantics.value) = _
  unfold gsOf CanonicalBinary.encodeNat CanonicalBinary.encodeBits CanonicalBinary.encodeBoolList
  rw [List.map_map]
  congr 1

theorem sgl_gsOf (n : ℕ) : sgl n.bits = (gsOf n).flatMap frame := by rw [sgl_eq]; rfl

/-! ## The layout -/

def incSl : Fin 5 → Fin 331 := ![3, 5, 4, 6, 7]
def serSl (j : Fin 129) : Fin 331 :=
  ⟨if j.val = 0 then 3 else if j.val = 2 then 4 else if j.val = 1 then 8 else j.val + 6, by split_ifs <;> omega⟩
def cpESl : Fin 4 → Fin 331 := ![83, 5, 135, 136]
def zSl : Fin 1 → Fin 331 := fun _ => 137
def pairSl (j : Fin 38) : Fin 331 :=
  ⟨if j.val = 2 then 137 else if j.val = 3 then 135 else if j.val < 2 then j.val + 138 else j.val + 136,
    by split_ifs <;> omega⟩
def cpTSl : Fin 4 → Fin 331 := ![162, 5, 174, 175]
def cpPSl : Fin 4 → Fin 331 := ![1, 5, 176, 177]
def cons1Sl (j : Fin 76) : Fin 331 :=
  ⟨if j.val = 2 then 174 else if j.val = 3 then 176 else if j.val < 2 then j.val + 178 else j.val + 176,
    by split_ifs <;> omega⟩
def cpCSl : Fin 4 → Fin 331 := ![240, 5, 252, 253]
def cpWSl : Fin 4 → Fin 331 := ![0, 5, 254, 255]
def cons2Sl (j : Fin 76) : Fin 331 :=
  ⟨if j.val = 2 then 254 else if j.val = 3 then 252 else if j.val < 2 then j.val + 256 else j.val + 254,
    by split_ifs <;> omega⟩
def appSl : Fin 4 → Fin 331 := ![318, 5, 2, 330]

theorem incSl_inj : Function.Injective incSl := by decide
theorem cpESl_inj : Function.Injective cpESl := by decide
theorem zSl_inj : Function.Injective zSl := fun a b _ => Subsingleton.elim a b
theorem cpTSl_inj : Function.Injective cpTSl := by decide
theorem cpPSl_inj : Function.Injective cpPSl := by decide
theorem cpCSl_inj : Function.Injective cpCSl := by decide
theorem cpWSl_inj : Function.Injective cpWSl := by decide
theorem appSl_inj : Function.Injective appSl := by decide
theorem serSl_inj : Function.Injective serSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [serSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem pairSl_inj : Function.Injective pairSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [pairSl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem cons1Sl_inj : Function.Injective cons1Sl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [cons1Sl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem cons2Sl_inj : Function.Injective cons2Sl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [cons2Sl] at hv; apply Fin.ext; split_ifs at hv <;> omega

theorem incSl_val (j : Fin 5) : (incSl j).val = [3, 5, 4, 6, 7].getD j.val 0 := by fin_cases j <;> rfl
theorem cpESl_val (j : Fin 4) : (cpESl j).val = [83, 5, 135, 136].getD j.val 0 := by fin_cases j <;> rfl
theorem cpTSl_val (j : Fin 4) : (cpTSl j).val = [162, 5, 174, 175].getD j.val 0 := by fin_cases j <;> rfl
theorem cpPSl_val (j : Fin 4) : (cpPSl j).val = [1, 5, 176, 177].getD j.val 0 := by fin_cases j <;> rfl
theorem cpCSl_val (j : Fin 4) : (cpCSl j).val = [240, 5, 252, 253].getD j.val 0 := by fin_cases j <;> rfl
theorem cpWSl_val (j : Fin 4) : (cpWSl j).val = [0, 5, 254, 255].getD j.val 0 := by fin_cases j <;> rfl
theorem appSl_val (j : Fin 4) : (appSl j).val = [318, 5, 2, 330].getD j.val 0 := by fin_cases j <;> rfl

noncomputable def cellR := RecoveryFocus.machine (fun _ : Fin 1 => (5 : Fin 331)) NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def incR := RecoveryFocus.machine incSl (Rewind.machine CWParCnt.incW.toProg.compile)
noncomputable def serR := RecoveryFocus.machine serSl serM
noncomputable def cpER := RecoveryFocus.machine cpESl (Rewind.machine cpW.toProg.compile)
noncomputable def zR := RecoveryFocus.machine zSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def pairR := RecoveryFocus.machine pairSl PCPPRequestPair.machine
noncomputable def cpTR := RecoveryFocus.machine cpTSl (Rewind.machine cpW.toProg.compile)
noncomputable def cpPR := RecoveryFocus.machine cpPSl (Rewind.machine cpW.toProg.compile)
noncomputable def cons1R := RecoveryFocus.machine cons1Sl PCPPRequestTaggedCons.machine
noncomputable def cpCR := RecoveryFocus.machine cpCSl (Rewind.machine cpW.toProg.compile)
noncomputable def cpWR := RecoveryFocus.machine cpWSl (Rewind.machine cpW.toProg.compile)
noncomputable def cons2R := RecoveryFocus.machine cons2Sl PCPPRequestTaggedCons.machine
noncomputable def appR := RecoveryFocus.machine appSl (Rewind.machine appendBW.toProg.compile)

/-- **The parity's bottom round worker.** -/
noncomputable def workerP :=
  Composition.machine cellR (Composition.machine incR (Composition.machine serR (Composition.machine cpER
    (Composition.machine zR (Composition.machine pairR (Composition.machine cpTR (Composition.machine cpPR
      (Composition.machine cons1R (Composition.machine cpCR (Composition.machine cpWR
        (Composition.machine cons2R appR)))))))))))

/-- The round's entry: the two codes, the accumulator, the counter and its count; every other tape blank. -/
def roundPIn (W P A C N : List Bool) : Fin 331 → List Bool :=
  fun t => if t.val = 0 then W else if t.val = 1 then P else if t.val = 2 then A else if t.val = 3 then C
    else if t.val = 4 then N else []

theorem zeroH (t : ℕ) (sl : Fin t → Fin 331) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- The round's fuel. -/
noncomputable def roundPCost (wl p3 j : ℕ) (accL : List (List Bool)) : ℕ :=
  1 + 1 + ((2 * (j.bits.length * 23 + 50) + 2) + 1 + (serCost (gsOf (j + 1)) + 1 + (
    (2 * (14 * (CanonicalBinary.encodeNat (j + 1)).bits.length + 5) + 2) + 1 + (1 + 1 + (
    PCPPRequestPair.budget 0 (CanonicalBinary.encodeNat (j + 1)) + 1 + (
    (2 * (14 * (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))).bits.length + 5) + 2) + 1 + (
    (2 * (14 * p3.bits.length + 5) + 2) + 1 + (
    PCPPRequestTaggedCons.budget (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))) p3 + 1 + (
    (2 * (14 * (cons (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))) p3).bits.length + 5) + 2) + 1 + (
    (2 * (14 * wl.bits.length + 5) + 2) + 1 + (
    PCPPRequestTaggedCons.budget wl (cons (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))) p3) + 1 + (
    (2 * appendBCost accL (codeB wl p3 j).bits + 2)))))))))))))

/-- **One round of the parity's bottoms**: the code of bottom `j` joins the accumulator; the counter becomes
`j + 1`; the two codes are kept. -/
theorem roundP_run (wl p3 j : ℕ) (accL : List (List Bool)) (hacc : ∀ g ∈ accL, g ≠ []) :
    ∃ out, ClockJoin.ReadyRun workerP (roundPCost wl p3 j accL)
        (roundPIn (frame wl.bits) (frame p3.bits) (accL.flatMap frame) (sgl j.bits)
          (CompareMachine.word j.bits.length)) out ∧
      out 0 = frame wl.bits ∧ out 1 = frame p3.bits ∧ out 2 = (accL ++ [(codeB wl p3 j).bits]).flatMap frame ∧
      out 3 = sgl (j + 1).bits ∧ out 4 = CompareMachine.word (j + 1).bits.length := by
  set E := CanonicalBinary.encodeNat (j + 1) with hE
  set θ := Nat.pair 0 E with hθ
  set c1 := cons θ p3 with hc1
  set B0 := roundPIn (frame wl.bits) (frame p3.bits) (accL.flatMap frame) (sgl j.bits)
    (CompareMachine.word j.bits.length) with hB0
  have f0 : ∀ t : Fin 331, 5 ≤ t.val → B0 t = [] := by
    intro t ht; simp only [hB0, roundPIn]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock (fun _ : Fin 1 => (5 : Fin 331))
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0) B0 (fun _ => rfl) (fun _ => f0 5 (by decide))
  rw [zeroH] at d1
  set B1 := install (fun _ : Fin 1 => (5 : Fin 331)) B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 331, t.val ≠ 5 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b15 : B1 5 = [false] := install_slot (fun _ : Fin 1 => (5 : Fin 331)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  have f1 : ∀ t : Fin 331, 6 ≤ t.val → B1 t = [] := fun t ht => by rw [b1 _ (by omega), f0 _ (by omega)]
  -- 2: the increment
  obtain ⟨o2, s2, i0, i1, i2⟩ := incStage j.bits
  have d2 := s2.dock incSl incSl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro k; rw [incIn_val]
    fin_cases k
    · show B1 3 = _; rw [b1 _ (by decide)]; simp [hB0, roundPIn]
    · show B1 5 = _; rw [b15]; rfl
    · show B1 4 = _; rw [b1 _ (by decide)]; simp [hB0, roundPIn]
    · show B1 6 = _; rw [f1 _ (by decide)]; rfl
    · show B1 7 = _; rw [f1 _ (by decide)]; rfl)
  rw [zeroH] at d2
  set B2 := install incSl B1 o2 with hB2
  have b2 : ∀ t : Fin 331, (∀ k, (incSl k).val ≠ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have b2hit : ∀ k, B2 (incSl k) = o2 k := fun k => install_slot _ incSl_inj _ _ _
  have f2 : ∀ t : Fin 331, 8 ≤ t.val → B2 t = [] := fun t ht => by
    rw [b2 _ (by intro k; rw [incSl_val]; fin_cases k <;> simp <;> omega), f1 _ (by omega)]
  have hC2 : B2 3 = (gsOf (j + 1)).flatMap frame := by
    rw [show (3 : Fin 331) = incSl 0 from rfl, b2hit, i0, ← bits_succ, sgl_gsOf]
  have hN2 : B2 4 = CompareMachine.word (gsOf (j + 1)).length := by
    rw [show (4 : Fin 331) = incSl 2 from rfl, b2hit, i2, ← bits_succ, gsOf, List.length_map]
  have h25 : B2 5 = [false] := by rw [show (5 : Fin 331) = incSl 1 from rfl, b2hit, i1]
  -- 3: the serializer: `encodeNat (j+1)`
  obtain ⟨o3, s3, z0, z2, z77⟩ := serStage (gsOf (j + 1))
  have d3 := s3.dock serSl serSl_inj (fun _ => 0) B2 (fun _ => rfl) (by
    intro k; rw [serIn_val]
    by_cases h0 : k.val = 0
    · rw [if_pos h0, show serSl k = (3 : Fin 331) from Fin.ext (by simp [serSl, h0]), hC2]
    · rw [if_neg h0]
      by_cases h2 : k.val = 2
      · rw [if_pos h2, show serSl k = (4 : Fin 331) from Fin.ext (by simp [serSl, h2]), hN2]
      · have hk := k.isLt
        rw [if_neg h2, f2 _ (by simp only [serSl]; split_ifs <;> omega)])
  rw [zeroH] at d3
  set B3 := install serSl B2 o3 with hB3
  have b3h : ∀ k, B3 (serSl k) = o3 k := fun k => install_slot _ serSl_inj _ _ _
  have b3 : ∀ t : Fin 331, (t.val < 3 ∨ t.val = 5 ∨ t.val = 6 ∨ t.val = 7 ∨ 135 ≤ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun k e => by
      have hv := congrArg Fin.val e; simp only [serSl] at hv; have hk := k.isLt; split_ifs at hv <;> omega)
  have f3 : ∀ t : Fin 331, 135 ≤ t.val → B3 t = [] := fun t ht => by rw [b3 _ (by omega), f2 _ (by omega)]
  have h383 : B3 83 = frame E.bits ++ List.replicate
      (PCPPairReusable.capacity (PCPSerializerMass.mass (gsOf (j + 1))) - (frame E.bits).length) false := by
    rw [show (83 : Fin 331) = serSl 77 from rfl, b3h 77, z77, code_gsOf]; rfl
  have h33 : B3 3 = (gsOf (j + 1)).flatMap frame := by
    rw [show (3 : Fin 331) = serSl 0 from rfl, b3h 0, z0]
  have h34 : B3 4 = CompareMachine.word (gsOf (j + 1)).length := by
    rw [show (4 : Fin 331) = serSl 2 from rfl, b3h 2, z2]
  -- 4: copy `frame E.bits`
  obtain ⟨o4, s4, -, k1, k2⟩ := cpStage E.bits (List.replicate
    (PCPPairReusable.capacity (PCPSerializerMass.mass (gsOf (j + 1))) - (frame E.bits).length) false)
  have d4 := s4.dock cpESl cpESl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B3 83 = _; rw [h383]; rfl
    · show B3 5 = _; rw [b3 _ (by decide), h25]; rfl
    · show B3 135 = _; rw [f3 _ (by decide)]; rfl
    · show B3 136 = _; rw [f3 _ (by decide)]; rfl)
  rw [zeroH] at d4
  set B4 := install cpESl B3 o4 with hB4
  have b4h : ∀ k, B4 (cpESl k) = o4 k := fun k => install_slot _ cpESl_inj _ _ _
  have b4 : ∀ t : Fin 331, (∀ k, (cpESl k).val ≠ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have f4 : ∀ t : Fin 331, 137 ≤ t.val → B4 t = [] := fun t ht => by
    rw [b4 _ (by intro k; rw [cpESl_val]; fin_cases k <;> simp <;> omega), f3 _ (by omega)]
  have h4E : B4 135 = frame E.bits := by
    rw [show (135 : Fin 331) = cpESl 2 from rfl, b4h 2, k2]
  have h45 : B4 5 = [false] := by rw [show (5 : Fin 331) = cpESl 1 from rfl, b4h 1, k1]
  -- 5: the constant `frame 0.bits = [false]`
  have d5 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock zSl zSl_inj (fun _ => 0) B4 (fun _ => rfl)
    (fun _ => f4 137 (by decide))
  rw [zeroH] at d5
  set B5 := install zSl B4 (fun _ => [false]) with hB5
  have b5 : ∀ t : Fin 331, t.val ≠ 137 → B5 t = B4 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have h5z : B5 137 = [false] := install_slot zSl zSl_inj _ _ 0
  have f5 : ∀ t : Fin 331, 138 ≤ t.val → B5 t = [] := fun t ht => by rw [b5 _ (by omega), f4 _ (by omega)]
  -- 6: the pair node: `encodeInt (j+1) = pair 0 E`
  obtain ⟨o6, r6, ⟨pd6, p26⟩, -⟩ := PCPPRequestPair.pair_run 0 E
  have d6 := (FrontLoopKit.step_of_ready r6).dock pairSl pairSl_inj (fun _ => 0) B5 (fun _ => rfl) (by
    intro k
    show B5 (pairSl k) = (if k.val = 2 then frame (0 : ℕ).bits else if k.val = 3 then frame E.bits else [])
    by_cases h2 : k.val = 2
    · rw [if_pos h2, show pairSl k = (137 : Fin 331) from Fin.ext (by simp [pairSl, h2]), h5z]; rfl
    · rw [if_neg h2]
      by_cases h3 : k.val = 3
      · rw [if_pos h3, show pairSl k = (135 : Fin 331) from Fin.ext (by simp [pairSl, h3]), b5 _ (by decide), h4E]
      · have hk := k.isLt
        rw [if_neg h3, f5 _ (by simp only [pairSl]; split_ifs <;> omega)])
  rw [zeroH] at d6
  set B6 := install pairSl B5 o6 with hB6
  have b6 : ∀ t : Fin 331, (t.val < 135 ∨ t.val = 136 ∨ 174 ≤ t.val) → B6 t = B5 t := fun t ht =>
    install_other _ _ _ _ (fun k e => by
      have hv := congrArg Fin.val e; simp only [pairSl] at hv; have hk := k.isLt; split_ifs at hv <;> omega)
  have f6 : ∀ t : Fin 331, 174 ≤ t.val → B6 t = [] := fun t ht => by rw [b6 _ (by omega), f5 _ (by omega)]
  have h6θ : B6 162 = frame θ.bits ++ List.replicate pd6 false :=
    (install_slot pairSl pairSl_inj B5 o6 26).trans p26
  -- 7: copy `frame θ.bits`
  obtain ⟨o7, s7, -, m1, m2⟩ := cpStage θ.bits (List.replicate pd6 false)
  have d7 := s7.dock cpTSl cpTSl_inj (fun _ => 0) B6 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B6 162 = _; rw [h6θ]; rfl
    · show B6 5 = _; rw [b6 _ (by decide), b5 _ (by decide), h45]; rfl
    · show B6 174 = _; rw [f6 _ (by decide)]; rfl
    · show B6 175 = _; rw [f6 _ (by decide)]; rfl)
  rw [zeroH] at d7
  set B7 := install cpTSl B6 o7 with hB7
  have b7h : ∀ k, B7 (cpTSl k) = o7 k := fun k => install_slot _ cpTSl_inj _ _ _
  have b7 : ∀ t : Fin 331, (∀ k, (cpTSl k).val ≠ t.val) → B7 t = B6 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have f7 : ∀ t : Fin 331, 176 ≤ t.val → B7 t = [] := fun t ht => by
    rw [b7 _ (by intro k; rw [cpTSl_val]; fin_cases k <;> simp <;> omega), f6 _ (by omega)]
  have h7θ : B7 174 = frame θ.bits := by
    rw [show (174 : Fin 331) = cpTSl 2 from rfl, b7h 2, m2]
  have h75 : B7 5 = [false] := by rw [show (5 : Fin 331) = cpTSl 1 from rfl, b7h 1, m1]
  have h71 : B7 1 = frame p3.bits := by
    rw [b7 _ (by intro k; rw [cpTSl_val]; fin_cases k <;> decide), b6 _ (by decide), b5 _ (by decide),
      b4 _ (by intro k; rw [cpESl_val]; fin_cases k <;> decide), b3 _ (by decide),
      b2 _ (by intro k; rw [incSl_val]; fin_cases k <;> decide), b1 _ (by decide)]
    simp [hB0, roundPIn]
  -- 8: copy `frame p3.bits`
  obtain ⟨o8, s8, n0, n1, n2⟩ := cpStage p3.bits []
  rw [List.append_nil] at s8 n0
  have d8 := s8.dock cpPSl cpPSl_inj (fun _ => 0) B7 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B7 1 = _; rw [h71]; rfl
    · show B7 5 = _; rw [h75]; rfl
    · show B7 176 = _; rw [f7 _ (by decide)]; rfl
    · show B7 177 = _; rw [f7 _ (by decide)]; rfl)
  rw [zeroH] at d8
  set B8 := install cpPSl B7 o8 with hB8
  have b8h : ∀ k, B8 (cpPSl k) = o8 k := fun k => install_slot _ cpPSl_inj _ _ _
  have b8 : ∀ t : Fin 331, (∀ k, (cpPSl k).val ≠ t.val) → B8 t = B7 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have f8 : ∀ t : Fin 331, 178 ≤ t.val → B8 t = [] := fun t ht => by
    rw [b8 _ (by intro k; rw [cpPSl_val]; fin_cases k <;> simp <;> omega), f7 _ (by omega)]
  have h8P : B8 176 = frame p3.bits := by
    rw [show (176 : Fin 331) = cpPSl 2 from rfl, b8h 2, n2]
  have h81 : B8 1 = frame p3.bits := by rw [show (1 : Fin 331) = cpPSl 0 from rfl, b8h 0, n0]
  have h85 : B8 5 = [false] := by rw [show (5 : Fin 331) = cpPSl 1 from rfl, b8h 1, n1]
  -- 9: the first cons: `cons θ p3`
  obtain ⟨o9, r9, ⟨pd9, q64⟩, -⟩ := PCPPRequestTaggedCons.cons_run θ p3
  have d9 := (FrontLoopKit.step_of_ready r9).dock cons1Sl cons1Sl_inj (fun _ => 0) B8 (fun _ => rfl) (by
    intro k
    show B8 (cons1Sl k) = PCPPRequestTaggedCons.input θ p3 k
    unfold PCPPRequestTaggedCons.input PCPPRequestPair.input PCPPairCanonical.input
    by_cases h2 : k.val = 2
    · rw [dif_pos (by omega)]; simp only [h2, if_true]
      rw [show cons1Sl k = (174 : Fin 331) from Fin.ext (by simp [cons1Sl, h2]), b8 _ (by
        intro k'; rw [cpPSl_val]; fin_cases k' <;> decide), h7θ]
    · by_cases h3 : k.val = 3
      · rw [dif_pos (by omega)]; simp only [h3, if_true, show (3 : ℕ) ≠ 2 by decide, if_false]
        rw [show cons1Sl k = (176 : Fin 331) from Fin.ext (by simp [cons1Sl, h3]), h8P]
      · have hk := k.isLt
        rw [f8 _ (by simp only [cons1Sl]; split_ifs <;> omega)]
        split_ifs <;> simp_all)
  rw [zeroH] at d9
  set B9 := install cons1Sl B8 o9 with hB9
  have b9 : ∀ t : Fin 331, (t.val < 174 ∨ t.val = 175 ∨ t.val = 177 ∨ 252 ≤ t.val) → B9 t = B8 t := fun t ht =>
    install_other _ _ _ _ (fun k e => by
      have hv := congrArg Fin.val e; simp only [cons1Sl] at hv; have hk := k.isLt; split_ifs at hv <;> omega)
  have f9 : ∀ t : Fin 331, 252 ≤ t.val → B9 t = [] := fun t ht => by rw [b9 _ (by omega), f8 _ (by omega)]
  have h9c : B9 240 = frame c1.bits ++ List.replicate pd9 false :=
    (install_slot cons1Sl cons1Sl_inj B8 o9 64).trans q64
  -- 10: copy `frame c1.bits`
  obtain ⟨o10, s10, -, u1, u2⟩ := cpStage c1.bits (List.replicate pd9 false)
  have d10 := s10.dock cpCSl cpCSl_inj (fun _ => 0) B9 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B9 240 = _; rw [h9c]; rfl
    · show B9 5 = _; rw [b9 _ (by decide), h85]; rfl
    · show B9 252 = _; rw [f9 _ (by decide)]; rfl
    · show B9 253 = _; rw [f9 _ (by decide)]; rfl)
  rw [zeroH] at d10
  set B10 := install cpCSl B9 o10 with hB10
  have b10h : ∀ k, B10 (cpCSl k) = o10 k := fun k => install_slot _ cpCSl_inj _ _ _
  have b10 : ∀ t : Fin 331, (∀ k, (cpCSl k).val ≠ t.val) → B10 t = B9 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have f10 : ∀ t : Fin 331, 254 ≤ t.val → B10 t = [] := fun t ht => by
    rw [b10 _ (by intro k; rw [cpCSl_val]; fin_cases k <;> simp <;> omega), f9 _ (by omega)]
  have h10c : B10 252 = frame c1.bits := by
    rw [show (252 : Fin 331) = cpCSl 2 from rfl, b10h 2, u2]
  have h105 : B10 5 = [false] := by
    rw [show (5 : Fin 331) = cpCSl 1 from rfl, b10h 1, u1]
  have h100 : B10 0 = frame wl.bits := by
    rw [b10 _ (by intro k; rw [cpCSl_val]; fin_cases k <;> decide), b9 _ (by decide),
      b8 _ (by intro k; rw [cpPSl_val]; fin_cases k <;> decide),
      b7 _ (by intro k; rw [cpTSl_val]; fin_cases k <;> decide), b6 _ (by decide), b5 _ (by decide),
      b4 _ (by intro k; rw [cpESl_val]; fin_cases k <;> decide), b3 _ (by decide),
      b2 _ (by intro k; rw [incSl_val]; fin_cases k <;> decide), b1 _ (by decide)]
    simp [hB0, roundPIn]
  -- 11: copy `frame wl.bits`
  obtain ⟨o11, s11, w0, w1, w2⟩ := cpStage wl.bits []
  rw [List.append_nil] at s11 w0
  have d11 := s11.dock cpWSl cpWSl_inj (fun _ => 0) B10 (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · show B10 0 = _; rw [h100]; rfl
    · show B10 5 = _; rw [h105]; rfl
    · show B10 254 = _; rw [f10 _ (by decide)]; rfl
    · show B10 255 = _; rw [f10 _ (by decide)]; rfl)
  rw [zeroH] at d11
  set B11 := install cpWSl B10 o11 with hB11
  have b11h : ∀ k, B11 (cpWSl k) = o11 k := fun k => install_slot _ cpWSl_inj _ _ _
  have b11 : ∀ t : Fin 331, (∀ k, (cpWSl k).val ≠ t.val) → B11 t = B10 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have f11 : ∀ t : Fin 331, 256 ≤ t.val → B11 t = [] := fun t ht => by
    rw [b11 _ (by intro k; rw [cpWSl_val]; fin_cases k <;> simp <;> omega), f10 _ (by omega)]
  have h11W : B11 254 = frame wl.bits := by
    rw [show (254 : Fin 331) = cpWSl 2 from rfl, b11h 2, w2]
  have h110 : B11 0 = frame wl.bits := by
    rw [show (0 : Fin 331) = cpWSl 0 from rfl, b11h 0, w0]
  have h115 : B11 5 = [false] := by
    rw [show (5 : Fin 331) = cpWSl 1 from rfl, b11h 1, w1]
  -- 12: the second cons: `cons wl c1`
  obtain ⟨o12, r12, ⟨pd12, v64⟩, -⟩ := PCPPRequestTaggedCons.cons_run wl c1
  have d12 := (FrontLoopKit.step_of_ready r12).dock cons2Sl cons2Sl_inj (fun _ => 0) B11 (fun _ => rfl) (by
    intro k
    show B11 (cons2Sl k) = PCPPRequestTaggedCons.input wl c1 k
    unfold PCPPRequestTaggedCons.input PCPPRequestPair.input PCPPairCanonical.input
    by_cases h2 : k.val = 2
    · rw [dif_pos (by omega)]; simp only [h2, if_true]
      rw [show cons2Sl k = (254 : Fin 331) from Fin.ext (by simp [cons2Sl, h2]), h11W]
    · by_cases h3 : k.val = 3
      · rw [dif_pos (by omega)]; simp only [h3, if_true, show (3 : ℕ) ≠ 2 by decide, if_false]
        rw [show cons2Sl k = (252 : Fin 331) from Fin.ext (by simp [cons2Sl, h3]),
          b11 _ (by intro k'; rw [cpWSl_val]; fin_cases k' <;> decide), h10c]
      · have hk := k.isLt
        rw [f11 _ (by simp only [cons2Sl]; split_ifs <;> omega)]
        split_ifs <;> simp_all)
  rw [zeroH] at d12
  set B12 := install cons2Sl B11 o12 with hB12
  have b12 : ∀ t : Fin 331, (t.val < 252 ∨ t.val = 253 ∨ t.val = 255 ∨ 330 ≤ t.val) → B12 t = B11 t := fun t ht =>
    install_other _ _ _ _ (fun k e => by
      have hv := congrArg Fin.val e; simp only [cons2Sl] at hv; have hk := k.isLt; split_ifs at hv <;> omega)
  have h12c : B12 318 = frame (codeB wl p3 j).bits ++ List.replicate pd12 false :=
    (install_slot cons2Sl cons2Sl_inj B11 o12 64).trans v64
  -- 13: the append
  obtain ⟨o13, s13, -, -, a2⟩ := appendBStage accL hacc (codeB wl p3 j).bits (List.replicate pd12 false)
  have d13 := s13.dock appSl appSl_inj (fun _ => 0) B12 (fun _ => rfl) (by
    intro k; rw [appendBIn_val]
    fin_cases k
    · show B12 318 = _; rw [h12c]; rfl
    · show B12 5 = _; rw [b12 _ (by decide), h115]; rfl
    · show B12 2 = _
      rw [b12 _ (by decide), b11 _ (by intro k'; rw [cpWSl_val]; fin_cases k' <;> decide),
        b10 _ (by intro k'; rw [cpCSl_val]; fin_cases k' <;> decide), b9 _ (by decide),
        b8 _ (by intro k'; rw [cpPSl_val]; fin_cases k' <;> decide),
        b7 _ (by intro k'; rw [cpTSl_val]; fin_cases k' <;> decide), b6 _ (by decide), b5 _ (by decide),
        b4 _ (by intro k'; rw [cpESl_val]; fin_cases k' <;> decide), b3 _ (by decide),
        b2 _ (by intro k'; rw [incSl_val]; fin_cases k' <;> decide), b1 _ (by decide)]
      simp [hB0, roundPIn]
    · show B12 330 = _; rw [b12 _ (by decide), f11 _ (by decide)]; rfl)
  rw [zeroH] at d13
  set B13 := install appSl B12 o13 with hB13
  have b13 : ∀ t : Fin 331, (∀ k, (appSl k).val ≠ t.val) → B13 t = B12 t := fun t ht =>
    install_other _ _ _ _ (fun k e => ht k (congrArg Fin.val e))
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq (d10.seq (d11.seq
    (d12.seq d13)))))))))))
  have run' : Step workerP _ (fun _ => 0) B0 (fun _ => 0) B13 := run
  refine ⟨B13, FrontKit.ready_of_step (run'.enlarge (by unfold roundPCost; exact le_refl _)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [b13 _ (by intro k; rw [appSl_val]; fin_cases k <;> decide), b12 _ (by decide), h110]
  · rw [b13 _ (by intro k; rw [appSl_val]; fin_cases k <;> decide), b12 _ (by decide),
      b11 _ (by intro k; rw [cpWSl_val]; fin_cases k <;> decide),
      b10 _ (by intro k; rw [cpCSl_val]; fin_cases k <;> decide), b9 _ (by decide), h81]
  · rw [show (2 : Fin 331) = appSl 2 from rfl]
    exact (install_slot appSl appSl_inj B12 o13 2).trans a2
  · rw [b13 _ (by intro k; rw [appSl_val]; fin_cases k <;> decide), b12 _ (by decide),
      b11 _ (by intro k; rw [cpWSl_val]; fin_cases k <;> decide),
      b10 _ (by intro k; rw [cpCSl_val]; fin_cases k <;> decide), b9 _ (by decide),
      b8 _ (by intro k; rw [cpPSl_val]; fin_cases k <;> decide),
      b7 _ (by intro k; rw [cpTSl_val]; fin_cases k <;> decide), b6 _ (by decide), b5 _ (by decide),
      b4 _ (by intro k; rw [cpESl_val]; fin_cases k <;> decide), h33, ← sgl_gsOf]
  · rw [b13 _ (by intro k; rw [appSl_val]; fin_cases k <;> decide), b12 _ (by decide),
      b11 _ (by intro k; rw [cpWSl_val]; fin_cases k <;> decide),
      b10 _ (by intro k; rw [cpCSl_val]; fin_cases k <;> decide), b9 _ (by decide),
      b8 _ (by intro k; rw [cpPSl_val]; fin_cases k <;> decide),
      b7 _ (by intro k; rw [cpTSl_val]; fin_cases k <;> decide), b6 _ (by decide), b5 _ (by decide),
      b4 _ (by intro k; rw [cpESl_val]; fin_cases k <;> decide), h34, gsOf, List.length_map]

/-! ## The loop: every bottom -/

open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.CWRoundA (idleA idleA_ready)

/-- The round's scratch: every tape but the two codes, the accumulator and the counter. -/
def scrP (k : Fin 326) : Fin 331 := ⟨k.val + 5, by omega⟩

theorem scrP_inj : Function.Injective scrP := fun a b h => Fin.ext (by have := congrArg Fin.val h; simp [scrP] at this; omega)

theorem scrP_iff (t : Fin 331) : (∃ k, scrP k = t) ↔ 5 ≤ t.val := by
  constructor
  · rintro ⟨k, rfl⟩; simp [scrP]
  · intro h; exact ⟨⟨t.val - 5, by omega⟩, Fin.ext (by simp [scrP]; omega)⟩

/-- **The bottoms' loop.** -/
noncomputable def foldP := foldLoop (foldBody workerP scrP (idleA (331 + 2)))

/-- The codes of the first `j` bottoms. -/
def accOf (wl p3 j : ℕ) : List (List Bool) := (List.range j).map fun i => (codeB wl p3 i).bits

theorem accOf_succ (wl p3 j : ℕ) : accOf wl p3 (j + 1) = accOf wl p3 j ++ [(codeB wl p3 j).bits] := by
  unfold accOf; rw [List.range_succ, List.map_append]; rfl

theorem codeB_pos (wl p3 j : ℕ) : 0 < codeB wl p3 j := by
  unfold codeB cons
  have := Nat.add_le_pair 1 (Nat.pair wl (Nat.pair 1 (Nat.pair (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))) p3)))
  omega

theorem accOf_ne (wl p3 j : ℕ) : ∀ g ∈ accOf wl p3 j, g ≠ [] := by
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  intro h
  have hp := codeB_pos wl p3 i
  have hv := CanonicalPositiveOutput.nat_bits_value (codeB wl p3 i)
  rw [h] at hv
  simp [RadixSemantics.value] at hv
  omega

/-- The round's entry at bottom `j`. -/
def Qp (wl p3 j : ℕ) : Fin 331 → List Bool :=
  roundPIn (frame wl.bits) (frame p3.bits) ((accOf wl p3 j).flatMap frame) (sgl j.bits)
    (CompareMachine.word j.bits.length)

/-- **The bottoms' loop is ready**: from the padded round tapes at bottom `0` and the unary count `k`, the loop ends
at the padded round tapes at bottom `k`: the codes of every bottom, in order, and the counter at `k`. -/
theorem foldP_run (wl p3 k total capT cw : ℕ) (hcap : total + 1 ≤ capT)
    (hcw : ∀ j < k, roundPCost wl p3 j (accOf wl p3 j) ≤ cw) (hcwT : cw + 1 ≤ total)
    (hlen : ∀ j ≤ k, ∀ t, (Qp wl p3 j t).length ≤ total) :
    ClockJoin.ReadyRun foldP (1 + 1 + (k * (cw + 1 + (2 * total + 4 + 1 + 0) + 2) + k + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch scrP total (Qp wl p3 0)) total capT) (fun _ => CompareMachine.word k))
      (Fin.addCases (roundTapes (padScratch scrP total (Qp wl p3 k)) total capT) (fun _ => CompareMachine.word k)) := by
  have hround : ∀ j, ∃ out : Fin 331 → List Bool, j < k →
      ClockJoin.ReadyRun workerP cw (Qp wl p3 j) out ∧ out 0 = frame wl.bits ∧ out 1 = frame p3.bits ∧
      out 2 = (accOf wl p3 (j + 1)).flatMap frame ∧ out 3 = sgl (j + 1).bits ∧
      out 4 = CompareMachine.word (j + 1).bits.length := by
    intro j
    by_cases hj : j < k
    · obtain ⟨out, h1, h2, h3, h4, h5, h6⟩ := roundP_run wl p3 j (accOf wl p3 j) (accOf_ne wl p3 j)
      exact ⟨out, fun _ => ⟨ClockJoin.enlarge _ _ _ _ _ h1 (hcw j hj), h2, h3, by rw [h4, accOf_succ], h5, h6⟩⟩
    · exact ⟨fun _ => [], fun h => absurd h hj⟩
  choose Q' hQ' using hround
  have hwork : ∀ j, j < k → ClockJoin.ReadyRun workerP cw (Qp wl p3 j) (Q' j) := fun j hj => (hQ' j hj).1
  exact uniformFold_ready workerP scrP scrP_inj (idleA (331 + 2)) total capT cw 0 k hcap (Qp wl p3) Q' hwork
    (fun j hj t => by
      have hl := ready_lengths (hwork j hj) total (hlen j hj.le) (scrP t)
      have : max total (cw + 1) = total := max_eq_left (by omega)
      omega)
    (fun j hj => by
      have e : blankScratch scrP (Q' j) = Qp wl p3 (j + 1) := by
        funext t
        unfold blankScratch
        by_cases ht : ∃ i, scrP i = t
        · rw [if_pos ht]
          have h5 := (scrP_iff t).mp ht
          unfold Qp roundPIn
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg ht]
          have h5 : t.val < 5 := by by_contra hc'; exact ht ((scrP_iff t).mpr (by omega))
          obtain ⟨-, o0, o1, o2, o3, o4⟩ := hQ' j hj
          unfold Qp roundPIn
          by_cases h0 : t.val = 0
          · rw [if_pos h0, show t = 0 from Fin.ext h0, o0]
          · by_cases h1 : t.val = 1
            · rw [if_neg h0, if_pos h1, show t = 1 from Fin.ext h1, o1]
            · by_cases h2 : t.val = 2
              · rw [if_neg h0, if_neg h1, if_pos h2, show t = 2 from Fin.ext h2, o2]
              · by_cases h3 : t.val = 3
                · rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3, show t = 3 from Fin.ext h3, o3]
                · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos (by omega), show t = 4 from Fin.ext (by omega),
                    o4]
      rw [e]; exact idleA_ready _ _)

end NearCubicWires.WireExponent3_5.UnionMachine.CWParRound
