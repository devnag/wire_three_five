import Proof.Wire_3_5.Compiler.MachineC3aCount
import Proof.Wire_3_5.Compiler.MachineTopWrite

/-! # C3a machine, the pool builder's constants (P3:1636-1664)

Paper: alg:pullback, "Every child becomes an equation `E_{j,y}(z) = a_{j,y}(z_L) + b_{j,y}(z_R) = 0`" with the
children "remain disjoint and represent the pulled-back threshold exactly" (P3:1636-1650), in the star instance with
the common pool of `P_ex` labels (P3:1661-1664). The pool builder's machine (`pool_run`) reads its registers and
streams from blank constants built from the request's unary sizes. Three writers here (the others are the C3
writers of `TopWrite`):
* **`k_run`**: the bit-length counter `false :: 1^{h + B + 1}` (it covers every child coefficient, `< 2^h` by
  `CoefFit`, and every child count, `≤ B`);
* **`ent_run`**: the first children-table entry `frame (entC Q' P_ex 0)` (label `0`: the size field `0^{Q'}`, the
  mark, the mask `binary P_ex 1`), with a branch on whether the pool is empty;
* **`zp_run`**: a zero-padding stream `streamTape (zeroRecs h k) []` (the `k` zero pairs padding a column half to the
  dense width), one pair of framed `0^h` per unit.
The paper quantities are the dense children's widths and the pool's label count. Main declarations: `kM`,
**`k_run`**, `entM`, **`ent_run`**, `zpM`, **`zp_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Const
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Top NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Dec NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Count
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

theorem flatten_rep_one (a : ℕ) (b : Bool) : (List.replicate a [b]).flatten = List.replicate a b := by
  induction a with
  | zero => rfl
  | succ a ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl

/-! ## The bit-length counter `false :: 1^{h + B + 1}` (tapes: `1^h`, `1^B`, the target) -/

noncomputable def kRawM := Composition.machine (Composition.machine (Composition.machine
  (RecoveryFocus.machine qT (putsM [false])) (RecoveryFocus.machine q0 (loopWM [true])))
  (RecoveryFocus.machine q1 (loopWM [true]))) (RecoveryFocus.machine qT (putsM [true]))
noncomputable def kM := MaskedReset.machine kRawM (fun _ => true)

def kRawCost (h B : ℕ) : ℕ := putsCost [false] + 1 + loopCost [true] h + 1 + loopCost [true] B + 1 + putsCost [true]
def kCost (h B : ℕ) : ℕ := 2 * kRawCost h B + 2

theorem k_raw (h B : ℕ) :
    Step kRawM (kRawCost h B) ![0, 0, 0] ![List.replicate h true, List.replicate B true, []]
      ![h, B, (false :: List.replicate (h + B + 1) true).length]
      ![List.replicate h true, List.replicate B true, false :: List.replicate (h + B + 1) true] := by
  have s1 := dockRun (puts_run [false] []) qT qT_inj ![0, 0, 0] ![List.replicate h true, List.replicate B true, []]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s1
  have s2 := dockRun (loopW_run0 [true] h ([] ++ [false])) q0 q0_inj ![0, 0, ([] ++ [false]).length]
    ![List.replicate h true, List.replicate B true, [] ++ [false]]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q0, dockH_q0] at s2
  have s3 := dockRun (loopW_run0 [true] B ([] ++ [false] ++ (List.replicate h [true]).flatten)) q1 q1_inj
    ![h, 0, ([] ++ [false] ++ (List.replicate h [true]).flatten).length]
    ![List.replicate h true, List.replicate B true, [] ++ [false] ++ (List.replicate h [true]).flatten]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q1, dockH_q1] at s3
  have s4 := dockRun (puts_run [true] ([] ++ [false] ++ (List.replicate h [true]).flatten ++
      (List.replicate B [true]).flatten)) qT qT_inj
    ![h, B, ([] ++ [false] ++ (List.replicate h [true]).flatten ++ (List.replicate B [true]).flatten).length]
    ![List.replicate h true, List.replicate B true,
      [] ++ [false] ++ (List.replicate h [true]).flatten ++ (List.replicate B [true]).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s4
  have e : [] ++ [false] ++ (List.replicate h [true]).flatten ++ (List.replicate B [true]).flatten ++ [true] =
      false :: List.replicate (h + B + 1) true := by
    rw [flatten_rep_one, flatten_rep_one, List.replicate_add, List.replicate_add]; simp
  rw [e] at s4
  exact (((s1.congr rfl rfl).seq (s2.congr rfl rfl)).seq (s3.congr rfl rfl)).seq (s4.congr rfl rfl)

/-- **The bit-length counter**, every head back at cell `0`. -/
theorem k_run (h B cap : ℕ) (hcap : kRawCost h B ≤ cap) :
    Step kM (kCost h B) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) ![List.replicate h true, List.replicate B true, []]
        (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        ![List.replicate h true, List.replicate B true, false :: List.replicate (h + B + 1) true]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := (k_raw h B).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  exact (m.congr_in (Top.addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (Top.mask_heads_zero _) rfl

/-! ## The first children-table entry `frame (entC Q' P_ex 0)` (tapes: `1^{Q'}`, `1^{P_ex}`, the target) -/

noncomputable def entRawM := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (RecoveryFocus.machine q0 (loopWM [true, false])) (RecoveryFocus.machine qT (putsM [true, true])))
  (branchM 1 (Composition.machine (RecoveryFocus.machine qT (putsM [true, true])) (RecoveryFocus.machine ![(1 : Fin 3)] moveM))
    (idle 3)))
  (RecoveryFocus.machine q1 (loopWM [true, false]))) (RecoveryFocus.machine qT (putsM [false]))
noncomputable def entM := MaskedReset.machine entRawM (fun _ => true)

def entRawCost (Q W : ℕ) : ℕ :=
  loopCost [true, false] Q + 1 + putsCost [true, true] + 1 + (putsCost [true, true] + 1 + 1 + 2) + 1 +
    loopCost [true, false] W + 1 + putsCost [false]
def entCost (Q W : ℕ) : ℕ := 2 * entRawCost Q W + 2

theorem ent_word0 (Q : ℕ) :
    [] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++ [] ++ [false] = frame (entC Q 0 0) := by
  simp [entC, entryWord, thermo, frame_pairs, List.map_replicate, binary]

theorem ent_word (Q k : ℕ) :
    [] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++ [true, true] ++
      (List.replicate k [true, false]).flatten ++ [false] = frame (entC Q (k + 1) 0) := by
  simp [entC, entryWord, thermo, frame_pairs, List.map_replicate, binary, GF2.binary_zero]

theorem ent_raw (Q W : ℕ) :
    Step entRawM (entRawCost Q W) ![0, 0, 0] ![List.replicate Q true, List.replicate W true, []]
      ![Q, W, (frame (entC Q W 0)).length] ![List.replicate Q true, List.replicate W true, frame (entC Q W 0)] := by
  have s1 := dockRun (loopW_run0 [true, false] Q []) q0 q0_inj ![0, 0, 0]
    ![List.replicate Q true, List.replicate W true, []] (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q0, dockH_q0] at s1
  set o1 := [] ++ (List.replicate Q [true, false]).flatten
  have s2 := dockRun (puts_run [true, true] o1) qT qT_inj ![Q, 0, o1.length]
    ![List.replicate Q true, List.replicate W true, o1] (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s2
  set o2 := o1 ++ [true, true]
  cases W with
  | zero =>
    have b := branch_false (1 : Fin 3)
      (Composition.machine (RecoveryFocus.machine qT (putsM [true, true])) (RecoveryFocus.machine ![(1 : Fin 3)] moveM))
      (idleStep ![Q, 0, o2.length] ![List.replicate Q true, List.replicate 0 true, o2]) (by rfl)
    have s4 := dockRun (loopW_run [true, false] [] [] rfl 0 o2) q1 q1_inj ![Q, 0, o2.length]
      ![List.replicate Q true, [] ++ List.replicate 0 true ++ [], o2] (by intro k; fin_cases k <;> rfl)
      (by intro k; fin_cases k <;> rfl)
    rw [install_q1, dockH_q1] at s4
    have s5 := dockRun (puts_run [false] (o2 ++ (List.replicate 0 [true, false]).flatten)) qT qT_inj
      ![Q, 0, (o2 ++ (List.replicate 0 [true, false]).flatten).length]
      ![List.replicate Q true, [] ++ List.replicate 0 true ++ [], o2 ++ (List.replicate 0 [true, false]).flatten]
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [install_qT, dockH_qT] at s5
    have e : o2 ++ (List.replicate 0 [true, false]).flatten ++ [false] = frame (entC Q 0 0) := by
      rw [← ent_word0]; simp [o2, o1]
    rw [e] at s5
    refine (((((s1.congr rfl rfl).seq (s2.congr rfl rfl)).seq b).seq (s4.congr rfl ?_)).seq (s5.congr ?_ ?_)).enlarge
      (by simp only [entRawCost, Top.loopCost, putsCost]; omega)
    · funext k; fin_cases k <;> rfl
    · funext k; fin_cases k <;> simp
    · funext k; fin_cases k <;> simp
  | succ k =>
    have p1 := dockRun (puts_run [true, true] o2) qT qT_inj ![Q, 0, o2.length]
      ![List.replicate Q true, List.replicate (k + 1) true, o2] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
    rw [install_qT, dockH_qT] at p1
    set o3 := o2 ++ [true, true]
    have p2 := dockRun (moveStep (List.replicate (k + 1) true) 0) ![(1 : Fin 3)] (one_inj _) ![Q, 0, o3.length]
      ![List.replicate Q true, List.replicate (k + 1) true, o3] (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
    rw [dockH_one, install_one] at p2
    simp only [Matrix.cons_val_zero, upd3_1] at p2
    have b := branch_true (1 : Fin 3) (idle 3) ((p1.congr rfl rfl).seq p2) (by rfl)
    have s4 := dockRun (loopW_run [true, false] [true] [] rfl k o3) q1 q1_inj ![Q, 1, o3.length]
      ![List.replicate Q true, [true] ++ List.replicate k true ++ [], o3] (by intro j; fin_cases j <;> rfl)
      (by intro j; fin_cases j <;> rfl)
    rw [install_q1, dockH_q1] at s4
    have s5 := dockRun (puts_run [false] (o3 ++ (List.replicate k [true, false]).flatten)) qT qT_inj
      ![Q, [true].length + k, (o3 ++ (List.replicate k [true, false]).flatten).length]
      ![List.replicate Q true, [true] ++ List.replicate k true ++ [], o3 ++ (List.replicate k [true, false]).flatten]
      (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
    rw [install_qT, dockH_qT] at s5
    have e : o3 ++ (List.replicate k [true, false]).flatten ++ [false] = frame (entC Q (k + 1) 0) := by
      rw [← ent_word]
    rw [e] at s5
    have s4' : Step (RecoveryFocus.machine q1 (loopWM [true, false])) (loopCost [true, false] k)
        ![Q, 1, o3.length] ![List.replicate Q true, List.replicate (k + 1) true, o3]
        ![Q, [true].length + k, (o3 ++ (List.replicate k [true, false]).flatten).length]
        ![List.replicate Q true, List.replicate (k + 1) true, o3 ++ (List.replicate k [true, false]).flatten] := by
      refine (s4.congr_in rfl ?_).congr rfl ?_
      · funext j; fin_cases j <;> simp [List.replicate_succ]
      · funext j; fin_cases j <;> simp [List.replicate_succ]
    have s5' : Step (RecoveryFocus.machine qT (putsM [false])) (putsCost [false])
        ![Q, [true].length + k, (o3 ++ (List.replicate k [true, false]).flatten).length]
        ![List.replicate Q true, List.replicate (k + 1) true, o3 ++ (List.replicate k [true, false]).flatten]
        ![Q, k + 1, (frame (entC Q (k + 1) 0)).length]
        ![List.replicate Q true, List.replicate (k + 1) true, frame (entC Q (k + 1) 0)] := by
      refine (s5.congr_in rfl ?_).congr ?_ ?_
      · funext j; fin_cases j <;> simp [List.replicate_succ]
      · funext j; fin_cases j <;> simp; omega
      · funext j; fin_cases j <;> simp [List.replicate_succ]
    have b' := b.congr (hout' := ![Q, 1, o3.length]) (by funext j; fin_cases j <;> rfl) rfl
    exact (((((s1.congr rfl rfl).seq (s2.congr rfl rfl)).seq b').seq s4').seq s5').enlarge
      (by simp only [entRawCost, Top.loopCost, putsCost]; omega)

/-- **The first children-table entry**, every head back at cell `0`. -/
theorem ent_run (Q W cap : ℕ) (hcap : entRawCost Q W ≤ cap) :
    Step entM (entCost Q W) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) ![List.replicate Q true, List.replicate W true, []]
        (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) ![List.replicate Q true, List.replicate W true, frame (entC Q W 0)]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := (ent_raw Q W).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  exact (m.congr_in (Top.addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (Top.mask_heads_zero _) rfl

/-! ## A zero-padding stream `streamTape (zeroRecs h k) []`
(tapes: `1^h`, the padded unary count `1^k`, the target, the record writer's log) -/

/-- One framed `0^h` at the target's cursor (tapes: `1^h`, the target). -/
noncomputable def recRawM := Composition.machine (loopWM [true, false]) (RecoveryFocus.machine ![(1 : Fin 2)] (putsM [false]))
/-- The same with the `1^h` cursor returned to cell `0` (the target's cursor stays at its end). -/
noncomputable def recM := MaskedReset.machine recRawM (fun i => decide (i = 0))

def recRawCost (h : ℕ) : ℕ := loopCost [true, false] h + 1 + putsCost [false]

theorem frame_zeros (h : ℕ) : (List.replicate h [true, false]).flatten ++ [false] = frame (binary h 0) := by
  rw [GF2.binary_zero, frame_pairs, pairs_rep]

theorem rec_run (h : ℕ) (o : List Bool) (capI : ℕ) (hcap : recRawCost h ≤ capI) :
    Step recM (2 * recRawCost h + 2)
      (Fin.addCases (motive := fun _ => ℕ) ![0, o.length] (fun _ : Fin 1 => 0))
      (Fin.addCases (motive := fun _ => List Bool) ![List.replicate h true, o] (fun _ : Fin 1 => List.replicate capI false))
      (Fin.addCases (motive := fun _ => ℕ) ![0, (o ++ frame (binary h 0)).length] (fun _ : Fin 1 => 0))
      (Fin.addCases (motive := fun _ => List Bool) ![List.replicate h true, o ++ frame (binary h 0)]
        (fun _ : Fin 1 => List.replicate capI false)) := by
  have s1 := loopW_run0 [true, false] h o
  have s2 := dockRun (puts_run [false] (o ++ (List.replicate h [true, false]).flatten)) ![(1 : Fin 2)] (one_inj _)
    ![h, (o ++ (List.replicate h [true, false]).flatten).length] ![List.replicate h true, o ++ (List.replicate h [true, false]).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [dockH_one, install_one] at s2
  simp only [Matrix.cons_val_zero, upd2_1] at s2
  have e : o ++ (List.replicate h [true, false]).flatten ++ [false] = o ++ frame (binary h 0) := by
    rw [List.append_assoc, frame_zeros]
  rw [e] at s2
  have m := (s1.seq s2).mask (fun i => decide (i = 0)) (by intro i hi; fin_cases i <;> simp_all) hcap
  have hh : (fun i : Fin 2 => if decide (i = 0) = true then 0 else ![h, (o ++ frame (binary h 0)).length] i) =
      ![0, (o ++ frame (binary h 0)).length] := by
    funext i; fin_cases i <;> rfl
  rw [hh] at m
  exact m

/-- The records written after `j` units. -/
def zpOut (h j : ℕ) : List Bool := (List.replicate (j + j) (frame (binary h 0))).flatten

def zpS : Fin 3 → Fin 4 := ![0, 2, 3]

theorem zpS_inj : Function.Injective zpS := by decide

/-- One unit: two framed `0^h`, then the count's cursor on. -/
noncomputable def zpBodyM := Composition.machine (Composition.machine (RecoveryFocus.machine zpS recM)
  (RecoveryFocus.machine zpS recM)) (RecoveryFocus.machine ![(1 : Fin 4)] moveM)
noncomputable def zpLoopM := StreamController.machine zpBodyM 1
noncomputable def zpRawM := Composition.machine zpLoopM (RecoveryFocus.machine ![(2 : Fin 4)] (putsM [false]))
/-- **The zero-padding stream writer**, every head back at cell `0`. -/
noncomputable def zpM := MaskedReset.machine zpRawM (fun _ => true)

def zpBodyCost (h : ℕ) : ℕ := (2 * recRawCost h + 2) + 1 + (2 * recRawCost h + 2) + 1 + 1
def zpRawCost (h k : ℕ) : ℕ := k * (zpBodyCost h + 2) + 1 + 1 + putsCost [false]
def zpCost (h k : ℕ) : ℕ := 2 * zpRawCost h k + 2

theorem zp_body (h k : ℕ) (post : List Bool) (capI : ℕ) (hcap : recRawCost h ≤ capI) (j : ℕ) :
    Step zpBodyM (zpBodyCost h) ![0, j, (zpOut h j).length, 0]
      ![List.replicate h true, [] ++ List.replicate k true ++ post, zpOut h j, List.replicate capI false]
      ![0, j + 1, (zpOut h (j + 1)).length, 0]
      ![List.replicate h true, [] ++ List.replicate k true ++ post, zpOut h (j + 1), List.replicate capI false] := by
  set SRC := [] ++ List.replicate k true ++ post
  have r1 := dockRun (rec_run h (zpOut h j) capI hcap) zpS zpS_inj ![0, j, (zpOut h j).length, 0]
    ![List.replicate h true, SRC, zpOut h j, List.replicate capI false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have ea : install zpS ![List.replicate h true, SRC, zpOut h j, List.replicate capI false]
      (Fin.addCases (motive := fun _ => List Bool) ![List.replicate h true, zpOut h j ++ frame (binary h 0)]
        (fun _ : Fin 1 => List.replicate capI false)) =
      ![List.replicate h true, SRC, zpOut h j ++ frame (binary h 0), List.replicate capI false] := by
    funext z; fin_cases z <;> (rw [install_eval _ zpS_inj]; rfl)
  have eh : dockH zpS ![0, j, (zpOut h j).length, 0]
      (Fin.addCases (motive := fun _ => ℕ) ![0, (zpOut h j ++ frame (binary h 0)).length] (fun _ : Fin 1 => 0)) =
      ![0, j, (zpOut h j ++ frame (binary h 0)).length, 0] := by
    funext z; fin_cases z <;> (rw [dockH_eval _ zpS_inj]; rfl)
  rw [ea, eh] at r1
  have r2 := dockRun (rec_run h (zpOut h j ++ frame (binary h 0)) capI hcap) zpS zpS_inj
    ![0, j, (zpOut h j ++ frame (binary h 0)).length, 0]
    ![List.replicate h true, SRC, zpOut h j ++ frame (binary h 0), List.replicate capI false]
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have ea2 : install zpS ![List.replicate h true, SRC, zpOut h j ++ frame (binary h 0), List.replicate capI false]
      (Fin.addCases (motive := fun _ => List Bool)
        ![List.replicate h true, zpOut h j ++ frame (binary h 0) ++ frame (binary h 0)]
        (fun _ : Fin 1 => List.replicate capI false)) =
      ![List.replicate h true, SRC, zpOut h j ++ frame (binary h 0) ++ frame (binary h 0), List.replicate capI false] := by
    funext z; fin_cases z <;> (rw [install_eval _ zpS_inj]; rfl)
  have eh2 : dockH zpS ![0, j, (zpOut h j ++ frame (binary h 0)).length, 0]
      (Fin.addCases (motive := fun _ => ℕ) ![0, (zpOut h j ++ frame (binary h 0) ++ frame (binary h 0)).length]
        (fun _ : Fin 1 => 0)) =
      ![0, j, (zpOut h j ++ frame (binary h 0) ++ frame (binary h 0)).length, 0] := by
    funext z; fin_cases z <;> (rw [dockH_eval _ zpS_inj]; rfl)
  rw [ea2, eh2] at r2
  have hout : zpOut h j ++ frame (binary h 0) ++ frame (binary h 0) = zpOut h (j + 1) := by
    unfold zpOut
    rw [show j + 1 + (j + 1) = (j + j) + 1 + 1 by omega, List.replicate_succ', List.replicate_succ']
    simp
  rw [hout] at r2
  have r3 := dockRun (moveStep SRC j) ![(1 : Fin 4)] (one_inj _) ![0, j, (zpOut h (j + 1)).length, 0]
    ![List.replicate h true, SRC, zpOut h (j + 1), List.replicate capI false]
    (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_one, install_one] at r3
  simp only [Matrix.cons_val_zero] at r3
  have u1 : Function.update ![0, j, (zpOut h (j + 1)).length, 0] (1 : Fin 4) (j + 1) =
      ![0, j + 1, (zpOut h (j + 1)).length, 0] := by funext z; fin_cases z <;> rfl
  have u2 : Function.update ![List.replicate h true, SRC, zpOut h (j + 1), List.replicate capI false] (1 : Fin 4) SRC =
      ![List.replicate h true, SRC, zpOut h (j + 1), List.replicate capI false] := by funext z; fin_cases z <;> rfl
  rw [u1, u2] at r3
  exact (r1.seq r2).seq r3

theorem upd4_2 {α : Type} (a b c d x : α) : Function.update ![a, b, c, d] 2 x = ![a, b, x, d] := by
  funext i; fin_cases i <;> rfl

theorem rep_pairs (x : List Bool) : ∀ k : ℕ,
    ((List.replicate k [x, x]).flatten).flatMap frame = (List.replicate (k + k) (frame x)).flatten
  | 0 => rfl
  | k + 1 => by
    have e : k + 1 + (k + 1) = (k + k).succ.succ := by omega
    rw [e, List.replicate_succ, List.replicate_succ, List.replicate_succ, List.flatten_cons, List.flatten_cons,
      List.flatten_cons, List.flatMap_append, rep_pairs x k]
    simp

/-- **The zero-padding stream**: from `1^h` and the padded count `1^k`, the stream of `k` zero pairs. -/
theorem zp_run (h k S capI cap : ℕ) (hcapI : recRawCost h ≤ capI) (hcap : zpRawCost h k ≤ cap) :
    Step zpM (zpCost h k) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        ![List.replicate h true, ZeroPadding.pad S (List.replicate k true), [], List.replicate capI false]
        (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        ![List.replicate h true, ZeroPadding.pad S (List.replicate k true), streamTape (zeroRecs h k) [],
          List.replicate capI false] (fun _ : Fin 1 => List.replicate cap false)) := by
  have hsrc : ZeroPadding.pad S (List.replicate k true) =
      [] ++ List.replicate k true ++ List.replicate (S - k) false := by
    simp [ZeroPadding.pad]
  have hl := onesRun zpBodyM 1 [] (List.replicate (S - k) false) k (by generalize S - k = c; cases c <;> rfl)
    (fun j => ![0, j, (zpOut h j).length, 0])
    (fun j => ![List.replicate h true, [] ++ List.replicate k true ++ List.replicate (S - k) false, zpOut h j,
      List.replicate capI false]) (fun _ => rfl) (fun j => by simp) (zpBodyCost h)
    (fun j _ => zp_body h k _ capI hcapI j)
  have hp := dockRun (puts_run [false] (zpOut h k)) ![(2 : Fin 4)] (one_inj _) ![0, k, (zpOut h k).length, 0]
    ![List.replicate h true, [] ++ List.replicate k true ++ List.replicate (S - k) false, zpOut h k,
      List.replicate capI false] (by intro i; fin_cases i; rfl) (by intro i; fin_cases i; rfl)
  rw [dockH_one, install_one] at hp
  simp only [Matrix.cons_val_zero] at hp
  have hw : zpOut h k ++ [false] = streamTape (zeroRecs h k) [] := by
    unfold zpOut zeroRecs streamTape pnWords
    simp only [pn, Int.toNat_zero, neg_zero]
    rw [rep_pairs]
  have raw : Step zpRawM (zpRawCost h k)
      ![0, 0, 0, 0] ![List.replicate h true, [] ++ List.replicate k true ++ List.replicate (S - k) false, [],
        List.replicate capI false]
      (Function.update ![0, k, (zpOut h k).length, 0] 2 (zpOut h k ++ [false]).length)
      (Function.update ![List.replicate h true, [] ++ List.replicate k true ++ List.replicate (S - k) false, zpOut h k,
        List.replicate capI false] 2 (zpOut h k ++ [false])) := by
    refine (hl.congr_in ?_ ?_).seq hp
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have m := raw.mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  rw [hw] at m
  refine (m.congr_in ?_ ?_).congr (Top.mask_heads_zero _) ?_
  · exact Top.addCases_zero _ (by intro i; fin_cases i <;> rfl)
  · rw [hsrc]
  · rw [hsrc, upd4_2]


end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Const
