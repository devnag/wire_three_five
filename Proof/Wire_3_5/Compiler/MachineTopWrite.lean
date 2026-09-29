import Proof.Wire_3_5.Compiler.MachineTopLoad

/-! # C3 v2 top level, T2 (part 1): writing the constant words (P3:1916-1936)

Paper: the compiler stages of alg:compiler, "Multiply the expression by `2^{m−1}` [...] Substitute the disjoint exact
children in each polynomial [...] Apply Lemma alg:binlift at precision `Q'` to each polynomial" (P3:1918-1932), run
on registers and templates whose widths are fixed by `Q'`, `P_ex`, `m`, `p` and the dense width. Before the stages run,
their constant tapes are written from the unary parameters of the input record (T1): each constant is a word of runs
of one bit, written by a loop over a unary tape (`loopW_run`: the fixed word `u` once per `1`) and fixed puts
(`puts_run`), with every head returned to cell 0 by a masked reset.

The writers (each with its paper quantity): `wRun` (`frame (b^a)`: the counter `frame (binary m 0)`, the all-ones
`frame (1^m)`, the zero field `frame (0^{p+1})`), `wZero` (the zero register `frame (zeroT Q' P_ex)`), `wZ0` (the entry of
the empty union `frame (ew Q' P_ex (0,0))`), `wLast` / `wLevel` (the lift templates `lastT`, `levelT`), `wRaw2` (the
unary width `1^{2·width}`), `wTS` (the empty stack stream) and `wCells` (the one-cell flags). Main declarations:
`putsM`, **`puts_run`**, `loopWM`, **`loopW_run`**, `frame_pairs`, the writers and their `_run` theorems. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## A fixed word -/

/-- The state count of `putsM`. -/
def putsS : List Bool → ℕ
  | [] => 1
  | _ :: u => 2 + putsS u

/-- Write the fixed word `u`, one cell per step. -/
noncomputable def putsM : (u : List Bool) → Machine 1 (putsS u)
  | [] => idle 1
  | b :: u => Composition.machine (putM b) (putsM u)

/-- The cost of `putsM u`. -/
def putsCost : List Bool → ℕ
  | [] => 0
  | _ :: u => 1 + 1 + putsCost u

theorem overlay_nil_right (o : List Bool) : overlay o [] = o := by simp [overlay]

/-- **A fixed word** is appended at the cursor. -/
theorem puts_run : ∀ (u o : List Bool),
    Step (putsM u) (putsCost u) ![o.length] ![o] ![(o ++ u).length] ![o ++ u]
  | [], o => by
    rw [List.append_nil]
    exact idleStep _ _
  | b :: u, o => by
    have h1 := putStep b (overlay o []) o.length
    rw [overlay_write, overlay_nil_right, overlay_nil_right] at h1
    have e1 : o.length + 1 = (o ++ [b]).length := by simp
    rw [e1] at h1
    have h2 := puts_run u (o ++ [b])
    have e3 : o ++ [b] ++ u = o ++ b :: u := by simp
    rw [e3] at h2
    exact h1.seq h2

/-! ## A fixed word once per `1` of a unary run -/

def w0 : Fin 1 → Fin 2 := ![0]
def w1 : Fin 1 → Fin 2 := ![1]

theorem w0_inj : Function.Injective w0 := by decide

theorem install_w0 (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install w0 A v = ![v 0, A 1] := by
  funext i
  fin_cases i
  · exact install_slot w0 w0_inj A v 0
  · exact install_other w0 A v 1 (by decide)

theorem dockH_w0 (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH w0 H v = ![v 0, H 1] := by
  funext i
  fin_cases i
  · exact dockH_slot w0 w0_inj H v 0
  · exact dockH_other w0 H v 1 (by decide)

theorem w1_inj : Function.Injective w1 := by decide

theorem install_w1 (A : Fin 2 → List Bool) (v : Fin 1 → List Bool) :
    install w1 A v = ![A 0, v 0] := by
  funext i
  fin_cases i
  · exact install_other w1 A v 0 (by decide)
  · exact install_slot w1 w1_inj A v 0

theorem dockH_w1 (H : Fin 2 → ℕ) (v : Fin 1 → ℕ) :
    dockH w1 H v = ![H 0, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other w1 H v 0 (by decide)
  · exact dockH_slot w1 w1_inj H v 0


/-- The loop body: step the unary source, append `u` to the target. -/
noncomputable def loopBodyM (u : List Bool) :=
  Composition.machine (RecoveryFocus.machine w0 moveM) (RecoveryFocus.machine w1 (putsM u))

/-- **The word loop**: `u` once per `1` of the source run. -/
noncomputable def loopWM (u : List Bool) := StreamController.machine (loopBodyM u) 0

/-- The cost of the word loop over `a` ones. -/
def loopCost (u : List Bool) (a : ℕ) : ℕ := a * (1 + 1 + putsCost u + 2) + 1

theorem flat_succ (u : List Bool) (j : ℕ) :
    (List.replicate (j + 1) u).flatten = (List.replicate j u).flatten ++ u := by
  rw [List.replicate_succ', List.flatten_append, List.flatten_singleton]

/-- **The word loop runs**: the target gets `u^a`, the source cursor passes the run. -/
theorem loopW_run (u P post : List Bool) (hpost : readTapeBit post 0 = false) (a : ℕ) (o : List Bool) :
    Step (loopWM u) (loopCost u a) ![P.length, o.length] ![P ++ List.replicate a true ++ post, o]
      ![P.length + a, (o ++ (List.replicate a u).flatten).length]
      ![P ++ List.replicate a true ++ post, o ++ (List.replicate a u).flatten] := by
  have h := onesRun (loopBodyM u) 0 P post a hpost
    (fun j => ![P.length + j, (o ++ (List.replicate j u).flatten).length])
    (fun j => ![P ++ List.replicate a true ++ post, o ++ (List.replicate j u).flatten]) (fun _ => rfl) (fun _ => rfl)
    (1 + 1 + putsCost u) (by
      intro j _
      have e1 := dockRun (moveStep (P ++ List.replicate a true ++ post) (P.length + j)) w0 w0_inj
        ![P.length + j, (o ++ (List.replicate j u).flatten).length]
        ![P ++ List.replicate a true ++ post, o ++ (List.replicate j u).flatten]
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_w0, dockH_w0] at e1
      have e2 := dockRun (puts_run u (o ++ (List.replicate j u).flatten)) w1 w1_inj
        ![P.length + j + 1, (o ++ (List.replicate j u).flatten).length]
        ![P ++ List.replicate a true ++ post, o ++ (List.replicate j u).flatten]
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_w1, dockH_w1] at e2
      have e := (e1.congr rfl rfl).seq (e2.congr rfl rfl)
      have ef : o ++ (List.replicate j u).flatten ++ u = o ++ (List.replicate (j + 1) u).flatten := by
        rw [flat_succ, List.append_assoc]
      refine e.congr ?_ ?_
      · funext k; fin_cases k
        · show P.length + j + 1 = P.length + (j + 1); omega
        · show (o ++ (List.replicate j u).flatten ++ u).length = (o ++ (List.replicate (j + 1) u).flatten).length
          rw [ef]
      · funext k; fin_cases k
        · rfl
        · show o ++ (List.replicate j u).flatten ++ u = o ++ (List.replicate (j + 1) u).flatten
          rw [ef])
  refine (h.congr_in ?_ ?_).congr rfl rfl
  · funext k; fin_cases k <;> simp
  · funext k; fin_cases k <;> simp

/-- The word loop from the start of an all-ones tape. -/
theorem loopW_run0 (u : List Bool) (a : ℕ) (o : List Bool) :
    Step (loopWM u) (loopCost u a) ![0, o.length] ![List.replicate a true, o]
      ![a, (o ++ (List.replicate a u).flatten).length] ![List.replicate a true, o ++ (List.replicate a u).flatten] := by
  have h := loopW_run u [] [] rfl a o
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h
  exact h

/-! ## Words of runs -/

theorem frame_pairs : ∀ l : List Bool, frame l = (l.map fun b => [true, b]).flatten ++ [false]
  | [] => rfl
  | b :: l => by rw [frame, frame_pairs l]; simp

theorem pairs_rep (a : ℕ) (b : Bool) :
    (List.replicate a [true, b]).flatten = ((List.replicate a b).map fun x => [true, x]).flatten := by
  rw [List.map_replicate]

/-- The masked heads of a whole-bank reset are all zero. -/
theorem mask_heads_zero {t : ℕ} (H : Fin t → ℕ) :
    Fin.addCases (motive := fun _ => ℕ) (fun i : Fin t => if (fun _ : Fin t => true) i = true then 0 else H i)
      (fun _ : Fin 1 => 0) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem addCases_zero {t : ℕ} (H : Fin t → ℕ) (hH : ∀ i, H i = 0) :
    Fin.addCases (motive := fun _ => ℕ) H (fun _ : Fin 1 => 0) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hH]

/-! ### `frame (b^a)` from `1^a` (tapes: the unary source, the target) -/

noncomputable def wRunRawM (b : Bool) := Composition.machine (loopWM [true, b]) (RecoveryFocus.machine w1 (putsM [false]))

def wRunCost (a : ℕ) : ℕ := loopCost [true, true] a + 1 + putsCost [false]

theorem wRun_raw (b : Bool) (a : ℕ) :
    Step (wRunRawM b) (wRunCost a) ![0, 0] ![List.replicate a true, []]
      ![a, ([] ++ (List.replicate a [true, b]).flatten ++ [false]).length]
      ![List.replicate a true, [] ++ (List.replicate a [true, b]).flatten ++ [false]] := by
  have s1 := loopW_run0 [true, b] a []
  have s2 := dockRun (puts_run [false] ([] ++ (List.replicate a [true, b]).flatten)) w1 w1_inj
    ![a, ([] ++ (List.replicate a [true, b]).flatten).length] ![List.replicate a true, [] ++ (List.replicate a [true, b]).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_w1, dockH_w1] at s2
  exact s1.seq (s2.congr rfl rfl)

/-- **`frame (b^a)` from `1^a`**, both heads back at cell 0. -/
noncomputable def wRunM (b : Bool) := MaskedReset.machine (wRunRawM b) (fun _ => true)

theorem wRun_run (b : Bool) (a cap : ℕ) (hcap : wRunCost a ≤ cap) :
    Step (wRunM b) (2 * wRunCost a + 2) (fun _ => 0)
      (Fin.addCases ![List.replicate a true, []] (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases ![List.replicate a true, frame (List.replicate a b)] (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := (wRun_raw b a).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  have ew : [] ++ (List.replicate a [true, b]).flatten ++ [false] = frame (List.replicate a b) := by
    rw [frame_pairs, pairs_rep, List.nil_append]
  rw [ew] at m
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl

/-! ### Three-tape writers (tapes: `1^{Q'}`, `1^{P_ex}`, the target) -/

def q0 : Fin 2 → Fin 3 := ![0, 2]
def q1 : Fin 2 → Fin 3 := ![1, 2]
def qT : Fin 1 → Fin 3 := ![2]
def qQ : Fin 1 → Fin 3 := ![0]

theorem q0_inj : Function.Injective q0 := by decide

theorem install_q0 (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    install q0 A v = ![v 0, A 1, v 1] := by
  funext i
  fin_cases i
  · exact install_slot q0 q0_inj A v 0
  · exact install_other q0 A v 1 (by decide)
  · exact install_slot q0 q0_inj A v 1

theorem dockH_q0 (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH q0 H v = ![v 0, H 1, v 1] := by
  funext i
  fin_cases i
  · exact dockH_slot q0 q0_inj H v 0
  · exact dockH_other q0 H v 1 (by decide)
  · exact dockH_slot q0 q0_inj H v 1

theorem q1_inj : Function.Injective q1 := by decide

theorem install_q1 (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    install q1 A v = ![A 0, v 0, v 1] := by
  funext i
  fin_cases i
  · exact install_other q1 A v 0 (by decide)
  · exact install_slot q1 q1_inj A v 0
  · exact install_slot q1 q1_inj A v 1

theorem dockH_q1 (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) :
    dockH q1 H v = ![H 0, v 0, v 1] := by
  funext i
  fin_cases i
  · exact dockH_other q1 H v 0 (by decide)
  · exact dockH_slot q1 q1_inj H v 0
  · exact dockH_slot q1 q1_inj H v 1

theorem qT_inj : Function.Injective qT := by decide

theorem install_qT (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install qT A v = ![A 0, A 1, v 0] := by
  funext i
  fin_cases i
  · exact install_other qT A v 0 (by decide)
  · exact install_other qT A v 1 (by decide)
  · exact install_slot qT qT_inj A v 0

theorem dockH_qT (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH qT H v = ![H 0, H 1, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other qT H v 0 (by decide)
  · exact dockH_other qT H v 1 (by decide)
  · exact dockH_slot qT qT_inj H v 0

theorem qQ_inj : Function.Injective qQ := by decide

theorem install_qQ (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    install qQ A v = ![v 0, A 1, A 2] := by
  funext i
  fin_cases i
  · exact install_slot qQ qQ_inj A v 0
  · exact install_other qQ A v 1 (by decide)
  · exact install_other qQ A v 2 (by decide)

theorem dockH_qQ (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) :
    dockH qQ H v = ![v 0, H 1, H 2] := by
  funext i
  fin_cases i
  · exact dockH_slot qQ qQ_inj H v 0
  · exact dockH_other qQ H v 1 (by decide)
  · exact dockH_other qQ H v 2 (by decide)


/-- Two word loops (`u` over `1^{Q'}`, `v` over `1^{P_ex}`) and a closing word `w`. -/
noncomputable def w3M (u v w : List Bool) := Composition.machine (Composition.machine (RecoveryFocus.machine q0 (loopWM u))
  (RecoveryFocus.machine q1 (loopWM v))) (RecoveryFocus.machine qT (putsM w))

def w3Cost (u v w : List Bool) (Q W : ℕ) : ℕ := loopCost u Q + 1 + loopCost v W + 1 + putsCost w

theorem w3_raw (u v w : List Bool) (Q W : ℕ) :
    Step (w3M u v w) (w3Cost u v w Q W) ![0, 0, 0] ![List.replicate Q true, List.replicate W true, []]
      ![Q, W, ([] ++ (List.replicate Q u).flatten ++ (List.replicate W v).flatten ++ w).length]
      ![List.replicate Q true, List.replicate W true,
        [] ++ (List.replicate Q u).flatten ++ (List.replicate W v).flatten ++ w] := by
  have s1 := dockRun (loopW_run0 u Q []) q0 q0_inj ![0, 0, 0] ![List.replicate Q true, List.replicate W true, []]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q0, dockH_q0] at s1
  have s2 := dockRun (loopW_run0 v W ([] ++ (List.replicate Q u).flatten)) q1 q1_inj
    ![Q, 0, ([] ++ (List.replicate Q u).flatten).length]
    ![List.replicate Q true, List.replicate W true, [] ++ (List.replicate Q u).flatten]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q1, dockH_q1] at s2
  have s3 := dockRun (puts_run w ([] ++ (List.replicate Q u).flatten ++ (List.replicate W v).flatten)) qT qT_inj
    ![Q, W, ([] ++ (List.replicate Q u).flatten ++ (List.replicate W v).flatten).length]
    ![List.replicate Q true, List.replicate W true, [] ++ (List.replicate Q u).flatten ++ (List.replicate W v).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s3
  exact ((s1.congr rfl rfl).seq (s2.congr rfl rfl)).seq (s3.congr rfl rfl)

/-- The masked three-tape writer. -/
noncomputable def w3RM (u v w : List Bool) := MaskedReset.machine (w3M u v w) (fun _ => true)

theorem w3_run (u v w : List Bool) (Q W cap : ℕ) (hcap : w3Cost u v w Q W ≤ cap) (target : List Bool)
    (ht : [] ++ (List.replicate Q u).flatten ++ (List.replicate W v).flatten ++ w = target) :
    Step (w3RM u v w) (2 * w3Cost u v w Q W + 2) (fun _ => 0)
      (Fin.addCases ![List.replicate Q true, List.replicate W true, []] (fun _ : Fin 1 => List.replicate cap false))
      (fun _ => 0)
      (Fin.addCases ![List.replicate Q true, List.replicate W true, target]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := (w3_raw u v w Q W).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  rw [ht] at m
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl

/-- **The zero register** `frame (zeroT Q' P_ex)`. -/
theorem zero_word (Q W : ℕ) :
    [] ++ (List.replicate Q [true, false]).flatten ++ (List.replicate W [true, false]).flatten ++ [true, false, false] =
      frame (Unions.zeroT Q W) := by
  rw [Unions.zeroT, frame_pairs, List.map_replicate, List.replicate_add, List.replicate_add, List.flatten_append,
    List.flatten_append]
  simp

/-- **The lift template** `frame (levelT Q' P_ex)`. -/
theorem level_word (Q W : ℕ) :
    [] ++ (List.replicate Q [true, true]).flatten ++ (List.replicate W [true, false]).flatten ++ [true, false, false] =
      frame (Unions.levelT Q W) := by
  rw [Unions.levelT, frame_pairs, List.map_append, List.map_replicate, List.map_replicate, List.replicate_add,
    List.flatten_append, List.flatten_append]
  simp

/-! ### The entry of the empty union and the last-level template -/

/-- Loop over `1^{Q'}`, a word, loop over `1^{P_ex}`, a word. -/
noncomputable def w4M (u x v w : List Bool) := Composition.machine (Composition.machine (Composition.machine
  (RecoveryFocus.machine q0 (loopWM u)) (RecoveryFocus.machine qT (putsM x))) (RecoveryFocus.machine q1 (loopWM v)))
  (RecoveryFocus.machine qT (putsM w))

def w4Cost (u x v w : List Bool) (Q W : ℕ) : ℕ :=
  loopCost u Q + 1 + putsCost x + 1 + loopCost v W + 1 + putsCost w

theorem w4_raw (u x v w : List Bool) (Q W : ℕ) :
    Step (w4M u x v w) (w4Cost u x v w Q W) ![0, 0, 0] ![List.replicate Q true, List.replicate W true, []]
      ![Q, W, ([] ++ (List.replicate Q u).flatten ++ x ++ (List.replicate W v).flatten ++ w).length]
      ![List.replicate Q true, List.replicate W true,
        [] ++ (List.replicate Q u).flatten ++ x ++ (List.replicate W v).flatten ++ w] := by
  have s1 := dockRun (loopW_run0 u Q []) q0 q0_inj ![0, 0, 0] ![List.replicate Q true, List.replicate W true, []]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q0, dockH_q0] at s1
  have s2 := dockRun (puts_run x ([] ++ (List.replicate Q u).flatten)) qT qT_inj
    ![Q, 0, ([] ++ (List.replicate Q u).flatten).length]
    ![List.replicate Q true, List.replicate W true, [] ++ (List.replicate Q u).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s2
  have s3 := dockRun (loopW_run0 v W ([] ++ (List.replicate Q u).flatten ++ x)) q1 q1_inj
    ![Q, 0, ([] ++ (List.replicate Q u).flatten ++ x).length]
    ![List.replicate Q true, List.replicate W true, [] ++ (List.replicate Q u).flatten ++ x]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q1, dockH_q1] at s3
  have s4 := dockRun (puts_run w ([] ++ (List.replicate Q u).flatten ++ x ++ (List.replicate W v).flatten)) qT qT_inj
    ![Q, W, ([] ++ (List.replicate Q u).flatten ++ x ++ (List.replicate W v).flatten).length]
    ![List.replicate Q true, List.replicate W true, [] ++ (List.replicate Q u).flatten ++ x ++ (List.replicate W v).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s4
  exact (((s1.congr rfl rfl).seq (s2.congr rfl rfl)).seq (s3.congr rfl rfl)).seq (s4.congr rfl rfl)

noncomputable def w4RM (u x v w : List Bool) := MaskedReset.machine (w4M u x v w) (fun _ => true)

theorem w4_run (u x v w : List Bool) (Q W cap : ℕ) (hcap : w4Cost u x v w Q W ≤ cap) (target : List Bool)
    (ht : [] ++ (List.replicate Q u).flatten ++ x ++ (List.replicate W v).flatten ++ w = target) :
    Step (w4RM u x v w) (2 * w4Cost u x v w Q W + 2) (fun _ => 0)
      (Fin.addCases ![List.replicate Q true, List.replicate W true, []] (fun _ : Fin 1 => List.replicate cap false))
      (fun _ => 0)
      (Fin.addCases ![List.replicate Q true, List.replicate W true, target]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := (w4_raw u x v w Q W).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  rw [ht] at m
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl

theorem binary_zero : ∀ W : ℕ, SignedSortKey.binary W 0 = List.replicate W false
  | 0 => rfl
  | W + 1 => by simp [SignedSortKey.binary, binary_zero W, List.replicate_succ]

/-- **The entry of the empty union** `frame (ew Q' P_ex (0, 0))`. -/
theorem z0_word (Q W : ℕ) :
    [] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++ (List.replicate W [true, false]).flatten ++ [false] =
      frame (Unions.ew Q W (0, 0)) := by
  rw [Unions.ew, Unions.entryWord, Unions.thermo, binary_zero, frame_pairs]
  simp [List.map_replicate, List.flatten_append]

/-- **The last-level template** `frame (lastT (Q'+1) P_ex)`, after one skip on the unary `Q'` tape. -/
noncomputable def wLastM := Composition.machine (RecoveryFocus.machine qQ moveM) (w4M [true, false] [true, true]
  [true, false] [true, false, false])

def wLastCost (Q W : ℕ) : ℕ := 1 + 1 + w4Cost [true, false] [true, true] [true, false] [true, false, false] Q W

theorem wLast_raw (Q W : ℕ) :
    Step wLastM (wLastCost Q W) ![0, 0, 0] ![List.replicate (Q + 1) true, List.replicate W true, []]
      ![Q + 1, W, ([] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++
        (List.replicate W [true, false]).flatten ++ [true, false, false]).length]
      ![List.replicate (Q + 1) true, List.replicate W true, [] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++
        (List.replicate W [true, false]).flatten ++ [true, false, false]] := by
  have s0 := dockRun (moveStep (List.replicate (Q + 1) true) 0) qQ qQ_inj ![0, 0, 0]
    ![List.replicate (Q + 1) true, List.replicate W true, []] (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qQ, dockH_qQ] at s0
  have s1 := dockRun (loopW_run [true, false] [true] [] rfl Q []) q0 q0_inj ![0 + 1, 0, 0]
    ![List.replicate (Q + 1) true, List.replicate W true, []]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> simp [q0, List.replicate_succ])
  rw [install_q0, dockH_q0] at s1
  have s1' := s1.congr (hout' := ![Q + 1, 0, ([] ++ (List.replicate Q [true, false]).flatten).length])
    (tout' := ![List.replicate (Q + 1) true, List.replicate W true, [] ++ (List.replicate Q [true, false]).flatten])
    (by funext k; fin_cases k <;> simp; omega) (by funext k; fin_cases k <;> simp [List.replicate_succ])
  have s2 := dockRun (puts_run [true, true] ([] ++ (List.replicate Q [true, false]).flatten)) qT qT_inj
    ![Q + 1, 0, ([] ++ (List.replicate Q [true, false]).flatten).length]
    ![List.replicate (Q + 1) true, List.replicate W true, [] ++ (List.replicate Q [true, false]).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s2
  have s3 := dockRun (loopW_run0 [true, false] W ([] ++ (List.replicate Q [true, false]).flatten ++ [true, true])) q1 q1_inj
    ![Q + 1, 0, ([] ++ (List.replicate Q [true, false]).flatten ++ [true, true]).length]
    ![List.replicate (Q + 1) true, List.replicate W true, [] ++ (List.replicate Q [true, false]).flatten ++ [true, true]]
    (by intro k; fin_cases k <;> rfl) (by intro k; fin_cases k <;> rfl)
  rw [install_q1, dockH_q1] at s3
  have s4 := dockRun (puts_run [true, false, false] ([] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++
      (List.replicate W [true, false]).flatten)) qT qT_inj
    ![Q + 1, W, ([] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++ (List.replicate W [true, false]).flatten).length]
    ![List.replicate (Q + 1) true, List.replicate W true,
      [] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++ (List.replicate W [true, false]).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_qT, dockH_qT] at s4
  have w := (((s1'.seq (s2.congr rfl rfl)).seq (s3.congr rfl rfl)).seq (s4.congr rfl rfl))
  exact (s0.congr rfl rfl).seq w

noncomputable def wLastRM := MaskedReset.machine wLastM (fun _ => true)

/-- **The last-level template**, every head back at cell 0. -/
theorem wLast_run (Q W cap : ℕ) (hcap : wLastCost Q W ≤ cap) :
    Step wLastRM (2 * wLastCost Q W + 2) (fun _ => 0)
      (Fin.addCases ![List.replicate (Q + 1) true, List.replicate W true, []] (fun _ : Fin 1 => List.replicate cap false))
      (fun _ => 0)
      (Fin.addCases ![List.replicate (Q + 1) true, List.replicate W true, frame (Unions.lastT (Q + 1) W)]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := (wLast_raw Q W).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  have ew : [] ++ (List.replicate Q [true, false]).flatten ++ [true, true] ++ (List.replicate W [true, false]).flatten ++
      [true, false, false] = frame (Unions.lastT (Q + 1) W) := by
    rw [Unions.lastT, frame_pairs, List.map_append, List.map_append, List.map_replicate, List.map_replicate,
      List.replicate_add, List.flatten_append, List.flatten_append, List.flatten_append]
    simp
  rw [ew] at m
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl

/-! ### Two-tape raw writers (tapes: the unary width, the target) -/

/-- A word loop and a closing word. -/
noncomputable def w2M (u w : List Bool) := Composition.machine (loopWM u) (RecoveryFocus.machine w1 (putsM w))

def w2Cost (u w : List Bool) (a : ℕ) : ℕ := loopCost u a + 1 + putsCost w

theorem w2_raw (u w : List Bool) (a : ℕ) :
    Step (w2M u w) (w2Cost u w a) ![0, 0] ![List.replicate a true, []]
      ![a, ([] ++ (List.replicate a u).flatten ++ w).length]
      ![List.replicate a true, [] ++ (List.replicate a u).flatten ++ w] := by
  have s1 := loopW_run0 u a []
  have s2 := dockRun (puts_run w ([] ++ (List.replicate a u).flatten)) w1 w1_inj
    ![a, ([] ++ (List.replicate a u).flatten).length] ![List.replicate a true, [] ++ (List.replicate a u).flatten]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [install_w1, dockH_w1] at s2
  exact s1.seq (s2.congr rfl rfl)

noncomputable def w2RM (u w : List Bool) := MaskedReset.machine (w2M u w) (fun _ => true)

theorem w2_run (u w : List Bool) (a cap : ℕ) (hcap : w2Cost u w a ≤ cap) (target : List Bool)
    (ht : [] ++ (List.replicate a u).flatten ++ w = target) :
    Step (w2RM u w) (2 * w2Cost u w a + 2) (fun _ => 0)
      (Fin.addCases ![List.replicate a true, []] (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases ![List.replicate a true, target] (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := (w2_raw u w a).mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  rw [ht] at m
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl

/-- **The unary width twice** `1^{width + width}`. -/
theorem raw2_word (a : ℕ) : [] ++ (List.replicate a [true, true]).flatten ++ [] = List.replicate (a + a) true := by
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [List.nil_append, List.append_nil] at ih ⊢
    rw [flat_succ, ih, show a + 1 + (a + 1) = a + a + 1 + 1 by omega, List.replicate_succ', List.replicate_succ']
    simp

/-- The stack record word, four records per unit. -/
def ts4 : List Bool := [true, true, false, true, true, false, true, true, false, true, true, false]

/-- **The empty stack stream**: `2·(2·width + 1)` sentinel records `[true]`, then the stream's end. -/
theorem ts_word (a : ℕ) :
    [] ++ (List.replicate a ts4).flatten ++ [true, true, false, true, true, false, false] =
      Kit.streamTape (List.replicate (2 * (a + a + 1)) [true]) [] := by
  have h : ∀ n : ℕ, (List.replicate n ts4).flatten = (List.replicate (4 * n) [true, true, false]).flatten := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [flat_succ, ih, show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by omega, flat_succ, flat_succ, flat_succ, flat_succ]
      simp [ts4]
  rw [List.nil_append, h, Kit.streamTape, show 2 * (a + a + 1) = 4 * a + 1 + 1 by omega]
  simp [List.replicate_succ', List.flatMap, List.flatten_append, frame]

/-! ### The one-cell flags (nine tapes) -/

def c0 : Fin 1 → Fin 9 := ![0]
def c1 : Fin 1 → Fin 9 := ![1]
def c2 : Fin 1 → Fin 9 := ![2]
def c3 : Fin 1 → Fin 9 := ![3]
def c4 : Fin 1 → Fin 9 := ![4]
def c5 : Fin 1 → Fin 9 := ![5]
def c6 : Fin 1 → Fin 9 := ![6]
def c7 : Fin 1 → Fin 9 := ![7]
def c8 : Fin 1 → Fin 9 := ![8]

theorem c0_inj : Function.Injective c0 := by decide

theorem install_c0 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c0 A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_slot c0 c0_inj A v 0
  · exact install_other c0 A v 1 (by decide)
  · exact install_other c0 A v 2 (by decide)
  · exact install_other c0 A v 3 (by decide)
  · exact install_other c0 A v 4 (by decide)
  · exact install_other c0 A v 5 (by decide)
  · exact install_other c0 A v 6 (by decide)
  · exact install_other c0 A v 7 (by decide)
  · exact install_other c0 A v 8 (by decide)

theorem dockH_c0 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c0 H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_slot c0 c0_inj H v 0
  · exact dockH_other c0 H v 1 (by decide)
  · exact dockH_other c0 H v 2 (by decide)
  · exact dockH_other c0 H v 3 (by decide)
  · exact dockH_other c0 H v 4 (by decide)
  · exact dockH_other c0 H v 5 (by decide)
  · exact dockH_other c0 H v 6 (by decide)
  · exact dockH_other c0 H v 7 (by decide)
  · exact dockH_other c0 H v 8 (by decide)

theorem c1_inj : Function.Injective c1 := by decide

theorem install_c1 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c1 A v = ![A 0, v 0, A 2, A 3, A 4, A 5, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_other c1 A v 0 (by decide)
  · exact install_slot c1 c1_inj A v 0
  · exact install_other c1 A v 2 (by decide)
  · exact install_other c1 A v 3 (by decide)
  · exact install_other c1 A v 4 (by decide)
  · exact install_other c1 A v 5 (by decide)
  · exact install_other c1 A v 6 (by decide)
  · exact install_other c1 A v 7 (by decide)
  · exact install_other c1 A v 8 (by decide)

theorem dockH_c1 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c1 H v = ![H 0, v 0, H 2, H 3, H 4, H 5, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other c1 H v 0 (by decide)
  · exact dockH_slot c1 c1_inj H v 0
  · exact dockH_other c1 H v 2 (by decide)
  · exact dockH_other c1 H v 3 (by decide)
  · exact dockH_other c1 H v 4 (by decide)
  · exact dockH_other c1 H v 5 (by decide)
  · exact dockH_other c1 H v 6 (by decide)
  · exact dockH_other c1 H v 7 (by decide)
  · exact dockH_other c1 H v 8 (by decide)

theorem c2_inj : Function.Injective c2 := by decide

theorem install_c2 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c2 A v = ![A 0, A 1, v 0, A 3, A 4, A 5, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_other c2 A v 0 (by decide)
  · exact install_other c2 A v 1 (by decide)
  · exact install_slot c2 c2_inj A v 0
  · exact install_other c2 A v 3 (by decide)
  · exact install_other c2 A v 4 (by decide)
  · exact install_other c2 A v 5 (by decide)
  · exact install_other c2 A v 6 (by decide)
  · exact install_other c2 A v 7 (by decide)
  · exact install_other c2 A v 8 (by decide)

theorem dockH_c2 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c2 H v = ![H 0, H 1, v 0, H 3, H 4, H 5, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other c2 H v 0 (by decide)
  · exact dockH_other c2 H v 1 (by decide)
  · exact dockH_slot c2 c2_inj H v 0
  · exact dockH_other c2 H v 3 (by decide)
  · exact dockH_other c2 H v 4 (by decide)
  · exact dockH_other c2 H v 5 (by decide)
  · exact dockH_other c2 H v 6 (by decide)
  · exact dockH_other c2 H v 7 (by decide)
  · exact dockH_other c2 H v 8 (by decide)

theorem c3_inj : Function.Injective c3 := by decide

theorem install_c3 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c3 A v = ![A 0, A 1, A 2, v 0, A 4, A 5, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_other c3 A v 0 (by decide)
  · exact install_other c3 A v 1 (by decide)
  · exact install_other c3 A v 2 (by decide)
  · exact install_slot c3 c3_inj A v 0
  · exact install_other c3 A v 4 (by decide)
  · exact install_other c3 A v 5 (by decide)
  · exact install_other c3 A v 6 (by decide)
  · exact install_other c3 A v 7 (by decide)
  · exact install_other c3 A v 8 (by decide)

theorem dockH_c3 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c3 H v = ![H 0, H 1, H 2, v 0, H 4, H 5, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other c3 H v 0 (by decide)
  · exact dockH_other c3 H v 1 (by decide)
  · exact dockH_other c3 H v 2 (by decide)
  · exact dockH_slot c3 c3_inj H v 0
  · exact dockH_other c3 H v 4 (by decide)
  · exact dockH_other c3 H v 5 (by decide)
  · exact dockH_other c3 H v 6 (by decide)
  · exact dockH_other c3 H v 7 (by decide)
  · exact dockH_other c3 H v 8 (by decide)

theorem c4_inj : Function.Injective c4 := by decide

theorem install_c4 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c4 A v = ![A 0, A 1, A 2, A 3, v 0, A 5, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_other c4 A v 0 (by decide)
  · exact install_other c4 A v 1 (by decide)
  · exact install_other c4 A v 2 (by decide)
  · exact install_other c4 A v 3 (by decide)
  · exact install_slot c4 c4_inj A v 0
  · exact install_other c4 A v 5 (by decide)
  · exact install_other c4 A v 6 (by decide)
  · exact install_other c4 A v 7 (by decide)
  · exact install_other c4 A v 8 (by decide)

theorem dockH_c4 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c4 H v = ![H 0, H 1, H 2, H 3, v 0, H 5, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other c4 H v 0 (by decide)
  · exact dockH_other c4 H v 1 (by decide)
  · exact dockH_other c4 H v 2 (by decide)
  · exact dockH_other c4 H v 3 (by decide)
  · exact dockH_slot c4 c4_inj H v 0
  · exact dockH_other c4 H v 5 (by decide)
  · exact dockH_other c4 H v 6 (by decide)
  · exact dockH_other c4 H v 7 (by decide)
  · exact dockH_other c4 H v 8 (by decide)

theorem c5_inj : Function.Injective c5 := by decide

theorem install_c5 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c5 A v = ![A 0, A 1, A 2, A 3, A 4, v 0, A 6, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_other c5 A v 0 (by decide)
  · exact install_other c5 A v 1 (by decide)
  · exact install_other c5 A v 2 (by decide)
  · exact install_other c5 A v 3 (by decide)
  · exact install_other c5 A v 4 (by decide)
  · exact install_slot c5 c5_inj A v 0
  · exact install_other c5 A v 6 (by decide)
  · exact install_other c5 A v 7 (by decide)
  · exact install_other c5 A v 8 (by decide)

theorem dockH_c5 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c5 H v = ![H 0, H 1, H 2, H 3, H 4, v 0, H 6, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other c5 H v 0 (by decide)
  · exact dockH_other c5 H v 1 (by decide)
  · exact dockH_other c5 H v 2 (by decide)
  · exact dockH_other c5 H v 3 (by decide)
  · exact dockH_other c5 H v 4 (by decide)
  · exact dockH_slot c5 c5_inj H v 0
  · exact dockH_other c5 H v 6 (by decide)
  · exact dockH_other c5 H v 7 (by decide)
  · exact dockH_other c5 H v 8 (by decide)

theorem c6_inj : Function.Injective c6 := by decide

theorem install_c6 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c6 A v = ![A 0, A 1, A 2, A 3, A 4, A 5, v 0, A 7, A 8] := by
  funext i
  fin_cases i
  · exact install_other c6 A v 0 (by decide)
  · exact install_other c6 A v 1 (by decide)
  · exact install_other c6 A v 2 (by decide)
  · exact install_other c6 A v 3 (by decide)
  · exact install_other c6 A v 4 (by decide)
  · exact install_other c6 A v 5 (by decide)
  · exact install_slot c6 c6_inj A v 0
  · exact install_other c6 A v 7 (by decide)
  · exact install_other c6 A v 8 (by decide)

theorem dockH_c6 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c6 H v = ![H 0, H 1, H 2, H 3, H 4, H 5, v 0, H 7, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other c6 H v 0 (by decide)
  · exact dockH_other c6 H v 1 (by decide)
  · exact dockH_other c6 H v 2 (by decide)
  · exact dockH_other c6 H v 3 (by decide)
  · exact dockH_other c6 H v 4 (by decide)
  · exact dockH_other c6 H v 5 (by decide)
  · exact dockH_slot c6 c6_inj H v 0
  · exact dockH_other c6 H v 7 (by decide)
  · exact dockH_other c6 H v 8 (by decide)

theorem c7_inj : Function.Injective c7 := by decide

theorem install_c7 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c7 A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, v 0, A 8] := by
  funext i
  fin_cases i
  · exact install_other c7 A v 0 (by decide)
  · exact install_other c7 A v 1 (by decide)
  · exact install_other c7 A v 2 (by decide)
  · exact install_other c7 A v 3 (by decide)
  · exact install_other c7 A v 4 (by decide)
  · exact install_other c7 A v 5 (by decide)
  · exact install_other c7 A v 6 (by decide)
  · exact install_slot c7 c7_inj A v 0
  · exact install_other c7 A v 8 (by decide)

theorem dockH_c7 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c7 H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, v 0, H 8] := by
  funext i
  fin_cases i
  · exact dockH_other c7 H v 0 (by decide)
  · exact dockH_other c7 H v 1 (by decide)
  · exact dockH_other c7 H v 2 (by decide)
  · exact dockH_other c7 H v 3 (by decide)
  · exact dockH_other c7 H v 4 (by decide)
  · exact dockH_other c7 H v 5 (by decide)
  · exact dockH_other c7 H v 6 (by decide)
  · exact dockH_slot c7 c7_inj H v 0
  · exact dockH_other c7 H v 8 (by decide)

theorem c8_inj : Function.Injective c8 := by decide

theorem install_c8 (A : Fin 9 → List Bool) (v : Fin 1 → List Bool) :
    install c8 A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, v 0] := by
  funext i
  fin_cases i
  · exact install_other c8 A v 0 (by decide)
  · exact install_other c8 A v 1 (by decide)
  · exact install_other c8 A v 2 (by decide)
  · exact install_other c8 A v 3 (by decide)
  · exact install_other c8 A v 4 (by decide)
  · exact install_other c8 A v 5 (by decide)
  · exact install_other c8 A v 6 (by decide)
  · exact install_other c8 A v 7 (by decide)
  · exact install_slot c8 c8_inj A v 0

theorem dockH_c8 (H : Fin 9 → ℕ) (v : Fin 1 → ℕ) :
    dockH c8 H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, v 0] := by
  funext i
  fin_cases i
  · exact dockH_other c8 H v 0 (by decide)
  · exact dockH_other c8 H v 1 (by decide)
  · exact dockH_other c8 H v 2 (by decide)
  · exact dockH_other c8 H v 3 (by decide)
  · exact dockH_other c8 H v 4 (by decide)
  · exact dockH_other c8 H v 5 (by decide)
  · exact dockH_other c8 H v 6 (by decide)
  · exact dockH_other c8 H v 7 (by decide)
  · exact dockH_slot c8 c8_inj H v 0


noncomputable def cellsM := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (RecoveryFocus.machine c0 (putsM [false])) (RecoveryFocus.machine c1 (putsM [false])))
  (RecoveryFocus.machine c2 (putsM [false]))) (RecoveryFocus.machine c3 (putsM [false])))
  (RecoveryFocus.machine c4 (putsM [false]))) (RecoveryFocus.machine c5 (putsM [false])))
  (RecoveryFocus.machine c6 (putsM [true]))) (RecoveryFocus.machine c7 (putsM [true])))
  (RecoveryFocus.machine c8 (putsM [false]))

def cellsCost : ℕ := putsCost [false] + 1 + putsCost [false] + 1 + putsCost [false] + 1 + putsCost [false] + 1 + putsCost [false] + 1 + putsCost [false] + 1 + putsCost [true] + 1 + putsCost [true] + 1 + putsCost [false]

theorem cells_raw :
    Step cellsM cellsCost ![0, 0, 0, 0, 0, 0, 0, 0, 0] ![[], [], [], [], [], [], [], [], []]
      ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, ([] ++ [true]).length, ([] ++ [false]).length]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [] ++ [true], [] ++ [false]] := by
  have s0 := dockRun (puts_run [false] []) c0 c0_inj ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![[], [], [], [], [], [], [], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c0, dockH_c0] at s0
  have t0 : Step (RecoveryFocus.machine c0 (putsM [false])) (putsCost [false]) ![0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![[], [], [], [], [], [], [], [], []] ![([] ++ [false]).length, 0, 0, 0, 0, 0, 0, 0, 0]
      ![[] ++ [false], [], [], [], [], [], [], [], []] := s0.congr rfl rfl
  have s1 := dockRun (puts_run [false] []) c1 c1_inj ![([] ++ [false]).length, 0, 0, 0, 0, 0, 0, 0, 0]
    ![[] ++ [false], [], [], [], [], [], [], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c1, dockH_c1] at s1
  have t1 : Step (RecoveryFocus.machine c1 (putsM [false])) (putsCost [false]) ![([] ++ [false]).length, 0, 0, 0, 0, 0, 0, 0, 0]
      ![[] ++ [false], [], [], [], [], [], [], [], []] ![([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [], [], [], [], [], [], []] := s1.congr rfl rfl
  have s2 := dockRun (puts_run [false] []) c2 c2_inj ![([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0, 0, 0]
    ![[] ++ [false], [] ++ [false], [], [], [], [], [], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c2, dockH_c2] at s2
  have t2 : Step (RecoveryFocus.machine c2 (putsM [false])) (putsCost [false]) ![([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [], [], [], [], [], [], []] ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [], [], [], [], [], []] := s2.congr rfl rfl
  have s3 := dockRun (puts_run [false] []) c3 c3_inj ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0, 0]
    ![[] ++ [false], [] ++ [false], [] ++ [false], [], [], [], [], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c3, dockH_c3] at s3
  have t3 : Step (RecoveryFocus.machine c3 (putsM [false])) (putsCost [false]) ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [], [], [], [], [], []] ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], [], [], []] := s3.congr rfl rfl
  have s4 := dockRun (puts_run [false] []) c4 c4_inj ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0]
    ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], [], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c4, dockH_c4] at s4
  have t4 : Step (RecoveryFocus.machine c4 (putsM [false])) (putsCost [false]) ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], [], [], []] ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], [], []] := s4.congr rfl rfl
  have s5 := dockRun (puts_run [false] []) c5 c5_inj ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0]
    ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c5, dockH_c5] at s5
  have t5 : Step (RecoveryFocus.machine c5 (putsM [false])) (putsCost [false]) ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], [], []] ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], []] := s5.congr rfl rfl
  have s6 := dockRun (puts_run [true] []) c6 c6_inj ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0]
    ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c6, dockH_c6] at s6
  have t6 : Step (RecoveryFocus.machine c6 (putsM [true])) (putsCost [true]) ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, 0, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [], [], []] ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [], []] := s6.congr rfl rfl
  have s7 := dockRun (puts_run [true] []) c7 c7_inj ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, 0, 0]
    ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c7, dockH_c7] at s7
  have t7 : Step (RecoveryFocus.machine c7 (putsM [true])) (putsCost [true]) ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, 0, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [], []] ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, ([] ++ [true]).length, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [] ++ [true], []] := s7.congr rfl rfl
  have s8 := dockRun (puts_run [false] []) c8 c8_inj ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, ([] ++ [true]).length, 0]
    ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [] ++ [true], []]
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [install_c8, dockH_c8] at s8
  have t8 : Step (RecoveryFocus.machine c8 (putsM [false])) (putsCost [false]) ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, ([] ++ [true]).length, 0]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [] ++ [true], []] ![([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [false]).length, ([] ++ [true]).length, ([] ++ [true]).length, ([] ++ [false]).length]
      ![[] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [false], [] ++ [true], [] ++ [true], [] ++ [false]] := s8.congr rfl rfl
  exact ((((((((t0).seq t1).seq t2).seq t3).seq t4).seq t5).seq t6).seq t7).seq t8

noncomputable def cellsRM := MaskedReset.machine cellsM (fun _ => true)

/-- **The one-cell flags**, every head back at cell 0. -/
theorem cells_run (cap : ℕ) (hcap : cellsCost ≤ cap) :
    Step cellsRM (2 * cellsCost + 2) (fun _ => 0)
      (Fin.addCases ![[], [], [], [], [], [], [], [], []] (fun _ : Fin 1 => List.replicate cap false)) (fun _ => 0)
      (Fin.addCases ![[false], [false], [false], [false], [false], [false], [true], [true], [false]]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have m := cells_raw.mask (fun _ => true) (by intro i _; fin_cases i <;> rfl) hcap
  exact (m.congr_in (addCases_zero _ (by intro i; fin_cases i <;> rfl)) rfl).congr (mask_heads_zero _) rfl


end NearCubicWires.WireExponent3_5.CompilerMachine.Top
