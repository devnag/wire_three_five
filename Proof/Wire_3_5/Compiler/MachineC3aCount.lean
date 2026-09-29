import Proof.Wire_3_5.Compiler.MachineC3aKit

/-! # C3a machine, the unary counts of the request: flip patterns and column sides (P3:1636-1664)

Paper: alg:pullback in the star instance, "For a common pool over all `2^k` rows [...] it gives
`P_ex ≤ 2^k n^{O(1)}`" (P3:1661-1664), and "Put its constant in the left half, sum the terms indexed by `I_L` in
`a_{j,y}`, and sum the remaining terms in `b_{j,y}`" (P3:1645-1648). The pool builder needs, in unary, the number of
flip patterns (the pool's size is the patterns times the children, `P_ex = |flips|·B`) and the sizes of the two column
halves (each half is padded to the dense width with zero pairs). Two masked loops read them off the request:
* **`nf_run`**: one `1` per record of the flip stream (skip the record, count it);
* **`sc_run`**: one `1` on the left tape per `true` side bit and one on the right tape per `false` side bit (move to
  the bit, branch on it, count it, move on).
The paper quantities are `|flips|` and the half sizes `|I_L|`, `|I_R|`. Main declarations: `nfM`, **`nf_run`**,
`scM`, **`sc_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Count
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Dec
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound

/-! ## Updates of short banks -/

theorem upd2_0 {α : Type} (a b x : α) : Function.update ![a, b] 0 x = ![x, b] := by
  funext i; fin_cases i <;> rfl
theorem upd2_1 {α : Type} (a b x : α) : Function.update ![a, b] 1 x = ![a, x] := by
  funext i; fin_cases i <;> rfl
theorem upd3_0 {α : Type} (a b c x : α) : Function.update ![a, b, c] 0 x = ![x, b, c] := by
  funext i; fin_cases i <;> rfl
theorem upd3_1 {α : Type} (a b c x : α) : Function.update ![a, b, c] 1 x = ![a, x, c] := by
  funext i; fin_cases i <;> rfl
theorem upd3_2 {α : Type} (a b c x : α) : Function.update ![a, b, c] 2 x = ![a, b, x] := by
  funext i; fin_cases i <;> rfl

theorem one_inj {u : ℕ} (x : Fin u) : Function.Injective ![x] := fun j k _ => Subsingleton.elim j k

theorem foldl_count {α : Type} (l : List α) : ∀ c : ℕ, l.foldl (fun c _ => c + 1) c = c + l.length := by
  induction l with
  | nil => intro c; simp
  | cons x l ih => intro c; rw [List.foldl_cons, ih]; simp; omega

theorem take_count {α : Type} (l : List α) (j : ℕ) (hj : j ≤ l.length) :
    (l.take j).foldl (fun c _ => c + 1) 0 = j := by
  rw [foldl_count, List.length_take]; omega

/-! ## The flip patterns, counted -/

/-- One record: skip it, count it. -/
noncomputable def nfBodyM :=
  Composition.machine (RecoveryFocus.machine ![(0 : Fin 2)] skipM) (RecoveryFocus.machine ![(1 : Fin 2)] (putM true))
noncomputable def nfLoopM := StreamController.machine nfBodyM 0
/-- **The flip count**, both heads back at cell `0`. -/
noncomputable def nfM := MaskedReset.machine nfLoopM (fun _ => true)

def nfBodyCost (w : ℕ) : ℕ := (2 * w + 1) + 1 + 1
def nfLoopCost (F w : ℕ) : ℕ := F * (nfBodyCost w + 2) + 1
def nfCost (F w : ℕ) : ℕ := 2 * nfLoopCost F w + 2

theorem nf_body (rs : List (List Bool)) (w : ℕ) (hw : ∀ r ∈ rs, r.length = w) (j : ℕ) (hj : j < rs.length) :
    Step nfBodyM (nfBodyCost w) ![off rs j, j] ![streamTape rs [], List.replicate j true]
      ![off rs (j + 1), j + 1] ![streamTape rs [], List.replicate (j + 1) true] := by
  have e1 := skipStep ((rs.take j).flatMap frame) rs[j] ((rs.drop (j + 1)).flatMap frame ++ false :: [])
  rw [← streamTape_split rs [] j hj] at e1
  have s1 := dockRun e1 ![(0 : Fin 2)] (one_inj _) ![off rs j, j] ![streamTape rs [], List.replicate j true]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [dockH_one, install_one] at s1
  simp only [Matrix.cons_val_zero, upd2_0] at s1
  have e2 := putStep true (List.replicate j true) j
  rw [write_end_replicate] at e2
  have s2 := dockRun e2 ![(1 : Fin 2)] (one_inj _) ![((rs.take j).flatMap frame).length + 2 * rs[j].length + 1, j]
    ![streamTape rs [], List.replicate j true] (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [dockH_one, install_one] at s2
  simp only [Matrix.cons_val_zero, upd2_1] at s2
  have hoff : ((rs.take j).flatMap frame).length + 2 * rs[j].length + 1 = off rs (j + 1) := by
    rw [off_succ rs j hj]; unfold off; omega
  rw [hoff] at s1 s2
  have hl := hw _ (List.getElem_mem hj)
  exact (s1.seq s2).enlarge (by unfold nfBodyCost; rw [hl])

/-- **The flip patterns are counted**: `1^{|flips|}` on the second tape (records of one positive length). -/
theorem nf_run (rs : List (List Bool)) (w : ℕ) (hw : ∀ r ∈ rs, r.length = w) (hw1 : 1 ≤ w) (cap : ℕ)
    (hcap : nfLoopCost rs.length w ≤ cap) :
    Step nfM (nfCost rs.length w) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) ![streamTape rs [], []] (fun _ : Fin 1 => List.replicate cap false))
      (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) ![streamTape rs [], List.replicate rs.length true]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have hne : ∀ r ∈ rs, r ≠ [] := by
    intro r hr h; have := hw r hr; rw [h] at this; simp at this; omega
  have hl := streamRun nfBodyM 0 rs [] hne (fun c _ => c + 1) 0 (fun st p => ![p, st])
    (fun st => ![streamTape rs [], List.replicate st true]) (fun _ => rfl) (fun _ _ => rfl) (nfBodyCost w) (by
      intro j hj
      rw [take_count rs j (by omega), take_count rs (j + 1) (by omega)]
      exact nf_body rs w hw j hj)
  rw [foldl_count] at hl
  simp only [Nat.zero_add] at hl
  have hl' : Step nfLoopM (nfLoopCost rs.length w) (fun _ => 0) ![streamTape rs [], []]
      ![(rs.flatMap frame).length, rs.length] ![streamTape rs [], List.replicate rs.length true] := by
    refine hl.congr_in ?_ ?_
    · funext i; fin_cases i <;> rfl
    · rfl
  have m := hl'.mask (fun _ => true) (by intro i _; rfl) hcap
  exact (m.congr_in addCases_zero' rfl).congr (mask_zero _) rfl

/-! ## The column sides, counted -/

/-- One side bit: move to it, count it on the left or the right tape, move on. -/
noncomputable def scBodyM :=
  Composition.machine (Composition.machine (RecoveryFocus.machine ![(0 : Fin 3)] moveM)
    (branchM 0 (RecoveryFocus.machine ![(1 : Fin 3)] (putM true)) (RecoveryFocus.machine ![(2 : Fin 3)] (putM true))))
    (RecoveryFocus.machine ![(0 : Fin 3)] moveM)
noncomputable def scLoopM := StreamController.machine scBodyM 0
/-- **The side counts**, every head back at cell `0`. -/
noncomputable def scM := MaskedReset.machine scLoopM (fun _ => true)

def scLoopCost (n : ℕ) : ℕ := n * (7 + 2) + 1
def scCost (n : ℕ) : ℕ := 2 * scLoopCost n + 2

/-- The counts after `j` bits. -/
def cntT (side : List Bool) (j : ℕ) : ℕ := ((side.take j).filter id).length
def cntF (side : List Bool) (j : ℕ) : ℕ := ((side.take j).filter (fun b => !b)).length

theorem cntT_succ (side : List Bool) (j : ℕ) (hj : j < side.length) :
    cntT side (j + 1) = cntT side j + (if side[j] then 1 else 0) := by
  unfold cntT
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.filter_append, List.length_append]
  cases side[j] <;> simp

theorem cntF_succ (side : List Bool) (j : ℕ) (hj : j < side.length) :
    cntF side (j + 1) = cntF side j + (if side[j] then 0 else 1) := by
  unfold cntF
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.filter_append, List.length_append]
  cases side[j] <;> simp

theorem sc_body (side : List Bool) (j : ℕ) (hj : j < side.length) :
    Step scBodyM 7 ![2 * j, cntT side j, cntF side j]
      ![frame side ++ [], List.replicate (cntT side j) true, List.replicate (cntF side j) true]
      ![2 * (j + 1), cntT side (j + 1), cntF side (j + 1)]
      ![frame side ++ [], List.replicate (cntT side (j + 1)) true, List.replicate (cntF side (j + 1)) true] := by
  set T := frame side ++ []
  have e1 := dockRun (moveStep T (2 * j)) ![(0 : Fin 3)] (one_inj _) ![2 * j, cntT side j, cntF side j]
    ![T, List.replicate (cntT side j) true, List.replicate (cntF side j) true]
    (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [dockH_one, install_one] at e1
  simp only [Matrix.cons_val_zero, upd3_0] at e1
  have hbit : readTapeBit T (2 * j + 1) = side[j] := read_frame_bit' side [] j hj
  have e3 := dockRun (moveStep T (2 * j + 1)) ![(0 : Fin 3)] (one_inj _)
  have ht := cntT_succ side j hj
  have hf := cntF_succ side j hj
  cases hs : side[j]
  · -- a right-side coordinate
    rw [hs] at ht hf hbit
    simp only [Bool.false_eq_true, if_false, Nat.add_zero] at ht hf
    have p2 := putStep true (List.replicate (cntF side j) true) (cntF side j)
    rw [write_end_replicate] at p2
    have d2 := dockRun p2 ![(2 : Fin 3)] (one_inj _) ![2 * j + 1, cntT side j, cntF side j]
      ![T, List.replicate (cntT side j) true, List.replicate (cntF side j) true]
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [dockH_one, install_one] at d2
    simp only [Matrix.cons_val_zero, upd3_2] at d2
    have b := branch_false (0 : Fin 3) (RecoveryFocus.machine ![(1 : Fin 3)] (putM true)) d2 (by exact hbit)
    have e3' := e3 ![2 * j + 1, cntT side j, cntF side j + 1]
      ![T, List.replicate (cntT side j) true, List.replicate (cntF side j + 1) true]
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [dockH_one, install_one] at e3'
    simp only [Matrix.cons_val_zero, upd3_0] at e3'
    rw [ht, hf]
    exact ((e1.seq b).seq e3').congr (by funext k; fin_cases k <;> rfl) rfl
  · -- a left-side coordinate
    rw [hs] at ht hf hbit
    simp only [if_true, Nat.add_zero] at ht hf
    have p1 := putStep true (List.replicate (cntT side j) true) (cntT side j)
    rw [write_end_replicate] at p1
    have d1 := dockRun p1 ![(1 : Fin 3)] (one_inj _) ![2 * j + 1, cntT side j, cntF side j]
      ![T, List.replicate (cntT side j) true, List.replicate (cntF side j) true]
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [dockH_one, install_one] at d1
    simp only [Matrix.cons_val_zero, upd3_1] at d1
    have b := branch_true (0 : Fin 3) (RecoveryFocus.machine ![(2 : Fin 3)] (putM true)) d1 (by exact hbit)
    have e3' := e3 ![2 * j + 1, cntT side j + 1, cntF side j]
      ![T, List.replicate (cntT side j + 1) true, List.replicate (cntF side j) true]
      (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
    rw [dockH_one, install_one] at e3'
    simp only [Matrix.cons_val_zero, upd3_0] at e3'
    rw [ht, hf]
    exact ((e1.seq b).seq e3').congr (by funext k; fin_cases k <;> rfl) rfl

/-- **The side counts**: `1^{#true}` and `1^{#false}` of the side bits. -/
theorem sc_run (side : List Bool) (cap : ℕ) (hcap : scLoopCost side.length ≤ cap) :
    Step scM (scCost side.length) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) ![frame side, [], []] (fun _ : Fin 1 => List.replicate cap false))
      (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        ![frame side, List.replicate (side.filter id).length true, List.replicate (side.filter (fun b => !b)).length true]
        (fun _ : Fin 1 => List.replicate cap false)) := by
  have hl := frameRun scBodyM 0 side [] (fun j => ![2 * j, cntT side j, cntF side j])
    (fun j => ![frame side ++ [], List.replicate (cntT side j) true, List.replicate (cntF side j) true])
    (fun _ => rfl) (fun _ => rfl) 7 (fun j hj => sc_body side j hj)
  have h0 : cntT side 0 = 0 ∧ cntF side 0 = 0 := by simp [cntT, cntF]
  have hL : cntT side side.length = (side.filter id).length ∧
      cntF side side.length = (side.filter (fun b => !b)).length := by simp [cntT, cntF]
  rw [h0.1, h0.2, hL.1, hL.2] at hl
  simp only [List.append_nil] at hl
  have hl' : Step scLoopM (scLoopCost side.length) (fun _ => 0) ![frame side, [], []]
      ![2 * side.length, (side.filter id).length, (side.filter (fun b => !b)).length]
      ![frame side, List.replicate (side.filter id).length true, List.replicate (side.filter (fun b => !b)).length true] := by
    refine hl.congr_in ?_ ?_
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have m := hl'.mask (fun _ => true) (by intro i _; rfl) hcap
  exact (m.congr_in addCases_zero' rfl).congr (mask_zero _) rfl


end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Count
