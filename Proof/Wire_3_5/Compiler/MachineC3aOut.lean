import Proof.Wire_3_5.Compiler.MachineC3aConst
import Proof.Wire_3_5.Compiler.MachineTopHeader

/-! # C3a machine, the output word: the children table after the pool stream (P3:1636-1664)

Paper: alg:pullback in the star instance: the common pool of the pulled-back exact children, over every flip pattern
and carrier gate (P3:1636-1664). C3a's output word is the pool stream (word (1)) closed by `false`, then the children
table (word (2), one atom stream per pool atom: `atomStream E = E.flatMap frame ++ [false]`). The pool builder writes
the two words on two tapes; the table is appended after the pool stream by a loop over the atoms (a unary count of
them), each pass copying one atom's frames (a stream loop), closing it with `false` and stepping past its terminator.
**`copyAt_run`**: a stream of frames after a prefix is appended; **`atom_run`**: one atom stream; **`tab_run`**: the
whole table (the output cursor at the output's end). The paper quantity is the contract's output word (the encoding of the pool
and its children table). Main declarations: **`copyAt_run`**, `atomM`, **`atom_run`**, `tabLoopM`, **`tab_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Out
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Top NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Dec NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Count
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- The cost of copying one frame of length `L` and stepping past it. -/
def cfCost (L : ℕ) : ℕ := (2 * L + 1) + 1 + 1

/-- **A stream of frames after a prefix is appended** (the source cursor stops on the stream's terminator). -/
theorem copyAt_run (P : List Bool) (rs : List (List Bool)) (stale : List Bool) (L : ℕ) (hne : ∀ r ∈ rs, r ≠ [])
    (hlen : ∀ r ∈ rs, r.length = L) (O0 : List Bool) :
    Step copyFramesM (rs.length * (cfCost L + 2) + 1) ![P.length, O0.length] ![P ++ streamTape rs stale, O0]
      ![P.length + (rs.flatMap frame).length, (O0 ++ rs.flatMap frame).length]
      ![P ++ streamTape rs stale, O0 ++ rs.flatMap frame] := by
  have h := streamRunAt cfBodyM 0 P rs stale hne (fun o r => o ++ frame r) O0
    (fun o p => ![p, o.length]) (fun o => ![P ++ streamTape rs stale, overlay o []]) (fun _ => rfl) (fun _ _ => rfl)
    (cfCost L) (by
      intro j hj
      have hsplit := streamTape_split rs stale j hj
      have e1 := copyStep (P ++ (rs.take j).flatMap frame) rs[j] ((rs.drop (j + 1)).flatMap frame ++ false :: stale)
        ((rs.take j).foldl (fun o r => o ++ frame r) O0) []
      have hsp : P ++ (rs.take j).flatMap frame ++ frame rs[j] ++ ((rs.drop (j + 1)).flatMap frame ++ false :: stale) =
          P ++ streamTape rs stale := by rw [hsplit]; simp only [List.append_assoc]
      rw [hsp] at e1
      have e2 := dockRun (moveStep (P ++ streamTape rs stale)
        ((P ++ (rs.take j).flatMap frame).length + 2 * rs[j].length)) w0 w0_inj
        ![(P ++ (rs.take j).flatMap frame).length + 2 * rs[j].length,
          ((rs.take j).foldl (fun o r => o ++ frame r) O0).length + (2 * rs[j].length + 1)]
        ![P ++ streamTape rs stale, overlay ((rs.take j).foldl (fun o r => o ++ frame r) O0 ++ frame rs[j]) []]
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_w0, dockH_w0] at e2
      have j2 := e1.seq (e2.congr rfl rfl)
      have hL := hlen _ (List.getElem_mem hj)
      have hst : (rs.take (j + 1)).foldl (fun o r => o ++ frame r) O0 =
          (rs.take j).foldl (fun o r => o ++ frame r) O0 ++ frame rs[j] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]; rfl
      rw [hst]
      refine ((j2.congr_in ?_ rfl).congr ?_ rfl).enlarge (le_of_eq (by unfold cfCost; rw [hL]))
      · funext k; fin_cases k
        · show (P ++ (rs.take j).flatMap frame).length = P.length + off rs j
          rw [List.length_append]; rfl
        · rfl
      · funext k; fin_cases k
        · show (P ++ (rs.take j).flatMap frame).length + 2 * rs[j].length + 1 = P.length + off rs (j + 1)
          rw [off_succ rs j hj, List.length_append]; unfold off; omega
        · show ((rs.take j).foldl (fun o r => o ++ frame r) O0).length + (2 * rs[j].length + 1) =
            ((rs.take j).foldl (fun o r => o ++ frame r) O0 ++ frame rs[j]).length
          rw [List.length_append, frame_length])
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · funext k; fin_cases k <;> rfl
  · funext k; fin_cases k
    · rfl
    · show overlay O0 [] = O0; rw [overlay_nil_right]
  · funext k; fin_cases k
    · rfl
    · show (rs.foldl (fun o r => o ++ frame r) O0).length = (O0 ++ rs.flatMap frame).length; rw [foldl_frames]
  · funext k; fin_cases k
    · rfl
    · show overlay (rs.foldl (fun o r => o ++ frame r) O0) [] = O0 ++ rs.flatMap frame
      rw [foldl_frames, overlay_nil_right]

/-! ## One atom stream -/

/-- Copy one atom stream: its frames, then its terminator. -/
noncomputable def atomM := Composition.machine (Composition.machine copyFramesM
  (RecoveryFocus.machine ![(1 : Fin 2)] (putM false))) (RecoveryFocus.machine ![(0 : Fin 2)] moveM)

def atomCost (m L : ℕ) : ℕ := (m * (cfCost L + 2) + 1) + 1 + 1 + 1 + 1

theorem atom_run (P rest O0 : List Bool) (E : List (List Bool)) (L : ℕ) (hne : ∀ r ∈ E, r ≠ [])
    (hlen : ∀ r ∈ E, r.length = L) :
    Step atomM (atomCost E.length L) ![P.length, O0.length] ![P ++ atomStream E ++ rest, O0]
      ![(P ++ atomStream E).length, (O0 ++ atomStream E).length]
      ![P ++ atomStream E ++ rest, O0 ++ atomStream E] := by
  have hT : P ++ atomStream E ++ rest = P ++ streamTape E rest := by simp [atomStream, streamTape]
  rw [hT]
  have c1 := copyAt_run P E rest L hne hlen O0
  have p1 := putStep false (O0 ++ E.flatMap frame) (O0 ++ E.flatMap frame).length
  rw [write_end] at p1
  have d1 := dockRun p1 ![(1 : Fin 2)] (one_inj _) ![P.length + (E.flatMap frame).length, (O0 ++ E.flatMap frame).length]
    ![P ++ streamTape E rest, O0 ++ E.flatMap frame] (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
  rw [dockH_one, install_one] at d1
  simp only [Matrix.cons_val_zero, upd2_1] at d1
  have m1 := dockRun (moveStep (P ++ streamTape E rest) (P.length + (E.flatMap frame).length)) ![(0 : Fin 2)] (one_inj _)
    ![P.length + (E.flatMap frame).length, (O0 ++ E.flatMap frame).length + 1]
    ![P ++ streamTape E rest, O0 ++ E.flatMap frame ++ [false]] (by intro k; fin_cases k; rfl)
    (by intro k; fin_cases k; rfl)
  rw [dockH_one, install_one] at m1
  simp only [Matrix.cons_val_zero, upd2_0] at m1
  have ho : O0 ++ E.flatMap frame ++ [false] = O0 ++ atomStream E := by simp [atomStream]
  rw [ho] at d1 m1
  refine ((c1.seq d1).seq m1).congr ?_ rfl
  funext k; fin_cases k
  · show P.length + (E.flatMap frame).length + 1 = (P ++ atomStream E).length
    simp only [atomStream, List.length_append, List.length_singleton]; omega
  · show (O0 ++ E.flatMap frame).length + 1 = (O0 ++ atomStream E).length
    simp only [atomStream, List.length_append, List.length_singleton]; omega

/-! ## The whole table (tapes: the table, the output, the atom count) -/

def sAO : Fin 2 → Fin 3 := ![0, 1]
theorem sAO_inj : Function.Injective sAO := by decide

/-- One atom: its stream copied, the count's cursor on. -/
noncomputable def tabBodyM :=
  Composition.machine (RecoveryFocus.machine sAO atomM) (RecoveryFocus.machine ![(2 : Fin 3)] moveM)
/-- **The table appended** (the output cursor starts and ends at the output's end). -/
noncomputable def tabLoopM := StreamController.machine tabBodyM 2

def tabLoopCost (a m L : ℕ) : ℕ := a * ((atomCost m L + 1 + 1) + 2) + 1

theorem atomCost_mono (m m' L : ℕ) (h : m ≤ m') : atomCost m L ≤ atomCost m' L := by
  unfold atomCost; have := Nat.mul_le_mul_right (cfCost L + 2) h; omega

/-- **The children table is appended to the output** (every atom stream's records nonempty of one length `L`,
at most `M` per atom). -/
theorem tab_run (Es : List (List (List Bool))) (L M : ℕ) (hne : ∀ E ∈ Es, ∀ r ∈ E, r ≠ [])
    (hlen : ∀ E ∈ Es, ∀ r ∈ E, r.length = L) (hM : ∀ E ∈ Es, E.length ≤ M) (O0 : List Bool) :
    Step tabLoopM (tabLoopCost Es.length M L) ![0, O0.length, 0]
      ![Es.flatMap atomStream, O0, List.replicate Es.length true]
      ![(Es.flatMap atomStream).length, (O0 ++ Es.flatMap atomStream).length, Es.length]
      ![Es.flatMap atomStream, O0 ++ Es.flatMap atomStream, List.replicate Es.length true] := by
  set T := Es.flatMap atomStream
  set N := List.replicate Es.length true
  have hl := onesRun tabBodyM 2 [] [] Es.length rfl
    (fun j => ![((Es.take j).flatMap atomStream).length, (O0 ++ (Es.take j).flatMap atomStream).length, j])
    (fun j => ![T, O0 ++ (Es.take j).flatMap atomStream, [] ++ N ++ []]) (fun _ => rfl) (fun j => by simp)
    ((atomCost M L + 1 + 1)) (by
      intro j hj
      have hsp := enc_split atomStream Es j hj
      have hE := List.getElem_mem hj
      have a1 := atom_run ((Es.take j).flatMap atomStream) ((Es.drop (j + 1)).flatMap atomStream)
        (O0 ++ (Es.take j).flatMap atomStream) Es[j] L (hne _ hE) (hlen _ hE)
      rw [← hsp] at a1
      have d1 := dockRun a1 sAO sAO_inj
        ![((Es.take j).flatMap atomStream).length, (O0 ++ (Es.take j).flatMap atomStream).length, j]
        ![T, O0 ++ (Es.take j).flatMap atomStream, [] ++ N ++ []] (by intro k; fin_cases k <;> rfl)
        (by intro k; fin_cases k <;> rfl)
      have ea : install sAO ![T, O0 ++ (Es.take j).flatMap atomStream, [] ++ N ++ []]
          ![T, O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j]] =
          ![T, O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j], [] ++ N ++ []] := by
        funext z; fin_cases z <;> (rw [install_eval _ sAO_inj]; rfl)
      have eh : dockH sAO ![((Es.take j).flatMap atomStream).length, (O0 ++ (Es.take j).flatMap atomStream).length, j]
          ![((Es.take j).flatMap atomStream ++ atomStream Es[j]).length,
            (O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j]).length] =
          ![((Es.take j).flatMap atomStream ++ atomStream Es[j]).length,
            (O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j]).length, j] := by
        funext z; fin_cases z <;> (rw [dockH_eval _ sAO_inj]; rfl)
      rw [ea, eh] at d1
      have m1 := dockRun (moveStep ([] ++ N ++ []) j) ![(2 : Fin 3)] (one_inj _)
        ![((Es.take j).flatMap atomStream ++ atomStream Es[j]).length,
          (O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j]).length, j]
        ![T, O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j], [] ++ N ++ []]
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [dockH_one, install_one] at m1
      simp only [Matrix.cons_val_zero, upd3_2] at m1
      have htk : (Es.take (j + 1)).flatMap atomStream = (Es.take j).flatMap atomStream ++ atomStream Es[j] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append]; simp
      have hc : atomCost Es[j].length L ≤ atomCost M L := atomCost_mono _ _ L (hM _ hE)
      refine ((d1.seq m1).congr ?_ ?_).enlarge (by omega)
      · funext k; fin_cases k
        · show ((Es.take j).flatMap atomStream ++ atomStream Es[j]).length = ((Es.take (j + 1)).flatMap atomStream).length
          rw [htk]
        · show (O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j]).length =
            (O0 ++ (Es.take (j + 1)).flatMap atomStream).length
          rw [htk, List.append_assoc]
        · rfl
      · funext k; fin_cases k
        · rfl
        · show O0 ++ (Es.take j).flatMap atomStream ++ atomStream Es[j] = O0 ++ (Es.take (j + 1)).flatMap atomStream
          rw [htk, List.append_assoc]
        · rfl)
  refine (hl.congr_in ?_ ?_).congr ?_ ?_
  · funext k; fin_cases k <;> simp
  · funext k; fin_cases k <;> simp
  · funext k; fin_cases k <;> simp [T]
  · funext k; fin_cases k <;> simp [T, N]


end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Out
