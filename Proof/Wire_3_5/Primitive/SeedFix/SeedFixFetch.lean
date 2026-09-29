import Proof.Wire_3_5.Primitive.SeedFix.SeedFixFoldRows

/-! # C4.Sb, machine part 5: one entry fetched from its state's block and multiplied in (P3:3011-3016)

The eight entries of a term group sit at scattered cells of the state's block, `N² = 2^{2kh}` entry records in
C2's cell order (`u`-major, then `v`). The fetch scans the block once with an entry counter in binary, compares it
with the target cell's number (`EqCell`), multiplies the entry's rows into the accumulator when they agree
(`rowsMul_run`) and passes the rows otherwise (`rowsSkip_run`), then increments the counter (`IncFlag`). After the
`2^{2kh}` entries the counter has wrapped back to `0`, so the fetch can run again.

Paper quantity of the main type: the accumulator `sfold A (entry e)` of the target entry `e` (`fetch_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)

/-- A state's block: its entry records, then a terminator. -/
def blockWord (ents : List (List SExpr)) : List Bool := ents.flatMap entryRec ++ [false]

/-- The block's head at entry `j`. -/
def entPos (ents : List (List SExpr)) (j : ℕ) : ℕ := ((ents.take j).flatMap entryRec).length

theorem ents_split (ents : List (List SExpr)) (tail : List Bool) (j : ℕ) (hj : j < ents.length) :
    blockWord ents ++ tail =
      (ents.take j).flatMap entryRec ++ entryRec ents[j] ++ ((ents.drop (j + 1)).flatMap entryRec ++ false :: tail) := by
  have e : ents = ents.take j ++ ents[j] :: ents.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  calc blockWord ents ++ tail = blockWord (ents.take j ++ ents[j] :: ents.drop (j + 1)) ++ tail :=
        congrArg (fun l => blockWord l ++ tail) e
    _ = _ := by simp only [blockWord, List.flatMap_append, List.flatMap_cons, List.append_assoc, List.cons_append,
      List.nil_append]

theorem ents_read (ents : List (List SExpr)) (tail : List Bool) (j : ℕ) (hj : j ≤ ents.length) :
    readTapeBit (blockWord ents ++ tail) (entPos ents j) = decide (j < ents.length) := by
  unfold entPos
  by_cases h : j < ents.length
  · rw [ents_split ents tail j h, decide_eq_true h, List.append_assoc]
    exact Streaming.read_append _ _ _
  · have hj' : j = ents.length := by omega
    subst hj'
    rw [decide_eq_false h, List.take_length, blockWord, List.append_assoc]
    exact Streaming.read_append _ _ _

theorem binary_inj (W a b : ℕ) (ha : a < 2 ^ W) (hb : b < 2 ^ W) : binary W a = binary W b ↔ a = b := by
  constructor
  · intro h
    rw [← binary_value W a ha, ← binary_value W b hb, h]
  · rintro rfl; rfl

/-! ## The bank (tapes 0–8 the fold's, 9 the entry counter, 10 the target, 11 the flag, 12 the unit cell, 13 a log) -/

def bank14 (B : List Bool) (s : FoldSt) (cI cT cA cC W j e cE : ℕ) (fl : Bool) : Fin 14 → List Bool :=
  ![B, s.X, s.Y, s.ROW, s.AT, List.replicate cI false, List.replicate cT false, List.replicate cA false,
    List.replicate cC false, frame (binary W j), frame (binary W e), [fl], [true], List.replicate cE false]

def hd14 (p : ℕ) : Fin 14 → ℕ := ![p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def k14F : Fin 9 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]

theorem install_k14F (A : Fin 14 → List Bool) (v : Fin 9 → List Bool) :
    RecoveryRootRound.install k14F A v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, A 9, A 10, A 11, A 12, A 13] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k14F (H : Fin 14 → ℕ) (v : Fin 9 → ℕ) :
    dockH k14F H v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, H 9, H 10, H 11, H 12, H 13] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_slot _ (by decide) _ _ 1
    | exact dockH_slot _ (by decide) _ _ 2
    | exact dockH_slot _ (by decide) _ _ 3
    | exact dockH_slot _ (by decide) _ _ 4
    | exact dockH_slot _ (by decide) _ _ 5
    | exact dockH_slot _ (by decide) _ _ 6
    | exact dockH_slot _ (by decide) _ _ 7
    | exact dockH_slot _ (by decide) _ _ 8
    | exact dockH_other _ _ _ _ (by decide)

def k14E : Fin 4 → Fin 14 := ![9, 10, 11, 13]

theorem install_k14E (A : Fin 14 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install k14E A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 0, v 1, v 2, A 12, v 3] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def k14I : Fin 3 → Fin 14 := ![9, 12, 13]

theorem install_k14I (A : Fin 14 → List Bool) (v : Fin 3 → List Bool) :
    RecoveryRootRound.install k14I A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 0, A 10, A 11, v 1, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def k14N : Fin 1 → Fin 14 := ![0]

theorem install_k14N (A : Fin 14 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install k14N A v = ![v 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_k14N (H : Fin 14 → ℕ) (v : Fin 1 → ℕ) :
    dockH k14N H v = ![v 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def selEq : Fin 3 → Bool := ![true, true, false]
def selInc : Fin 2 → Bool := ![true, false]

noncomputable def mulBr := RecoveryFocus.machine k14F rowsMulM
noncomputable def skipBr := RecoveryFocus.machine k14F rowsSkipM

/-- One entry: compare, past its marker, multiply or pass its rows, past its terminator, count it. -/
noncomputable def entBody :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine k14E (MaskedReset.machine (EqCell.machine false) selEq)) (RecoveryFocus.machine k14N nudgeM))
    (branchM (11 : Fin 14) mulBr skipBr)) (RecoveryFocus.machine k14N nudgeM))
    (RecoveryFocus.machine k14I (MaskedReset.machine IncFlag.machine selInc))

noncomputable def fetchM := StreamController.machine entBody 0

/-- The accumulator after the entries before `j`. -/
def fetchSt (s0 : FoldSt) (ents : List (List SExpr)) (e j : ℕ) : FoldSt :=
  if e < j then foldAt s0 (ents.getD e []) (ents.getD e []).length else s0

def flagAt (f0 : Bool) (e j : ℕ) : Bool := if j = 0 then f0 else decide (j - 1 = e)

def entCost (s0 : FoldSt) (ents : List (List SExpr)) (W e j : ℕ) : ℕ :=
  2 * (2 * W + 1) + 2 + 1 + 1 + 1 +
    ((if j = e then rowsMulCost s0 (ents.getD j []) else rowsSkipCost (ents.getD j [])) + 2) + 1 + 1 + 1 +
    (2 * (2 * W + 2) + 2)

end NearCubicWires.WireExponent3_5.SeedFix
