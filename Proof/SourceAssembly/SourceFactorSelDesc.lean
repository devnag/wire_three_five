import Proof.SourceAssembly.SLoadMaskFrame

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Desc
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## The descriptor shape -/

/-- The kind of a factor slot. -/
inductive Kind where
  | absent
  | sys
  | orig
deriving DecidableEq

/-- The systematic kind flag. -/
def flagS : Kind → List Bool
  | .sys => [true]
  | _ => []

/-- The original kind flag. -/
def flagO : Kind → List Bool
  | .orig => [true]
  | _ => []

/-- **The sixteen descriptors of one slot** (the common shape of `ThrSwitch.descAt` / `SymSwitch.descAt`). -/
def gdesc (tpl uP uW uL bm bits : List Bool) : Kind → Nat → List Bool
  | .absent, _ => []
  | .sys, n => if n = 0 ∨ n = 2 then bm else if n = 1 ∨ n = 3 then tpl else if n = 14 then [true] else []
  | .orig, n => if n = 4 ∨ n = 9 then frame bits else if n = 5 ∨ n = 10 then tpl
      else if n = 6 ∨ n = 11 then uP else if n = 7 ∨ n = 12 then uW
      else if n = 8 ∨ n = 13 then uL else if n = 15 then [true] else []

/-- Descriptor `n`'s local tape. -/
def dT (n : Fin 16) : Fin 27 := ⟨11 + n.val, by omega⟩

theorem pad_pad (C D : Nat) (w : List Bool) (h : C ≤ D) :
    ZeroPadding.pad D (ZeroPadding.pad C w) = ZeroPadding.pad D w := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc,
    ← List.replicate_add]
  congr 2
  omega

theorem pad_nil (R : Nat) : ZeroPadding.pad R ([] : List Bool) = List.replicate R false := by
  simp [ZeroPadding.pad]

/-! ## The two primitives -/

/-- One bounded copy at heads `0`: the source (any padding) onto a blank `R`-cell target, driver `1^D`. -/
theorem copy_local (Q Qd D C R : Nat) (w : List Bool) (hw : w.length ≤ D) (hDR : D ≤ R) (hC : D + 1 ≤ C) :
    Step RecoveryBoundedTapeCopy.machine (2 * D + 4) (fun _ => 0)
      ![ZeroPadding.pad Q w, List.replicate R false, ZeroPadding.pad Qd (List.replicate D true),
        List.replicate C false] (fun _ => 0)
      ![ZeroPadding.pad Q w, ZeroPadding.pad R w, ZeroPadding.pad Qd (List.replicate D true),
        List.replicate C false] := by
  have base := (Step.of_ready (RecoveryBoundedTapeCopy.copy_ready (ZeroPadding.pad Q w) D C)).pad
    ![0, R, Qd, 0]
  have hcop : RecoveryBoundedTapeCopy.copied (ZeroPadding.pad Q w) D = ZeroPadding.pad D w := by
    have he : readTapeBit (ZeroPadding.pad Q w) = readTapeBit w := funext (ZeroPadding.read_pad Q w)
    have h := CloseoutRowsMetadataCopy.copied_pad w D hw
    simpa only [RecoveryBoundedTapeCopy.copied, he] using h
  have hmax : max C (D + 1) = C := by omega
  refine (base.congr_in rfl ?_).congr rfl ?_
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · exact pad_nil R
    · rfl
    · exact ZeroPadding.pad_zero _
  · funext i
    fin_cases i
    · exact ZeroPadding.pad_zero _
    · show ZeroPadding.pad R (RecoveryBoundedTapeCopy.copied (ZeroPadding.pad Q w) D) = _
      rw [hcop, pad_pad D R w hDR]
      rfl
    · rfl
    · show ZeroPadding.pad 0 (List.replicate (max C (D + 1)) false) = _
      rw [ZeroPadding.pad_zero, hmax]
      rfl

/-- The docked bounded copy: `![src, dst, driver, log]`. -/
def copyM {U : Nat} (s d v l : Fin U) :=
  RecoveryFocus.machine (![s, d, v, l] : Fin 4 → Fin U) RecoveryBoundedTapeCopy.machine

theorem copy_step {U : Nat} (s d v l : Fin U) (h1 : s ≠ d) (h2 : s ≠ v) (h3 : s ≠ l) (h4 : d ≠ v)
    (h5 : d ≠ l) (h6 : v ≠ l)
    (Q Qd D C R : Nat) (w : List Bool) (hw : w.length ≤ D) (hDR : D ≤ R) (hC : D + 1 ≤ C)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHs : H s = 0) (hHd : H d = 0) (hHv : H v = 0) (hHl : H l = 0)
    (hs : A s = ZeroPadding.pad Q w) (hd : A d = List.replicate R false)
    (hv : A v = ZeroPadding.pad Qd (List.replicate D true)) (hl : A l = List.replicate C false) :
    Step (copyM s d v l) (2 * D + 4) H A H (Function.update A d (ZeroPadding.pad R w)) := by
  have hinj := SLoad.MaskFrame.quad_injective s d v l h1 h2 h3 h4 h5 h6
  exact SLoad.step_update (copy_local Q Qd D C R w hw hDR hC) 1
    (by
      intro i hi
      fin_cases i
      · rfl
      · exact absurd rfl hi
      · rfl
      · rfl)
    _ hinj H A
    (by intro i; fin_cases i <;> assumption)
    (by intro i; fin_cases i <;> assumption)

/-! ## The machine -/

/-- Copy local tape `s` onto descriptor tape `d` (driver `9`, log `10`). -/
def cp (s d : Fin 27) := copyM s d (9 : Fin 27) (10 : Fin 27)

/-- The systematic writer: bitmap → 0, 2; template → 1, 3; flag S → 14. -/
def sysW := Composition.machine (cp 2 11) (Composition.machine (cp 4 12)
  (Composition.machine (cp 2 13) (Composition.machine (cp 4 14) (cp 0 25))))

def sysCost (D : Nat) : Nat := 5 * (2 * D + 4) + 4

/-! ## The two writers' runs -/

theorem sys_run (tpl bm : List Bool) (Qf Qb Qt Qd D C R : Nat) (E : Fin 27 → List Bool)
    (h0 : E 0 = ZeroPadding.pad Qf [true]) (h2 : E 2 = ZeroPadding.pad Qb bm)
    (h4 : E 4 = ZeroPadding.pad Qt tpl) (h9 : E 9 = ZeroPadding.pad Qd (List.replicate D true))
    (h10 : E 10 = List.replicate C false) (hout : ∀ j : Fin 27, 11 ≤ j.val → E j = List.replicate R false)
    (hbm : bm.length ≤ D) (htpl : tpl.length ≤ D) (h1 : 1 ≤ D) (hDR : D ≤ R) (hC : D + 1 ≤ C) :
    Step sysW (sysCost D) (fun _ => 0) E (fun _ => 0)
      (Function.update (Function.update (Function.update (Function.update (Function.update E
        11 (ZeroPadding.pad R bm)) 12 (ZeroPadding.pad R tpl)) 13 (ZeroPadding.pad R bm))
        14 (ZeroPadding.pad R tpl)) 25 (ZeroPadding.pad R [true])) := by
  set E1 := Function.update E 11 (ZeroPadding.pad R bm) with hE1
  set E2 := Function.update E1 12 (ZeroPadding.pad R tpl) with hE2
  set E3 := Function.update E2 13 (ZeroPadding.pad R bm) with hE3
  set E4 := Function.update E3 14 (ZeroPadding.pad R tpl) with hE4
  have s1 := copy_step (2 : Fin 27) 11 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qb Qd D C R bm hbm hDR hC (fun _ => 0) E rfl rfl rfl rfl h2 (hout 11 (by decide)) h9 h10
  have s2 := copy_step (4 : Fin 27) 12 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qt Qd D C R tpl htpl hDR hC (fun _ => 0) E1 rfl rfl rfl rfl
    (by simp [E1, Function.update_apply, h4]) (by simp [E1, Function.update_apply, hout 12 (by decide)])
    (by simp [E1, Function.update_apply, h9]) (by simp [E1, Function.update_apply, h10])
  have s3 := copy_step (2 : Fin 27) 13 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qb Qd D C R bm hbm hDR hC (fun _ => 0) E2 rfl rfl rfl rfl
    (by simp [E1, E2, Function.update_apply, h2])
    (by simp [E1, E2, Function.update_apply, hout 13 (by decide)])
    (by simp [E1, E2, Function.update_apply, h9]) (by simp [E1, E2, Function.update_apply, h10])
  have s4 := copy_step (4 : Fin 27) 14 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qt Qd D C R tpl htpl hDR hC (fun _ => 0) E3 rfl rfl rfl rfl
    (by simp [E1, E2, E3, Function.update_apply, h4])
    (by simp [E1, E2, E3, Function.update_apply, hout 14 (by decide)])
    (by simp [E1, E2, E3, Function.update_apply, h9]) (by simp [E1, E2, E3, Function.update_apply, h10])
  have s5 := copy_step (0 : Fin 27) 25 9 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) Qf Qd D C R [true] (by simpa using h1) hDR hC (fun _ => 0) E4 rfl rfl rfl rfl
    (by simp [E1, E2, E3, E4, Function.update_apply, h0])
    (by simp [E1, E2, E3, E4, Function.update_apply, hout 25 (by decide)])
    (by simp [E1, E2, E3, E4, Function.update_apply, h9])
    (by simp [E1, E2, E3, E4, Function.update_apply, h10])
  have hall : Step sysW _ _ _ _ _ := s1.seq (s2.seq (s3.seq (s4.seq s5)))
  exact hall.enlarge (by unfold sysCost; omega)

/-! ## The switch -/

theorem read_true (R : Nat) : readTapeBit (ZeroPadding.pad R [true]) 0 = true := by
  simp [ZeroPadding.pad, readTapeBit]
theorem read_blank (R : Nat) : readTapeBit (ZeroPadding.pad R []) 0 = false := by
  simp [ZeroPadding.pad, readTapeBit]

theorem stop_step (A : Fin 27 → List Bool) :
    Step (CloseoutRowsOriginalSwitch.stop 27) 0 (fun _ => 0) A (fun _ => 0) A :=
  ⟨_, rfl, rfl, rfl, le_refl _⟩


end
end NearCubicWires.SourceFactorSel.Desc
