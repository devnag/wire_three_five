import Proof.Wire_3_5.Primitive.SeedFix.C4SI
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes

/-! # C4 per-call setup (item 3), part 10: the SYM stage's layout and its one-input stages

P3:3011-3016 ("The processor writes the pool, the enumeration's rulers and constants, and the compiler request's
numbers before the loop"), P3:2929-2941 (the seed field and its modulus), P3:1886-1906 (the compiler's request
fields): the SYM stage's bank (`Stage3`: the framed request, the SYM batch word, the output port, then the scratch),
one region per setup machine in the order they run, then the erase log, the loop's cells, the finisher's tapes.

* `Lay` (the power machines' degree, the C3 writer, the loop's cell count, the finisher's tape count), `N`, the named
  tapes `gP0 … gLG`, `gW` (the thirty-nine words), the regions `oCP … oLP`;
* `ext0`, **`stage0`** (a one-input stage docked on its region), `stageE` (`stageP`'s exists form);
* `eraseS` (base `SelectedErase`: the loop's cells to `R` falses from the driver `1^R`, the log to `R + 1` falses).

Paper quantities of the main types: the setup's words on their tapes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

/-! ## One-input stages -/

/-- A stage's one input: its tape `0` onto the bank's tape `g`. -/
def ext0 {t u : ℕ} (g : Fin u) (j : Fin t) : Option (Fin u) := if j.val = 0 then some g else none

theorem ext0_some {t u : ℕ} {g g' : Fin u} {j : Fin t} (h : ext0 g j = some g') : j.val = 0 ∧ g' = g := by
  unfold ext0 at h
  split_ifs at h with h0
  exact ⟨h0, (Option.some.inj h).symm⟩

theorem ext0_none {t u : ℕ} {g : Fin u} {j : Fin t} (h : ext0 g j = none) : j.val ≠ 0 := by
  unfold ext0 at h
  split_ifs at h with h0
  exact h0

/-- **A docked stage** (`stageP`, exists form). -/
theorem stageE {t u s n : ℕ} {M : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) (off : ℕ) (hoff : off + t ≤ u) (ext : Fin t → Option (Fin u))
    (hinj : ∀ i j g, ext i = some g → ext j = some g → i = j) (hlt : ∀ i g, ext i = some g → g.val < off)
    (B : Fin u → List Bool) (hex : ∀ j g, ext j = some g → B g = tin j)
    (hblank : ∀ i : Fin u, off ≤ i.val → B i = []) (htin : ∀ j, ext j = none → tin j = []) :
    ∃ B' : Fin u → List Bool, Step (RecoveryFocus.machine (slx off hoff ext) M) n (fun _ => 0) B (fun _ => 0) B' ∧
      (∀ i : Fin u, off + t ≤ i.val → B' i = []) ∧
      (∀ i : Fin u, i.val < off → (∀ j, ext j ≠ some i) → B' i = B i) ∧
      (∀ (j : Fin t) (i : Fin u), ext j = none → i.val = off + j.val → B' i = tout j) ∧
      (∀ j g, ext j = some g → B' g = tout j) :=
  ⟨_, stageP h off hoff ext hinj hlt B hex hblank htin⟩

/-- **A docked one-input stage**: a run from `X` on its tape `0` (every other tape blank), docked with tape `0` onto
the bank's `g` below the region, the bank blank from the region up. -/
theorem stage0 {t u s n : ℕ} {M : Machine t s} {X : List Bool} {tout : Fin t → List Bool}
    (h : Step M n (fun _ => 0) (fun j => if j.val = 0 then X else []) (fun _ => 0) tout) (h0 : 0 < t)
    (off : ℕ) (hoff : off + t ≤ u) (g : Fin u) (hg : g.val < off) (B : Fin u → List Bool) (hB : B g = X)
    (hblank : ∀ i : Fin u, off ≤ i.val → B i = []) :
    ∃ B' : Fin u → List Bool, Step (RecoveryFocus.machine (slx off hoff (ext0 g)) M) n (fun _ => 0) B (fun _ => 0) B' ∧
      (∀ i : Fin u, off + t ≤ i.val → B' i = []) ∧ (∀ i : Fin u, i.val < off → i ≠ g → B' i = B i) ∧
      (∀ (j : Fin t) (i : Fin u), j.val ≠ 0 → i.val = off + j.val → B' i = tout j) ∧ B' g = tout ⟨0, h0⟩ := by
  obtain ⟨B', st, bl, un, pv, ex⟩ := stageE h off hoff (ext0 g)
    (fun i j g' hi hj => Fin.ext (by rw [(ext0_some hi).1, (ext0_some hj).1]))
    (fun i g' hi => by rw [(ext0_some hi).2]; exact hg) B
    (fun j g' hj => by obtain ⟨h1, rfl⟩ := ext0_some hj; simp [h1, hB])
    hblank (fun j hj => by simp [ext0_none hj])
  refine ⟨B', st, bl, fun i hi hne => un i hi (fun j e => hne (ext0_some e).2), fun j i hj hi => pv j i
    (by simp [ext0, hj]) hi, ?_⟩
  exact ex ⟨0, h0⟩ g (by simp [ext0])

/-! ## The erase -/

/-- **The pads**: base `SelectedErase` from the driver `1^R` and a blank log: every masked tape (at most `R` long) to
`R` falses, the log to `R + 1` falses, every other tape unchanged, every head at `0`. -/
theorem eraseS {u : ℕ} (mask : Fin u → Bool) (drv lg : Fin u) (hd : mask drv = false) (hl : mask lg = false)
    (hne : drv ≠ lg) (R : ℕ) (B : Fin u → List Bool) (hb : ∀ i, mask i = true → (B i).length ≤ R)
    (hdrv : B drv = List.replicate R true) (hlg : B lg = []) :
    Step (CloseoutWitness.SelectedErase.machine mask drv lg) (2 * R + 4) (fun _ => 0) B (fun _ => 0)
      (CloseoutWitness.SelectedErase.output mask lg R B) := by
  obtain ⟨r, hr, -, hh, ht⟩ := CloseoutWitness.SelectedErase.erase_run mask drv lg hd hl hne R (fun _ => 0) B
    (fun _ _ => rfl) hb hdrv hlg
  exact Step.of_run hr hh ht

/-! ## Bank reads -/

theorem ac_lt {m n : ℕ} {α : Type} (f : Fin m → α) (g : Fin n → α) (j : Fin (m + n)) (h : j.val < m) :
    Fin.addCases (motive := fun _ => α) f g j = f ⟨j.val, h⟩ := by
  obtain ⟨k, hk⟩ := j
  simp only at h
  show Fin.addCases (motive := fun _ => α) f g (Fin.castAdd n ⟨k, h⟩) = _
  rw [Fin.addCases_left]

theorem ac_ge {m n : ℕ} {α : Type} (f : Fin m → α) (g : Fin n → α) (j : Fin (m + n)) (h : m ≤ j.val) :
    Fin.addCases (motive := fun _ => α) f g j = g ⟨j.val - m, by omega⟩ := by
  obtain ⟨k, hk⟩ := j
  simp only at h
  have e : (⟨k, hk⟩ : Fin (m + n)) = Fin.natAdd m ⟨k - m, by omega⟩ := Fin.ext (by simp; omega)
  conv_lhs => rw [e]
  rw [Fin.addCases_right]

/-! ## The layout -/

/-- **The SYM stage's layout parameters**: the power machines' degree `D`, the C3 request writer, the loop's cell
count `T`, the finisher's tape count `tS`. -/
structure Lay where
  D : ℕ
  S3 : C3ReqIface.C3Stage
  T : ℕ
  tS : ℕ

namespace Lay
variable (L : Lay)

/-- The power machine's tapes. -/
abbrev U : ℕ := UnaryCalc.tapes L.D
/-- The stage's scratch count. -/
def X : ℕ := 10657 + 3 * L.U + L.S3.t + L.T + L.tS
/-- The stage's tapes. -/
abbrev N : ℕ := 3 + L.X

theorem N_eq : L.N = 10660 + 3 * L.U + L.S3.t + L.T + L.tS := by unfold N X; omega

theorem U_pos : 0 < L.U := (UnaryCalc.inputTape L.D).pos
theorem U_eq : L.U = RepairSource.ProjectionNormalization.DimensionPolynomial.tapes L.D := rfl
theorem out_lt : (UnaryCalc.outputTape L.D).val < L.U := (UnaryCalc.outputTape L.D).isLt

/-- The regions, in running order. -/
def oU2 : ℕ := 18 + L.U
def oU3 : ℕ := 18 + 2 * L.U
def oDA : ℕ := 18 + 3 * L.U
def oCP : ℕ := 9920 + 3 * L.U
def oBG : ℕ := 9924 + 3 * L.U
def oM1 : ℕ := 10601 + 3 * L.U
def oM2 : ℕ := 10618 + 3 * L.U
def oCU : ℕ := 10635 + 3 * L.U
def oCR2 : ℕ := 10647 + 3 * L.U
def oC3 : ℕ := 10659 + 3 * L.U
def oLP : ℕ := 10660 + 3 * L.U + L.S3.t

/-- The ports: the framed request, the SYM batch word, the output. -/
def gP0 : Fin L.N := ⟨0, by rw [N_eq]; omega⟩
def gP1 : Fin L.N := ⟨1, by rw [N_eq]; omega⟩
def gP2 : Fin L.N := ⟨2, by rw [N_eq]; omega⟩
/-- The raw request. -/
def gRAW : Fin L.N := ⟨4, by rw [N_eq]; omega⟩
/-- `1^n`. -/
def gN1 : Fin L.N := ⟨14, by rw [N_eq]; omega⟩
/-- The three powers of `n + 1`. -/
def gUL : Fin L.N := ⟨18 + (UnaryCalc.outputTape L.D).val, by have := L.out_lt; rw [N_eq]; omega⟩
def gUD : Fin L.N := ⟨18 + L.U + (UnaryCalc.outputTape L.D).val, by have := L.out_lt; rw [N_eq]; omega⟩
def gUW : Fin L.N := ⟨18 + 2 * L.U + (UnaryCalc.outputTape L.D).val, by have := L.out_lt; rw [N_eq]; omega⟩
/-- The data word. -/
def gDO : Fin L.N := ⟨24 + 3 * L.U, by rw [N_eq]; omega⟩
/-- The call's counts. -/
def gU : Fin L.N := ⟨9922 + 3 * L.U, by rw [N_eq]; omega⟩
/-- **The thirty-nine words** (the numbers machine's streams `symO`). -/
def gW (j : Fin 39) : Fin L.N := ⟨9925 + 3 * L.U + (symO j).val, by have := (symO j).isLt; rw [N_eq]; omega⟩
/-- The two modulus words. -/
def gMA : Fin L.N := ⟨10613 + 3 * L.U, by rw [N_eq]; omega⟩
def gMB : Fin L.N := ⟨10630 + 3 * L.U, by rw [N_eq]; omega⟩
/-- `1^{2^{2·dRow}}` and the driver `1^R`. -/
def gUU : Fin L.N := ⟨10643 + 3 * L.U, by rw [N_eq]; omega⟩
def gRR : Fin L.N := ⟨10655 + 3 * L.U, by rw [N_eq]; omega⟩
/-- The compiler request's fields. -/
def gPRE : Fin L.N := ⟨10659 + 3 * L.U + L.S3.preS.val, by have := L.S3.preS.isLt; rw [N_eq]; omega⟩
def gPOST : Fin L.N := ⟨10659 + 3 * L.U + L.S3.postS.val, by have := L.S3.postS.isLt; rw [N_eq]; omega⟩
/-- The erase log. -/
def gLG : Fin L.N := ⟨10659 + 3 * L.U + L.S3.t, by rw [N_eq]; omega⟩

/-- The loop's cells. -/
def maskLP (i : Fin L.N) : Bool := decide (L.oLP ≤ i.val ∧ i.val < L.oLP + L.T)

theorem symO_inj : Function.Injective symO := by decide

theorem symO_ge (j : Fin 39) : 120 ≤ (symO j).val := by revert j; decide
theorem symO_le (j : Fin 39) : (symO j).val ≤ 159 := by revert j; decide

theorem gW_inj {j k : Fin 39} (h : L.gW j = L.gW k) : j = k := by
  have hv := congrArg Fin.val h
  simp only [gW] at hv
  exact symO_inj (Fin.ext (by omega))

end Lay

end NearCubicWires.WireExponent3_5.PrimT.C4Set
