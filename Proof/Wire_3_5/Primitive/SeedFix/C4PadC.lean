import Proof.Wire_3_5.Primitive.SeedFix.C4PadB
import Proof.Wire_3_5.Primitive.SeedFix.C4SJ
import Proof.Wire_3_5.Primitive.SeedFix.C4WA

/-! # (c′) (B), part 3: the branched stage (mode-generic)

At a call with no rows the compiler's precondition `1 ≤ m` fails (P3:1886-1906 against P3:3011-3016's empty entries);
the stage runs on the padded batch instead. **`padStage S`** (any C4 stage `S`): read the tape word's second bit
(`testS`) into a flag; if set (rows present) run `S` unchanged on the ports; if clear (every entry empty, `vE E`) write
the padded word (`padS`) on a scratch tape and run `S` with that tape as its port `1`. The ports `0`, `1` stay; the
output is `S`'s.

* `padStage`; **`padStage_plain`** (from `S`'s run on `v`, `v`'s second bit set) and **`padStage_deg`** (from `S`'s
  run on the padded word, `v = blockWord (replicate E [])`, `E ≥ 1`).

Paper quantity of the main type: the stage's output at the call (its seed word), through the padded batch at `R = 0`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Pad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Set (slx stageE)
open NearCubicWires.WireExponent3_5.Block (branchM branch_true branch_false)
open NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes (Stage3 Stage3Run stageIn stageOut)

/-! ## The banks -/

theorem stageIn_val (x : ℕ) (w v : List Bool) (i : Fin (3 + x)) :
    stageIn x w v i = if i.val = 0 then frame w else if i.val = 1 then v else [] := by
  unfold stageIn
  refine Fin.addCases (fun k => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]; fin_cases k <;> simp
  · rw [Fin.addCases_right, if_neg (by simp only [Fin.val_natAdd]; omega),
      if_neg (by simp only [Fin.val_natAdd]; omega)]

theorem step_of_run {x s : ℕ} {M : Machine (3 + x) s} {B : ℕ} {w v y : List Bool}
    (h : Stage3Run ⟨x, s, M⟩ B w v y) : ∃ J : Fin x → List Bool,
      Step M B (fun _ => 0) (stageIn x w v) (fun _ => 0) (stageOut x w v y J) := by
  obtain ⟨J, -, r, hr, ht, hh, hs⟩ := h
  exact ⟨J, r, hr, funext hh, ht, hs⟩

/-! ## The machine -/

section Mach
variable (x : ℕ)

/-- The scratch count: `S`'s, the flag, the padded word, two regions of four, a region for `S`. -/
def xP : ℕ := x + 10 + (3 + x)

def iF : Fin (3 + xP x) := ⟨3 + x, by unfold xP; omega⟩
def iP : Fin (3 + xP x) := ⟨3 + x + 1, by unfold xP; omega⟩
def i1 : Fin (3 + xP x) := ⟨1, by unfold xP; omega⟩

theorem h1 : (3 + x + 2) + (1 + 2 + 0 + 1) ≤ 3 + xP x := by unfold xP; omega
theorem h2 : (3 + x + 6) + (1 + 2 + 0 + 1) ≤ 3 + xP x := by unfold xP; omega
theorem hS : (3 + x + 10) + (3 + x) ≤ 3 + xP x := by unfold xP; omega

/-- The test's ports: its tape `0` on port `1`, its tape `2` on the flag. -/
def ext1 (j : Fin (1 + 2 + 0 + 1)) : Option (Fin (3 + xP x)) :=
  if j.val = 0 then some (i1 x) else if j.val = 2 then some (iF x) else none

/-- The padding's ports: its tape `0` on port `1`, its tape `2` on the padded word. -/
def ext2 (j : Fin (1 + 2 + 0 + 1)) : Option (Fin (3 + xP x)) :=
  if j.val = 0 then some (i1 x) else if j.val = 2 then some (iP x) else none

/-- A tape of `S` at its own index. -/
def lo (j : Fin (3 + x)) : Fin (3 + xP x) := ⟨j.val, by unfold xP; omega⟩

theorem lo_val (j : Fin (3 + x)) : (lo x j).val = j.val := rfl
theorem i1_val : (i1 x).val = 1 := rfl
theorem iP_val : (iP x).val = 3 + x + 1 := rfl

/-- `S` on the ports. -/
def extP (j : Fin (3 + x)) : Option (Fin (3 + xP x)) := some (lo x j)

/-- `S` with its port `1` on the padded word. -/
def extD (j : Fin (3 + x)) : Option (Fin (3 + xP x)) := some (if j.val = 1 then iP x else lo x j)

end Mach

/-- **The branched stage.** -/
noncomputable def padStage (S : Stage3) : Stage3 :=
  ⟨xP S.x, _, Composition.machine (RecoveryFocus.machine (slx (3 + S.x + 2) (h1 S.x) (ext1 S.x)) testZ)
    (branchM (iF S.x) (RecoveryFocus.machine (slx (3 + S.x + 10) (hS S.x) (extP S.x)) S.M)
      (Composition.machine (RecoveryFocus.machine (slx (3 + S.x + 6) (h2 S.x) (ext2 S.x)) padZ)
        (RecoveryFocus.machine (slx (3 + S.x + 10) (hS S.x) (extD S.x)) S.M)))⟩

/-! ## The ports' facts -/

section Facts
variable (x : ℕ)

theorem ext1_val {j : Fin (1 + 2 + 0 + 1)} {g : Fin (3 + xP x)} (h : ext1 x j = some g) :
    (j.val = 0 ∧ g.val = 1) ∨ (j.val = 2 ∧ g.val = 3 + x) := by
  unfold ext1 at h
  split_ifs at h with a b
  · cases h; exact Or.inl ⟨a, rfl⟩
  · cases h; exact Or.inr ⟨b, rfl⟩

theorem ext1_none {j : Fin (1 + 2 + 0 + 1)} (h : ext1 x j = none) : j.val ≠ 0 := by
  intro a; unfold ext1 at h; rw [if_pos a] at h; cases h

theorem ext1_inj : ∀ i j g, ext1 x i = some g → ext1 x j = some g → i = j := by
  intro i j g hi hj
  apply Fin.ext
  rcases ext1_val x hi with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases ext1_val x hj with ⟨c, d⟩ | ⟨c, d⟩ <;> omega

theorem ext1_lt : ∀ i g, ext1 x i = some g → g.val < 3 + x + 2 := by
  intro i g hi
  rcases ext1_val x hi with ⟨a, b⟩ | ⟨a, b⟩ <;> omega

theorem ext2_val {j : Fin (1 + 2 + 0 + 1)} {g : Fin (3 + xP x)} (h : ext2 x j = some g) :
    (j.val = 0 ∧ g.val = 1) ∨ (j.val = 2 ∧ g.val = 3 + x + 1) := by
  unfold ext2 at h
  split_ifs at h with a b
  · cases h; exact Or.inl ⟨a, rfl⟩
  · cases h; exact Or.inr ⟨b, rfl⟩

theorem ext2_none {j : Fin (1 + 2 + 0 + 1)} (h : ext2 x j = none) : j.val ≠ 0 := by
  intro a; unfold ext2 at h; rw [if_pos a] at h; cases h

theorem ext2_inj : ∀ i j g, ext2 x i = some g → ext2 x j = some g → i = j := by
  intro i j g hi hj
  apply Fin.ext
  rcases ext2_val x hi with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases ext2_val x hj with ⟨c, d⟩ | ⟨c, d⟩ <;> omega

theorem ext2_lt : ∀ i g, ext2 x i = some g → g.val < 3 + x + 6 := by
  intro i g hi
  rcases ext2_val x hi with ⟨a, b⟩ | ⟨a, b⟩ <;> omega

theorem extP_val {j : Fin (3 + x)} {g : Fin (3 + xP x)} (h : extP x j = some g) : g.val = j.val := by
  unfold extP at h; cases h; rfl

theorem extP_inj : ∀ i j g, extP x i = some g → extP x j = some g → i = j := by
  intro i j g hi hj
  apply Fin.ext
  have a := extP_val x hi
  have b := extP_val x hj
  omega

theorem extP_lt : ∀ i g, extP x i = some g → g.val < 3 + x + 10 := by
  intro i g hi
  have a := extP_val x hi
  have := i.isLt
  omega

theorem extD_val {j : Fin (3 + x)} {g : Fin (3 + xP x)} (h : extD x j = some g) :
    (j.val = 1 ∧ g.val = 3 + x + 1) ∨ (j.val ≠ 1 ∧ g.val = j.val) := by
  unfold extD at h
  cases h
  split_ifs with a
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨a, rfl⟩

theorem extD_inj : ∀ i j g, extD x i = some g → extD x j = some g → i = j := by
  intro i j g hi hj
  apply Fin.ext
  have := i.isLt
  have := j.isLt
  rcases extD_val x hi with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases extD_val x hj with ⟨c, d⟩ | ⟨c, d⟩ <;> omega

theorem extD_lt : ∀ i g, extD x i = some g → g.val < 3 + x + 10 := by
  intro i g hi
  have := i.isLt
  rcases extD_val x hi with ⟨a, b⟩ | ⟨a, b⟩ <;> omega

end Facts

/-! ## The runs -/

theorem stIn_hi (x : ℕ) (w v : List Bool) (i : Fin (3 + xP x)) (hi : 2 ≤ i.val) : stageIn (xP x) w v i = [] := by
  rw [stageIn_val, if_neg (by omega), if_neg (by omega)]

theorem stIn_1 (x : ℕ) (w v : List Bool) : stageIn (xP x) w v (i1 x) = v := by
  rw [stageIn_val]; simp [i1]

theorem stIn_lo (x : ℕ) (w v : List Bool) (j : Fin (3 + x)) :
    stageIn (xP x) w v ⟨j.val, by unfold xP; omega⟩ = stageIn x w v j := by
  rw [stageIn_val, stageIn_val]

/-- The test docked on port `1` and the flag. -/
theorem test_dock (x : ℕ) (w v : List Bool) : ∃ B1 : Fin (3 + xP x) → List Bool,
    Step (RecoveryFocus.machine (slx (3 + x + 2) (h1 x) (ext1 x)) testZ) (2 * 4 + 2) (fun _ => 0) (stageIn (xP x) w v)
      (fun _ => 0) B1 ∧
    (∀ i : Fin (3 + xP x), 3 + x + 6 ≤ i.val → B1 i = []) ∧ B1 (iF x) = [v.getD 1 false] ∧ B1 (iP x) = [] ∧
    (∀ i : Fin (3 + xP x), i.val < 3 + x → B1 i = stageIn (xP x) w v i) := by
  obtain ⟨tt, htS, ht0, ht2⟩ := testS v
  obtain ⟨B1, s1, b1hi, b1keep, -, b1map⟩ := stageE htS (3 + x + 2) (h1 x) (ext1 x) (ext1_inj x) (ext1_lt x)
    (stageIn (xP x) w v)
    (fun j g hj => by
      rcases ext1_val x hj with ⟨a, b⟩ | ⟨a, b⟩
      · rw [stageIn_val, if_neg (by omega), if_pos b, if_pos a]
      · rw [stageIn_val, if_neg (by omega), if_neg (by omega), if_neg (by omega)])
    (fun i hi => stIn_hi x w v i (by omega))
    (fun j hj => by rw [if_neg (ext1_none x hj)])
  refine ⟨B1, s1, fun i hi => b1hi i (by omega), ?_, ?_, fun i hi => ?_⟩
  · rw [b1map ⟨2, by omega⟩ (iF x) (by unfold ext1; simp [iF]), ht2]
  · rw [b1keep (iP x) (by rw [iP_val]; omega) (fun j hj => by
      rcases ext1_val x hj with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [iP_val] at b <;> omega)]
    exact stIn_hi x w v (iP x) (by rw [iP_val]; omega)
  · by_cases h1' : i.val = 1
    · have e : i = i1 x := Fin.ext h1'
      subst e
      rw [b1map ⟨0, by omega⟩ (i1 x) (by unfold ext1; simp), ht0, stIn_1]
    · refine b1keep i (by omega) (fun j hj => ?_)
      rcases ext1_val x hj with ⟨a, b⟩ | ⟨a, b⟩ <;> omega

/-- **The branched stage when rows are present**: `S`'s run on `v` (its second bit set). -/
theorem padStage_plain (S : Stage3) (w v y : List Bool) (B : ℕ) (h : Stage3Run S B w v y)
    (hv : v.getD 1 false = true) : Stage3Run (padStage S) (B + 20) w v y := by
  obtain ⟨x, s, M⟩ := S
  obtain ⟨J, hM⟩ := step_of_run h
  obtain ⟨B1, s1, b1hi, hF, -, hlow⟩ := test_dock x w v
  rw [hv] at hF
  obtain ⟨B2, s2, -, -, -, b2map⟩ := stageE hM (3 + x + 10) (hS x) (extP x) (extP_inj x) (extP_lt x) B1
    (fun j g hj => by
      have e : g = lo x j := Fin.ext (extP_val x hj)
      subst e
      rw [hlow _ j.isLt, lo, stIn_lo])
    (fun i hi => b1hi i (by omega))
    (fun j hj => by unfold extP at hj; cases hj)
  have hstep := s1.seq (branch_true (iF x) (Composition.machine (RecoveryFocus.machine (slx (3 + x + 6) (h2 x) (ext2 x)) padZ)
    (RecoveryFocus.machine (slx (3 + x + 10) (hS x) (extD x)) M)) s2 (by rw [hF]; rfl))
  refine C4Wrap.stage3_of_step hstep ?_ ?_ ?_ (B + 20) (by omega)
  · rw [b2map ⟨0, by omega⟩ ⟨0, by unfold xP; omega⟩ rfl]; rfl
  · rw [b2map ⟨1, by omega⟩ ⟨1, by unfold xP; omega⟩ rfl]; rfl
  · rw [b2map ⟨2, by omega⟩ ⟨2, by unfold xP; omega⟩ rfl]; rfl

/-- **The branched stage at a call with no rows**: `S`'s run on the padded word. -/
theorem padStage_deg (S : Stage3) (w y : List Bool) (E : ℕ) (hE : 1 ≤ E) (B : ℕ)
    (h : Stage3Run S B w (blockWord (padEnts (List.replicate E []))) y) :
    Stage3Run (padStage S) (B + padCost E + 20) w (blockWord (List.replicate E [])) y := by
  obtain ⟨x, s, M⟩ := S
  obtain ⟨J, hM⟩ := step_of_run h
  rw [← vE_eq]
  obtain ⟨B1, s1, b1hi, hF, hB1P, hlow⟩ := test_dock x w (vE E)
  rw [vE_one E hE] at hF
  obtain ⟨tp, hpS, hp0, hp2⟩ := padS E
  obtain ⟨B2, s2, b2hi, b2keep, -, b2map⟩ := stageE hpS (3 + x + 6) (h2 x) (ext2 x) (ext2_inj x) (ext2_lt x) B1
    (fun j g hj => by
      rcases ext2_val x hj with ⟨a, b⟩ | ⟨a, b⟩
      · have e : g = i1 x := Fin.ext b
        subst e
        rw [hlow (i1 x) (by rw [i1_val]; omega), stIn_1, if_pos a]
      · have e : g = iP x := Fin.ext b
        subst e
        rw [hB1P, if_neg (by omega)])
    (fun i hi => b1hi i hi)
    (fun j hj => by rw [if_neg (ext2_none x hj)])
  have hP : B2 (iP x) = blockWord (padEnts (List.replicate E [])) := by
    rw [b2map ⟨2, by omega⟩ (iP x) (by unfold ext2; simp [iP]), hp2]
  have h21 : B2 (i1 x) = vE E := by rw [b2map ⟨0, by omega⟩ (i1 x) (by unfold ext2; simp), hp0]
  have hlow2 : ∀ i : Fin (3 + xP x), i.val < 3 + x → i.val ≠ 1 → B2 i = stageIn (xP x) w (vE E) i := by
    intro i hi hi1
    rw [b2keep i (by omega) (fun j hj => by rcases ext2_val x hj with ⟨a, b⟩ | ⟨a, b⟩ <;> omega)]
    exact hlow i hi
  obtain ⟨B3, s3, -, b3keep, -, b3map⟩ := stageE hM (3 + x + 10) (hS x) (extD x) (extD_inj x) (extD_lt x) B2
    (fun j g hj => by
      rcases extD_val x hj with ⟨a, b⟩ | ⟨a, b⟩
      · have e : g = iP x := Fin.ext b
        subst e
        rw [hP, stageIn_val, if_neg (by omega), if_pos a]
      · have e : g = lo x j := Fin.ext b
        subst e
        rw [hlow2 _ j.isLt a, stageIn_val, stageIn_val, lo_val]
        simp [a])
    (fun i hi => b2hi i (by omega))
    (fun j hj => by unfold extD at hj; cases hj)
  have hstep := s1.seq (branch_false (iF x) (RecoveryFocus.machine (slx (3 + x + 10) (hS x) (extP x)) M) (s2.seq s3)
    (by rw [hF]; rfl))
  refine C4Wrap.stage3_of_step hstep ?_ ?_ ?_ (B + padCost E + 20) (by omega)
  · rw [b3map ⟨0, by omega⟩ ⟨0, by unfold xP; omega⟩ rfl]; rfl
  · show B3 (i1 x) = vE E
    rw [b3keep (i1 x) (by rw [i1_val]; omega) (fun j hj => by
      rcases extD_val x hj with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [i1_val] at b <;> omega), h21]
  · rw [b3map ⟨2, by omega⟩ ⟨2, by unfold xP; omega⟩ rfl]; rfl

end NearCubicWires.WireExponent3_5.PrimT.C4Pad
