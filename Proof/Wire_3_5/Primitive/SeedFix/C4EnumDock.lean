import Proof.Wire_3_5.Primitive.SeedFix.C4Enum
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixJLink

/-! # SEEDFIX C4.L, the enumeration dock: one child's printed objective (P3:2915-2917, 3034-3035)

"For every seed prefix, its per-column conditional potential is an explicit rational polynomial in at most `2h`
Boolean matrix-entry factors per term" (P3:2915-2917); "For each candidate child prefix, print its signed equation
expression" (P3:3034-3035). The child of bit `b` of the prefix `p` prints `V_{p ++ [b]}` with SeedFix's enumeration
(`JLink.sampEnum_run`, the printed objective `sampTerms`). This module is the **enumeration unit** of the child, on
`95` tapes: the arm (`C4Arm.armW b`: C5's word layout on `47 + 2 + 17` tapes and its log), `17` per-call constant
tapes (`kc`: the bank's constant words `QM ONE ONES8 BAT R8 RL RK R1 R7 RK2 PW Z9 Z18 ONEW`, the split's two
constant rulers, the loop counter `word (nT·2^w)`), and `11` blank tapes. The enumeration's `65` tapes sit on the
arm's streams `11 … 47`, the constants and the blanks (`enSl`):

`euM b = arm ; the counter head to 1 ; sampEnum docked at enSl ; the counter head to 0`.

* `arm_bank`: the arm's exit bank read at `enSl` is the enumeration's entry list (`jInit`, the split's four, the
  counter; `C4Enum.jt_init`);
* **`eu_step`**: from the rulers, the framed prefix `p`, the constants and blanks (every head at `0`), under the
  enumeration's side conditions `EnumOk` (SeedFix's hypotheses, carried to C4.K), the unit ends with every head at
  `0`, the OUT tape holding `exprWord (sampTerms P nT R batch |p ++ [b]| (listNum (p ++ [b])))`, and the rulers, the
  prefix and the constants unchanged.

Paper quantity of the main type: the printed conditional objective `sampTerms` of the child prefix `p ++ [b]`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Dock
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.PrimT.C4Enum (jX S0 jInit)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.Sampler

/-! ## The layout -/

/-- The arm's tapes: C5's word layout `47 + 2 + 17` and its log. -/
abbrev AT : ℕ := 47 + 2 + 17 + 1

/-- The unit's tapes: the arm, `17` constants, `11` blanks. -/
abbrev EU : ℕ := AT + (17 + 11)

/-- The arm's tape of stream `d`. -/
def aS (d : Fin (47 + 1)) : Fin EU := Fin.castAdd (17 + 11) (Fin.castAdd 1 (sTape (ns := 47) (nr := 17) d))

/-- Constant tape `k`. -/
def kS (k : Fin 17) : Fin EU := Fin.natAdd AT (Fin.castAdd 11 k)

/-- Blank tape `k`. -/
def bS (k : Fin 11) : Fin EU := Fin.natAdd AT (Fin.natAdd 17 k)

theorem aS_val (d : Fin (47 + 1)) : (aS d).val = if d.val = 0 then 0 else d.val + 1 := rfl

/-- The enumeration's tapes in the unit (JT order, the split's four, the loop counter). -/
def enL : List (Fin EU) := [aS 11, aS 12, aS 13, aS 14, aS 15, aS 16, kS 0, aS 17, aS 18, kS 1, bS 0, kS 2, aS 19, bS 1, bS 2, bS 3, bS 4, kS 3, aS 20, aS 21, aS 22, aS 23, aS 24, kS 4, kS 5, kS 6, kS 7, kS 8, kS 9, aS 25, aS 26, aS 27, kS 10, bS 5, aS 28, aS 29, kS 11, aS 30, aS 31, bS 6, aS 32, kS 12, bS 7, kS 13, bS 8, bS 9, aS 33, aS 34, aS 35, bS 10, aS 36, aS 37, aS 38, aS 39, aS 40, aS 41, aS 42, aS 43, aS 44, aS 45, kS 14, kS 15, aS 46, aS 47, kS 16]

/-- **The enumeration's slot map.** -/
def enSl (j : Fin 65) : Fin EU := enL.getD j.val (kS 16)

/-- Its inverse on the image. -/
def enBack (i : Fin EU) : Fin 65 := ⟨([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 7, 8, 12, 18, 19, 20, 21, 22, 29, 30, 31, 34, 35, 37, 38, 40, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 9, 11, 17, 23, 24, 25, 26, 27, 28, 32, 36, 41, 43, 60, 61, 64, 10, 13, 14, 15, 16, 33, 39, 42, 44, 45, 49] : List ℕ).getD i.val 0 % 65, Nat.mod_lt _ (by norm_num)⟩

theorem enBack_enSl (j : Fin 65) : enBack (enSl j) = j := by
  fin_cases j <;> rfl

theorem enSl_inj : Function.Injective enSl := fun i j h => by
  rw [← enBack_enSl i, ← enBack_enSl j, h]

theorem enSl_ge (j : Fin 65) : 12 ≤ (enSl j).val := by
  fin_cases j <;> decide

/-- The loop counter's tape. -/
def cntT : Fin EU := kS 16

theorem enSl_64 : enSl 64 = cntT := rfl

theorem enSl_eq_cnt (j : Fin 65) (h : enSl j = cntT) : j.val = 64 := by
  have e := congrArg enBack h
  rw [enBack_enSl] at e
  rw [e]
  rfl

/-! ## The constants and the entry bank -/

section Bank
variable (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT : ℕ)

/-- **The per-call constants** of the unit: the bank's constant words, the split's unit ruler and state-word ruler,
and the loop counter `word (nT·2^w)`. -/
def kc : Fin 17 → List Bool :=
  ![frame (binary P.ell (P.Q - 1)), [true], frame (List.replicate 8 true), SeedFix.blockWord ents,
    List.replicate 8 true ++ [false], List.replicate P.ell true ++ [false], List.replicate P.kh true ++ [false],
    List.replicate 1 true ++ [false], List.replicate 7 true ++ [false], List.replicate (2 * P.kh) true ++ [false],
    frame (binary P.ell P.modulus), [false], [false], frame (binary P.ell 1),
    List.replicate 1 true ++ [false], List.replicate TWd true ++ [false],
    RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh))]

/-- The arm's rulers at the call: `ℓ, kh, TWd, Cap, 2kh, Wt, |RT|, w+1, wT+1, 8ℓ`. -/
def nums : C4Arm.Nums :=
  ⟨P.ell, P.kh, TWd, Cap, 2 * P.kh, 2 * P.kh + TWd, 8 * (P.ell * (2 * P.ell + 1)) + Cap,
    8 + 8 * P.ell + 8 * P.kh + 1, 8 + 8 * P.ell + 8 * P.kh + TWd + 1, 8 * P.ell⟩

/-- **The unit's entry bank**: the arm's rulers and framed prefix `p` (every other arm tape blank), the constants,
the blanks. -/
def euIn (p : List Bool) : Fin EU → List Bool :=
  Fin.addCases (Fin.addCases (C4Pipe.wblank (C4Arm.armSt (nums P TWd Cap) p)) (fun _ : Fin 1 => []))
    (Fin.addCases (kc P ents TWd nT) (fun _ : Fin 11 => []))

/-- The enumeration's entry tapes of the child prefix `p'`, as a list. -/
def eL (p' : List Bool) : List (List Bool) :=
  jInit P ents TWd Cap p' ++ [SeedFix.SplitT.ext (jX P ents TWd Cap p') 0 0, SeedFix.SplitT.ext (jX P ents TWd Cap p') 0 1,
    SeedFix.SplitT.ext (jX P ents TWd Cap p') 0 2, SeedFix.SplitT.ext (jX P ents TWd Cap p') 0 3,
    RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ (jX P ents TWd Cap p').w)]

theorem armWrs_len (N : C4Arm.Nums) : (C4Arm.armWrs N).length = 35 := rfl

theorem jInit_length (p' : List Bool) : (jInit P ents TWd Cap p').length = 60 := rfl

/-- The enumeration's entry bank (`sampEnum_run`'s) is the list `eL`. -/
theorem tin_eq (p' : List Bool) (hp : p'.length ≤ 8 * P.ell) (hQ : 1 ≤ P.Q) (j : Fin 65) :
    Fin.addCases (m := 64) (n := 1)
        (SeedFix.SplitT.lay (jX P ents TWd Cap p')
          ((SeedFix.SplitT.at_ (jX P ents TWd Cap p') (SeedFix.SplitT.tOf (jX P ents TWd Cap p') 0)).jt 0 (S0 P) [] 0) 0)
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ (jX P ents TWd Cap p').w)) j =
      (eL P ents TWd Cap nT p').getD j.val [] := by
  have hT := C4Enum.jt_init P ents TWd Cap p' hp hQ
  refine Fin.addCases (m := 64) (n := 1) (fun i => ?_) (fun i => ?_) j
  · rw [Fin.addCases_left]
    unfold SeedFix.SplitT.lay
    refine Fin.addCases (m := 60) (n := 4) (fun i' => ?_) (fun i' => ?_) i
    · rw [Fin.addCases_left]
      show (((SeedFix.SplitT.at_ (jX P ents TWd Cap p') (SeedFix.SplitT.tOf (jX P ents TWd Cap p') 0)).jt 0 (S0 P) []
        0).toList.getD i'.val []) = _
      rw [hT]
      simp only [Fin.val_castAdd, eL]
      rw [List.getD_append _ _ _ _ (by rw [jInit_length]; exact i'.isLt)]
    · rw [Fin.addCases_right]
      fin_cases i' <;> rfl
  · fin_cases i
    rfl

end Bank

/-! ## The arm's exit bank is the enumeration's entry bank -/

section ArmBank
variable (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT : ℕ)

/-- **The arm's exit bank read at `enSl`** is the enumeration's entry list of the child prefix `p ++ [b]`. -/
theorem arm_bank (b : Bool) (p : List Bool) (τ : C4Arm.AS) (B1 : Fin EU → List Bool)
    (hArm : ∀ d, B1 (aS d) = τ.st d) (hK : ∀ k, B1 (kS k) = kc P ents TWd nT k) (hBl : ∀ k, B1 (bS k) = [])
    (hwr : ∀ x ∈ C4Arm.armWrs (nums P TWd Cap), τ.st x.d = x.w) (h30 : τ.st 30 = frame (p ++ [b]))
    (h34 : τ.st 34 = List.replicate ((nums P TWd Cap).l8 - (p.length + 1)) true ++ List.replicate (p.length + 1) false)
    (j : Fin 65) : B1 (enSl j) = (eL P ents TWd Cap nT (p ++ [b])).getD j.val [] := by
  fin_cases j
  · have hx := hwr _ (List.getElem_mem (show 0 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 11).trans hx
  · have hx := hwr _ (List.getElem_mem (show 1 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 12).trans hx
  · have hx := hwr _ (List.getElem_mem (show 2 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 13).trans hx
  · have hx := hwr _ (List.getElem_mem (show 3 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 14).trans hx
  · have hx := hwr _ (List.getElem_mem (show 4 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 15).trans hx
  · have hx := hwr _ (List.getElem_mem (show 5 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 16).trans hx
  · exact hK 0
  · have hx := hwr _ (List.getElem_mem (show 6 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 17).trans hx
  · have hx := hwr _ (List.getElem_mem (show 7 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 18).trans hx
  · exact hK 1
  · exact hBl 0
  · exact hK 2
  · have hx := hwr _ (List.getElem_mem (show 8 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 19).trans hx
  · exact hBl 1
  · exact hBl 2
  · exact hBl 3
  · exact hBl 4
  · exact (hK 3).trans (List.append_nil _).symm
  · have hx := hwr _ (List.getElem_mem (show 9 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 20).trans hx
  · have hx := hwr _ (List.getElem_mem (show 10 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 21).trans hx
  · have hx := hwr _ (List.getElem_mem (show 11 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 22).trans hx
  · have hx := hwr _ (List.getElem_mem (show 12 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 23).trans hx
  · have hx := hwr _ (List.getElem_mem (show 13 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 24).trans hx
  · exact hK 4
  · exact hK 5
  · exact hK 6
  · exact hK 7
  · exact hK 8
  · exact hK 9
  · have hx := hwr _ (List.getElem_mem (show 14 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 25).trans hx
  · have hx := hwr _ (List.getElem_mem (show 15 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 26).trans hx
  · have hx := hwr _ (List.getElem_mem (show 16 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 27).trans (hx.trans ((C4Arm.reps_single _ _).trans List.replicate_append_replicate.symm))
  · exact hK 10
  · exact hBl 5
  · have hx := hwr _ (List.getElem_mem (show 17 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 28).trans hx
  · have hx := hwr _ (List.getElem_mem (show 18 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 29).trans hx
  · exact hK 11
  · exact (hArm 30).trans h30
  · have hx := hwr _ (List.getElem_mem (show 19 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 31).trans hx
  · exact hBl 6
  · have hx := hwr _ (List.getElem_mem (show 20 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 32).trans hx
  · exact hK 12
  · exact hBl 7
  · exact hK 13
  · exact hBl 8
  · exact hBl 9
  · have hx := hwr _ (List.getElem_mem (show 21 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 33).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · refine (hArm 34).trans (h34.trans ?_)
    show _ = List.replicate (8 * P.ell - (p ++ [b]).length) true ++ C4Enum.zs (p ++ [b]).length
    simp [nums]
  · have hx := hwr _ (List.getElem_mem (show 22 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 35).trans hx
  · exact hBl 10
  · have hx := hwr _ (List.getElem_mem (show 23 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 36).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 24 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 37).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 25 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 38).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 26 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 39).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 27 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 40).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 28 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 41).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 29 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 42).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 30 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 43).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 31 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 44).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · have hx := hwr _ (List.getElem_mem (show 32 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 45).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · exact hK 14
  · exact hK 15
  · have hx := hwr _ (List.getElem_mem (show 33 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 46).trans (hx.trans ((C4Arm.reps_single _ _).trans (C4Enum.binary_zero (8 + 8 * P.ell + 8 * P.kh + TWd + 1)).symm))
  · have hx := hwr _ (List.getElem_mem (show 34 < (C4Arm.armWrs (nums P TWd Cap)).length by rw [armWrs_len]; decide))
    exact (hArm 47).trans (hx.trans ((C4Arm.reps_single _ _).trans rfl))
  · exact hK 16

end ArmBank

/-! ## The unit -/

section Unit
variable (P : SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT R K : ℕ) (batch : List SeedFix.SExpr)

/-- **The enumeration's side conditions** at the child prefix `p'`: SeedFix's `sampEnum_run` hypotheses (the batch's
entries, `1 ≤ Q`, `nT ≤ 2^TWd`, the capacities, a uniform cell cost `K`, the group capacities at every valid counter
value), carried to C4.K. -/
structure EnumOk (p' : List Bool) : Prop where
  hE : SeedFix.JLink.EntsOk P.N nT R batch ents
  hQ : 1 ≤ P.Q
  hnT : nT ≤ 2 ^ TWd
  hc : SeedFix.JBody.CellOk (jX P ents TWd Cap p')
  hs : SeedFix.JEnum.SplitOk (jX P ents TWd Cap p')
  hK : ∀ j, j < nT * 2 ^ (jX P ents TWd Cap p').w →
    SeedFix.JEnum.cellCost (jX P ents TWd Cap p') j (SeedFix.JEnum.outAt (jX P ents TWd Cap p') j) ≤ K
  hg : ∀ j, j < nT * 2 ^ (jX P ents TWd Cap p').w →
    (SeedFix.SplitT.at_ (jX P ents TWd Cap p') (SeedFix.SplitT.tOf (jX P ents TWd Cap p') j)).validJ j = true →
      SeedFix.JBody.GroupOk (SeedFix.SplitT.at_ (jX P ents TWd Cap p') (SeedFix.SplitT.tOf (jX P ents TWd Cap p') j))
        j (SeedFix.JEnum.stAt (jX P ents TWd Cap p') (S0 P) j) (SeedFix.JEnum.outAt (jX P ents TWd Cap p') j)

/-- The arm, embedded in the unit. -/
noncomputable def armE (b : Bool) :=
  TapeEmbedding.machine (17 + 11) (MaskedReset.machine (C4Arm.armW b).toProg.compile (fun _ => true))

/-- The counter head to `1`. -/
def fwdP : Prog EU := .act (fun _ => none) (moveAt cntT .right)

/-- The counter head back to `0`. -/
def bwdP : Prog EU := .act (fun _ => none) (moveAt cntT .left)

/-- The heads with the counter head at `1`. -/
def h1 : Fin EU → ℕ := fun i => if i = cntT then 1 else 0

theorem fwd_step (B : Fin EU → List Bool) : Step fwdP.compile 1 (fun _ => 0) B h1 B := by
  have h := act_step (⟨fun _ => 0, B⟩ : Bank EU) (fun _ => none) (moveAt cntT .right)
  refine h.congr ?_ ?_
  · funext i
    by_cases hi : i = cntT
    · simp [Bank.act, moveAt, hi, HeadMove.apply, h1]
    · simp [Bank.act, moveAt, hi, HeadMove.apply, h1]
  · funext i
    rfl

theorem bwd_step (B : Fin EU → List Bool) : Step bwdP.compile 1 h1 B (fun _ => 0) B := by
  have h := act_step (⟨h1, B⟩ : Bank EU) (fun _ => none) (moveAt cntT .left)
  refine h.congr ?_ ?_
  · funext i
    by_cases hi : i = cntT
    · simp [Bank.act, moveAt, hi, HeadMove.apply, h1]
    · simp [Bank.act, moveAt, hi, HeadMove.apply, h1]
  · funext i
    rfl

/-- The enumeration, docked. -/
noncomputable def enumD := RecoveryFocus.machine enSl (CloseoutRowsDegreeLoop.machine SeedFix.JEnum.bodyT)

/-- **The enumeration unit** of child bit `b`. -/
noncomputable def euM (b : Bool) :=
  Composition.machine (armE b) (Composition.machine fwdP.compile (Composition.machine enumD bwdP.compile))

/-- The unit's step bound. -/
def euCost : ℕ :=
  2 * C4Arm.armCost (nums P TWd Cap) + 2 + 1 +
    (1 + 1 + (nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) * (K + 3) + 3 + 1 + 1))

theorem addCases_zero' : Fin.addCases (m := AT) (n := 17 + 11) (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0) =
    fun _ => 0 := by
  funext i
  refine Fin.addCases (motive := fun i => Fin.addCases (m := AT) (n := 17 + 11) (motive := fun _ => ℕ) (fun _ => 0)
    (fun _ => 0) i = 0) (fun k => ?_) (fun k => ?_) i <;> simp

/-- **The enumeration unit's run**: the child prefix's printed objective on OUT; the rulers, the prefix and the
constants unchanged; every head back at `0`. -/
theorem eu_step (b : Bool) (p : List Bool) (hp : p.length + 1 ≤ 8 * P.ell)
    (ok : EnumOk P ents TWd Cap nT R K batch (p ++ [b])) :
    ∃ A' : Fin EU → List Bool,
      Step (euM b) (euCost P TWd Cap nT K) (fun _ => 0) (euIn P ents TWd Cap nT p) (fun _ => 0) A' ∧
      A' (aS 24) = ListMachine.Rec.exprWord
        (SeedFix.sampTerms P nT R batch (p ++ [b]).length (SeedFix.listNum (p ++ [b]))) ∧
      (∀ d : Fin (47 + 1), d.val ≤ 10 → A' (aS d) = euIn P ents TWd Cap nT p (aS d)) ∧
      ∀ k : Fin 17, A' (kS k) = kc P ents TWd nT k := by
  -- 1: the arm
  obtain ⟨τ, c, hw, hcle, hwr, h30, h34, hlow⟩ :=
    C4Arm.armW_spec (4 * (nums P TWd Cap).mx + 20) b (nums P TWd Cap) p hp le_rfl
  obtain ⟨A1, s1, hA1⟩ := C4Pipe.wm_blank (4 * (nums P TWd Cap).mx + 20) (C4Arm.armCost (nums P TWd Cap))
    (C4Arm.armW b) (C4Arm.armSt (nums P TWd Cap) p) τ c hw (fun _ => rfl) (fun _ => rfl) rfl hcle
  have s1e := (s1.enlarge (show 2 * c + 2 ≤ 2 * C4Arm.armCost (nums P TWd Cap) + 2 by omega)).embed
    (fun _ : Fin (17 + 11) => 0) (Fin.addCases (kc P ents TWd nT) (fun _ : Fin 11 => []))
  rw [addCases_zero'] at s1e
  set B1 : Fin EU → List Bool := Fin.addCases A1 (Fin.addCases (kc P ents TWd nT) (fun _ : Fin 11 => [])) with hB1
  have hArm : ∀ d, B1 (aS d) = τ.st d := fun d => by
    simp only [hB1, aS, Fin.addCases_left]
    exact hA1 d
  have hB1k : ∀ k, B1 (kS k) = kc P ents TWd nT k := fun k => by
    simp only [hB1, kS, Fin.addCases_right, Fin.addCases_left]
  have hB1b : ∀ k, B1 (bS k) = [] := fun k => by
    simp only [hB1, bS, Fin.addCases_right]
  -- 2: the counter head to 1
  have s2 := fwd_step B1
  -- 3: the enumeration
  have hQ := ok.hQ
  have hp' : (p ++ [b]).length ≤ 8 * P.ell := by simp; omega
  have se := SeedFix.JLink.sampEnum_run (jX P ents TWd Cap (p ++ [b])) (S0 P) nT R K batch ok.hE ok.hQ ok.hnT ok.hc
    ok.hs ok.hK ok.hg
  have hA := fun j : Fin 65 =>
    (arm_bank P ents TWd Cap nT b p τ B1 hArm hB1k hB1b hwr h30 h34 j).trans
      (tin_eq P ents TWd Cap nT (p ++ [b]) hp' hQ j).symm
  have hH : ∀ j : Fin 65, h1 (enSl j) = Fin.addCases (m := 64) (n := 1) (fun _ => 0) (fun _ => 1) j := by
    intro j
    refine Fin.addCases (m := 64) (n := 1) (fun i => ?_) (fun i => ?_) j
    · rw [Fin.addCases_left]
      have hne : enSl (Fin.castAdd 1 i) ≠ cntT := fun e => by
        have := enSl_eq_cnt _ e
        have := i.isLt
        simp at *
        omega
      simp [h1, hne]
    · rw [Fin.addCases_right]
      have e : Fin.natAdd 64 i = (64 : Fin 65) := by fin_cases i; rfl
      rw [e, enSl_64]
      simp [h1]
  have s3 := se.dock enSl enSl_inj h1 B1 hH hA
  rw [dockH_existing enSl h1 _ hH] at s3
  -- 4: the counter head back to 0
  have st := s1e.seq (s2.seq (s3.seq (bwd_step _)))
  refine ⟨_, st, ?_, ?_, ?_⟩
  · refine (install_slot enSl enSl_inj B1 _ 22).trans ?_
    show StablePartition.Workspace.overlay (ListMachine.Rec.exprWord
      (SeedFix.sampTerms P nT R batch (p ++ [b]).length (SeedFix.listNum (p ++ [b])))) [] = _
    simp [StablePartition.Workspace.overlay]
  · intro d hd
    have hne : ∀ j, enSl j ≠ aS d := fun j e => by
      have h1 := enSl_ge j
      rw [e, aS_val] at h1
      split_ifs at h1 <;> omega
    rw [install_other enSl B1 _ (aS d) hne, hArm d, hlow d hd]
    simp [euIn, aS, C4Pipe.wblank, role_sTape]
  · intro k
    fin_cases k
    · exact (install_slot enSl enSl_inj B1 _ ⟨6, by decide⟩).trans ((hA ⟨6, by decide⟩).symm.trans (hB1k 0))
    · exact (install_slot enSl enSl_inj B1 _ ⟨9, by decide⟩).trans ((hA ⟨9, by decide⟩).symm.trans (hB1k 1))
    · exact (install_slot enSl enSl_inj B1 _ ⟨11, by decide⟩).trans ((hA ⟨11, by decide⟩).symm.trans (hB1k 2))
    · exact (install_slot enSl enSl_inj B1 _ ⟨17, by decide⟩).trans ((hA ⟨17, by decide⟩).symm.trans (hB1k 3))
    · exact (install_slot enSl enSl_inj B1 _ ⟨23, by decide⟩).trans ((hA ⟨23, by decide⟩).symm.trans (hB1k 4))
    · exact (install_slot enSl enSl_inj B1 _ ⟨24, by decide⟩).trans ((hA ⟨24, by decide⟩).symm.trans (hB1k 5))
    · exact (install_slot enSl enSl_inj B1 _ ⟨25, by decide⟩).trans ((hA ⟨25, by decide⟩).symm.trans (hB1k 6))
    · exact (install_slot enSl enSl_inj B1 _ ⟨26, by decide⟩).trans ((hA ⟨26, by decide⟩).symm.trans (hB1k 7))
    · exact (install_slot enSl enSl_inj B1 _ ⟨27, by decide⟩).trans ((hA ⟨27, by decide⟩).symm.trans (hB1k 8))
    · exact (install_slot enSl enSl_inj B1 _ ⟨28, by decide⟩).trans ((hA ⟨28, by decide⟩).symm.trans (hB1k 9))
    · exact (install_slot enSl enSl_inj B1 _ ⟨32, by decide⟩).trans ((hA ⟨32, by decide⟩).symm.trans (hB1k 10))
    · exact (install_slot enSl enSl_inj B1 _ ⟨36, by decide⟩).trans ((hA ⟨36, by decide⟩).symm.trans (hB1k 11))
    · exact (install_slot enSl enSl_inj B1 _ ⟨41, by decide⟩).trans ((hA ⟨41, by decide⟩).symm.trans (hB1k 12))
    · exact (install_slot enSl enSl_inj B1 _ ⟨43, by decide⟩).trans ((hA ⟨43, by decide⟩).symm.trans (hB1k 13))
    · exact (install_slot enSl enSl_inj B1 _ ⟨60, by decide⟩).trans ((hA ⟨60, by decide⟩).symm.trans (hB1k 14))
    · exact (install_slot enSl enSl_inj B1 _ ⟨61, by decide⟩).trans ((hA ⟨61, by decide⟩).symm.trans (hB1k 15))
    · exact (install_slot enSl enSl_inj B1 _ ⟨64, by decide⟩).trans ((hA ⟨64, by decide⟩).symm.trans (hB1k 16))

end Unit

end NearCubicWires.WireExponent3_5.PrimT.C4Dock
