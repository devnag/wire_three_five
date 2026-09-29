import Proof.Wire_3_5.UnionMachine.EwBin

/-! # C6, e/W_j, part 5: the eight binary words

From the width `wd` (register `36`), `M` (`0`), `J` (`4`) and `8KA` (`37`) in unary registers, X1's binary writer
(`BinW.binW`) writes the eight width-`wd` words of the `e` computation on blank streams: `Mw = M` (`1`),
`Jw = J` (`2`), `Cw = 8KA` (`3`), `P = C = Q = 1` (`4`, `5`, `8`), `S = X = 0` (`6`, `7`); register `37` cleared
(**`e2_spec`**, exact final state).

Paper quantity: none (the operands of `e = ⌈log₂(8K·A(M + J·M^{2t}) + 1)⌉ + 1`, `Primitive.listE`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ)

/-- The binary writer's registers around a value register `g` (width `36`, scratch `42 … 47`). -/
def rgOf (g : Fin 48) : Fin 8 → Fin 48 := ![g, 36, 42, 43, 44, 45, 46, 47]

theorem rg_zero (g : Fin 48) (τ : WState 8 48) (h42 : τ.val 42 = 0) (h43 : τ.val 43 = 0) (h44 : τ.val 44 = 0)
    (h45 : τ.val 45 = 0) (h46 : τ.val 46 = 0) (h47 : τ.val 47 = 0) : ∀ j : Fin 8, 2 ≤ j.val → τ.val (rgOf g j) = 0 := by
  intro j hj
  fin_cases j <;> simp_all [rgOf]

/-- A width-`w` word. -/
def fw (w v : ℕ) : List Bool := frame (binary w v)

/-- **The eight words.** -/
def e2W : WM 8 48 :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq
    (BinW.binW 1 (rgOf 0)) (BinW.binW 2 (rgOf 4))) (BinW.binW 3 (rgOf 37))) (WM.clear 37)) (BinW.binW 6 (rgOf 7)))
    (BinW.binW 7 (rgOf 7))) (.inc 7)) (BinW.binW 4 (rgOf 7))) (BinW.binW 5 (rgOf 7))) (BinW.binW 8 (rgOf 7))) (.dec 7)

/-- The words' state. -/
def wordsSt (σ : WState 8 48) (wd M J c8 : ℕ) : WState 8 48 :=
  ((((((((σ.sets 1 (fw wd M)).sets 2 (fw wd J)).sets 3 (fw wd c8)).setv 37 0).sets 6 (fw wd 0)).sets 7 (fw wd 0)).sets 4
    (fw wd 1)).sets 5 (fw wd 1)).sets 8 (fw wd 1)

theorem e2_spec (σ : WState 8 48) (M J c8 wd : ℕ) (hM : σ.val 0 = M) (hJ : σ.val 4 = J) (h36 : σ.val 36 = wd)
    (h37 : σ.val 37 = c8) (z7 : σ.val 7 = 0) (z42 : σ.val 42 = 0) (z43 : σ.val 43 = 0) (z44 : σ.val 44 = 0)
    (z45 : σ.val 45 = 0) (z46 : σ.val 46 = 0) (z47 : σ.val 47 = 0)
    (hs : ∀ i : Fin 9, i ≠ 0 → σ.st i = [] ∧ σ.sh i = 0) (hcap : M + J + c8 + 2 * wd + 4 ≤ cap) :
    WExec cap e2W σ (wordsSt σ wd M J c8) (600 * (M + J + c8 + wd + 2) * (M + J + c8 + wd + 2)) := by
  have b1 := (hs 1 (by decide)).1
  have e1 := (hs 1 (by decide)).2
  have b2 := (hs 2 (by decide)).1
  have e2 := (hs 2 (by decide)).2
  have b3 := (hs 3 (by decide)).1
  have e3 := (hs 3 (by decide)).2
  have b4 := (hs 4 (by decide)).1
  have e4 := (hs 4 (by decide)).2
  have b5 := (hs 5 (by decide)).1
  have e5 := (hs 5 (by decide)).2
  have b6 := (hs 6 (by decide)).1
  have e6 := (hs 6 (by decide)).2
  have b7 := (hs 7 (by decide)).1
  have e7 := (hs 7 (by decide)).2
  have b8 := (hs 8 (by decide)).1
  have e8 := (hs 8 (by decide)).2
  have c1 := BinW.binW_spec cap 1 (rgOf 0) (by decide) σ M wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega)
  have c2 := WExec.seq c1 (BinW.binW_spec cap 2 (rgOf 4) (by decide) _ J wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega))
  have c3 := WExec.seq c2 (BinW.binW_spec cap 3 (rgOf 37) (by decide) _ c8 wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega))
  have c4 := WExec.seq c3 (wclear_spec cap 37 c8 _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]; omega))
  have c5 := WExec.seq c4 (BinW.binW_spec cap 6 (rgOf 7) (by decide) _ 0 wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega))
  have c6 := WExec.seq c5 (BinW.binW_spec cap 7 (rgOf 7) (by decide) _ 0 wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega))
  have c7 := WExec.seq c6 (WExec.inc (cap := cap) 7 _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]; omega))
  have c8' := WExec.seq c7 (BinW.binW_spec cap 4 (rgOf 7) (by decide) _ 1 wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega))
  have c9 := WExec.seq c8' (BinW.binW_spec cap 5 (rgOf 7) (by decide) _ 1 wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega))
  have c10 := WExec.seq c9 (BinW.binW_spec cap 8 (rgOf 7) (by decide) _ 1 wd (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])
    (rg_zero _ _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8])) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]) (by omega))
  have c11 := WExec.seq c10 (WExec.dec (cap := cap) 7 _ (by simp [Function.update_apply, rgOf, hM, hJ, h36, h37, z7, z42, z43, z44, z45, z46, z47, b1, b2, b3, b4, b5, b6, b7, b8, e1, e2, e3, e4, e5, e6, e7, e8]; omega))
  refine WExec.cast cap c11 ?_ ?_
  · clear c1 c2 c3 c4 c5 c6 c7 c8' c9 c10 c11
    unfold wordsSt
    apply WState.eq
    · simp
    · simp [fw]
    · funext r
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · simp
  · unfold BinW.binCost
    obtain ⟨Y, hY⟩ : ∃ Y, Y = M + J + c8 + wd + 2 := ⟨_, rfl⟩
    rw [← hY]
    have q1 : (M + 1) * (wd + 1) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
    have q2 : (J + 1) * (wd + 1) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
    have q3 : (c8 + 1) * (wd + 1) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
    have q4 : (0 + 1) * (wd + 1) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
    have q5 : (1 + 1) * (wd + 1) ≤ Y * Y := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

end NearCubicWires.WireExponent3_5.UnionMachine.EwWords
