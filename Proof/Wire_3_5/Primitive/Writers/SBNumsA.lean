import Proof.Wire_3_5.Primitive.Writers.NumsXT2
import Proof.Wire_3_5.Primitive.Writers.SymQM
import Proof.Wire_3_5.Primitive.Writers.PopSetupNums

/-! # SB, part 12: S4's small numbers, phase A (the star numbers, the sparse count, the mode's cap)

The registers of S4's small numbers (`s4Small2`, P3:3170-3181) on `112` registers (`NRB`): from `n` in `16` and the
request's mode bit in `60`, the star numbers (`StarNums`, registers `16 … 35`: `L, r, s, b, r/2, n−rb, s·r/2, k, fe·L`),
the sparse count (`SparseNum`, `36 … 59`) and the mode's cap `B_m(n)` (`CapNum.capM` on `HH`, into `69`):

* `SS`, `GG`, `HH`; `aW`, `aOut`, `aCost`, **`a_run`**, **`a_vals`**.

Paper quantity of the main type: the call's star parameters and the filter's cap `B_m` (P3:1188-1189, 3425-3430). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires.WireExponent3_5.PrimAsm.CapNum

/-- The register file of S4's small numbers. -/
abbrev NRB : ℕ := 112

def SS : Fin 20 ↪ Fin NRB := ⟨fun i => ⟨i.val + 16, by have := i.isLt; unfold NRB; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
@[simp] theorem SS_val (i : Fin 20) : (SS i).val = i.val + 16 := rfl

def GG : Fin 24 ↪ Fin NRB := ⟨fun i => ⟨i.val + 36, by have := i.isLt; unfold NRB; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
@[simp] theorem GG_val (i : Fin 24) : (GG i).val = i.val + 36 := rfl

def HH : Fin 32 ↪ Fin NRB := ⟨![(16 : Fin NRB), (19 : Fin NRB), (48 : Fin NRB), (17 : Fin NRB), (60 : Fin NRB), (61 : Fin NRB), (62 : Fin NRB), (63 : Fin NRB), (64 : Fin NRB), (65 : Fin NRB), (66 : Fin NRB), (67 : Fin NRB), (68 : Fin NRB), (69 : Fin NRB), (70 : Fin NRB), (71 : Fin NRB), (72 : Fin NRB), (73 : Fin NRB), (74 : Fin NRB), (75 : Fin NRB), (76 : Fin NRB), (77 : Fin NRB), (78 : Fin NRB), (79 : Fin NRB), (80 : Fin NRB), (81 : Fin NRB), (82 : Fin NRB), (83 : Fin NRB), (84 : Fin NRB), (85 : Fin NRB), (86 : Fin NRB), (87 : Fin NRB)], by decide⟩
@[simp] theorem HH_apply (i : Fin 32) : HH i = ![(16 : Fin NRB), (19 : Fin NRB), (48 : Fin NRB), (17 : Fin NRB), (60 : Fin NRB), (61 : Fin NRB), (62 : Fin NRB), (63 : Fin NRB), (64 : Fin NRB), (65 : Fin NRB), (66 : Fin NRB), (67 : Fin NRB), (68 : Fin NRB), (69 : Fin NRB), (70 : Fin NRB), (71 : Fin NRB), (72 : Fin NRB), (73 : Fin NRB), (74 : Fin NRB), (75 : Fin NRB), (76 : Fin NRB), (77 : Fin NRB), (78 : Fin NRB), (79 : Fin NRB), (80 : Fin NRB), (81 : Fin NRB), (82 : Fin NRB), (83 : Fin NRB), (84 : Fin NRB), (85 : Fin NRB), (86 : Fin NRB), (87 : Fin NRB)] i := rfl

section Run
variable {ns : ℕ} (cap : ℕ)

/-- **Phase A**: the star numbers, the sparse count, the mode's cap. -/
def aW (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM ns NRB :=
  .seq (StarNums.starNumsM cr fe SS) (.seq (FinalPass.Hash4.wcopyR ((17 : Fin NRB)) ((36 : Fin NRB)) ((18 : Fin NRB))) (.seq (SparseNum.sparseM ζ Cδ GG) (.seq (WM.clear ((36 : Fin NRB))) (.seq (WM.clear ((47 : Fin NRB))) (.seq (CapNum.capM C HH) (WM.clear ((48 : Fin NRB))))))))

/-- Phase A's exit state. -/
def aOut (σ : WState ns NRB) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) : WState ns NRB :=
  (((((((((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0))).setv (((47 : Fin NRB))) (0))).setv (HH 13) (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n))).setv (((48 : Fin NRB))) (0))

/-- Phase A's cost. -/
def aCost (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (cr : ℕ) : ℕ :=
  StarNums.starCost P.n cr fe + 1 + ((UnaryPow.sq cap) + 1 + (((Ledger.rowBt h0 h1 P.n + 5) * (40 * UnaryPow.sq cap)) + 1 + ((3 * (Nat.clog 2 (P.n + 2)) + 1) + 1 + ((3 * (Ledger.rowBLambda h0 h1 2 P.n) + 1) + 1 + ((((cap + 2) * 200 + 1500) * UnaryPow.sq cap) + 1 + ((3 * (Ledger.rowBSparse h0 h1 2 Cδ P.n) + 1)))))))

theorem a_run (cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ)
    (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (σ : WState ns NRB) (hn : σ.val ((16 : Fin NRB)) = P.n)
    (hm : decide (σ.val ((60 : Fin NRB)) ≠ 0) = Codec.modeBit m)
    (hz : ∀ r : Fin NRB, r ≠ 16 → r ≠ 60 → r ≠ 88 → r ≠ 89 → r ≠ 90 → σ.val r = 0)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : SymDec.CapNeed C m P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap) (hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ cap) :
    WExec cap (aW cr fe ζ Cδ C) σ (aOut σ P h0 h1 Cδ C m fe) (aCost cap P h0 h1 Cδ C m fe cr) := by
  have hq := hcC.hq
  have hr := hcC.hr
  have hs := hcC.hs
  have hL1 := hcC.hL1
  have hL1' : Nat.clog 2 (P.n + 2) ≤ cap := hL1
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have hc1 := hcC.hc1
  have s0 := StarNums.starNums_spec cap cr fe SS P hrP σ hn
    (fun i hi => by
      have hi' : i.val ≠ 0 := fun e => hi (Fin.ext e)
      have hlt := i.isLt
      have v16 : ((16 : Fin NRB)).val = 16 := rfl
      have v60 : ((60 : Fin NRB)).val = 60 := rfl
      have v88 : ((88 : Fin NRB)).val = 88 := rfl
      have v89 : ((89 : Fin NRB)).val = 89 := rfl
      have v90 : ((90 : Fin NRB)).val = 90 := rfl
      exact hz _ (fun e => by have := congrArg Fin.val e; rw [SS_val, v16] at this; omega)
        (fun e => by have := congrArg Fin.val e; rw [SS_val, v60] at this; omega)
        (fun e => by have := congrArg Fin.val e; rw [SS_val, v88] at this; omega)
        (fun e => by have := congrArg Fin.val e; rw [SS_val, v89] at this; omega)
        (fun e => by have := congrArg Fin.val e; rw [SS_val, v90] at this; omega)) hcS
  have a0 : WExec cap (FinalPass.Hash4.wcopyR ((17 : Fin NRB)) ((36 : Fin NRB)) ((18 : Fin NRB))) (StarNums.starOut σ SS P fe) (((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2))) (UnaryPow.sq cap) :=
    SparseNum.copy1 cap ((17 : Fin NRB)) ((36 : Fin NRB)) ((18 : Fin NRB)) (by decide) (by decide) (by decide) (Nat.clog 2 (P.n + 2)) _ (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]) (by omega)
  have a1 : WExec cap (SparseNum.sparseM ζ Cδ GG) (((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2))) (((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n)) ((Ledger.rowBt h0 h1 P.n + 5) * (40 * UnaryPow.sq cap)) :=
    SparseNum.sparse_spec cap h0 h1 Cδ GG _ P.n (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]) (fun i hi => by fin_cases i <;> simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz] at hi ⊢) hcP
  have a2 : WExec cap (WM.clear ((36 : Fin NRB))) (((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n)) (((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0)) (3 * (Nat.clog 2 (P.n + 2)) + 1) :=
    wclear_spec cap ((36 : Fin NRB)) (Nat.clog 2 (P.n + 2)) _ (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]; omega)
  have a3 : WExec cap (WM.clear ((47 : Fin NRB))) (((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0)) (((((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0))).setv (((47 : Fin NRB))) (0)) (3 * (Ledger.rowBLambda h0 h1 2 P.n) + 1) :=
    wclear_spec cap ((47 : Fin NRB)) (Ledger.rowBLambda h0 h1 2 P.n) _ (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]; omega)
  have a4 : WExec cap (CapNum.capM C HH) (((((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0))).setv (((47 : Fin NRB))) (0)) (((((((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0))).setv (((47 : Fin NRB))) (0))).setv (HH 13) (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)) (((cap + 2) * 200 + 1500) * UnaryPow.sq cap) :=
    CapNum.capM_spec cap C m HH _ P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz, HH_apply]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz, HH_apply]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz, HH_apply]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz, HH_apply]) (by simpa [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz, HH_apply] using hm) (fun i hi => by fin_cases i <;> simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz, HH_apply] at hi ⊢) hcC.hc1 hcC.hr hcC.hs hcC.hq hcC.hL1 hcC.h48 hcC.h32 hcC.h64 hcC.h4832 hcC.hrsq hcC.hC hcC.hnum hcC.hLK hcC.hsum hcC.hroot1 hcC.h3 hcC.h3q hcC.hCe hcC.hE hcC.hroot2
  have a5 : WExec cap (WM.clear ((48 : Fin NRB))) (((((((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0))).setv (((47 : Fin NRB))) (0))).setv (HH 13) (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)) (((((((((((((((StarNums.starOut σ SS P fe)).setv (((36 : Fin NRB))) (Nat.clog 2 (P.n + 2)))).setv (GG 11) (Ledger.rowBLambda h0 h1 2 P.n))).setv (GG 12) (Ledger.rowBSparse h0 h1 2 Cδ P.n))).setv (((36 : Fin NRB))) (0))).setv (((47 : Fin NRB))) (0))).setv (HH 13) (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n))).setv (((48 : Fin NRB))) (0)) (3 * (Ledger.rowBSparse h0 h1 2 Cδ P.n) + 1) :=
    wclear_spec cap ((48 : Fin NRB)) (Ledger.rowBSparse h0 h1 2 Cδ P.n) _ (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]) (by simp [Function.update_apply, Fin.ext_iff, NRB, SS_val, GG_val, StarNums.starOut, Ledger.Lq, hn, hz]; omega)
  unfold aW aOut aCost
  exact WExec.seq s0 (WExec.seq a0 (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 (WExec.seq a4 a5)))))

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.SBNums
