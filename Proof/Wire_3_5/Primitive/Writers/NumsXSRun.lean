import Proof.Wire_3_5.Primitive.Writers.NumsXS
import Proof.Wire_3_5.Primitive.Writers.ShellT2

/-! # The SYM dimension stage at `m_S`, part 2: the stage and its `DimOK`

The whole dimension program: `n` from the request, phase A (the cap `B_S`), phase B (the POP term `T` into `rF`),
phase C (clears), then THR's dimension tail at `KF` (`NumsXT`: the star numbers, `m = 2·kh + L`, `m += KF·L²`), then
`m += T` and the CapReader source of `2^(m_S)`, `m_S = mOfT KF P + T`.

* `tS`, **`mS`** (the dimension), `numsWS`, **`numsWS_spec`**, `numsMS`, **`nums_stepS`**, **`dimOK_numsS`** (the stage
  meets `ShellT.DimOK` at `mS`: the SYM shell v2 `ShellS.shell_runS` runs at `2^(mS …)`).

Paper quantity of the main type: the SYM writer's dimension `2^(m_S)` (`m_S = O(Ψ_S)`, prim:runtime P3:3089-3108),
reaching the POP rows' `2^{Θ(√B·L)}` and the FILTER rows' `2^{Θ(L²)}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.NumsXS
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.NumsX
open NearCubicWires.WireExponent3_5.PrimAsm.NumsXT
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- **The POP term** `T = (3·J·(4S + 257) + 1)·(L·D₂ + K₀)`. -/
def tS (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) : ℕ :=
  (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0)

/-- **The SYM writer's dimension** `m_S = mOfT KF P + T`. -/
def mS (KF : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    (D2 K0 : ℕ) : ℕ :=
  PrimThrW.Shell2.mOfT KF P + tS P h0 h1 Cδ C D2 K0

section Vals

theorem forall32 (Q : Fin NR → Prop) (h0 : Q 0) (h1 : Q 1) (h2 : Q 2) (h3 : Q 3) (h4 : Q 4) (h5 : Q 5) (h6 : Q 6) (h7 : Q 7) (h8 : Q 8) (h9 : Q 9) (h10 : Q 10) (h11 : Q 11) (h12 : Q 12) (h13 : Q 13) (h14 : Q 14) (h15 : Q 15) (h16 : Q 16) (h17 : Q 17) (h18 : Q 18) (h19 : Q 19) (h20 : Q 20) (h21 : Q 21) (h22 : Q 22) (h23 : Q 23) (h24 : Q 24) (h25 : Q 25) (h26 : Q 26) (h27 : Q 27) (h28 : Q 28) (h29 : Q 29) (h30 : Q 30) (h31 : Q 31) : ∀ r, Q r := by
  intro r
  fin_cases r
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31

theorem pA_vals (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (σ : WState NS NR) (hn0 : σ.val (0 : Fin NR) = P.n) (hz : ∀ r : Fin NR, r ≠ 0 → σ.val r = 0) :
    (pAOut σ P h0 h1 Cδ C).val (0 : Fin NR) = P.n ∧ (pAOut σ P h0 h1 Cδ C).val (1 : Fin NR) = Nat.clog 2 (P.n + 2) ∧
    (pAOut σ P h0 h1 Cδ C).val (3 : Fin NR) = P.r ∧ (pAOut σ P h0 h1 Cδ C).val (12 : Fin NR) = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n ∧
    (pAOut σ P h0 h1 Cδ C).val (20 : Fin NR) = Ledger.rowBSparse h0 h1 2 Cδ P.n ∧ (∀ r : Fin NR, r ≠ 0 → r ≠ 1 → r ≠ 3 → r ≠ 12 → r ≠ 20 → (pAOut σ P h0 h1 Cδ C).val r = 0) := by
  have z2 : (pAOut σ P h0 h1 Cδ C).val (2 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z4 : (pAOut σ P h0 h1 Cδ C).val (4 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z5 : (pAOut σ P h0 h1 Cδ C).val (5 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z6 : (pAOut σ P h0 h1 Cδ C).val (6 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z7 : (pAOut σ P h0 h1 Cδ C).val (7 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z8 : (pAOut σ P h0 h1 Cδ C).val (8 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z9 : (pAOut σ P h0 h1 Cδ C).val (9 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z10 : (pAOut σ P h0 h1 Cδ C).val (10 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z11 : (pAOut σ P h0 h1 Cδ C).val (11 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z13 : (pAOut σ P h0 h1 Cδ C).val (13 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z14 : (pAOut σ P h0 h1 Cδ C).val (14 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z15 : (pAOut σ P h0 h1 Cδ C).val (15 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z16 : (pAOut σ P h0 h1 Cδ C).val (16 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z17 : (pAOut σ P h0 h1 Cδ C).val (17 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z18 : (pAOut σ P h0 h1 Cδ C).val (18 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z19 : (pAOut σ P h0 h1 Cδ C).val (19 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z21 : (pAOut σ P h0 h1 Cδ C).val (21 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z22 : (pAOut σ P h0 h1 Cδ C).val (22 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z23 : (pAOut σ P h0 h1 Cδ C).val (23 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z24 : (pAOut σ P h0 h1 Cδ C).val (24 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z25 : (pAOut σ P h0 h1 Cδ C).val (25 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z26 : (pAOut σ P h0 h1 Cδ C).val (26 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z27 : (pAOut σ P h0 h1 Cδ C).val (27 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z28 : (pAOut σ P h0 h1 Cδ C).val (28 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z29 : (pAOut σ P h0 h1 Cδ C).val (29 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z30 : (pAOut σ P h0 h1 Cδ C).val (30 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  have z31 : (pAOut σ P h0 h1 Cδ C).val (31 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply]
  exact ⟨by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply], by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply], by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply], by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply], by simp [Function.update_apply, Fin.ext_iff, NR, SN_val, StarNums.starOut, Gs_val, Ledger.Lq, hn0, hz, pAOut, Hc_apply],
    forall32 _ (fun h => absurd rfl h) (fun _ h => absurd rfl h) (fun _ _ _ _ _ => z2) (fun _ _ h => absurd rfl h) (fun _ _ _ _ _ => z4) (fun _ _ _ _ _ => z5) (fun _ _ _ _ _ => z6) (fun _ _ _ _ _ => z7) (fun _ _ _ _ _ => z8) (fun _ _ _ _ _ => z9) (fun _ _ _ _ _ => z10) (fun _ _ _ _ _ => z11) (fun _ _ _ h => absurd rfl h) (fun _ _ _ _ _ => z13) (fun _ _ _ _ _ => z14) (fun _ _ _ _ _ => z15) (fun _ _ _ _ _ => z16) (fun _ _ _ _ _ => z17) (fun _ _ _ _ _ => z18) (fun _ _ _ _ _ => z19) (fun _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ => z21) (fun _ _ _ _ _ => z22) (fun _ _ _ _ _ => z23) (fun _ _ _ _ _ => z24) (fun _ _ _ _ _ => z25) (fun _ _ _ _ _ => z26) (fun _ _ _ _ _ => z27) (fun _ _ _ _ _ => z28) (fun _ _ _ _ _ => z29) (fun _ _ _ _ _ => z30) (fun _ _ _ _ _ => z31)⟩

theorem pB_vals (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) (σ : WState NS NR) (h0' : σ.val (0 : Fin NR) = P.n) (h1' : σ.val (1 : Fin NR) = Nat.clog 2 (P.n + 2)) (h3' : σ.val (3 : Fin NR) = P.r) (h12' : σ.val (12 : Fin NR) = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (h20' : σ.val (20 : Fin NR) = Ledger.rowBSparse h0 h1 2 Cδ P.n) (hz : ∀ r : Fin NR, r ≠ 0 → r ≠ 1 → r ≠ 3 → r ≠ 12 → r ≠ 20 → σ.val r = 0) :
    (pBOut σ P h0 h1 Cδ C D2 K0).val (0 : Fin NR) = P.n ∧ (pBOut σ P h0 h1 Cδ C D2 K0).val (1 : Fin NR) = Nat.clog 2 (P.n + 2) ∧
    (pBOut σ P h0 h1 Cδ C D2 K0).val (3 : Fin NR) = P.r ∧ (pBOut σ P h0 h1 Cδ C D2 K0).val (4 : Fin NR) = 33554432 ∧
    (pBOut σ P h0 h1 Cδ C D2 K0).val (5 : Fin NR) = (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432 ∧ (pBOut σ P h0 h1 Cδ C D2 K0).val (10 : Fin NR) = CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432) ∧
    (pBOut σ P h0 h1 Cδ C D2 K0).val (12 : Fin NR) = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n ∧ (pBOut σ P h0 h1 Cδ C D2 K0).val (14 : Fin NR) = 3 ∧
    (pBOut σ P h0 h1 Cδ C D2 K0).val (18 : Fin NR) = (Nat.clog 2 (P.n + 2)) * D2 + K0 ∧ (pBOut σ P h0 h1 Cδ C D2 K0).val (19 : Fin NR) = D2 ∧
    (pBOut σ P h0 h1 Cδ C D2 K0).val (20 : Fin NR) = (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0) ∧ (pBOut σ P h0 h1 Cδ C D2 K0).val (21 : Fin NR) = (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192 ∧
    (pBOut σ P h0 h1 Cδ C D2 K0).val (22 : Fin NR) = 8192 ∧ (pBOut σ P h0 h1 Cδ C D2 K0).val (29 : Fin NR) = (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0) ∧
    (pBOut σ P h0 h1 Cδ C D2 K0).val (30 : Fin NR) = 2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257 ∧ (∀ r : Fin NR, r ≠ 0 → r ≠ 1 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 10 → r ≠ 12 → r ≠ 14 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 29 → r ≠ 30 → (pBOut σ P h0 h1 Cδ C D2 K0).val r = 0) := by
  have z2 : (pBOut σ P h0 h1 Cδ C D2 K0).val (2 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z6 : (pBOut σ P h0 h1 Cδ C D2 K0).val (6 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z7 : (pBOut σ P h0 h1 Cδ C D2 K0).val (7 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z8 : (pBOut σ P h0 h1 Cδ C D2 K0).val (8 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z9 : (pBOut σ P h0 h1 Cδ C D2 K0).val (9 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z11 : (pBOut σ P h0 h1 Cδ C D2 K0).val (11 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z13 : (pBOut σ P h0 h1 Cδ C D2 K0).val (13 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z15 : (pBOut σ P h0 h1 Cδ C D2 K0).val (15 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z16 : (pBOut σ P h0 h1 Cδ C D2 K0).val (16 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z17 : (pBOut σ P h0 h1 Cδ C D2 K0).val (17 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z23 : (pBOut σ P h0 h1 Cδ C D2 K0).val (23 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z24 : (pBOut σ P h0 h1 Cδ C D2 K0).val (24 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z25 : (pBOut σ P h0 h1 Cδ C D2 K0).val (25 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z26 : (pBOut σ P h0 h1 Cδ C D2 K0).val (26 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z27 : (pBOut σ P h0 h1 Cδ C D2 K0).val (27 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z28 : (pBOut σ P h0 h1 Cδ C D2 K0).val (28 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  have z31 : (pBOut σ P h0 h1 Cδ C D2 K0).val (31 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply]
  exact ⟨by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply], by simp [Function.update_apply, Fin.ext_iff, NR, pBOut, h0', h1', h3', h12', h20', hz, Qs_apply, Bl_apply],
    forall32 _ (fun h => absurd rfl h) (fun _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z2) (fun _ _ h => absurd rfl h) (fun _ _ _ h => absurd rfl h) (fun _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z6) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z7) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z8) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z9) (fun _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z11) (fun _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z13) (fun _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z15) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z16) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z17) (fun _ _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z23) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z24) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z25) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z26) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z27) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z28) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd rfl h) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => z31)⟩

theorem pC_vals (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) (σ : WState NS NR) (c0 : σ.val (0 : Fin NR) = P.n) (c20 : σ.val (20 : Fin NR) = (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0)) (hz : ∀ r : Fin NR, r ≠ 0 → r ≠ 1 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 10 → r ≠ 12 → r ≠ 14 → r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 29 → r ≠ 30 → σ.val r = 0) (c1 : σ.val (1 : Fin NR) = Nat.clog 2 (P.n + 2)) (c3 : σ.val (3 : Fin NR) = P.r) (c4 : σ.val (4 : Fin NR) = 33554432) (c5 : σ.val (5 : Fin NR) = (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432) (c10 : σ.val (10 : Fin NR) = CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432)) (c12 : σ.val (12 : Fin NR) = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) (c14 : σ.val (14 : Fin NR) = 3) (c18 : σ.val (18 : Fin NR) = (Nat.clog 2 (P.n + 2)) * D2 + K0) (c19 : σ.val (19 : Fin NR) = D2) (c21 : σ.val (21 : Fin NR) = (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) (c22 : σ.val (22 : Fin NR) = 8192) (c29 : σ.val (29 : Fin NR) = (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0)) (c30 : σ.val (30 : Fin NR) = 2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257) :
    (pCOut σ P h0 h1 Cδ C D2 K0).val (0 : Fin NR) = P.n ∧ (pCOut σ P h0 h1 Cδ C D2 K0).val (20 : Fin NR) = (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0) ∧
    (∀ r : Fin NR, r ≠ 0 → r ≠ 20 → (pCOut σ P h0 h1 Cδ C D2 K0).val r = 0) := by
  have z1 : (pCOut σ P h0 h1 Cδ C D2 K0).val (1 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z2 : (pCOut σ P h0 h1 Cδ C D2 K0).val (2 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z3 : (pCOut σ P h0 h1 Cδ C D2 K0).val (3 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z4 : (pCOut σ P h0 h1 Cδ C D2 K0).val (4 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z5 : (pCOut σ P h0 h1 Cδ C D2 K0).val (5 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z6 : (pCOut σ P h0 h1 Cδ C D2 K0).val (6 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z7 : (pCOut σ P h0 h1 Cδ C D2 K0).val (7 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z8 : (pCOut σ P h0 h1 Cδ C D2 K0).val (8 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z9 : (pCOut σ P h0 h1 Cδ C D2 K0).val (9 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z10 : (pCOut σ P h0 h1 Cδ C D2 K0).val (10 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z11 : (pCOut σ P h0 h1 Cδ C D2 K0).val (11 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z12 : (pCOut σ P h0 h1 Cδ C D2 K0).val (12 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z13 : (pCOut σ P h0 h1 Cδ C D2 K0).val (13 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z14 : (pCOut σ P h0 h1 Cδ C D2 K0).val (14 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z15 : (pCOut σ P h0 h1 Cδ C D2 K0).val (15 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z16 : (pCOut σ P h0 h1 Cδ C D2 K0).val (16 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z17 : (pCOut σ P h0 h1 Cδ C D2 K0).val (17 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z18 : (pCOut σ P h0 h1 Cδ C D2 K0).val (18 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z19 : (pCOut σ P h0 h1 Cδ C D2 K0).val (19 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z21 : (pCOut σ P h0 h1 Cδ C D2 K0).val (21 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z22 : (pCOut σ P h0 h1 Cδ C D2 K0).val (22 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z23 : (pCOut σ P h0 h1 Cδ C D2 K0).val (23 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z24 : (pCOut σ P h0 h1 Cδ C D2 K0).val (24 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z25 : (pCOut σ P h0 h1 Cδ C D2 K0).val (25 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z26 : (pCOut σ P h0 h1 Cδ C D2 K0).val (26 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z27 : (pCOut σ P h0 h1 Cδ C D2 K0).val (27 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z28 : (pCOut σ P h0 h1 Cδ C D2 K0).val (28 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z29 : (pCOut σ P h0 h1 Cδ C D2 K0).val (29 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z30 : (pCOut σ P h0 h1 Cδ C D2 K0).val (30 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  have z31 : (pCOut σ P h0 h1 Cδ C D2 K0).val (31 : Fin NR) = 0 := by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz]
  exact ⟨by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz], by simp [Function.update_apply, Fin.ext_iff, NR, pCOut, c0, c1, c3, c4, c5, c10, c12, c14, c18, c19, c20, c21, c22, c29, c30, hz],
    forall32 _ (fun h => absurd rfl h) (fun _ _ => z1) (fun _ _ => z2) (fun _ _ => z3) (fun _ _ => z4) (fun _ _ => z5) (fun _ _ => z6) (fun _ _ => z7) (fun _ _ => z8) (fun _ _ => z9) (fun _ _ => z10) (fun _ _ => z11) (fun _ _ => z12) (fun _ _ => z13) (fun _ _ => z14) (fun _ _ => z15) (fun _ _ => z16) (fun _ _ => z17) (fun _ _ => z18) (fun _ _ => z19) (fun _ h => absurd rfl h) (fun _ _ => z21) (fun _ _ => z22) (fun _ _ => z23) (fun _ _ => z24) (fun _ _ => z25) (fun _ _ => z26) (fun _ _ => z27) (fun _ _ => z28) (fun _ _ => z29) (fun _ _ => z30) (fun _ _ => z31)⟩

end Vals

/-! ## The stage -/

section Stage

theorem pAOut_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) : (pAOut σ P h0 h1 Cδ C).st = σ.st ∧ (pAOut σ P h0 h1 Cδ C).sh = σ.sh ∧
      (pAOut σ P h0 h1 Cδ C).cell = σ.cell := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pAOut, StarNums.starOut]

theorem pBOut_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (D2 K0 : ℕ) : (pBOut σ P h0 h1 Cδ C D2 K0).st = σ.st ∧
      (pBOut σ P h0 h1 Cδ C D2 K0).sh = σ.sh ∧ (pBOut σ P h0 h1 Cδ C D2 K0).cell = σ.cell := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pBOut]

theorem pCOut_st (σ : WState NS NR) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (D2 K0 : ℕ) : (pCOut σ P h0 h1 Cδ C D2 K0).st = σ.st ∧
      (pCOut σ P h0 h1 Cδ C D2 K0).sh = σ.sh ∧ (pCOut σ P h0 h1 Cδ C D2 K0).cell = σ.cell := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [pCOut]

/-- Phases A–C. -/
def phW (cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) : WM NS NR :=
  .seq (pAW cr ζ Cδ C) (.seq (pBW D2 K0) pCW)

/-- **Phases A–C, run**: from `n` in `SN 0` (every other register `0`), phase C's exit state. -/
theorem phases_run (cap cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) (σ : WState NS NR) (v10 : σ.val (SN 0) = P.n)
    (v1 : ∀ r : Fin NR, r ≠ 0 → σ.val r = 0) (hcS : (0 + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : SymDec.CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap) (hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ cap)
    (hX : ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432 + 2) * ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432 + 2) + (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432 + 10 ≤ cap) (hT : (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0) + (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) + ((Nat.clog 2 (P.n + 2)) * D2 + K0) + ((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) + (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257) + (natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) + (Nat.clog 2 (P.n + 2)) * D2 + D2 + K0 + (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192 + 8192 + 33554432 + (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (Ledger.rowBSparse h0 h1 2 Cδ P.n) + (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432)) + (Nat.clog 2 (P.n + 2)) + P.r ≤ cap) :
    WExec cap (phW cr ζ Cδ C D2 K0) σ (pCOut (pBOut (pAOut σ P h0 h1 Cδ C) P h0 h1 Cδ C D2 K0) P h0 h1 Cδ C D2 K0)
      (pACost cap P cr h0 h1 Cδ C + 1 + (pBCost cap P h0 h1 Cδ C D2 K0 + 1 + pCCost P h0 h1 Cδ C D2 K0)) := by
  obtain ⟨a0, a1, a3, a12, a20, az⟩ := pA_vals P h0 h1 Cδ C σ v10 v1
  obtain ⟨b0, b1, b3, b4, b5, b10, b12, b14, b18, b19, b20, b21, b22, b29, b30, bz⟩ :=
    pB_vals P h0 h1 Cδ C D2 K0 (pAOut σ P h0 h1 Cδ C) a0 a1 a3 a12 a20 az
  exact WExec.seq (pA_run cap cr h0 h1 Cδ C P hrP σ v10 v1 hcS hcP hcC hlam)
    (WExec.seq (pB_run cap P h0 h1 Cδ C D2 K0 _ a0 a1 a3 a12 a20 az hX hT)
      (pC_run cap P h0 h1 Cδ C D2 K0 _ b0 b1 b3 b4 b5 b10 b12 b14 b18 b19 b20 b21 b22 b29 b30 bz hX hT))

/-- THR's dimension tail at `KF`, then `m += T`, then the source. -/
def tailW (KF cr : ℕ) : WM NS NR :=
  .seq (StarNums.starNumsM cr 0 SN) (.seq mW (.seq (klW KF) (.seq (addTo rF rM rT) srcW)))

/-- The tail's cost bound. -/
def tailCost (cap : ℕ) (P : Shared.StarParams) (KF cr Tv : ℕ) : ℕ :=
  StarNums.starCost P.n cr 0 + 300 * P.n + 600 + 60 * (KF * (P.n + 2) * (P.n + 2)) + 60 * Tv +
    10 * UnaryPow.sq cap + 100

/-- **The tail, run**: from `n` in `SN 0` and `T` in `rF` (every other register `0`), the source of
`2^(mOfT KF P + T)` on the output stream, every other stream kept. -/
theorem tail_run (KF cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (Tv : ℕ)
    (σC : WState NS NR) (vC0 : σC.val (SN 0) = P.n) (vCF : σC.val rF = Tv)
    (vCz : ∀ r : Fin NR, r ≠ 0 → r ≠ 20 → σC.val r = 0) (hO : σC.st xOUT = []) (hOh : σC.sh xOUT = 0)
    (hW : 2 * P.n + cr + 16 + KF * (P.n + 2) ^ 2 ≤ W)
    (hM : 2 * (PrimThrW.Shell2.mOfT KF P + Tv) + 3 ≤ 2 * W + 2) :
    ∃ τ c, WExec (2 * W + 2) (tailW KF cr) σC τ c ∧ τ.st xOUT = srcWord (PrimThrW.Shell2.mOfT KF P + Tv) ∧
      (∀ s, s ≠ xOUT → τ.st s = σC.st s) ∧ c ≤ tailCost (2 * W + 2) P KF cr Tv := by
  set cap := 2 * W + 2 with hcap
  have hkh := kh2_le P
  have hL := clog_le P.n
  have hmo := mOf_le P
  have hsq := UnaryPow.sq_ge cap
  have hL1 : 1 ≤ Nat.clog 2 (P.n + 2) := Nat.clog_pos (by norm_num) (by omega)
  have hp2 : KF * (P.n + 2) ^ 2 = KF * (P.n + 2) * (P.n + 2) := by ring
  have hKL1 : KF ≤ KF * (P.n + 2) * (P.n + 2) := by
    have : 1 ≤ (P.n + 2) * (P.n + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc KF = KF * 1 := (mul_one _).symm
      _ ≤ KF * ((P.n + 2) * (P.n + 2)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have hLK : Nat.clog 2 (P.n + 2) * KF ≤ KF * (P.n + 2) * (P.n + 2) := by
    have h1 : Nat.clog 2 (P.n + 2) * KF ≤ (P.n + 2) * KF := Nat.mul_le_mul_right _ hL
    have h2 : (P.n + 2) * KF ≤ KF * (P.n + 2) * (P.n + 2) := by nlinarith
    omega
  have hLKL : Nat.clog 2 (P.n + 2) * KF * Nat.clog 2 (P.n + 2) ≤ KF * (P.n + 2) * (P.n + 2) := by
    have h1 : Nat.clog 2 (P.n + 2) * KF * Nat.clog 2 (P.n + 2) ≤ (P.n + 2) * KF * (P.n + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hL) hL
    have h2 : (P.n + 2) * KF * (P.n + 2) = KF * (P.n + 2) * (P.n + 2) := by ring
    omega
  have hmT0 := mOfT_eq KF P
  have hmm : PrimThrW.Shell2.mOfT KF P ≤ 2 * P.n + 2 + KF * (P.n + 2) * (P.n + 2) := by
    rw [← hmT0]
    have : (0 + Nat.clog 2 (P.n + 2) * KF) * Nat.clog 2 (P.n + 2) =
      Nat.clog 2 (P.n + 2) * KF * Nat.clog 2 (P.n + 2) := by ring
    omega
  have hTle : Tv ≤ cap := by omega
  -- 1: the star numbers
  have r2 := StarNums.starNums_spec cap cr 0 SN P hrP σC vC0
    (fun i hi => vCz _ (fun e => hi (SN.injective (e.trans (rfl : (0 : Fin NR) = SN 0)))) (SN_ne i _ (by decide)))
    (by omega)
  set σ2 := StarNums.starOut σC SN P 0 with hσ2
  obtain ⟨o1, -, -, -, -, -, o8, -, -⟩ := StarNums.starOut_val σC SN P 0
  have hi20 : ∀ r : Fin NR, 20 ≤ r.val → σ2.val r = σC.val r := fun r hr => by rw [hσ2, starOut_hi _ _ _ _ hr]
  -- 2: `m`
  have r3 := mW_spec cap σ2 (P.s * (P.r / 2)) (Nat.clog 2 (P.n + 2)) o8 o1
    (by rw [hi20 _ (by decide)]; exact vCz _ (by decide) (by decide))
    (by rw [hi20 _ (by decide)]; exact vCz _ (by decide) (by decide)) (by omega)
  set σ3 := σ2.setv rM (2 * (P.s * (P.r / 2)) + Nat.clog 2 (P.n + 2)) with hσ3
  have v3 : ∀ r : Fin NR, 20 ≤ r.val → r ≠ rM → σ3.val r = σC.val r := by
    intro r hr hrm
    rw [hσ3]
    simp only [WState.setv_val, Function.update_apply, if_neg hrm]
    exact hi20 r hr
  have o1' : σ3.val (SN 1) = Nat.clog 2 (P.n + 2) := by
    rw [hσ3, WState.setv_val, Function.update_of_ne (SN_ne 1 rM (by decide))]; exact o1
  have o3m : σ3.val rM = mOf P := by rw [hσ3, WState.setv_val, Function.update_self]; rfl
  have z3 : ∀ r : Fin NR, 21 ≤ r.val → r ≠ rM → σ3.val r = 0 := fun r hr hrm => by
    rw [v3 r (by omega) hrm]
    exact vCz r (fun e => by subst e; exact absurd hr (by decide)) (fun e => by subst e; exact absurd hr (by decide))
  -- 3: `m += (L·KF)·L`
  set Lv := Nat.clog 2 (P.n + 2) with hLd
  have hn0 : (0 + Lv * KF) * Lv = Lv * KF * Lv := by ring
  have ka := SparseNum.copy1 cap (SN 1) rA rT (by decide) (by decide) (by decide) Lv σ3 o1'
    (z3 rA (by decide) (by decide)) (z3 rT (by decide) (by decide)) (by omega)
  obtain ⟨σa, hσa⟩ : ∃ y, y = σ3.setv rA Lv := ⟨_, rfl⟩
  rw [← hσa] at ka
  have va : ∀ r : Fin NR, r ≠ rA → σa.val r = σ3.val r := fun r h => by
    rw [hσa, WState.setv_val, Function.update_of_ne h]
  have kb := SparseNum.incN0 cap rQ KF σa (by rw [va _ (by decide)]; exact z3 rQ (by decide) (by decide)) (by omega)
  obtain ⟨σb, hσb⟩ : ∃ y, y = σa.setv rQ KF := ⟨_, rfl⟩
  rw [← hσb] at kb
  have vb : ∀ r : Fin NR, r ≠ rQ → σb.val r = σa.val r := fun r h => by
    rw [hσb, WState.setv_val, Function.update_of_ne h]
  have kc := SparseNum.mulAdd1 cap mLK Lv KF 0 σb
    (show σb.val (SN 1) = Lv by rw [vb _ (by decide), va _ (by decide)]; exact o1')
    (show σb.val rQ = KF by rw [hσb, WState.setv_val, Function.update_self])
    (show σb.val rB = 0 by rw [vb _ (by decide), va _ (by decide)]; exact z3 rB (by decide) (by decide))
    (show σb.val rX = 0 by rw [vb _ (by decide), va _ (by decide)]; exact z3 rX (by decide) (by decide))
    (show σb.val rY = 0 by rw [vb _ (by decide), va _ (by decide)]; exact z3 rY (by decide) (by decide))
    (by omega) (by omega) (by omega)
  obtain ⟨σc, hσc⟩ : ∃ y, y = σb.setv rB (0 + Lv * KF) := ⟨_, rfl⟩
  have kc' : WExec cap (mulAddW mLK) σb σc (UnaryPow.sq cap) := by rw [hσc]; exact kc
  have vc : ∀ r : Fin NR, r ≠ rB → σc.val r = σb.val r := fun r h => by
    rw [hσc, WState.setv_val, Function.update_of_ne h]
  have kd := SparseNum.mulAdd1 cap mML (0 + Lv * KF) Lv (mOf P) σc
    (show σc.val rB = 0 + Lv * KF by rw [hσc, WState.setv_val, Function.update_self])
    (show σc.val rA = Lv by rw [vc _ (by decide), vb _ (by decide), hσa, WState.setv_val, Function.update_self])
    (show σc.val rM = mOf P by rw [vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact o3m)
    (show σc.val rX = 0 by rw [vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact z3 rX (by decide) (by decide))
    (show σc.val rY = 0 by rw [vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact z3 rY (by decide) (by decide))
    (by omega) (by omega) (by omega)
  obtain ⟨σd, hσd⟩ : ∃ y, y = σc.setv rM (mOf P + (0 + Lv * KF) * Lv) := ⟨_, rfl⟩
  have kd' : WExec cap (mulAddW mML) σc σd (UnaryPow.sq cap) := by rw [hσd]; exact kd
  have vd : ∀ r : Fin NR, r ≠ rM → σd.val r = σc.val r := fun r h => by
    rw [hσd, WState.setv_val, Function.update_of_ne h]
  have hmT : mOf P + (0 + Lv * KF) * Lv = PrimThrW.Shell2.mOfT KF P := mOfT_eq KF P
  -- 4: `m += T`
  have ke := CapNum.add1 cap rF rM rT (by decide) (by decide) (by decide) Tv (PrimThrW.Shell2.mOfT KF P) σd
    (by rw [vd _ (by decide), vc _ (by decide), vb _ (by decide), va _ (by decide), v3 _ (by decide) (by decide)]; exact vCF)
    (by rw [hσd, WState.setv_val, Function.update_self]; exact hmT)
    (by rw [vd _ (by decide), vc _ (by decide), vb _ (by decide), va _ (by decide)]; exact z3 rT (by decide) (by decide))
    hTle (by omega)
  obtain ⟨σe, hσe⟩ : ∃ y, y = σd.setv rM (PrimThrW.Shell2.mOfT KF P + Tv) := ⟨_, rfl⟩
  rw [← hσe] at ke
  have ve : ∀ r : Fin NR, r ≠ rM → σe.val r = σd.val r := fun r h => by
    rw [hσe, WState.setv_val, Function.update_of_ne h]
  have ez : ∀ r : Fin NR, 21 ≤ r.val → r ≠ rM → r ≠ rA → r ≠ rQ → r ≠ rB → σe.val r = 0 := by
    intro r h1 h2 h3 h4 h5
    rw [ve _ h2, vd _ h2, vc _ h5, vb _ h4, va _ h3]
    exact z3 r h1 h2
  -- 5: the source
  have hst : σe.st = σC.st := by rw [hσe, hσd, hσc, hσb, hσa]; simp [hσ3, hσ2, StarNums.starOut]
  have hsh : σe.sh = σC.sh := by rw [hσe, hσd, hσc, hσb, hσa]; simp [hσ3, hσ2, StarNums.starOut]
  have r4 := srcW_spec cap σe (PrimThrW.Shell2.mOfT KF P + Tv)
    (by rw [hσe, WState.setv_val, Function.update_self])
    (ez rK (by decide) (by decide) (by decide) (by decide) (by decide))
    (ez rT (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hst]; exact hO) (by rw [hsh]; exact hOh)
    (ez rOP (by decide) (by decide) (by decide) (by decide) (by decide)) (by omega)
  refine ⟨_, _, WExec.seq r2 (WExec.seq r3 (WExec.seq (WExec.seq ka (WExec.seq kb (WExec.seq kc' kd')))
    (WExec.seq ke r4))), ?_, ?_, ?_⟩
  · simp [appendO, hst, hO]
  · intro s hs
    simp [appendO, hst, Function.update_apply, hs]
  · unfold tailCost
    have e1 : 18 * (P.s * (P.r / 2)) + 3 + 1 + (18 * (P.s * (P.r / 2)) + 3 + 1 + (18 * Nat.clog 2 (P.n + 2) + 3)) ≤
        18 * P.n + 18 * (P.n + 2) + 11 := by omega
    have hs1 := UnaryPow.lin_le_sq cap
    unfold StarNums.starCost
    omega

end Stage

/-! ## The whole program and the stage -/

section Whole

/-- **The SYM dimension program**: `n`, phases A–C (`T` into `rF`), THR's tail at `KF`, `m += T`, the source. -/
def numsWS (KF cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) : WM NS NR :=
  .seq (readNatM true xIN rF rC (SN 0) rP rT) (.seq (phW cr ζ Cδ C D2 K0) (tailW KF cr))

/-- **The stage's capacity needs** at the fill count `W` (capacity `2W + 2`). -/
structure SNeed (W : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (D2 K0 KF cr : ℕ) : Prop where
  hW : 2 * P.n + cr + 16 + KF * (P.n + 2) ^ 2 ≤ W
  hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ 2 * W + 2
  hcC : SymDec.CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) (2 * W + 2)
  hlam : Ledger.rowBLambda h0 h1 2 P.n ≤ 2 * W + 2
  hX : ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432 + 2) * ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432 + 2) + (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432 + 10 ≤ 2 * W + 2
  hT : (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) * ((Nat.clog 2 (P.n + 2)) * D2 + K0) + (((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) * 3 + 1) + ((Nat.clog 2 (P.n + 2)) * D2 + K0) + ((natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) * (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257)) + (2 * (2 * (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432))) + 257) + (natBitLength ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192) + 9) + (Nat.clog 2 (P.n + 2)) * D2 + D2 + K0 + (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 8192 + 8192 + 33554432 + (Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (Ledger.rowBSparse h0 h1 2 Cδ P.n) + (CanonicalFourfoldRowProgram.natCeilSqrt ((Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * 33554432)) + (Nat.clog 2 (P.n + 2)) + P.r ≤ 2 * W + 2
  hM : 2 * mS KF P h0 h1 Cδ C D2 K0 + 3 ≤ 2 * W + 2

/-- The stage's cost bound. -/
def numsCostS (cap : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (D2 K0 KF cr : ℕ) : ℕ :=
  (natBitLength P.n + 2) * (40 * 2 ^ natBitLength P.n + 40) + 1 + (pACost cap P cr h0 h1 Cδ C + 1 +
    (pBCost cap P h0 h1 Cδ C D2 K0 + 1 + pCCost P h0 h1 Cδ C D2 K0) + 1 + tailCost cap P KF cr (tS P h0 h1 Cδ C D2 K0))

/-- **The SYM dimension program's run**: from the filled state, the output stream holds the source of
`2^(mS …)`; the request and the fill count stay. -/
theorem numsWS_spec (KF cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hN : SNeed W P h0 h1 Cδ C D2 K0 KF cr) :
    ∃ σF c, WExec (2 * W + 2) (numsWS KF cr ζ Cδ C D2 K0) (σN w W) σF c ∧
      σF.st xOUT = srcWord (mS KF P h0 h1 Cδ C D2 K0) ∧ σF.st xIN = RepairOrdinary.frame w ∧
      σF.st xCT = List.replicate W true ∧ c ≤ numsCostS (2 * W + 2) P h0 h1 Cδ C D2 K0 KF cr := by
  have hW := hN.hW
  have hpow := CopyNat.two_pow_natBitLength_le P.n
  -- 1: `n` into `SN 0`
  have r1 := readNatM_spec (2 * W + 2) true xIN rF rC (SN 0) rP rT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) P.n [] (marks sfx ++ [false]) (σN w W)
    (by simp only [σN, if_pos rfl]; rw [hw]; exact frame_split _ _) (by rfl) rfl rfl rfl rfl
    (by simp only [σN]; rw [pow_succ]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = ((σN w W).seth xIN (([] : List Bool).length +
      stp true * (RepairRepresentation.natWord P.n).length)).setv (SN 0) ((σN w W).val (SN 0) + P.n) := ⟨_, rfl⟩
  rw [← hσ1] at r1
  have v1 : ∀ r : Fin NR, r ≠ 0 → σ1.val r = 0 := by
    intro r hr
    have : r ≠ SN 0 := hr
    rw [hσ1]; simp [Function.update_apply, this, σN]
  have v10 : σ1.val (SN 0) = P.n := by rw [hσ1]; simp [σN]
  have s1 : σ1.st = (σN w W).st := by rw [hσ1]; rfl
  have sh1O : σ1.sh xOUT = 0 := by rw [hσ1]; simp [σN, xOUT, xIN]
  -- 2: phases A–C
  have eP := phases_run (2 * W + 2) cr P hrP h0 h1 Cδ C D2 K0 σ1 v10 v1 (by omega) hN.hcP hN.hcC hN.hlam hN.hX hN.hT
  obtain ⟨σA, hσA⟩ : ∃ y, y = pAOut σ1 P h0 h1 Cδ C := ⟨_, rfl⟩
  obtain ⟨σB, hσB⟩ : ∃ y, y = pBOut σA P h0 h1 Cδ C D2 K0 := ⟨_, rfl⟩
  obtain ⟨σC, hσC⟩ : ∃ y, y = pCOut σB P h0 h1 Cδ C D2 K0 := ⟨_, rfl⟩
  rw [← hσA, ← hσB, ← hσC] at eP
  obtain ⟨a0, a1, a3, a12, a20, az⟩ := pA_vals P h0 h1 Cδ C σ1 v10 v1
  rw [← hσA] at a0 a1 a3 a12 a20 az
  obtain ⟨b0, b1, b3, b4, b5, b10, b12, b14, b18, b19, b20, b21, b22, b29, b30, bz⟩ :=
    pB_vals P h0 h1 Cδ C D2 K0 σA a0 a1 a3 a12 a20 az
  rw [← hσB] at b0 b1 b3 b4 b5 b10 b12 b14 b18 b19 b20 b21 b22 b29 b30 bz
  obtain ⟨c0, c20, cz⟩ := pC_vals P h0 h1 Cδ C D2 K0 σB b0 b20 bz b1 b3 b4 b5 b10 b12 b14 b18 b19 b21 b22 b29 b30
  rw [← hσC] at c0 c20 cz
  have stC : σC.st = σ1.st := by
    rw [hσC, (pCOut_st _ P h0 h1 Cδ C D2 K0).1, hσB, (pBOut_st _ P h0 h1 Cδ C D2 K0).1, hσA,
      (pAOut_st σ1 P h0 h1 Cδ C).1]
  have shC : σC.sh = σ1.sh := by
    rw [hσC, (pCOut_st _ P h0 h1 Cδ C D2 K0).2.1, hσB, (pBOut_st _ P h0 h1 Cδ C D2 K0).2.1, hσA,
      (pAOut_st σ1 P h0 h1 Cδ C).2.1]
  -- 3: the tail
  obtain ⟨τ, c, eT, tO, tK, tc⟩ := tail_run KF cr W P hrP (tS P h0 h1 Cδ C D2 K0) σC c0 c20 cz
    (by rw [stC, s1]; simp [σN, xOUT, xIN, xCT, xAUX]) (by rw [shC]; exact sh1O) hW hN.hM
  refine ⟨τ, _, WExec.seq r1 (WExec.seq eP eT), tO, ?_, ?_, ?_⟩
  · rw [tK _ (by decide), stC, s1]; simp [σN]
  · rw [tK _ (by decide), stC, s1]; simp [σN, xCT, xIN]
  · unfold numsCostS; omega

/-- The stage before its teardown: the fill, then the program. -/
noncomputable def numsPS (KF cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) :=
  Composition.machine fillX.compile (numsWS KF cr ζ Cδ C D2 K0).toProg.compile

/-- **The SYM dimension stage** (every head back at `0`). -/
noncomputable def numsMS (KF cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) :=
  MaskedReset.machine (numsPS KF cr ζ Cδ C D2 K0) (fun _ => true)

/-- The stage's cost before the teardown. -/
def numsStageCostS (W : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (D2 K0 KF cr : ℕ) : ℕ :=
  11 * W + 20 + 1 + 1 + 1 + numsCostS (2 * W + 2) P h0 h1 Cδ C D2 K0 KF cr

/-- **The SYM dimension stage's run**: from `frame w` (`w = natWord n ++ sfx`) and `1^W`, every head back at `0`, the
output stream holds the CapReader source `srcWord (mS …)`; the request and the fill count stay. -/
theorem nums_stepS (KF cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (D2 K0 : ℕ) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hN : SNeed W P h0 h1 Cδ C D2 K0 KF cr) :
    ∃ (tout : Fin (NS + 2 + NR) → List Bool) (m : ℕ),
      Step (numsMS KF cr ζ Cδ C D2 K0) (2 * numsStageCostS W P h0 h1 Cδ C D2 K0 KF cr + 2) (fun _ => 0)
        (Fin.addCases (rawInX w W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape xOUT) = srcWord (mS KF P h0 h1 Cδ C D2 K0) ∧ tout (sTape xIN) = RepairOrdinary.frame w ∧
      tout (sTape xCT) = List.replicate W true := by
  have s0 := Exec.step (fillX_exec w W)
  obtain ⟨σF, c, hx, o, i, ct, hc⟩ := numsWS_spec KF cr W P hrP h0 h1 Cδ C D2 K0 sfx w hw hN
  have s1 := Exec.step (WExec.exec (2 * W + 2) hx)
  have core : Step (numsPS KF cr ζ Cδ C D2 K0) (numsStageCostS W P h0 h1 Cδ C D2 K0 KF cr) (fun _ => 0) (rawInX w W)
      (wenc (2 * W + 2) σF).H (wenc (2 * W + 2) σF).A := (s0.seq s1).enlarge (by unfold numsStageCostS; omega)
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc (2 * W + 2) σF).H i)
      (fun _ : Fin 1 => 0) : Fin (NS + 2 + NR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc (2 * W + 2) σF).A, m, (hm.congr_in eh rfl).congr eh' rfl, ?_, ?_, ?_⟩
  · rw [wenc_A_s, o]
  · rw [wenc_A_s, i]
  · rw [wenc_A_s, ct]

end Whole

section Dim
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.ShellT
variable {x D D2 Dv DL : ℕ}

/-- **The SYM dimension stage meets `DimOK`** at `mS …` (ShellX's `x2_step` with `nums_stepS`): the SYM shell v2
(`ShellS.shell_runS`) runs at `2^(m_S)`. -/
theorem dimOK_numsS (KF cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (D2' K0 : ℕ) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (W : ℕ) (hN : SNeed W P h0 h1 Cδ C D2' K0 KF cr) :
    DimOK x D D2 Dv DL (numsMS KF cr ζ Cδ C D2' K0) (2 * numsStageCostS W P h0 h1 Cδ C D2' K0 KF cr + 2)
      (mS KF P h0 h1 Cδ C D2' K0) w W := by
  intro B hB0 hct hb
  obtain ⟨tout, m, h, o, i, -⟩ := nums_stepS KF cr W P hrP h0 h1 Cδ C D2' K0 sfx w hw hN
  have hJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hH : ∀ j, HI (q2 x D D2 Dv DL j) = 0 := by
    intro j
    apply HI_ne
    apply ne_TJ
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;>
      rw [e, hJ]
    · rw [T0_val]; omega
    · rw [TW_val]; omega
    · have := nu_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j; omega
  have hA : ∀ j, B (q2 x D D2 Dv DL j) =
      Fin.addCases (NumsX.rawInX w W) (fun _ : Fin 1 => List.replicate 0 false) j := by
    intro j
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨h1', e⟩ | ⟨h1', h2', e⟩ | ⟨h1', h2', e⟩ <;>
      rw [e]
    · subst h1'
      rw [hB0]
      simp [iN, NumsX.rawInX]
    · subst h2'
      rw [hct]
      simp [cN, NumsX.rawInX, NumsX.xIN, NumsX.xCT, NumsX.sTape_eq_iffX]
    · rw [hb j]
      revert h1' h2'
      refine Fin.addCases (fun t => ?_) (fun u => ?_) j
      · intro h1' h2'
        have t1 : t ≠ sTape NumsX.xIN := fun e => h1' (by rw [e]; rfl)
        have t2 : t ≠ sTape NumsX.xCT := fun e => h2' (by rw [e]; rfl)
        simp [NumsX.rawInX, t1, t2]
      · intro _ _
        simp
  have d := dock0 h (q2 x D D2 Dv DL) q2_inj HI B hH hA
  refine ⟨_, d, ?_, ?_⟩
  · simp only [oN, Fin.addCases_left]
    exact o
  · simp only [iN, Fin.addCases_left]
    exact i

end Dim

end NearCubicWires.WireExponent3_5.PrimAsm.NumsXS
