import Proof.Wire_3_5.Primitive.Writers.HashCall
import Proof.Wire_3_5.Primitive.Writers.ShellH

/-! # (HASH (d1)): the HASH writer's run at one call, with the budgets as hypotheses

The HASH writer is ShellH's shell (`shellMGH`: the v3 data stage, the HASH dimension stage `NumsXH.numsMH KL KH cr`,
the loop) with PA's unit machine `CellUnit.unitM W (hdecW W FS cr)` (the HASH unit decode with the aux FILTER bank).

* `costH` (the budget `2·shellCostG + 2` at the HASH dimension stage, the per-unit budget capped at the scrub `R`),
  `costH_eq` (= THR v2's `costT` plus the aux terms), `KcH`, **`costH_le`** (the budget is
  `Kc(|w|+n+cc+2)^Ec + Kc(2^m+1)^Ec + b·(2nU + 2R + 10)`, `Ec = EcT`);
* **`hash_ready`**: at a THR call (`w = (thrReq …).word`), from the numeric budget hypotheses (the capacity `cap`, the
  unit budget `nU`, the FILTER pipeline's bound `BP` at every aux seed and cell, the scrub `R = C(2^m+1)^D` at
  `m = mOfH KL KH P`, the loop's length `b ≥ nHash·5`), the writer's run within `Bud` prints the HASH tape
  `hashTape` (`shell_runH` + `unitOK_of_dec` + `hash_dec` + `hash_units` + `dimOK_numsH`).

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226), written within
the budget `Bud`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline

/-! ## The budget -/

/-- **The HASH shell's budget**: `2·shellCostG + 2` at the HASH dimension stage, the unit budget capped at `R`. -/
def costH (D C D2 C2 Dv Cv cr DL CL KL KH : ℕ) (lw n cc nU m : ℕ) : ℕ :=
  2 * shellCostG (List.replicate lw false) n D C D2 C2 cc Dv Cv
    (2 * NumsXH.numsStageCostH n cr KL KH (UnaryCalc.value Dv Cv n) + 2) m DL CL
    (min nU (UnaryCalc.value D C (2 ^ m))) + 2

theorem costH_eq (D C D2 C2 Dv Cv cr DL CL KL KH : ℕ) (lw n cc nU m : ℕ) :
    costH D C D2 C2 Dv Cv cr DL CL KL KH lw n cc nU m = costT D C D2 C2 Dv Cv cr DL CL KL lw n cc nU m +
      2 * (120 * (KH * (n + 2) * (n + 2) * (n + 2)) + 16 * UnaryPow.sq (2 * UnaryCalc.value Dv Cv n + 2)) := by
  unfold costH costT shellCostG bootXCostG NumsXH.numsStageCostH NumsXH.numsCostH NumsXT.numsStageCostT
  ring

/-- The HASH budget's coefficient. -/
def KcH (D C D2 C2 Dv Cv cr DL CL KL KH : ℕ) : ℕ :=
  KcT D C D2 C2 Dv Cv cr DL CL KL + 1920 * KH + 6400 * ((2 * Cv + 4) * (2 * Cv + 4))

/-- **The HASH budget's bound**: polynomial in the request side and in the dimension `2^m`, plus the loop. -/
theorem costH_le (D C D2 C2 Dv Cv cr DL CL KL KH : ℕ) (lw n cc nU m : ℕ) :
    costH D C D2 C2 Dv Cv cr DL CL KL KH lw n cc nU m ≤
      KcH D C D2 C2 Dv Cv cr DL CL KL KH * (lw + n + cc + 2) ^ EcT D D2 Dv DL +
      KcH D C D2 C2 Dv Cv cr DL CL KL KH * (2 ^ m + 1) ^ EcT D D2 Dv DL +
      UnaryCalc.value DL CL (2 ^ m) * (2 * nU + 2 * UnaryCalc.value D C (2 ^ m) + 10) := by
  rw [costH_eq]
  have hT := costT_le D C D2 C2 Dv Cv cr DL CL KL lw n cc nU m
  obtain ⟨E, hE⟩ : ∃ e, e = EcT D D2 Dv DL := ⟨_, rfl⟩
  have hE4 : D + D2 + 3 * Dv + DL + 4 = E := by rw [hE]; rfl
  rw [← hE] at hT ⊢
  obtain ⟨PX, hPX⟩ : ∃ p, p = (lw + n + cc + 2) ^ E := ⟨_, rfl⟩
  obtain ⟨PY, hPY⟩ : ∃ p, p = (2 ^ m + 1) ^ E := ⟨_, rfl⟩
  rw [← hPX, ← hPY] at hT ⊢
  have hX1 : 1 ≤ lw + n + cc + 2 := by omega
  have pw : ∀ d, d ≤ E → (n + 1) ^ d ≤ PX := fun d hd => by
    rw [hPX]; exact le_trans (Nat.pow_le_pow_left (by omega) d) (Nat.pow_le_pow_right hX1 hd)
  have fK : 240 * (KH * (n + 2) * (n + 2) * (n + 2)) ≤ 1920 * KH * PX := by
    have h1 : (n + 2) * (n + 2) * (n + 2) ≤ 8 * ((n + 1) ^ 3) := by
      have : (n + 1) ^ 3 = (n + 1) * (n + 1) * (n + 1) := by ring
      rw [this]; nlinarith
    have h2 := pw 3 (by omega)
    have h3 : KH * (n + 2) * (n + 2) * (n + 2) = KH * ((n + 2) * (n + 2) * (n + 2)) := by ring
    rw [h3]
    have h4 : KH * ((n + 2) * (n + 2) * (n + 2)) ≤ KH * (8 * PX) :=
      Nat.mul_le_mul_left _ (le_trans h1 (by omega))
    have h5 : 1920 * KH * PX = 240 * (KH * (8 * PX)) := by ring
    omega
  have fS : 32 * UnaryPow.sq (2 * UnaryCalc.value Dv Cv n + 2) ≤ 6400 * ((2 * Cv + 4) * (2 * Cv + 4)) * PX := by
    have h1 : 2 * UnaryCalc.value Dv Cv n + 2 + 2 ≤ (2 * Cv + 4) * (n + 1) ^ Dv := by
      have p1 : 1 ≤ (n + 1) ^ Dv := Nat.one_le_pow _ _ (by omega)
      unfold UnaryCalc.value
      have : (2 * Cv + 4) * (n + 1) ^ Dv = 2 * (Cv * (n + 1) ^ Dv) + 4 * (n + 1) ^ Dv := by ring
      omega
    have h2 := Nat.mul_le_mul h1 h1
    have h3 : (2 * Cv + 4) * (n + 1) ^ Dv * ((2 * Cv + 4) * (n + 1) ^ Dv) =
        (2 * Cv + 4) * (2 * Cv + 4) * (n + 1) ^ (Dv + Dv) := by rw [pow_add]; ring
    have h4 := Nat.mul_le_mul_left ((2 * Cv + 4) * (2 * Cv + 4)) (pw (Dv + Dv) (by omega))
    unfold UnaryPow.sq
    have h5 : 32 * (200 * (2 * UnaryCalc.value Dv Cv n + 2 + 2) * (2 * UnaryCalc.value Dv Cv n + 2 + 2)) =
        6400 * ((2 * UnaryCalc.value Dv Cv n + 2 + 2) * (2 * UnaryCalc.value Dv Cv n + 2 + 2)) := by ring
    have h6 : 6400 * ((2 * Cv + 4) * (2 * Cv + 4)) * PX = 6400 * ((2 * Cv + 4) * (2 * Cv + 4) * PX) := by ring
    rw [h5, h6]
    exact Nat.mul_le_mul_left _ (le_trans h2 (by rw [h3]; exact h4))
  have eK1 : KcH D C D2 C2 Dv Cv cr DL CL KL KH * PX =
      KcT D C D2 C2 Dv Cv cr DL CL KL * PX + 1920 * KH * PX + 6400 * ((2 * Cv + 4) * (2 * Cv + 4)) * PX := by
    unfold KcH; ring
  have eK2 : KcH D C D2 C2 Dv Cv cr DL CL KL KH * PY =
      KcT D C D2 C2 Dv Cv cr DL CL KL * PY + 1920 * KH * PY + 6400 * ((2 * Cv + 4) * (2 * Cv + 4)) * PY := by
    unfold KcH; ring
  have hsplit : 2 * (120 * (KH * (n + 2) * (n + 2) * (n + 2)) + 16 * UnaryPow.sq (2 * UnaryCalc.value Dv Cv n + 2)) =
      240 * (KH * (n + 2) * (n + 2) * (n + 2)) + 32 * UnaryPow.sq (2 * UnaryCalc.value Dv Cv n + 2) := by ring
  have z1 : 0 ≤ 1920 * KH * PY := Nat.zero_le _
  rw [hsplit, eK1, eK2]
  omega

/-! ## The units -/

section Units
open NearCubicWires.WireExponent3_5.Filters

/-- **Every HASH unit meets the loop's contract** (generic in the aux parameters `Pa`, the numbers `hsl`, the slice
lengths `xs`, `tg`, the pool size `pool` and the loop's length `Lp`): `hash_dec` then `unitOK_of_dec`. -/
theorem hash_unitOK (cap : ℕ) (W : PrimT.WalkBank.WalkBankProducer) (FS : FiltSetup.FiltSetupSpec5 W) (cr : ℕ)
    (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w : List Bool) (codes cc : List ℕ) (tl : List Bool)
    (hw : w = Data.reqW P.n true codes cc tl) (hsl xs : List ℕ) (tg : ℕ) (hhs : hsl.length = 16)
    (hxs : xs.length ≤ 2) (h0v : hsl.getD 0 0 = xs.length) (Pa : GapParams) (hPl : Pa.len = 2 * xs.sum)
    (hPc : Pa.cap = (xs.length + 1) * 4096 * hsl.getD 1 0) (hPe : Pa.errExp = hsl.getD 13 0) (hPc1 : 1 ≤ Pa.cap)
    (pool : ℕ) (hpool : 2 * xs.sum + hsl.getD 8 0 = pool) (nU Bf BP Lp : ℕ)
    (hc1 : 2 * w.length + 2 ≤ cap) (hc2 : 2 ^ (natBitLength P.n + 1) ≤ cap) (hc3 : 4 * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcl : ∀ v ∈ hsl ++ (xs ++ [tg]), v ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap)
    (hcD1 : Pa.errExp + Pa.len + Pa.cap + (xs.length + 1) * 4096 + hsl.getD 1 0 + 10 ≤ cap)
    (hcG1 : Pa.cap * 32 + 2 ≤ cap) (hcG2 : Pa.len + 8 ≤ cap) (hcG3 : Pa.errExp + 4 ≤ cap)
    (hcG4 : 2 ^ (Pa.seedBits + 1) ≤ cap) (hcG5 : Pa.labelBits + Pa.fieldBits + Pa.walkLen + 512 ≤ cap)
    (hcD3 : pool + 2 ^ Pa.seedBits + 2 ^ (2 * (P.s * (P.r / 2)) + 1) +
      2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 10 ≤ cap)
    (hcJ : 4 * Lp + 2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 2 ^ Pa.seedBits + 30 ≤ cap)
    (hFc : SymDec.hbCost cap + FS.bound cap ≤ Bf)
    (hFN : ∀ q ≤ Lp, FS.need Pa.len Pa.cap Pa.errExp Pa.len (2 * (2 * (q / Fintype.card (GapSeed Pa)))) pool 0
          (Fintype.card (GapSeed Pa)) ≤ cap ∧
        FiltPipe.filtPipeBound Pa (SymDec.hseed Pa q) Pa.len (2 * (2 * (q / Fintype.card (GapSeed Pa)))) pool 0
          (FiltSetup.rulerW Pa) (FiltSetup.rulerW Pa) ≤ BP)
    (hnU : CellLoopD.cpCost (Data.unaryList (hsl ++ (xs ++ [tg]))).length + 1 +
      (SymDec.hNCost P.n w.length cr cap + 1 + (Bf + 12) + 1 + (BP + 4) + 1 + (3 * Lp + 3)) ≤ nU) :
    ∀ j < Lp, ∀ out : List Bool, PrimThrW.Shell.UnitOK cap W.x (CellUnit.unitM W (SymDec.hdecW W FS cr)) nU w
      (Data.unaryList (hsl ++ (xs ++ [tg])))
      (SymDec.unitE (2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5) 1 0 (SymDec.hrq Pa pool)) j out := by
  intro j hj out
  have hcl' : ∀ k, (hsl ++ (xs ++ [tg])).getD k 0 ≤ cap := by
    intro k
    by_cases hk : k < (hsl ++ (xs ++ [tg])).length
    · rw [List.getD_eq_getElem _ _ hk]
      exact hcl _ (List.getElem_mem hk)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _
  have hcD1' : hsl.getD 13 0 + 2 * xs.sum + (xs.length + 1) * 4096 * hsl.getD 1 0 + (xs.length + 1) * 4096 +
      hsl.getD 1 0 + 10 ≤ cap := by
    rw [← hPe, ← hPc, ← hPl]
    omega
  have hcD3' : 2 * xs.sum + hsl.getD 8 0 + 2 ^ Pa.seedBits + 2 ^ (2 * (P.s * (P.r / 2)) + 1) +
      2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 10 ≤ cap := by
    rw [hpool]; exact hcD3
  have hq : j / 5 ≤ Lp := le_trans (Nat.div_le_self _ _) hj.le
  obtain ⟨hF1, hF2⟩ := hFN (j / 5) hq
  rw [← hpool] at hF1 hF2
  have a1 : j / 5 / 2 ^ Pa.seedBits ≤ j := le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)
  have hLc : 4 * Lp ≤ cap :=
    le_trans (le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) hcJ
  have hj4 : j ≤ 4 * Lp := by omega
  have hc4 : 4 * (j / 5 / 2 ^ Pa.seedBits) ≤ cap := le_trans (Nat.mul_le_mul_left 4 (le_trans a1 hj.le)) hLc
  have hcI : j + 2 ^ Pa.seedBits * 2 ^ (2 * (P.s * (P.r / 2))) * 5 + 2 ^ Pa.seedBits + 30 ≤ cap :=
    le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hj4 _) _) _) hcJ
  obtain ⟨σD, m, hd, hok, d0, d2, d2h, mle⟩ := SymDec.hash_dec cap W FS cr P hrP w out j codes cc tl hw hsl xs tg
    hhs hxs h0v Pa hPl hPc hPe hPc1 hc1 hc2 (by omega) hcl' hcs hcD1' hcG1 hcG2 hcG3 hcG4 hcG5 hcD3' hcI hc4 Bf BP
    hFc ⟨hF1, hF2⟩
  rw [hpool] at hok
  exact PrimThrW.Shell.unitOK_of_dec cap W (SymDec.hdecW W FS cr) nU _ _ _ j out
    ⟨σD, m, BP, hd, hok, d0, d2, d2h, by omega⟩

end Units

/-! ## The run at one call -/

section Ready
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface NearCubicWires.WireExponent3_5.PrimAsm.Records
open NearCubicWires.WireExponent3_5.PrimAsm.HashFlat NearCubicWires.WireExponent3_5.PrimAsm.HashCall

end Ready

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
