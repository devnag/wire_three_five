import Proof.Wire_3_5.FinalPass.SeamsProgBase

/-! # PA2: the S5 sub-seam — the front's two halves and how they compose to `FrontOut`

The final pass's front phase (S5, `PlanFP.FpPhases.front`) runs from `fpEntry` (the framed input `fpIn` on tape `0`,
every other tape blank) to a bank meeting the `Seams.FrontOut` at `Seams.frontWords`. It is
split in two machines run in sequence, each on its own tapes of one common layout:

1. **the THR half** (**`S5Thr`**) runs FIRST. It writes the THR slots `8 … 15` of `frontWords` (for a SYM
   request, or off the star hypotheses, they stay `[]`), uses only its scratch tapes `thrSc` (register tapes of
   the layout), leaves them blank of length at most `len r ≤ Kc·(|fpIn|+1)^{Dc} + 1`, keeps every other tape, and
   returns every head to `0`.
2. **the core half** (**`S5Core`**) runs SECOND, from the THR half's exit (`ThrExit`): the input on tape `0`, the
   THR slots written, its own slots and scratch blank, the THR scratch blank of length `≤ Kc·(|fpIn|+1)^{Dc} + 1`. It
   writes S4's slots `0 … 7` (`s4Core`) and the SYM slots `16 …` (`E3`'s words and numbers), the numbers `Num = 0`,
   `Den = fpDen` in `W`-bit binary on `tN`, `tD` (`W` its choice, `ptCount·vmax < 2^W`; for a THR request it reads
   `|𝒢|` and the primes from the THR slots `15`, `13`), and blanks every other tape to exactly S4's register length
   (`Kc·(|fpIn|+1)^{Dc} + 1` on register tapes, `0` elsewhere): `FrontOut` at `frontWords`.

* **`S5Lay`**: the layout (S4's `t`, `wd`, `tN`, `tD`, `reg`, `Kc`, `Dc`; the halves' scratch sets), with the facts the
  halves need: tape `0` is a register tape (a machine cannot shrink a tape, and `FrontOut.blank` asks for exact
  lengths), the scratch tapes are register tapes off the word and number tapes, the two scratch sets disjoint;
* **`S5Thr L`** (the half), **`ThrExit`** (its exit, the core's entry), **`S5Core L`** (the half).

Paper quantity of the main types: the front's words `Seams.frontWords` (S4's words and the per-point evaluators'
call words, P3:3046-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch

section Family
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (E3 : SymPtEval)

/-- The THR slots `8 … 15` of `frontWords`. -/
def thrSlot {nw : ℕ} (k : Fin (17 + nw)) : Prop := 8 ≤ k.val ∧ k.val < 16

/-- **The front's layout** (S4's `SeedsProg` layout, plus the halves' scratch sets). -/
structure S5Lay (nw : ℕ) where
  t : ℕ
  ht : 1 ≤ t
  wd : Fin (17 + nw) → Fin t
  tN : Fin t
  tD : Fin t
  reg : Fin t → Bool
  Kc : ℕ
  Dc : ℕ
  thrSc : Fin t → Bool
  coreSc : Fin t → Bool
  wdInj : Function.Injective wd
  hND : tN ≠ tD
  wdN : ∀ k, wd k ≠ tN
  wdD : ∀ k, wd k ≠ tD
  in0 : ∀ k, (wd k).val ≠ 0
  inN : tN.val ≠ 0
  inD : tD.val ≠ 0
  reg0 : reg ⟨0, ht⟩ = true
  thrReg : ∀ j, thrSc j = true → reg j = true
  coreReg : ∀ j, coreSc j = true → reg j = true
  thrOff : ∀ j, thrSc j = true → j.val ≠ 0 ∧ (∀ k, j ≠ wd k) ∧ j ≠ tN ∧ j ≠ tD
  coreOff : ∀ j, coreSc j = true → j.val ≠ 0 ∧ (∀ k, j ≠ wd k) ∧ j ≠ tN ∧ j ≠ tD
  disj : ∀ j, thrSc j = true → coreSc j = false

end Family

end NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
