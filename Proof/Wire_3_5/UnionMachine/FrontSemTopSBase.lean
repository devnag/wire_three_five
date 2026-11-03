import Proof.Wire_3_5.UnionMachine.FrontSemEnvSBase

/-! # C6 front, the semantic core (20): the machine's parameters at the pinned setup (P3:3669-3691)

The front's fixed parameters at `SUE`, each from a polynomial bound in the width: the thresholds' numerators and
denominators (`aVS`, `bVS`, `aTS`, `bTS`, and `c0S` their sum), the master bound `MSS := MS c0S`, the data bound
`KbS (q+1)^{DbS} ≥ BK (MSS q)` (**`KbS_spec`**), the width `KwS (q+1)^{DwS} ≥ Wreq q` (**`KwS_spec`**: every width
requirement of `PathCaps`, `EndCaps` and `NumsCaps`), the fold's exponents (`DeS`, `CeS`, `tS`, `DtS`, `CtS`), C1's
input-size degree `dS`.

Paper quantity: none (the front's time, fixed polynomials of the width). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (PQ)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2 (BK PW)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (CN EW)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound (eT)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold (eMt)

/-- A nonnegative rational's numerator as a natural number. -/
def numN (r : ℚ) : ℕ := r.num.toNat

theorem num_div_den (r : ℚ) (hr : 0 ≤ r) : r = (numN r : ℚ) / r.den := by
  have h1 : (0 : ℤ) ≤ r.num := Rat.num_nonneg.mpr hr
  have h2 : ((numN r : ℕ) : ℤ) = r.num := by unfold numN; exact Int.toNat_of_nonneg h1
  have h3 : ((numN r : ℕ) : ℚ) = (r.num : ℚ) := by exact_mod_cast h2
  rw [h3]
  exact (Rat.num_div_den r).symm

section SUE





end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS
