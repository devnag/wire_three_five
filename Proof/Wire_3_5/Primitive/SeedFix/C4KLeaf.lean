import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.C4Front
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K, the consumer of the per-mode contract: `c4Leaf_of`

"There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact printer calls. Under the
displayed allowances the printer applies, and the explicit descriptions and their construction give the middle term in
`prim:runtime`" (P3:3170-3173). The C4 part's four stages each run within `c₄·seedClasses E₄` at the ledger's
`(n, kOf n, psiOf n)`: the front (`C4Front.front_req`, `70·|req.word| + 64` steps, the word polynomial in `n` by
`CallSize.wordBound_poly`) and the three modes' stages (`C4K.SymLeafC4`, `ThrLeafC4`, `HashLeafC4`). C4.K combines
them: `E₄` is the componentwise maximum of the modes' floors and the front's (`Asel` at the word's degree), `CD₄` the
maximum of the modes' load floors, `c₄` the sum of the coefficients; a stage's run stays a run under a larger budget
(`stage3Run_mono`) and the budget grows with `E` and `c` at `n ≥ 1` (`seedClasses_mono`; every call is on-star).

* `emax`, `classLE_trans`, `le_emax_left/right`, **`seedClasses_mono`**, **`seedBudget_mono`**, **`stage3Run_mono`**;
* `frontE`, `frontC`, **`front_budget`**;
* **`c4Leaf_of : SymLeafC4 l → ThrLeafC4 l → HashLeafC4 l → C4Leaf l`**.

Paper quantity of the main type: the C4 part `C4Leaf` (the fixed seeds within `c₄·seedClasses E₄`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4K
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes

/-! ## The floors -/

section Budget
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The seed budget grows with the envelope and the coefficient** at `n ≥ 1`. -/
theorem seedBudget_mono {E E' : Envelope} (hE : ClassLE E E') {c c' : ℕ} (hc : c ≤ c') (n : ℕ) (hn : 1 ≤ n) :
    seedBudget l F E c kclk coef A a ha n ≤ seedBudget l F E' c' kclk coef A a ha n :=
  Nat.mul_le_mul hc (seedClasses_mono hE _ _ _ hn)

end Budget

/-! ## The front's budget -/

/-- **The front's steps are within its budget** at every call. -/
theorem front_budget (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (E : Envelope)
    (hE : ClassLE frontE E) (c : ℕ) (hc : frontC ≤ c) (req : PrimRequest)
    (h : (callInputs l F kclk coef A a ha).Call req) :
    70 * req.word.length + 64 ≤ seedBudget l F E c kclk coef A a ha req.n := by
  have hn : 1 ≤ req.n := SeedFix.starAt_pos _ h.2.2.2.2.2.1
  have hw := PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha req h
  have hp := word_le req.n
  have h1 : (req.n + 1) ^ wD ≤ 2 ^ wD * req.n ^ wD := by
    rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h2 : 1 ≤ req.n ^ wD := Nat.one_le_pow _ _ (by omega)
  have h3 : 70 * req.word.length + 64 ≤ frontC * req.n ^ wD := by
    unfold frontC
    have : 70 * req.word.length ≤ 70 * wC * 2 ^ wD * req.n ^ wD := by
      calc 70 * req.word.length ≤ 70 * (wC * (2 ^ wD * req.n ^ wD)) :=
            Nat.mul_le_mul_left _ (hw.trans (hp.trans (Nat.mul_le_mul_left _ h1)))
        _ = 70 * wC * 2 ^ wD * req.n ^ wD := by ring
    nlinarith
  have h4 : frontC * req.n ^ wD ≤ seedBudget l F frontE frontC kclk coef A a ha req.n := by
    unfold seedBudget seedClasses
    apply Nat.mul_le_mul_left
    have : req.n ^ wD ≤ classBound frontE .selection req.n (((gate0 l F).budget kclk coef A a ha).kOf req.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf req.n) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  exact h3.trans (h4.trans (seedBudget_mono l F kclk coef A a ha hE hc req.n hn))

/-! ## The assembly -/

/-- **The C4 part from the three modes' stages** (C4.K): the front is `C4Front.frontS`; `E₄` is the componentwise
maximum of the floors, `CD₄` the maximum, `c₄` the sum of the coefficients. -/
noncomputable def c4Leaf_of (l : Literals) (hS : SymLeafC4 l) (hT : ThrLeafC4 l) (hH : HashLeafC4 l) : C4Leaf l := by
  intro fe
  obtain ⟨ES, CS, fS⟩ := hS fe
  obtain ⟨ET, CT, fT⟩ := hT fe
  obtain ⟨EH, CH, fH⟩ := hH fe
  refine ⟨emax (emax ES ET) (emax EH frontE), max (max CS CT) CH, fun F hfe hE hCD => ?_⟩
  have eS : ClassLE ES F.E := classLE_trans (classLE_trans (le_emax_left _ _) (le_emax_left _ _)) hE
  have eT : ClassLE ET F.E := classLE_trans (classLE_trans (le_emax_right _ _) (le_emax_left _ _)) hE
  have eH : ClassLE EH F.E := classLE_trans (classLE_trans (le_emax_left _ _) (le_emax_right _ _)) hE
  obtain ⟨cS, gS⟩ := fS F hfe eS (by omega)
  obtain ⟨cT, gT⟩ := fT F hfe eT (by omega)
  obtain ⟨cH, gH⟩ := fH F hfe eH (by omega)
  refine ⟨cS + cT + cH + frontC, fun kclk coef A a ha => ?_⟩
  obtain ⟨SS, rS⟩ := gS kclk coef A a ha
  obtain ⟨ST, rT⟩ := gT kclk coef A a ha
  obtain ⟨SH, rH⟩ := gH kclk coef A a ha
  have e4S : ClassLE ES (emax (emax ES ET) (emax EH frontE)) :=
    classLE_trans (le_emax_left _ _) (le_emax_left _ _)
  have e4T : ClassLE ET (emax (emax ES ET) (emax EH frontE)) :=
    classLE_trans (le_emax_right _ _) (le_emax_left _ _)
  have e4H : ClassLE EH (emax (emax ES ET) (emax EH frontE)) :=
    classLE_trans (le_emax_left _ _) (le_emax_right _ _)
  have e4F : ClassLE frontE (emax (emax ES ET) (emax EH frontE)) :=
    classLE_trans (le_emax_right _ _) (le_emax_right _ _)
  exact
    { front := C4Front.frontS
      front_run := fun req hc => C4Front.front_req req _
        (front_budget l F kclk coef A a ha _ e4F _ (by omega) req hc)
      sym := SS
      sym_run := fun n a' ha' Cs carriers translation hc hs =>
        stage3Run_mono (rS n a' ha' Cs carriers translation hc hs)
          (seedBudget_mono l F kclk coef A a ha e4S (by omega) n (SeedFix.starAt_pos _ hs))
      hash := SH
      hash_run := fun n a' ha' Cs carriers translation hc hs =>
        stage3Run_mono (rH n a' ha' Cs carriers translation hc hs)
          (seedBudget_mono l F kclk coef A a ha e4H (by omega) n (SeedFix.starAt_pos _ hs))
      thr := ST
      thr_run := fun n a' ha' Cs carriers translation hc hs =>
        stage3Run_mono (rT n a' ha' Cs carriers translation hc hs)
          (seedBudget_mono l F kclk coef A a ha e4T (by omega) n (SeedFix.starAt_pos _ hs)) }

end NearCubicWires.WireExponent3_5.PrimT.C4K

end
