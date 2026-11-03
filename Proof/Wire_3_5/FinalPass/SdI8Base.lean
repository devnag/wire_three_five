import Proof.Wire_3_5.FinalPass.SdI7

/-! # S4 (the seeds phase), part 57: the run's cost in the seeds phase's shape (P3:3170-3178)

**`cost_gen`**: at a star call with the sizes below `X`, S4's run's step count
`prep + 1 + Bud + 1 + (bodyA + slCost)` is within `seedsShape |E| tab (|E|·2^{dRow}·2^{dR}·Q) pt ov` whenever
`10⁵·X³ ≤ tab`, `23000·X⁴ ≤ pt` and the prep, the writer and the body's fixed steps fit `ov`. The family's constants
(`cXf`, `KcF`/`DcF`, `CtF`/`DtF`, `CpF`/`DpF`, `CoF`/`DoF`) and their bounds against `s5Bound` (`s5_ge`).

Paper quantity of the main type: the seeds phase's running time `|E|·tab + (|centers|·|E|·Q)·pt + ov`
(P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL)
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

theorem ul_ofFn {m : ℕ} (f : Fin m → ℕ) : (PrimAsm.Data.unaryList (List.ofFn f)).length = (∑ i, f i) + m := by
  rw [ThrPt.unaryList_length, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp, Finset.sum_add_distrib]

/-- **The run's cost in the seeds phase's shape.** -/
theorem cost_gen (P : StarParams) (carriers : List (Carrier P.n)) (FP : GapParams) (X : ℕ)
    (H : AtomsX P carriers FP X) (cap nn Bud Q nEv Vm T tabV ptV ovV : ℕ) (hQ : 1 ≤ Q) (hnE : nEv ≤ X)
    (hV : Vm ≤ X) (hT : T ≤ X) (htab : 100000 * (X * X * X) ≤ tabV) (hpt : 23000 * (X * X * X * X) ≤ ptV)
    (hov : 10000 * (X * X) + 1 + Bud + 1 + (bodyA cap nn + 1) ≤ ovV) :
    prepCost (Seams.s4Small2 P carriers FP) + 1 + Bud + 1 + (bodyA cap nn +
      slCost FP P carriers Q P.s P.b (P.r / 2) (P.n - P.r * P.b) nEv Vm T
        (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length (esOf FP)) ≤
      Seams.seedsShape (Fintype.card (GapSeed FP)) tabV (Fintype.card (GapSeed FP) * (2 ^ dRow P * 2 ^ dR P * Q)) ptV
        ovV := by
  obtain ⟨e0, es, hes⟩ := esOf_cons FP
  have hsl := slCost_le FP P carriers Q P.s P.b (P.r / 2) (P.n - P.r * P.b) nEv Vm T
    (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length e0 hQ (esOf FP)
  rw [esOf_length] at hsl
  have h1 := Nat.mul_le_mul_left (Fintype.card (GapSeed FP))
    ((tabB_X P carriers FP X H e0).trans htab)
  have h2 := Nat.mul_le_mul_left (Fintype.card (GapSeed FP) * (2 ^ dRow P * 2 ^ dR P * Q))
    ((ptB_X P carriers FP X H nEv Vm T hnE hV hT e0).trans hpt)
  have h3 := prep_X P carriers FP X H
  unfold Seams.seedsShape
  omega

section Family





end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

