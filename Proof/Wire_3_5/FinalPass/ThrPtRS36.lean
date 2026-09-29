import Proof.Wire_3_5.FinalPass.ThrPtRS35

/-! # S2: the THR per-point evaluator (P3:2587-2630, 3170-3178)

**`thrPtProg : Seams.ThrPtProg2`** — the evaluator of `Σ_{g,p} R̂_{g,p}(c, u, v)` (`rsumThr` at the list report
`listReportFast D`) over the THR calls, reading the call's words `thrWords` and numbers `thrNums`: from every `PtIn2`
entry at the point `(c, e_L(u), e_R(v))` with capacity `≥ needE (ptSize)`, its word program `thrProg S R` runs in at
most `boundE (ptSize)` steps and meets `PtOut` with that sum in the accumulator; both bounds `≤ thrC·(ptSize+1)^thrD`.
Paper quantity: the per-point sum `Σ_{g,p} R̂_{g,p}(c, u, v)` of row:thr-reported (P3:2587-2630) and its evaluation
cost `poly(ptSize)` (P3:3170-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- **S2: the THR per-point evaluator.** -/
noncomputable def thrPtProg : Seams.ThrPtProg2 where
  nsc := 7
  nrs := 113
  prog := fun S R => thrProg S R
  need := needE
  bound := boundE
  C := thrC
  D := thrD
  need_le := fun U => (Nat.le_add_right _ _).trans (nb_le U)
  bound_le := fun U => (Nat.le_add_left _ _).trans (nb_le U)
  run := fun S R k c u v cap σ hin hcap => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := setupCaps_ok k cap hcap
    obtain ⟨τ', e, hout⟩ := thrCall_run cap k S R c u v σ hin
      (fun j hj p hp => rowCaps_ok k c u v cap hcap _ p hp) h1 h2 h3 h4 h5 h6
    exact ⟨τ', WExec.mono e (cost_ok k c u v), hout⟩

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
