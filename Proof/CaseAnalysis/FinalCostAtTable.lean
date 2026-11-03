import Proof.CaseAnalysis.FinalFuelEnvelope

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The residual table cell, as a per-call fuel -/

/-- **The paper's `2^q/q^sigma` (`paper.tex:3555-3557`), as a budget.**  This is
byte-for-byte the cell `ledger_of_parts`' `hrow` binder
(`Proof/CaseAnalysis/FinalLedgerAssembly.lean`) already allows for one external row, with
`kappa := ledgerExponent sources r degree` (`Proof/CaseAnalysis/FinalPartsSchedule.lean`),
which is A.8's `kappa >= h_D + sigma + c_1` (`paper.tex:2307`; 2306 is the opening `\[`). -/
def hotFuel (sources : EightSources) (k r degree N : ℕ) : ℕ :=
  2 ^ (widthAt sources k N
      - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1))

/-- **The new ceiling DOMINATES the old one.**  Taken from `envelope_split`
(`Proof/CaseAnalysis/FinalFuelEnvelope.lean`), which states the DEFECT (`polyFuel` never
reaches `2^q`) and the DOMINATION (`polyFuel` fits inside one residual table factor) as ONE
conjunction precisely so that no consumer can take half of it: elaborating this proof term
forces both halves.  The domination half is why the move is free -- everything already
established under the `polyFuel` pin is still under the new one; the defect half is why the
move is necessary at all. -/
theorem polyFuel_le_hotFuel (sources : EightSources) (k r degree C d N : ℕ)
    (hd : d + 1 ≤ k + 2) (hN : repinOnset sources k r degree C ≤ N) :
    polyFuel C d N ≤ hotFuel sources k r degree N := by
  unfold hotFuel
  exact (envelope_split sources k r degree C d hd).2 N hN

/-! ## Section 2  `hrow` with `cost` at the cell -/

/-! ## Section 3  The `Parts` instance with `cost` at the cell -/

/-! ## Section 4  Nothing already proved is lost -/

/-! ## Section 5  The payoff -/


end
end NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable
