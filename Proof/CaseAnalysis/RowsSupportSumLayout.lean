import Proof.CaseAnalysis.RowsSupportAppendBank
import Proof.CaseAnalysis.RowsSupportExchange
import Proof.CaseAnalysis.RowsSupportSumBody
import Proof.CaseAnalysis.WitnessSumCursor

/-! The counted term driver keeps its original outer2532 alias. Static
renaming and the unchanged528-tape bank place support at final3061. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
open LocalBitMultitape CloseoutWitness RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def renamed {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  TapeRenaming.machine (Exchange.layout 2532) (SumBody.machine circuit k q)
noncomputable def body {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  AppendBank.machine (e:=528) (renamed circuit k q)

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.SumWork
