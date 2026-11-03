import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ7Base

/-! # T3 THR decode front, packaging part 8: the run at a THR call

**`call_run`**: at every THR call of the gate, every output `out`, unit `j` and capacity `cap ≥ c₀(n)`, the decode
front `frontM` (the front end `TW l`, W6 `NW l`, the gate's `c_r` and `f_e`) runs from the unit's fresh cell to
`ThrDec.ThrDecOut`, in at most `fK·(c₀+1)^{fD}` steps, where `c₀(n) = cZero (Q_F) (L²) (aE l f_e)`.

Paper quantity of the main type: the THR call's rows (FILTER and RADIX) at each unit of the THR tape (P3:2543-2558,
2019-2054, 2585-2623). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.ThrDec

theorem thrCodes_len {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) :
    (ReqBridge.thrCodes Cs).length = a' := by
  unfold ReqBridge.thrCodes; rw [List.length_ofFn]

section Call
variable (x : ℕ) (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
 {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
 (translation : List ℕ) 
 

set_option quotPrecheck false in
local notation "PP" => (callInputs l F kclk coef A a ha).starParams n hs
set_option quotPrecheck false in
local notation "FPT" => (callInputs l F kclk coef A a ha).filterParams Mode.thr n
set_option quotPrecheck false in
local notation "HS" => ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
  (callInputs l F kclk coef A a ha).D ((callInputs l F kclk coef A a ha).filterParams Mode.thr n).cap
set_option quotPrecheck false in
local notation "KH" => ((callInputs l F kclk coef A a ha).starParams n hs).s *
  (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)
set_option quotPrecheck false in
local notation "VV" => PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs
  (PrimT.W6.litAlg l) 1 carriers.length ((ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs
    carriers (gate0 l F).alg (callInputs l F kclk coef A a ha).D
    ((callInputs l F kclk coef A a ha).filterParams Mode.thr n).cap).getD 1 0)
set_option quotPrecheck false in
local notation "XS" => carriers.map List.length
set_option quotPrecheck false in
local notation "TOTC" => 2 ^ (FPT).seedBits * (HS).getD 2 0 * (HS).getD 6 0 * 2 ^ (2 * (KH)) *
  ((carriers.length + 1) * 3 + 2)

end Call

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
