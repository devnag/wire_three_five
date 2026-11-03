import Proof.SourceAssembly.SourceRequestSelHG7Site
import Proof.SourceAssembly.SourceFactorSelG7Fam

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
namespace NearCubicWires.SourceRequest.SelG7Spec
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

def g7costW (sources : EightSources) (mask : MaskProducer) (MB : List Bool) (a : PointwisePCPPAlgorithm) (rq : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output rq).clauseBits))
    (coordinate : Fin ((a.output rq).systematicBits + (a.output rq).auxiliaryBits) →
      ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom (a.output rq)) 1)
    (bits : List Bool) (ph : CloseoutRowsOriginalSchedule.Phase) (L target cwid cw D b Pw W Ld : Nat) : Bool → Nat → Nat
  | false => Item4.g7Cost (fun m => SelLocal.selThrCost a rq ci coordinate bits ph L target cwid cw D b m)
      (fun m => Words.wordsCost mask (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources)) (requestAt coordinate ph ci L target false m) MB)
      (SelBack.PT (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci L target
  | true => Item4.g7Cost (fun m => SelLocal.selSymCost a rq ci coordinate bits ph L target cwid cw D b m)
      (fun m => Words.wordsCost mask (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources)) (requestAt coordinate ph ci L target true m) MB)
      (SelBackSym.PS (pcpp := a.output rq) (decompositionOf sources) Pw W Ld) coordinate ph ci L target

section site
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔡" => NearCubicWires.SourceSkeleton.FirstW.dSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔇" => NearCubicWires.SourceSkeleton.FirstW.dSite selector xtra mask packets rows sources gamma hg hh p

end site

end
end NearCubicWires.SourceRequest.SelG7Spec
end

