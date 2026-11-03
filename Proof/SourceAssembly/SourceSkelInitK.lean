import Proof.SourceAssembly.SourceSkelInitAll
import Proof.SourceAssembly.SourceSkelCodeR
import Proof.Packets.BudgetReaderCaps

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open NearCubicWires.PolynomialSchedule
namespace NearCubicWires.SourceSkeleton.Params
noncomputable section

/-! ## 1. The description cap `Ld` and the wire cap `W` -/

/-- `Ld`'s coefficient: AD's polynomial bound of `symDescCap` at the clause degree, raised to `4`. -/
def ldC : SourceBudget.ParNat := fun _ _ _ _ p =>
  max 4 (Classical.choose (Admission.symDescCap_polynomial p.clauseDegree))

/-- `Ld`'s exponent. -/
def ldE : SourceBudget.ParNat := fun _ _ _ _ p =>
  Classical.choose (Classical.choose_spec (Admission.symDescCap_polynomial p.clauseDegree))

theorem ldC_ge (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : 4 ≤ ldC sources gamma hg hh p :=
  le_max_left _ _

/-! ## 2. The circuit cap `P` -/

/-- Both modes' admission capacities at the code width of `Ld`. -/
def pSum (cL eL q : ℕ) : ℕ :=
  SourceBudget.pCap SourceRequest.ThrSwitch.codeWidth cL eL q +
    SourceBudget.pCap SourceRequest.SymOriginal.symCodeWidth cL eL q

theorem pSum_poly (cL eL : ℕ) : PolynomiallyBounded (pSum cL eL) := by
  have ht : PolynomiallyBounded (fun q => SourceBudget.pCap SourceRequest.ThrSwitch.codeWidth cL eL q) := by
    simpa only [SourceBudget.pCap] using polynomiallyBounded_comp SourceBudget.capacity_poly
      (polynomiallyBounded_comp SourceBudget.thrWidth_poly (SourceBudget.ldCap_poly cL eL))
  have hs : PolynomiallyBounded (fun q => SourceBudget.pCap SourceRequest.SymOriginal.symCodeWidth cL eL q) := by
    simpa only [SourceBudget.pCap] using polynomiallyBounded_comp SourceBudget.capacity_poly
      (polynomiallyBounded_comp SourceBudget.symWidth_poly (SourceBudget.ldCap_poly cL eL))
  change PolynomiallyBounded (fun q => pSum cL eL q)
  simpa only [pSum] using polynomiallyBounded_add ht hs

/-- `P`'s coefficient. -/
def pC : SourceBudget.ParNat := fun s g hg hh p =>
  Classical.choose (pSum_poly (ldC s g hg hh p) (ldE s g hg hh p))

/-- `P`'s exponent. -/
def pE : SourceBudget.ParNat := fun s g hg hh p =>
  Classical.choose (Classical.choose_spec (pSum_poly (ldC s g hg hh p) (ldE s g hg hh p)))

def dSum (cL eL cP eP q : ℕ) : ℕ :=
  (q + 2) + cP * (q+1)^eP + SourceBudget.wCap q + SourceBudget.ldCap cL eL q +
    (2 * (SourceRequest.ThrSwitch.codeWidth (SourceBudget.ldCap cL eL q) +
      SourceRequest.SymOriginal.symCodeWidth (SourceBudget.ldCap cL eL q)) + 1)

theorem dSum_poly (cL eL cP eP : ℕ) : PolynomiallyBounded (dSum cL eL cP eP) := by
  have hld := SourceBudget.ldCap_poly cL eL
  have ht : PolynomiallyBounded (fun q => SourceRequest.ThrSwitch.codeWidth (SourceBudget.ldCap cL eL q)) :=
    polynomiallyBounded_comp SourceBudget.thrWidth_poly hld
  have hs : PolynomiallyBounded (fun q => SourceRequest.SymOriginal.symCodeWidth (SourceBudget.ldCap cL eL q)) :=
    polynomiallyBounded_comp SourceBudget.symWidth_poly hld
  have hP : PolynomiallyBounded (fun q : ℕ => cP * (q+1)^eP) :=
    polynomiallyBounded_mul (polynomiallyBounded_constant cP)
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) eP)
  have hW : PolynomiallyBounded (fun q => SourceBudget.wCap q) := by
    simpa only [SourceBudget.wCap] using
      polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 1)) 3
  have hq2 : PolynomiallyBounded (fun q : ℕ => q + 2) :=
    polynomiallyBounded_add polynomiallyBounded_id (polynomiallyBounded_constant 2)
  have hF : PolynomiallyBounded (fun q => 2 * (SourceRequest.ThrSwitch.codeWidth (SourceBudget.ldCap cL eL q) +
      SourceRequest.SymOriginal.symCodeWidth (SourceBudget.ldCap cL eL q)) + 1) :=
    polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_constant 2) (polynomiallyBounded_add ht hs))
      (polynomiallyBounded_constant 1)
  change PolynomiallyBounded (fun q => dSum cL eL cP eP q)
  simpa only [dSum] using
    polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add hq2 hP) hW) hld) hF

/-- `D`'s coefficient. -/
def dC : SourceBudget.ParNat := fun s g hg hh p =>
  Classical.choose (dSum_poly (ldC s g hg hh p) (ldE s g hg hh p) (pC s g hg hh p) (pE s g hg hh p))

/-- `D`'s exponent. -/
def dE : SourceBudget.ParNat := fun s g hg hh p =>
  Classical.choose (Classical.choose_spec (dSum_poly (ldC s g hg hh p) (ldE s g hg hh p) (pC s g hg hh p) (pE s g hg hh p)))

/-! ## 4. The coefficient record width `cw` -/

def cwC : SourceBudget.ParNat := fun s _ _ _ p =>
  Classical.choose (CloseoutFinalC10ModeNativeSchedule.jointCap_polynomial s p)

/-- `cw`'s exponent. -/
def cwE : SourceBudget.ParNat := fun s _ _ _ p =>
  Classical.choose (Classical.choose_spec (CloseoutFinalC10ModeNativeSchedule.jointCap_polynomial s p))

/-! ## 5. F6's masters -/

/-- The workspace master's coefficient: `workspace printer V = sC·(V+1)` (`rfl`). -/
def sC : SourceBudget.ParNat := fun s _ _ _ _ =>
  2 * P1TopDownPaidReusableReserves.coefficient (SourceConstruction.printerOf s) + 20

/-- The rewind master's coefficient: `rewind printer V = rC·(V+1)` (`rfl`). -/
def rC : SourceBudget.ParNat := fun s _ _ _ _ =>
  P1TopDownPaidReusableReserves.coefficient (SourceConstruction.printerOf s) + 2

/-- The init's strip size (S R-S6: `hrT 0..11`, `hrD`, `hrC`, `hrG 0..7`). -/
abbrev initNR : ℕ := 22

/-- Room reserved for the decision-72/75 extension of the init (framed meta words on `hrG 3/4`, `1^b` on `hrG 5`): a
generous fixed count of scratch tapes. -/
abbrev extW : ℕ := 4096

/-- SI's init workspace width at the reserve/`V` exponents (`InitExt.hX`, with equality). -/
def initX (hR hV : SourceBudget.ParNat) : SourceBudget.ParNat := fun s g hg hh p =>
  SourceConstruction.Dimension.P (hR s g hg hh p) (hV s g hg hh p) + 292

/-- The header scratch (`HeadExt`, `nsOf DP DW DL`) at `DP = pE`, `DW = 3`, `DL = ldE`. -/
def initNS : SourceBudget.ParNat := fun s g hg hh p =>
  SourceConstruction.InitRun.nsOf (pE s g hg hh p) 3 (ldE s g hg hh p)

/-- The extension scratch (`uAll DD Dcw`) at `DD = dE`, `Dcw = cwE`, plus the decision-72/75 room. -/
def initNE : SourceBudget.ParNat := fun s g hg hh p =>
  InitS.uAll (dE s g hg hh p) (cwE s g hg hh p) + extW

def xROf (hR hV : SourceBudget.ParNat) : SourceBudget.ParNat := fun s g hg hh p =>
  25 + initX hR hV s g hg hh p + initNS s g hg hh p + initNE s g hg hh p

theorem two_le_xROf (hR hV : SourceBudget.ParNat) (sources : EightSources) (gamma : Real) (hg : 0 < gamma)
    (hh : gamma < 1/2) (p : Parameters sources gamma) : 2 ≤ xROf hR hV sources gamma hg hh p := by
  unfold xROf; omega

end
end NearCubicWires.SourceSkeleton.Params
end

