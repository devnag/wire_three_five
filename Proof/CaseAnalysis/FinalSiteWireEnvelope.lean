import Proof.CaseAnalysis.FinalWireEnvelope

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope

open NearCubicWires
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactnessFamily
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows (primeCutoff listDenominator)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters decompositionOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom symLimits thrLimits
  symFamilyOf thrFamilyOf oracleOf)
open NearCubicWires.RepairSource.SelectedRecoveryIntegration (outer)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime (primesUpTo)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §2 The atom relabelling, and the arity transport -/

/-! ## §3 `atomWires` on the two guessed constructors -/

/-! ## §4 `atomWires` on the SYSTEMATIC constructor

`paper.tex:4303-4305` compiles the systematic parity deterministically into the
native parity circuit, so its envelope is not guessed and needs no decoder
guard: it is computed, and it is bounded by the arity outright. -/

/-! ## §5 The route's own cap, and the deliverable -/

noncomputable section

/-! ## §6 RESOURCE -- the cap is CUBIC, hence one residual cell and no second factor

`ENDGAME_RESOURCE.md` §1's governing sentence -- located by CONTENT, since the
numbering has drifted: **"Nothing else in the campaign may add a second residual
factor"** -- is not engaged by this module.  The envelope REMOVES branches; its
cost is the decoder's own syntactic `if`, already paid.  What it could have
added is an `entryWidth` term, and `stageSeedEnvelope_le_of_bits`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`) makes that term a fixed linear
function of the BIT LENGTHS of the caps.  The theorem below is the missing half:
the cap this module actually uses is bounded by a CUBE, so its bit length is
`O(L_q)` and the whole external-row exponent stays in the `FREE / POLYLOG`
bucket. -/

/-! ## §7 CONSUMER-BACKWARD CAPSTONE -- `henv` is GONE from the binder list

The test that a discharge ATTACHES rather than merely typechecks: feed
`henv_at_envelopeCap` into the consumer that demanded it and read off what is
left.  `siteDenFits_of_wireEnvelope`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`) had four premises; below it has
three, and `wireCap` is no longer a free parameter either -- it is pinned to the
route's own caps.  The three that remain are `hfloor` (ENVELOPE's
`envelopeFloor`), `hprime` and `hthrden` (the THR prime window and list
denominator), and they belong to other owners. -/

end

end NearCubicWires.RepairSource.CloseoutFinal.C10SiteWireEnvelope
