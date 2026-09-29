import Proof.Wire_3_5.Recovery.CertCommonPrefix
import Proof.Wire_3_5.Recovery.HybridProgTwoDirect

/-! # The hybrid `E^NP` program: static layout (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramLayout`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: Static layout of the one common oracle program. Its five worker banks are fresh except for the listed retained inputs and the ONE query/output. All parameters are fixed before running on the final ordinary input.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open OrdinaryOracleCompose CloseoutLanguage
open NearCubicWires.WireExponent3_5
set_option autoImplicit false
noncomputable section

/-- The hybrid program's parameters: the literal set, the gate, the clock exponent, a fixed Case-1 copy count, the
prefix and Case-2 capacity exponents, the onset, the capacities and the refuter. The source, degrees, clock and
schedule words are derived from `l`, `G` and `kclk`. -/
structure Parameters where
  l : Literals
  G : Split.Gate
  kclk : ℕ
  copies : ℕ
  e1 : ℕ
  e2 : ℕ
  e3 : ℕ
  f1 : ℕ
  f2 : ℕ
  f3 : ℕ
  f4 : ℕ
  onset : ℕ
  Aw : ℕ
  Bw : ℕ
  Aq : ℕ
  Bq : ℕ
  refuter : OrdinaryOracleProgram

namespace Parameters
theorem sources (p : Parameters) : EightSources := p.l.eightSources
def k (p : Parameters) : ℕ := p.kclk
def degree (p : Parameters) : ℕ := Transfer.recOracleDeg p.l
def D (p : Parameters) : ℕ := Transfer.recDG p.l
def clock (p : Parameters) : OrdinaryClock (fun n => n ^ (p.k + 2)) := PolynomialClock.ordinaryClock p.kclk
def A (p : Parameters) : ℕ := p.G.Apad
def u (p : Parameters) : ℕ := Transfer.zu (Transfer.gateCParams1 p.l).ζ
def v (p : Parameters) : ℕ := Transfer.zv (Transfer.gateCParams1 p.l).ζ
end Parameters

def source (p : Parameters):=fixedProjection p.sources
def hierarchy (p : Parameters):=(p.sources.hierarchy (fun n=>n^(p.k+2)) p.clock).hierarchy
def pad (p : Parameters):=padding p.sources p.k p.clock
def code (p : Parameters):=VerifierEncoding.code (hierarchy p).verifier
def amp (p : Parameters):=(selectedAmplifier p.sources.amplification p.degree).constructor.program
def work (p : Parameters):=Transfer.CertPrefixPrep.prefixTapes p.D
def prefixProgram (p : Parameters):=WireExponent3_5.Cert.prefixProgram p.sources p.k p.A p.u p.v p.D p.e1 p.e2 p.e3
  p.onset p.Aw p.Bw p.clock p.refuter
def recovery (p : Parameters):=RecoveryBoundedCold.program (source p) p.k p.degree
  (hierarchy p).coefficient (pad p) (code p)
def one (p : Parameters):=RecoveryCaseOnePaddedBit.program (source p) (amp p) p.k
  (hierarchy p).coefficient (pad p) (code p)
def two (p : Parameters):=Transfer.CaseTwoRuns.twoMachine p.l p.G p.kclk p.f1 p.f2 p.f3 p.f4
def rn (p : Parameters):=RecoveryBoundedCold.tapes (source p) p.k p.degree
def on (p : Parameters):=(one p).base.tapeCount
def tn (p : Parameters):=HDirect.tapes (Transfer.gateSource p.l) (Transfer.gatePCPP p.l) p.kclk (Transfer.recDG p.l)
def n0 (p : Parameters):=(prefixProgram p).base.tapeCount+1
def n1 (p : Parameters):=n0 p+rn p
def n2 (p : Parameters):=n1 p+28
def n3 (p : Parameters):=n2 p+on p
def n4 (p : Parameters):=n3 p+tn p
def tapes (p : Parameters):=n4 p+2

def word0 (p : Parameters) : Fin (n0 p):=
  (CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k (CloseoutCommonPrepare.hierarchySlot p.k)).castAdd 1
def capacity0 (p : Parameters) : Fin (n0 p):=
  (CloseoutCommonPrefix.prepareSlots (work p) p.refuter p.k (CloseoutCommonPrepare.capacitySlot p.k)).castAdd 1
def query0 (p : Parameters) : Fin (n0 p):=(prefixProgram p).queryTape.castAdd 1
def output0 (p : Parameters) : Fin (n0 p):=(0 : Fin 1).natAdd (prefixProgram p).base.tapeCount
def address0 (p : Parameters) : Fin (n0 p):=⟨0,by unfold n0;omega⟩
def lift0 (p : Parameters) (i : Fin (n0 p)) : Fin (tapes p):=
  ((((i.castAdd (rn p)).castAdd 28).castAdd (on p)).castAdd (tn p)).castAdd 2
def lift1 (p : Parameters) (i : Fin (n1 p)) : Fin (tapes p):=
  (((i.castAdd 28).castAdd (on p)).castAdd (tn p)).castAdd 2
def lift2 (p : Parameters) (i : Fin (n2 p)) : Fin (tapes p):=
  ((i.castAdd (on p)).castAdd (tn p)).castAdd 2
def lift3 (p : Parameters) (i : Fin (n3 p)) : Fin (tapes p):=(i.castAdd (tn p)).castAdd 2
def prefixSlot (p : Parameters) (i : Fin (prefixProgram p).base.tapeCount):=lift0 p (i.castAdd 1)

def recoveryShared (p : Parameters) : Fin 3→Fin (n0 p):=![word0 p,capacity0 p,query0 p]
def recoveryBank (p : Parameters):=CloseoutCommonPortBank.slot
  (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree) (recoveryShared p)
def recoverySlot (p : Parameters) (i : Fin (rn p)):=lift1 p (recoveryBank p i)
def scalarBank (p : Parameters) (j : Fin 5) : Fin (n1 p):=recoveryBank p
  ((RecoveryBoundedColdSourceGraph.graphSlots (source p) p.k p.degree (j.natAdd 1659)).castAdd 790)
def descriptionBank (p : Parameters) : Fin (n1 p):=recoveryBank p
  ((787 : Fin 790).natAdd (RecoveryBoundedCold.oldTapes (source p) p.k p.degree))
def flagBank (p : Parameters) : Fin (n1 p):=recoveryBank p
  ((369 : Fin 790).natAdd (RecoveryBoundedCold.oldTapes (source p) p.k p.degree))

def clearLocal : Fin 2→Fin 28:=![0,26]
def clearShared (p : Parameters) : Fin 2→Fin (n1 p):=
  ![(address0 p).castAdd (rn p),(query0 p).castAdd (rn p)]
def clearBank (p : Parameters):=CloseoutCommonPortBank.slot clearLocal (clearShared p)
def clearSlot (p : Parameters) (i : Fin 28):=lift2 p (clearBank p i)

def oneLocal (p : Parameters) : Fin 4→Fin (on p):=
  ![⟨0,(one p).base.twoTapes.trans_lt' (by decide)⟩,
    ⟨RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+16,by
      change _<RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+45;omega⟩,
    (one p).queryTape,(one p).base.outputTape]
def oneShared (p : Parameters) : Fin 4→Fin (n2 p):=
  ![((word0 p).castAdd (rn p)).castAdd 28,((address0 p).castAdd (rn p)).castAdd 28,
    ((query0 p).castAdd (rn p)).castAdd 28,((output0 p).castAdd (rn p)).castAdd 28]
def oneBank (p : Parameters):=CloseoutCommonPortBank.slot (oneLocal p) (oneShared p)
def oneSlot (p : Parameters) (i : Fin (on p)):=lift3 p (oneBank p i)

def twoLocal (p : Parameters) : Fin 6→Fin (tn p):=
  Fin.addCases (m:=5) (n:=1) (HDirect.ports (Transfer.gateSource p.l) (Transfer.gatePCPP p.l) p.kclk (Transfer.recDG p.l))
    (fun _=>HDirect.outputPort (Transfer.gateSource p.l) (Transfer.gatePCPP p.l) p.kclk (Transfer.recDG p.l))
def twoShared (p : Parameters) : Fin 6→Fin (n3 p):=
  ![(((word0 p).castAdd (rn p)).castAdd 28).castAdd (on p),
    ((descriptionBank p).castAdd 28).castAdd (on p),
    (((address0 p).castAdd (rn p)).castAdd 28).castAdd (on p),
    ((scalarBank p 0).castAdd 28).castAdd (on p),
    ((scalarBank p 2).castAdd 28).castAdd (on p),
    (((output0 p).castAdd (rn p)).castAdd 28).castAdd (on p)]
def twoBank (p : Parameters):=CloseoutCommonPortBank.slot (twoLocal p) (twoShared p)
def twoSlot (p : Parameters) (i : Fin (tn p)):=(twoBank p i).castAdd 2
def falseLocal : Fin 1→Fin 2:=fun _=>0
def falseShared (p : Parameters) : Fin 1→Fin (n4 p):=
  fun _=>((((output0 p).castAdd (rn p)).castAdd 28).castAdd (on p)).castAdd (tn p)
def falseSlot (p : Parameters):=CloseoutCommonPortBank.slot falseLocal (falseShared p)

def ports (p : Parameters) : Ports (tapes p) where
  twoTapes:=by unfold tapes;omega
  outputTape:=lift0 p (output0 p)
  outputFresh:=by
    have h:=(prefixProgram p).base.twoTapes
    change (prefixProgram p).base.tapeCount+0≠0
    omega
  queryTape:=lift0 p (query0 p)
  queryFresh:=(prefixProgram p).queryFresh

end
end NearCubicWires.RepairSource.HybridProgram
