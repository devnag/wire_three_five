import Proof.Amplification.RecoveryPreliminaryBound

/-! The selected capped valuation parser on physically produced dimensions.
Only its false-only comparison backing is omitted by inverse padding;
source, zero-index frame and both true unary drivers are literal inputs. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width (bits : List Bool) := RecoveryColdHeader.width bits
def cap (bits : List Bool) := RecoveryColdHeaderCap.limit bits
def capacity (bits : List Bool) := 8192*(width bits+1)^2
def data (bits word : List Bool) : RecoveryValuationStream.Data :=
  ⟨frame word,0,width bits,RecoveryColdHeader.zeroWord bits,[],false,false,false,capacity bits⟩
def heads : Fin 10→Nat := ![0,0,1,0,0,0,0,0,1,1]
def tapes (bits word : List Bool) : Fin 10→List Bool :=
  ![frame word,[],CompareMachine.word (width bits+1),frame (RecoveryColdHeader.zeroWord bits),
    [false],[false],[],[false],[false],CompareMachine.word (cap bits)]
def caps (bits : List Bool) (i : Fin 10) : Nat := if i.val=6 then capacity bits else 0
noncomputable def machine := RecoveryValuationCount.machine

theorem padded_input (bits word : List Bool) :
    ZeroPadding.config (caps bits) (⟨machine.start,heads,tapes bits word⟩ : Configuration 10 _)=
      RecoveryValuationCount.cfg (data bits word) 0 (cap bits) machine.start := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [ZeroPadding.config,caps,tapes,RecoveryValuationCount.cfg,
      RecoveryValuationStream.Data.cfg,data,TapeEmbedding.config,Fin.addCases,CompareMachine.word,
      ZeroPadding.pad]

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
