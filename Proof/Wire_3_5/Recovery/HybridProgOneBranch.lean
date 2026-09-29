import Proof.Wire_3_5.Recovery.HybridProgClearRecovered
import Proof.Wire_3_5.Recovery.HybridProgOneRecovered
import Proof.Wire_3_5.Recovery.HybridProgOneAfterClear
import Proof.Wire_3_5.Recovery.HybridProgClearRun
import Proof.Wire_3_5.Recovery.HybridProgOneRun
import Proof.Wire_3_5.Recovery.HybridProgTwoBranch

/-! # The hybrid `E^NP` program: OneBranch (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramOneBranch`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: The false recovery branch pays the actual query clear, executes the original Case1 worker on retained inputs, and halts the same common program.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose RecoveryRootRound RecoveryExecution
set_option autoImplicit false
noncomputable section

theorem one_branch (p : Parameters) (bits word : List Bool) (padding fuel : ℕ)
    (out : Fin (prefixProgram p).base.tapeCount→List Bool) (final : (recovery p).Config)
    (halt : (recovery p).base.machine.halted final.control=true)
    (flag : readTapeBit (final.tapes (recoveryFlagLocal p)) 0=false)
    (flagHead : final.heads (recoveryFlagLocal p)=0)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits)
    (hw : final.tapes (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0)=word)
    (hhw : final.heads (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0)=0)
    (hhq : final.heads (RecoveryBoundedCold.queryPort (source p) p.k p.degree)=0)
    (hq : ((recovered p bits out padding final).tapes (ports p).queryTape).length ≤
      CloseoutCapacity.capacity p.Aq p.Bq bits.length)
    (answer : Fin (on p)→List Bool)
    (actual : Ready RecoveryOracle.correctedSat (one p) fuel (oneColdInput p word bits) answer) :
    ∃ cost ≤ CloseoutCommonQueryClear.budget p.Aq p.Bq bits+fuel+3,∃ result,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program p) cost
        (controlConfig (RecoveryCalls.code (fun j=>(pieces p j).states) 1)
          (recovered p bits out padding final)) result ∧
      (program p).base.machine.halted result.control=true ∧
      result.tapes (ports p).outputTape=answer (one p).base.outputTape:=by
  let c:=recovered p bits out padding final
  have entry:=clear_recovered_entry p bits padding out final ha hhq
  have hf:=recovered_flag p bits out padding final false flag flagHead
  have jump:=graph_return RecoveryOracle.correctedSat (ports p) (pieces p) 0 (next p) 1 2 c halt (by
    change some (if c.scanned (recoveryFlag p) then (4 : Fin 6) else 2)=some 2
    rw [hf]
    rfl)
  obtain ⟨clearCost,hclear,clearOut,clearRun,clearQuery,clearAddress⟩:=
    clear_edge p bits (c.tapes (ports p).queryTape) hq c.heads c.tapes entry.1 entry.2
  have fresh (i : Fin (on p)) : c.tapes (lift3 p (i.natAdd (n2 p)))=[]:=by
    have boundary : n1 p ≤ (lift3 p (i.natAdd (n2 p))).val:=
      (Nat.le_add_right (n1 p) 28).trans (Nat.le_add_right (n2 p) i.val)
    exact (recovered_fresh p bits out padding final _ boundary).2
  have oneEntry:=one_after_clear_entry p word bits
    (CloseoutCapacity.capacity p.Aq p.Bq bits.length) c.tapes clearOut
    ((recovered_hierarchy p bits out padding final).1.trans hw)
    (recovered_output p bits out padding final).2 fresh clearAddress clearQuery
  obtain ⟨padded,paddedRun,paddedOutput⟩:=one_padded_ready p word bits
    (CloseoutCapacity.capacity p.Aq p.Bq bits.length) fuel answer actual
  obtain ⟨result,lastRun,lastHalt,lastOutput⟩:=one_finish p fuel _ padded paddedRun c.heads
    (install (clearSlot p) c.tapes clearOut) oneEntry
    (one_recovered_heads p bits out padding final ha hhw hhq)
  exact ⟨1+(clearCost+(fuel+1)),by omega,result,trans jump (trans clearRun lastRun),
    lastHalt,lastOutput.trans paddedOutput⟩

end
end NearCubicWires.RepairSource.HybridProgram
