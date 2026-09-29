import Proof.SourceAssembly.SourceRequestSymOriginalForward
import Proof.SourceAssembly.SourceRequestThrSwitch

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.SymOriginal
open PCJd4d1d9d7d1fa4313_Production
open ThrOriginal (thrAt input input_at move_then start_heads heads_native heads_support)
attribute [local irreducible] CloseoutRowsSupportStream.Symmetric.machine CloseoutRowsSupportStream.Symmetric.program

/-! ## The code -/

def symCodeWidth (L : Nat) : Nat := RecoveryWitnessPolicy.canonicalSymmetricCircuitCodeBitBound L

/-! ## The writer and its two framed chains -/

def writer := Composition.machine (CompetitorCountTable.moveMachine (1674 : Fin 1704))
  CloseoutRowsSupportStream.Symmetric.machine

theorem writer_native_forward : CursorRestore.NoLeft writer (1688 : Fin 1704) :=
  CursorRestore.composition_forward _ _ _ (ThrOriginalForward.move_forward _ _)
    SymOriginalForward.native_forward

/-- The bottom support stream of `c` (the writer's tape 1703). -/
def stream {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List Bool :=
  CloseoutRowsSupportStream.supportWord (List.ofFn c.bottom)

theorem sym_input (P q W L : Nat) (bits : List Bool) :
    CloseoutRowsSupportStream.Symmetric.input P q W L bits [] [] = input P q W L bits := rfl
theorem sym_heads (n s : List Bool) :
    CloseoutRowsSupportStream.Symmetric.heads n s = CloseoutRowsSupportStream.Threshold.heads n s := rfl

theorem writer_run {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (P W L : Nat) (bits : List Bool)
    (hcap : CloseoutRowsCircuitCapacity.capacity bits.length ≤ P)
    (hd : decodeNormalizedSymmetricThresholdCircuit q (value bits) = some c)
    (hW : c.wireCount ≤ W) (hL : c.descriptionBits ≤ L) :
    ∃ source : ExecutionReceipt 1704 (2 + CloseoutRowsSupportStream.Symmetric.program.1),
      run writer (1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length)
        (input P q W L bits) = some source ∧
      source.steps ≤ 1 + 1 + CloseoutRowsSupportStream.circuitBudget P q bits.length ∧
      source.final.tapes 1688 = symWord c ∧ source.final.heads 1688 = (symWord c).length ∧
      source.final.tapes 1703 = stream c ∧ source.final.heads 1703 = (stream c).length := by
  obtain ⟨typed, native⟩ := CloseoutRowsCircuitMeaning.symmetric_typed c W L bits hd
  have hp := typed.mpr ⟨hW, hL⟩
  obtain ⟨f, hf, hfs, _fh, _flag, _rh, _raw, _dh, _drv, good⟩ :=
    CloseoutRowsSupportStream.Symmetric.cold_run P q W L bits [] [] hcap
  obtain ⟨heads, word, _arity, _driver, _W, _L, _raw', support, _bound⟩ := good hp
  rw [sym_heads, start_heads, sym_input] at hf
  obtain ⟨r, hr, rs, rh, rt⟩ := move_then (1674 : Fin 1704) CloseoutRowsSupportStream.Symmetric.machine _ _ f hf
  have hsup := CloseoutRowsSupportStream.Symmetric.support_typed c bits hd
  refine ⟨r, hr, by omega, ?_, ?_, ?_, ?_⟩
  · rw [rt, word, List.nil_append, native]
    rfl
  · rw [rh, heads, sym_heads, heads_native, List.nil_append, native]
    rfl
  · rw [rt, support, List.nil_append, hsup]
    rfl
  · rw [rh, heads, sym_heads, heads_support, List.nil_append, hsup]
    rfl

def chainA := AppendOutputFrame.machine writer (1688 : Fin 1704)

/-! ## The three-stage layout in `Fin 3422` -/





section normal
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal

end normal
end NearCubicWires.SourceRequest.SymOriginal

