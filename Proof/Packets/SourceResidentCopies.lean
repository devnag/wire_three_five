import Proof.CaseAnalysis.RowsTupleSeekFrame

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceResident
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## The masked reset from zero heads, with the log's length bounded -/

/-! ## One framed copy, rewound -/

/-- The rewound framed-word copier: tape 0 the source, tape 1 the copy, tape 2 the reset log. -/
def copyM := MaskedReset.machine (CloseoutRowsTupleSeek.frameMachine true) (fun _ => true)


/-- Which source feeds target `5 + i`: native, support, support, TOP, `1^q`, `1^q`, `1^K`. -/
def srcIx : Fin 7 → Fin 5 := ![0, 1, 1, 2, 3, 3, 4]

/-- Source port of copy `i`. -/
def srcP (i : Fin 7) : Fin 13 := ⟨(srcIx i).val, by have := (srcIx i).isLt; omega⟩
/-- Target port of copy `i`. -/
def tgtP (i : Fin 7) : Fin 13 := ⟨5 + i.val, by omega⟩
/-- The shared reset log. -/
def logP : Fin 13 := ⟨12, by omega⟩

/-- Copy `i`, docked on its source, target and the log. -/
def cM (i : Fin 7) := RecoveryFocus.machine ![srcP i, tgtP i, logP] copyM

/-- **The copies stage** (one fixed machine). -/
def copiesM :=
  Composition.machine (cM ⟨0, by omega⟩) (Composition.machine (cM ⟨1, by omega⟩)
    (Composition.machine (cM ⟨2, by omega⟩) (Composition.machine (cM ⟨3, by omega⟩)
      (Composition.machine (cM ⟨4, by omega⟩) (Composition.machine (cM ⟨5, by omega⟩) (cM ⟨6, by omega⟩))))))

/-- Cost of copy `i`. -/
def cc (w : Fin 5 → List Bool) (i : Fin 7) : ℕ := 2 * (2 * (w (srcIx i)).length + 1) + 2

/-- Cost of the stage (`R`-free: linear in the five words' lengths). -/
def copiesCost (w : Fin 5 → List Bool) : ℕ :=
  cc w ⟨0, by omega⟩ + 1 + (cc w ⟨1, by omega⟩ + 1 + (cc w ⟨2, by omega⟩ + 1 + (cc w ⟨3, by omega⟩ + 1 +
    (cc w ⟨4, by omega⟩ + 1 + (cc w ⟨5, by omega⟩ + 1 + cc w ⟨6, by omega⟩)))))

end
end NearCubicWires.SourceResident

