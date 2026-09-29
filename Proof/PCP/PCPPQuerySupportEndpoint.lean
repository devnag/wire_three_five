import Proof.PCP.PCPPQuerySupportReusable

/-! Literal entry and paid result-buffer erasure for repeated cached queries.
A row consumer reads exactly arity raw cells before this clearing call. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
open LocalBitMultitape RepairRepresentation SourceInterfaces RepairSource.VerifierDecoding RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem entry_literal (source : List Bool) (arity index C : ℕ) :
    entry source arity index C=⟨machine.start,heads,data source arity index C []⟩ := by
  apply configuration_ext
  · rfl
  · funext j; fin_cases j <;> rfl
  · funext j
    fin_cases j <;> simp [entry,Composition.leftConfig,TapeEmbedding.config,ZeroPadding.config,
      resultCaps,PCPPQuerySupportReset.entry,PCPPQuerySupportReset.caps,Rewind.recording,
      Rewind.config,PCPPQuerySupport.ready,Fin.addCases,data,extra,ZeroPadding.pad]


end NearCubicWires.RepairOrdinary.PCPPQuerySupportReuse
