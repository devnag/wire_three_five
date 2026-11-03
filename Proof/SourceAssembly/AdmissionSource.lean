import Proof.SourceAssembly.AdmissionDegree
import Proof.Assembly.CappedCoordinate
import Proof.CaseAnalysis.FinalSiteWireEnvelope
import Proof.CaseAnalysis.FinalModeNativeEnvelope
import Proof.CaseAnalysis.WitnessInputCutoff
import Proof.CaseAnalysis.FinalLedgerAssembly

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open PCJd4d1d9d7d1fa4313_Production

noncomputable section

section
variable (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2)))
  {gamma : ℝ} (p : Parameters sources gamma) (den : ℕ)
  {n : ℕ} (x : BitInput n) (oracle : BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n))
  (bits : List Bool)

/-- Past `inputCutoff`, the atom arity is the native width. -/
theorem req_arity (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) :
    (req sources k clock x oracle).arity = (outer sources k clock).result.pcp.nativeWidth n :=
  CloseoutWitnessPolicy.input_cutoff_arity sources k clock x oracle hN

theorem symCap_eq (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) :
    (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).wireCap =
      carriedWireCap den 5 (req sources k clock x oracle).arity := by
  rw [req_arity sources k clock x oracle hN]
  rfl

theorem thrCap_eq (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) :
    (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle).wireCap =
      carriedWireCap den 9 (req sources k clock x oracle).arity := by
  rw [req_arity sources k clock x oracle hN]
  rfl

theorem symDesc_eq (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) :
    (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).descriptionCap =
      carriedSymDescription den p.clauseDegree (req sources k clock x oracle).arity := by
  have e := req_arity sources k clock x oracle hN
  calc (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).descriptionCap
      = RepairSource.CloseoutRawRows.symmetricDescription (req sources k clock x oracle).arity
          ((req sources k clock x oracle).arity +
            clauseWidth p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n) + 1)
          ⌊wireScale (1 / (den : ℝ)) 5 ((outer sources k clock).result.pcp.nativeWidth n)⌋₊ := rfl
    _ = carriedSymDescription den p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n) := by
        rw [e]
    _ = carriedSymDescription den p.clauseDegree (req sources k clock x oracle).arity := by rw [e]

theorem thrDesc_eq (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n) :
    (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle).descriptionCap =
      carriedThrDescription den p.clauseDegree (req sources k clock x oracle).arity := by
  have e := req_arity sources k clock x oracle hN
  calc (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle).descriptionCap
      = RepairSource.CloseoutRawRows.thresholdDescription (req sources k clock x oracle).arity
          ((req sources k clock x oracle).arity +
            clauseWidth p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n) + 1)
          ⌊wireScale (1 / (den : ℝ)) 9 ((outer sources k clock).result.pcp.nativeWidth n)⌋₊ := rfl
    _ = carriedThrDescription den p.clauseDegree ((outer sources k clock).result.pcp.nativeWidth n) := by
        rw [e]
    _ = carriedThrDescription den p.clauseDegree (req sources k clock x oracle).arity := by rw [e]

/-- **Every atom of every guessed proof coordinate is admitted** (the capped decoder's own
`wires_le`/`description_le`, `paper.tex:4292-4302`). -/
theorem coordinate_admitted (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).FactorsSatisfy
      (AtomAdmitted den p.clauseDegree) := by
  by_cases hs : RepairOrdinary.CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k clock p den x oracle bits hs j]
    apply C10SiteWireEnvelope.mapPolynomial_factorsSatisfy
    intro m hm c hc
    have hw := C10SiteWireEnvelope.familyCoordinate_factorsSatisfy_wires rfl
      (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits) j m hm c hc
    have hd := RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope.familyCoordinate_description rfl
      (P1Independent.CappedDecode.symFamilyOf sources k clock p den x oracle bits) j m hm c hc
    exact ⟨hw.trans (le_of_eq (symCap_eq sources k clock p den x oracle hN)),
      hd.trans (le_of_eq (symDesc_eq sources k clock p den x oracle hN))⟩
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k clock p den x oracle bits hs j]
    apply C10SiteWireEnvelope.mapPolynomial_factorsSatisfy
    intro m hm c hc
    have hw := C10SiteWireEnvelope.familyCoordinate_factorsSatisfy_wires rfl
      (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits) j m hm c hc
    have hd := RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope.familyCoordinate_description rfl
      (P1Independent.CappedDecode.thrFamilyOf sources k clock p den x oracle bits) j m hm c hc
    exact ⟨hw.trans (le_of_eq (thrCap_eq sources k clock p den x oracle hN)),
      hd.trans (le_of_eq (thrDesc_eq sources k clock p den x oracle hN))⟩

/-- **The source's issued requests are admitted**: every monomial the site expansion prints at any phase
and clause address, past `inputCutoff`. -/
theorem issued_admitted (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (ci : Fin (2^(pcppAt sources k clock x oracle).clauseBits))
    (m : CircuitMonomial (Atom (pcppAt sources k clock x oracle)) 4)
    (hm : m ∈ (RepairOrdinary.CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k clock x oracle)
      (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) Atom.systematic ci).monomials) :
    Admitted den p.clauseDegree m.factors := by
  refine ⟨m.degree_le, ?_⟩
  exact C10SiteWireEnvelope.siteCalls_factorsSatisfy ph (pcppAt sources k clock x oracle)
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) Atom.systematic
    (AtomAdmitted den p.clauseDegree) (coordinate_admitted sources k clock p den x oracle bits hN)
    (fun _ => trivial) ci m hm

/-- The same, in `SourceTrace`'s form: the atoms of call `j` of any ordering of the site's monomials. -/
theorem trace_atoms_admitted (hN : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (ph : RepairOrdinary.CloseoutRowsOriginalSchedule.Phase)
    (ci : Fin (2^(pcppAt sources k clock x oracle).clauseBits))
    (order : List (CircuitMonomial (Atom (pcppAt sources k clock x oracle)) 4))
    (horder : order.Perm (RepairOrdinary.CloseoutFinalC10SupplierCalls.siteCalls ph
      (pcppAt sources k clock x oracle)
      (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) Atom.systematic ci).monomials)
    (j : ℕ) : Admitted den p.clauseDegree ((order.map (fun m => m.factors)).getD j []) := by
  rcases Nat.lt_or_ge j order.length with hj | hj
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
    exact issued_admitted sources k clock p den x oracle bits hN ph ci _
      (horder.mem_iff.mp (List.getElem_mem hj))
  · rw [List.getD_eq_default _ _ (by simpa using hj)]
    exact ⟨by simp, fun a ha => by cases ha⟩

end


end
end NearCubicWires.Admission
