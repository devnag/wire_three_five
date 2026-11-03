import Proof.MachineModel.Layout
import Proof.CaseAnalysis.FinalAppendWorkspaceInit
import Proof.CaseAnalysis.FinalCacheAtAdmission
import Proof.CaseAnalysis.FinalTailCompose
import Proof.CaseAnalysis.WitnessBoundedFamilySupportLayout
import Proof.CaseAnalysis.FinalOriginalFrame
import Proof.CaseAnalysis.FinalSeedEngine
import Proof.CaseAnalysis.FinalSupplierCall
import Proof.CaseAnalysis.RowsOriginalCount
import Proof.CaseAnalysis.WitnessLegalCacheFields
import Proof.Circuits.DecompositionCountPosition

/-! The actual admitted cold/prologue/count/append entry on the selected tape layout.
All local frames are supplied by the same physical executions; the counter stays
parked at head 1. The caller still pays its control branches and loop/suffix. -/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry

open NearCubicWires LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open ProjectionNormalization CloseoutWitness CloseoutFinal ExtDecompositionBatch CanonicalWitnessCodec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section



private theorem count_append
    (B : Nat)
    (cache : Fin 19 → Fin B)
    (countSlots : Fin 74 → Fin B)
    (appendSlots : Fin 42 → Fin B)
    (cacheData : Fin 19 → List Bool)
    (clauseCount : Nat)
    (sys : Nat)
    (b : Nat)
    (countFuel : Nat)
    (actualBank : Fin B → List Bool)
    (hc : Function.Injective countSlots)
    (hfirst : ∀ j : Fin 19,countSlots (j.castAdd 55)=cache j)
    (ha : Function.Injective appendSlots)
    (hdis : ∀ i j,countSlots i≠appendSlots j)
    (hcount : ∃ out, Step CloseoutRowsOriginalCount.machine countFuel (CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads) (CloseoutRowsOriginalCount.input cacheData) (CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads) out ∧ (∀ j : Fin 19,out (j.castAdd 55)=cacheData j) ∧ out 70=UnaryTemplate.tape clauseCount ∧ out 72=List.replicate clauseCount true ∧ out 28=UnaryTemplate.tape sys)
    (hcache : ∀ j,actualBank (cache j)=cacheData j)
    (hfresh : ∀ j : Fin 55,actualBank (countSlots (Fin.natAdd 19 j))=[])
    (happend : ∀ j,actualBank (appendSlots j)=CloseoutFinalC10AppendWorkspaceInit.input b j) :
    ∃ finalBank, Step (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .right else .stay)) (Composition.machine (RecoveryFocus.machine countSlots CloseoutRowsOriginalCount.machine) (Composition.machine (DecompositionCountPosition.move (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then .left else .stay)) (RecoveryFocus.machine appendSlots CloseoutFinalC10AppendWorkspaceInit.machine)))) (countFuel+CloseoutFinalC10AppendWorkspaceInit.budget b+5) (fun _ => 0) actualBank (fun _ => 0) finalBank ∧ (∀ j,finalBank (cache j)=cacheData j) ∧ finalBank (countSlots 28)=UnaryTemplate.tape sys ∧ finalBank (countSlots 70)=UnaryTemplate.tape clauseCount ∧ finalBank (countSlots 72)=List.replicate clauseCount true ∧ finalBank (appendSlots 0)=List.replicate b true ∧ finalBank (appendSlots 20)=UnaryTemplate.tape (20*b+22) ∧ finalBank (appendSlots 39)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ finalBank (appendSlots 40)=List.replicate (CloseoutFinalC10AppendWorkspaceInit.capacity b) false ∧ (∀ v,(∀ i,countSlots i≠v) → (∀ i,appendSlots i≠v) → finalBank v=actualBank v) :=
  open RepairOrdinary LocalBitMultitape ExtDecompositionBatch RecoveryRootRound in
  by
    let HR : Fin B → Nat := (fun i : Fin B => if i=cache 13 ∨ i=cache 14 then 1 else 0)
    let rightDirs : Fin B → HeadMove := fun i => if i=cache 13 ∨ i=cache 14 then .right else .stay
    let leftDirs : Fin B → HeadMove := fun i => if i=cache 13 ∨ i=cache 14 then .left else .stay
    obtain ⟨mr,hmr,mrf,_ms⟩ := DecompositionCountPosition.move_run rightDirs (fun _ => 0) actualBank
    have hmrH : mr.final.heads=HR := by
      rw [mrf]
      funext i
      dsimp [HR,rightDirs]
      split_ifs <;> rfl
    have moveRight := Step.of_run hmr hmrH (congrArg Configuration.tapes mrf)
    obtain ⟨C,hC,keepC,Mt,Mr,S⟩ := hcount
    have hHC : ∀ i,HR (countSlots i)=CloseoutRowsOriginalCount.heads PCPPQueryClauseReuse.heads i := by
      intro i
      have eq13 : countSlots i=cache 13 ↔ i=(13 : Fin 19).castAdd 55 := by
        rw [←hfirst 13]
        exact hc.eq_iff
      have eq14 : countSlots i=cache 14 ↔ i=(14 : Fin 19).castAdd 55 := by
        rw [←hfirst 14]
        exact hc.eq_iff
      dsimp only [HR]
      simp only [eq13,eq14]
      refine Fin.addCases (m:=19) (n:=55) (fun j => ?_) (fun j => ?_) i
      · change (if j.castAdd 55=(13 : Fin 19).castAdd 55 ∨ j.castAdd 55=(14 : Fin 19).castAdd 55 then 1 else 0)=_
        simp only [Fin.castAdd_inj]
        rw [show j.castAdd 55=(j.castAdd 37).castAdd 18 from Fin.ext rfl,
          CloseoutRowsOriginalCount.heads,Fin.addCases_left,CloseoutCaseTwo.Metadata.heads,Fin.addCases_left]
        rfl
      · have n13 : Fin.natAdd 19 j≠(13 : Fin 19).castAdd 55 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
        have n14 : Fin.natAdd 19 j≠(14 : Fin 19).castAdd 55 := by intro he;have hv:=congrArg Fin.val he;dsimp at hv;omega
        rw [if_neg (by simp only [n13,n14,or_self,not_false_eq_true])]
        simp [CloseoutRowsOriginalCount.heads, CloseoutCaseTwo.Metadata.heads,Fin.addCases]
    have hAC : ∀ i,actualBank (countSlots i)=CloseoutRowsOriginalCount.input cacheData i := by
      intro i
      refine Fin.addCases (m:=19) (n:=55) (fun j => ?_) (fun j => ?_) i
      · rw [hfirst]
        rw [show j.castAdd 55=(j.castAdd 37).castAdd 18 from Fin.ext rfl,
          CloseoutRowsOriginalCount.input,Fin.addCases_left,CloseoutCaseTwo.Metadata.input,Fin.addCases_left]
        exact hcache j
      · rw [hfresh]
        simp [CloseoutRowsOriginalCount.input, CloseoutCaseTwo.Metadata.input,Fin.addCases]
    let AC := install countSlots actualBank C
    have countRun := (hC.dock countSlots hc HR actualBank hHC hAC).congr (dockH_existing countSlots HR _ hHC) rfl
    obtain ⟨ml,hml,mlf,_mts⟩ := DecompositionCountPosition.move_run leftDirs HR AC
    have hmlH : ml.final.heads=(fun _ => 0) := by
      rw [mlf]
      funext i
      dsimp [HR,leftDirs]
      split_ifs <;> rfl
    have moveLeft := Step.of_run hml hmlH (congrArg Configuration.tapes mlf)
    obtain ⟨A,hA,bkeep,width,copylog,resetlog⟩ := CloseoutFinalC10AppendWorkspaceInit.initialize_run b
    have hAA : ∀ i,AC (appendSlots i)=CloseoutFinalC10AppendWorkspaceInit.input b i := by
      intro i
      exact (install_other countSlots actualBank C _ (fun j => hdis j i)).trans (happend i)
    have appendRun := (hA.dock appendSlots ha (fun _ => 0) AC (by intro i;rfl) hAA).congr
      (dockH_existing appendSlots (fun _ => 0) _ (by intro i;rfl)) rfl
    have all := moveRight.seq (countRun.seq (moveLeft.seq appendRun))
    have ht : 1+1+(countFuel+1+(1+1+CloseoutFinalC10AppendWorkspaceInit.budget b))=countFuel+CloseoutFinalC10AppendWorkspaceInit.budget b+5 := by omega
    rw [ht] at all
    refine ⟨_,all,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro j
      rw [←hfirst j,install_other appendSlots AC A _ (fun i he => hdis (j.castAdd 55) i he.symm)]
      exact (install_slot countSlots hc actualBank C _).trans (keepC j)
    · rw [install_other appendSlots AC A _ (fun i he => hdis 28 i he.symm)]
      exact (install_slot countSlots hc actualBank C 28).trans S
    · rw [install_other appendSlots AC A _ (fun i he => hdis 70 i he.symm)]
      exact (install_slot countSlots hc actualBank C 70).trans Mt
    · rw [install_other appendSlots AC A _ (fun i he => hdis 72 i he.symm)]
      exact (install_slot countSlots hc actualBank C 72).trans Mr
    · exact (install_slot appendSlots ha AC A 0).trans bkeep
    · exact (install_slot appendSlots ha AC A 20).trans width
    · exact (install_slot appendSlots ha AC A 39).trans copylog
    · exact (install_slot appendSlots ha AC A 40).trans resetlog
    · intro v hvC hvA
      exact (install_other appendSlots AC A v hvA).trans (install_other countSlots actualBank C v hvC)
  



private theorem cache_injective
    (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
    (a : PointwisePCPPAlgorithm)
    (k : Nat)
    (D : Nat)
    (G : Nat)
    (E : Nat)
    (mode : Bool) :
    Function.Injective (CloseoutFinalC10ColdCacheAtAdmission.cacheSlot source a k D G E mode) :=
  open CloseoutWitness in
  by
    intro i j he
    have one := BoundedFamilySupport.slots_injective source a k D G E mode he
    have two := (Fin.castAdd_injective _ _) one
    have three := (Fin.castAdd_injective _ _) two
    have threeB := (Fin.castAdd_injective _ _) three
    have threeC := (Fin.castAdd_injective _ _) threeB
    have four := (Fin.castAdd_injective _ _) threeC
    have five := NativePipeline.Dock.slots_injective a D G (ColdNative.fields source k)
      (ColdNative.fields_injective source k) four
    have six := NativePolicy.Call.slots_injective a D (NativePipeline.counter G)
      (NativeScreen.slots_injective G) five
    exact ColdLegal.native_cache_injective a ((Fin.castAdd_injective _ _) six)
  



attribute [local irreducible] BoundedFamily.workspace CloseoutFinalC10SeedEngine.tapesOf
  CloseoutFinalC10ColdCacheAtAdmission.cacheSlot


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry
