import Proof.MachineModel.TopDownWorkspaceBoundedGateEntry

/-! Concrete admission data for the literal guarded endpoint. The capacity
parameters and cold cutoff are produced before k; the actual parser, paid
zero-head rewind, outer gate flag and original-input budget are fixed here.
The complete retained parser bank and admitted original-cache fact are exported.
The estimator continuation and its Runtime are not supplied by this module. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedAdmission
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
open WorkspaceGuardedWorker (input entry reference)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine
  CloseoutFinalC10ColdCacheRewind.machine

structure Capacity (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) where
  K : Nat
  E : Nat
  positive : 0<K
  bound : ∀ N, FamilyResources.capacity
    (ColdFamily.scale (fixedProjection sources) (CloseoutLanguage.selectedPCPP sources)
      p.degree p.clauseDegree p.copies (CompetitorRationalGap.zeta (constantsOf sources)) N)
    ≤ K*(N+1)^E

@[irreducible] def capacity (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) : Capacity sources p := by
  let h := FamilyResources.source_envelope (CloseoutLanguage.selectedPCPP sources)
    (fixedProjection sources).coefficient (fixedProjection sources).degrees.queries
    p.degree p.clauseDegree (CompetitorRationalGap.zeta (constantsOf sources)) p.copies
  exact ⟨Classical.choose h,Classical.choose (Classical.choose_spec h),
    (Classical.choose_spec (Classical.choose_spec h)).1,
    (Classical.choose_spec (Classical.choose_spec h)).2⟩

def coldCutoff (sources : EightSources) : Nat := 2^(CloseoutLanguage.selectedPCPP sources).minimumArity

def originalTapes (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k : Nat) : Nat :=
  WorkspaceBoundedGateEntry.originalTapes sources p k (capacity sources p).E

def originalProgram (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  WorkspaceBoundedGateEntry.originalProgram sources p k clock (coldCutoff sources)
    (capacity sources p).E (capacity sources p).K

def admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  TapeEmbedding.machine 1 (CloseoutFinalC10ColdCacheRewind.machine (originalProgram sources p k clock).2)

def preFuel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) : Nat :=
  2*WorkspaceBoundedGateEntry.fuel sources p k clock (coldCutoff sources)
    (capacity sources p).E (capacity sources p).K n+2

def Cached (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) {n : Nat} (x : BitInput n) (bits : List Bool)
    (A : Fin (originalTapes sources p k) → List Bool) : Prop :=
  ∃ H,CloseoutFinalC10ColdCacheAtAdmission.Cached (fixedProjection sources)
    (CloseoutLanguage.selectedPCPP sources) k (SelectedSource.hierarchy sources k clock).coefficient
    (padding sources k clock) p.clauseDegree p.degree (capacity sources p).E
    (SelectedSource.code sources k clock) x bits (Nat.le_max_right _ _) H A

theorem input_blank {t : Nat} (ht : 2≤t) (x bits : List Bool) :
    Fin.addCases (input x bits : Fin t → List Bool) (fun _ : Fin 1 => []) = input x bits := by
  funext i
  refine Fin.addCases (m:=t) (n:=1) ?_ ?_ i
  · intro j
    simp only [Fin.addCases_left,input,Fin.val_castAdd]
    rfl
  · intro j
    simp only [Fin.addCases_right,input,Fin.val_natAdd]
    rw [if_neg (by omega),if_neg (by omega)]

theorem zero_heads (t : Nat) :
    Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin 1 => 0) = (fun _ => 0) := by
  funext i
  exact Fin.addCases (fun _ => by rw [Fin.addCases_left]) (fun _ => by rw [Fin.addCases_right]) i

end
end NearCubicWires.P1TopDown.WorkspaceSelectedAdmission
