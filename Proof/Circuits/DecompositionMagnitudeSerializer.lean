import Proof.Circuits.DecompositionMagnitudeReady
import Proof.Circuits.DecompositionSerializerCount

/-! The actual native preparation endpoint docks into the ONE shared
serializer. This positive-magnitude tail uses the parsed width and byte
stream; a later physical nonzero branch selects it or the zero output. -/
namespace NearCubicWires.RepairOrdinary.DecompositionMagnitudeSerializer
open LocalBitMultitape RecoveryRootRound RepairRepresentation SignedSortKey
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 128) : Fin 136 :=
  if i=0 then 7 else if i=2 then 3 else if i=1 then 10 else ⟨i.val+8,by omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff,Fin.val_zero,Fin.val_one ]
  all_goals omega
theorem slots_fresh (i : Fin 128) (h0 : i≠0) (h2 : i≠2) : 10 ≤ (slots i).val := by
  unfold slots
  simp only [h0,h2,ite_false]
  split
  · decide
  · have h1 : i.val≠1 := by intro h; have : i=1 := Fin.ext h; contradiction
    have hz : i.val≠0 := fun h => h0 (Fin.ext h)
    change 10 ≤ i.val+8
    omega

noncomputable def machine := RecoveryFocus.machine slots PCPTraversal.machine


end NearCubicWires.RepairOrdinary.DecompositionMagnitudeSerializer
