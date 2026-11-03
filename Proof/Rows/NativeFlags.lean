import Proof.Rows.NativeFlagsLoop

/-! Complete native circuit-list flag stream, including the final true offset
flag. The empty family produces that flag and actual count one. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_NativeFlags
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_UniformMinimumBounds
open PCJ45bee56da9f34d5a_NativeFlagsLoop
noncomputable section


def word {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q) :=
 output cs live x cs.length++[true]

theorem word_length {q : Nat} (cs : List (Circuit q)) (live : Finset (Fin q)) (x : BitInput q) :
 (word cs live x).length=(cs.map (fun c=>c.1.length+1)).sum+1 :=by
 simp only [word,output,List.take_length,List.length_append,List.length_cons,List.length_nil,Nat.zero_add]
 congr 1
 induction cs with
 | nil=>rfl
 | cons c cs ih=>
   simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,
    PCJ45bee56da9f34d5a_NativeCircuitFlags.flags,List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.zero_add] at ih ⊢
   omega

end
end PCJ45bee56da9f34d5a_NativeFlags
