import Proof.MachineModel.GeneratedAmplifierRuntime

/-! The literal generated-table evaluator, with the required linear
input-length times address-width bound. The result is a RAW singleton;
only the ordinary input carrier is additionally framed. -/
namespace NearCubicWires.RepairOrdinary.GeneratedAmplifier
open LocalBitMultitape RadixSemantics SourceInterfaces ExecutableInterfaces RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem runtime_bound {n : ℕ} (f : BoolFunction n) (address : BitInput n) :
    Runtime.budget f address≤128*(payload f address).length*(n+1)+128 := by
  let L := (payload f address).length
  have hp : n+1≤2^n := Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hlen := payload_length f address
  have ht : 2^n≤L := by dsimp only [L]; omega
  have hn : n≤L := by omega
  have hw : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hm : n*n.bits.length≤L*(n+1) := Nat.mul_le_mul hn (by omega)
  have hi : value (List.ofFn address)+1≤L := (Nat.succ_le_of_lt (address_lt address)).trans ht
  have hl := Nat.mul_le_mul_right (4*n+7) hi
  have he : (frame n.bits++(boolFunctionTable f++frame (List.ofFn address))).length=L := by
    simp only [L,payload,List.append_assoc]
  change Runtime.budget f address≤128*L*(n+1)+128
  simp only [Runtime.budget,Entry.budget,Prepared.budget,Arity.budget,MatrixUnaryTemplate.budget,
    Lookup.cost,he]
  nlinarith

end NearCubicWires.RepairOrdinary.GeneratedAmplifier
