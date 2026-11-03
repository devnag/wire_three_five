import Proof.Rows.NativeFamilyFlags
import Proof.Rows.NativeCircuitCodec
import Proof.Assembly.LiveRows

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymMeaning
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open scoped BigOperators
noncomputable section

/-! ## 1. The SYM circuits in the flag traversal's shape -/

def symGates {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List (NormalizedThresholdGate q) :=
  List.ofFn (fun i => (c.bottom i).gate)

def symTop {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List Bool := List.ofFn c.top

def circuits (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :=
  r.circuits.map (fun c => (symGates c, symTop c))

theorem symWord_eq {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) :
    PCJd4d1d9d7d1fa4313_Production.symWord c =
      PCJ45bee56da9f34d5a_NativeCircuitFlags.payload (symGates c) (symTop c) := by
  simp only [PCJd4d1d9d7d1fa4313_Production.symWord, PCJ45bee56da9f34d5a_NativeCircuitFlags.payload,
    symGates, symTop, List.length_ofFn, PCJ45bee56da9f34d5a_NativeGateLoop.stream]
  have hm : (List.ofFn c.bottom).map (fun g => g.gate) = List.ofFn (fun i => (c.bottom i).gate) := by
    rw [List.map_ofFn]; rfl
  rw [← hm, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro g _
  exact PCJ45bee56da9f34d5a_NativeCircuitCodec.native_gate g

theorem native_stream (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :
    PCJ45bee56da9f34d5a_NativeFlagsLoop.stream (circuits r) =
      r.circuits.flatMap (fun c => frame (PCJd4d1d9d7d1fa4313_Production.symWord c)) := by
  simp only [PCJ45bee56da9f34d5a_NativeFlagsLoop.stream, circuits, List.flatMap_map,
    PCJ45bee56da9f34d5a_NativeFlagsLoop.word, symWord_eq]

/-! ## 2. The flag word -/

/-- Circuit `c`'s block of bottom-gate flags (without its target flag). -/
def block {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) (I : Finset (Fin q)) (x : BitInput q) :
    List Bool :=
  (symGates c).map (fun g => residualConstant g I x)

/-! ## 3. Prefix counts -/

/-- The flag word of a block list: each block, then a `true` target flag. -/
def flagged (bs : List (List Bool)) : List Bool := bs.flatMap (fun b => b ++ [true])

theorem flagged_length (bs : List (List Bool)) :
    (flagged bs).length = ((bs.map (fun b => b.length + 1)).sum) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [flagged, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp

theorem take_app (A B C : List Bool) : (A ++ (B ++ C)).take (A.length + B.length) = A ++ B := by
  induction A with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add]
    induction B with
    | nil => simp
    | cons b B ih => simp [ih]
  | cons a A ih =>
    rw [List.cons_append, List.length_cons, show A.length + 1 + B.length = (A.length + B.length) + 1 by omega,
      List.take_succ_cons, ih, List.cons_append]

/-- Cutting the flag word at the end of block `c`'s gate flags. -/
theorem take_prefix (bs : List (List Bool)) (tail : List Bool) (c : Nat) (hc : c < bs.length) :
    (flagged bs ++ tail).take ((flagged (bs.take c)).length + (bs[c]'hc).length) =
      flagged (bs.take c) ++ bs[c]'hc := by
  have hsplit : bs = bs.take c ++ (bs[c]'hc :: bs.drop (c+1)) := by
    rw [← List.drop_eq_getElem_cons hc, List.take_append_drop]
  have hw : flagged bs ++ tail =
      flagged (bs.take c) ++ (bs[c]'hc ++ ([true] ++ (flagged (bs.drop (c+1)) ++ tail))) := by
    conv_lhs => rw [hsplit]
    simp only [flagged, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hw, take_app]

/-! ## 4. Cumulative equality is per-block equality -/

theorem map_take_sum {α : Type} (l : List α) (F : α → Nat) (c : Nat) :
    ((l.take c).map F).sum = ∑ i ∈ Finset.range c, (l.map F).getD i 0 := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    cases c with
    | zero => simp
    | succ c =>
      rw [List.take_succ_cons, List.map_cons, List.sum_cons, ih, Finset.sum_range_succ']
      simp only [List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
      omega

/-! ## 5. The per-slot numbers and the SYM verdict -/

variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-- Number of bottom gates of circuit `c` (0 past the last circuit): request-only, cell-free. -/
def gateCount (c : Nat) : Nat := (r.circuits.map (fun k => (symGates k).length)).getD c 0

/-- Driver length for slot `c`: the flag position just after circuit `c`'s last gate flag. -/
def driverLen (c : Nat) : Nat :=
  if c < r.circuits.length then (∑ i ∈ Finset.range c, (gateCount r i + 1)) + gateCount r c else 0

/-- The offset tuple, extended by `0`. -/
def offsetN (offset : Fin r.circuits.length → Nat) (c : Nat) : Nat :=
  if h : c < r.circuits.length then offset ⟨c, h⟩ else 0

/-- Target for slot `c`: the cumulative target count. -/
def targetCount (offset : Fin r.circuits.length → Nat) (c : Nat) : Nat :=
  if c < r.circuits.length then (∑ i ∈ Finset.range c, (offsetN r offset i + 1)) + offsetN r offset c
  else 0

theorem driverLen_eq (I : Finset (Fin r.q)) (x : BitInput r.q) (c : Nat) (hc : c < r.circuits.length)
    (hc' : c < (r.circuits.map (fun k => block k I x)).length) :
    driverLen r c = (flagged ((r.circuits.map (fun k => block k I x)).take c)).length +
      ((r.circuits.map (fun k => block k I x))[c]'hc').length := by
  unfold driverLen
  rw [if_pos hc, flagged_length]
  have h1 : ((List.take c (r.circuits.map (fun k => block k I x))).map (fun b => b.length + 1)).sum =
      ∑ i ∈ Finset.range c, (gateCount r i + 1) := by
    rw [map_take_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < r.circuits.length := by have := Finset.mem_range.mp hi; omega
    simp [gateCount, block, List.getD_eq_getElem?_getD, hi']
  have h2 : ((r.circuits.map (fun k => block k I x))[c]'hc').length = gateCount r c := by
    simp [gateCount, block, List.getD_eq_getElem?_getD, hc]
  rw [h1, h2]

/-- The driver never runs past the flag word. -/
theorem driverLen_le (I : Finset (Fin r.q)) (x : BitInput r.q) (c : Nat) :
    driverLen r c ≤ (flagged (r.circuits.map (fun k => block k I x)) ++ [true]).length := by
  by_cases hc : c < r.circuits.length
  · have hc' : c < (r.circuits.map (fun k => block k I x)).length := by simpa using hc
    have ht := take_prefix (r.circuits.map (fun k => block k I x)) [true] c hc'
    have hl := congrArg List.length ht
    rw [driverLen_eq r I x c hc hc']
    simp only [List.length_take, List.length_append, List.length_singleton] at hl ⊢
    omega
  · unfold driverLen
    rw [if_neg hc]
    exact Nat.zero_le _

/-- The traversal's source word is the request's own SYM native word. -/
theorem native_eq (four : r.circuits.length ≤ 4) (L target : Nat) :
    PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (circuits r) =
      (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).nativeWord := by
  unfold PCJ45bee56da9f34d5a_NativeFamilyFlags.source PCJ45bee56da9f34d5a_CircuitCountCopy.source
  rw [native_stream]
  simp only [circuits, List.length_map, PCJd4d1d9d7d1fa4313_Production.Request.nativeWord,
    List.append_assoc]

end
end RowsConstruction.SymMeaning
