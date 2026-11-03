import Proof.Wire_3_5.FinalPass.SymOcc
import Proof.Wire_3_5.FinalPass.SymPool

/-! # The printer's gate budget at a SYM call, part 2: the pool's and the expression's sizes

alg:eq-budget's `log₂(P_ex+1)` and `log₂ A` (P3:1897-1900) at a SYM call: the dense pool has
`|flips|·Σ_g |children| ≤ 4·2^k·8(n+1)^{26}·symBud` children (`P_ex`), so `P_ex + 1 ≤ 2^{k + cDa·L}` with `cDa` of the
decomposition algorithm alone; the child expression has `≤ n_T·N^8·2^{8ℓ}·2^8·T^{8R}` terms (`A`).
* `densePool_length_le`, `symPool_length_le`, `cDa`, **`symD_le`**;
* **`occ_sym`**: the printer's budget at a SYM call from `A ≤ 2^{eV}`, `eV ≤ A₁(k+L)`, under the floors.
Paper quantities of the main types: `P_ex` and `A` of alg:compiler at a SYM call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

/-- The dense pool has `|flips|·Σ_g |children|` children. -/
theorem densePool_length_le (a : RepairRepresentation.DecompositionAlgorithm) {n : ℕ}
    (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ) (flips : List (List Bool)) (Bud : ℕ)
    (hB : ∀ g ∈ gates, (ExtDecompositionBatch.children a g).length ≤ Bud) :
    (Pool.densePool a gates side width flips).flatten.length ≤ flips.length * (gates.length * Bud) := by
  unfold Pool.densePool
  rw [List.length_flatten]
  have hg : ∀ f ∈ flips, ((gates.map fun g => (ExtDecompositionBatch.children a g).map
      (Pool.pullDense side f width)).map List.length).sum ≤ gates.length * Bud := by
    intro f _
    rw [List.map_map]
    have : ∀ g ∈ gates, (List.length ∘ fun g => (ExtDecompositionBatch.children a g).map
        (Pool.pullDense side f width)) g ≤ Bud := fun g hg => by simpa using hB g hg
    calc _ ≤ (gates.map fun _ => Bud).sum := List.sum_le_sum this
      _ = gates.length * Bud := by simp
  induction flips with
  | nil => simp
  | cons f fl ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    have h1 := hg f List.mem_cons_self
    have h2 := ih fun f' hf' => hg f' (List.mem_cons_of_mem _ hf')
    omega

/-- The SYM pool has at most `8(n+1)^{26}` gates at a call (`≤ 2` carriers, `≤ 4` circuits). -/
theorem symPool_length_le {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (hcar : ∀ X ∈ carriers, X.WithinEnvelope 26) (hnc : carriers.length ≤ 2)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) :
    (Records.symPool Cs carriers).length ≤ 8 * (n + 1) ^ 26 := by
  rw [SymDec.pool_length]
  have h1 : (carriers.map (·.length)).sum ≤ carriers.length * (n + 1) ^ 26 := by
    calc _ ≤ (carriers.map fun _ => (n + 1) ^ 26).sum := List.sum_le_sum fun X hX => (hcar X hX).1
      _ = _ := by simp
  have h2 : (SymDec.cyOf Cs).sum ≤ a' * (n + 1) ^ 26 := by
    unfold SymDec.cyOf
    rw [List.sum_ofFn]
    calc _ ≤ ∑ _i : Fin a', (n + 1) ^ 26 := Finset.sum_le_sum fun i _ => by
          rw [length_symGates]; exact CallIndex.bottomCount_le (Cs i) (hd i)
      _ = _ := by simp
  have h3 := Nat.mul_le_mul_right ((n + 1) ^ 26) hnc
  have h4 := Nat.mul_le_mul_right ((n + 1) ^ 26) ha'
  omega

/-- The decomposition algorithm's constant in the dense pool's size. -/
def cDa (a : RepairRepresentation.DecompositionAlgorithm) : ℕ :=
  32 + Nat.clog 2 (a.coefficient * 4 ^ a.degree) + 26 * a.degree

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

