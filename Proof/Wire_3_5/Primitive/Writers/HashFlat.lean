import Proof.Wire_3_5.Primitive.Writers.SymFlat

/-! # PA (d), the HASH tape as one flat stream of units (the HASH writer loop's emissions)

The HASH writer (for C4.Hb; built on C6's tail with PA's FILTER unit pipeline, `UnitReady.filtPipe_ready`) is one
bounded loop over a flat index `j`; unit `j` appends `symEmit 1 0 (hashUnit …) j`: every HASH entry is ONE printed row
with ONE request, the aux FILTER row `hashRow … (auxEnum (q % nE)) G (q / nE) n` of cell `q / nE` and aux seed
`q % nE` (`WriterIface.hashExprs`). **`hashTape_flat`**: the units' concatenation, closed by `false`, is the HASH tape
`WriterIface.hashTape` (C4's `blockWord` of the single-row entries). Units per entry: `[true]` (entry open), `[true]`
(row open), the request's body, `[false]` (row close), `[false]` (entry close): `5` units.

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter of the THR primitive, P3:2220-2226). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashFlat
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.SymFlat NearCubicWires.SupplierPipeline

section Hash
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))

/-- The HASH entry `q`'s row: the aux FILTER row of cell `q / nE`, aux seed `q % nE`. -/
def hashRowQ (q : ℕ) : RowReq :=
  hashRow (I.starParams n hs) carriers (I.filterParams .thr n) (thrCallE alg I hs Cs carriers)
    (auxEnum alg I hs Cs carriers (q % nE alg I hs Cs carriers)) (thrPool (I.starParams n hs) Cs carriers).length
    (q / nE alg I hs Cs carriers) n

/-- The HASH request units (entry `q`, its only row, its only request). -/
def hashUnit (q _r _s : ℕ) : List Bool := unitBody (hashRowQ alg I hs Cs carriers q)

/-- The number of HASH entries `N²·nE`. -/
abbrev nHash : ℕ := (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 * nE alg I hs Cs carriers

theorem hashExprs_eq : hashExprs alg I hs Cs carriers =
    (List.range (nHash alg I hs Cs carriers)).map fun q => refOf (hashRowQ alg I hs Cs carriers q) := by
  unfold hashExprs hashBatch
  rw [List.map_map]
  rfl

/-- **The HASH tape is the writer loop's units, closed** (one printed row, one request per entry). -/
theorem hashTape_flat :
    (List.range (nHash alg I hs Cs carriers * (1 * (0 + 3) + 2))).flatMap
      (symEmit 1 0 (hashUnit alg I hs Cs carriers)) ++ [false] = hashTape alg I hs Cs carriers := by
  rw [units_blockWord 1 0 (nHash alg I hs Cs carriers) (hashUnit alg I hs Cs carriers)
    (fun q => [[hashRowQ alg I hs Cs carriers q]]) (fun _ _ => rfl) (fun q _ r hr => by
      have : r = 0 := by omega
      subst this
      simp [hashUnit])]
  unfold hashTape
  rw [hashExprs_eq, List.map_map]
  congr 1

end Hash

end NearCubicWires.WireExponent3_5.PrimAsm.HashFlat
