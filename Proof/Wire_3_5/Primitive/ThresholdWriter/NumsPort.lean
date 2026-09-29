import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins

/-! # THR, W6 in PORT form: `NumsPort`, the THR numbers for any layout

P3:2543-2558, 2596-2599, 2604, 2150-2157 (as `Joins.ThrNumsSpec`): the THR call's numbers. W6 is a TM-level machine
(the decomposition algorithm's constructor, the primitive-modulus search), so a consumer in another layout (finalpass
stages 4/8, the THR cells) docks it on ports by base `Block.focusedInto`, as `WalkBankProducer`:

* `numsInPorts w ncar capT` (port `0` the framed request word, `1` `1^{ncar}`, `2` `1^{cap_T}`, `3 … 19` blank),
  `numsOutPorts … v` (the inputs kept; ports `3 … 16` the fourteen values in unary, `17` the primes, `18` the level
  records, `19` the modulus word);
* **`NumsPort alg Dexp`**: one machine on `20 + x` tapes; for every THR tuple, from the in-ports (scratch blank, heads
  `0`), within `cost (n + cap_T)`, every head back at `0`, the out-ports at `thrNumVals P Cs alg Dexp ncar capT`, residues
  bounded by the cost.

Paper quantities of the main type: as `ThrNumsSpec` (`|𝒢|`, `K`, the cutoff, `Σp`, `τ₀`, the fixed hash's `M, A, B_*, J,
t, e, ℓ₀, p`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.NumsP
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimThrW.Joins NearCubicWires.SupplierPipeline

/-- W6's in-ports: the framed request word, `1^{ncar}`, `1^{cap_T}`, then seventeen blank output ports. -/
def numsInPorts (w : List Bool) (ncar capT : ℕ) : Fin 20 → List Bool := fun i =>
  if i.val = 0 then frame w else if i.val = 1 then List.replicate ncar true
  else if i.val = 2 then List.replicate capT true else []

/-- W6's out-ports: the inputs kept, the fourteen values in unary on `3 … 16`, the primes on `17`, the level records on
`18`, the modulus word on `19`. -/
def numsOutPorts (w : List Bool) (ncar capT : ℕ) (v : ThrNumVals) : Fin 20 → List Bool := fun i =>
  if i.val = 0 then frame w else if i.val = 1 then List.replicate ncar true
  else if i.val = 2 then List.replicate capT true
  else if h : i.val < 17 then List.replicate (v.get ⟨i.val - 3, by omega⟩) true
  else if i.val = 17 then Data.unaryList (primesList v.cut)
  else if i.val = 18 then winRecs (thrMP v.M v.A v.Bs v.den)
  else frame (SignedSortKey.binary v.ell0 v.pMod)

theorem numsOutPorts_val (w : List Bool) (ncar capT : ℕ) (v : ThrNumVals) (k : Fin 14) :
    numsOutPorts w ncar capT v ⟨k.val + 3, by omega⟩ = List.replicate (v.get k) true := by
  have h1 : k.val + 3 ≠ 0 := by omega
  have h2 : k.val + 3 ≠ 1 := by omega
  have h3 : k.val + 3 ≠ 2 := by omega
  have h4 : k.val + 3 < 17 := by omega
  simp only [numsOutPorts, h1, h2, h3, h4, if_false, dif_pos]
  congr 2

end NearCubicWires.WireExponent3_5.PrimThrW.NumsP
