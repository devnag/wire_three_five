import Proof.Wire_3_5.Primitive.ThresholdWriter.PortsE

/-! # W6 in port form, v3: `NumsPort3`, the THR numbers with the count in-port `1^V`

P3:2543-2558, 2596-2599, 2604, 2150-2157 (as `Joins.ThrNumsSpec`): the THR call's numbers. v2 (`PortsE.NumsPort2`) asks
for a cost polynomial in `n + cap_T` for EVERY carrier list, but the only verified front end (W16, `TF3Cost.topFront3`,
through PA's request split) copies the carriers' codes too, so its count `V` must dominate them (`TopFront2.TF2Ok`).
Both consumers already hold such a `V` (its word capacity; the THR unit: `value D2 C2 n`), so v3 takes it as an
in-port, exactly as the front end does:

* `nums3InPorts w ncar capT V` (ports `0 … 19` as `NumsP.numsInPorts`, port `20` the count `1^V`),
  `nums3OutPorts w ncar capT V v` (ports `0 … 19` as `NumsP.numsOutPorts`, port `20` kept);
* **`NumsPort3 alg Dexp`**: one machine on `21 + x` tapes; for every THR tuple (`a' ≤ 4`) with `TF2Ok Cs codes V`, from
  the in-ports (scratch blank, heads `0`), within `cost (n + V + cap_T)` (the `n` term: `K = 8(|𝒢|+1)n^D` is unary and
  at `a' = 0` `V` may be about `log n`), every head at `0`, the out-ports, residues bounded by the cost;
* `nums3Out_low`, `nums3Out_val`, `nums3Out_count`.

Paper quantities of the main type: as `NumsPort2` (`|𝒢|`, `K`, the cutoff, `Σp`, `τ₀`, the fixed hash's
`M, A, B_*, J, t, e, ℓ₀, p`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.Nums3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimThrW.Joins NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimThrW.NumsP

/-- W6's in-ports, v3: NumsPort's twenty, then the count `1^V` on port `20`. -/
def nums3InPorts (w : List Bool) (ncar capT V : ℕ) : Fin 21 → List Bool := fun i =>
  if h : i.val < 20 then numsInPorts w ncar capT ⟨i.val, h⟩ else List.replicate V true

/-- W6's out-ports, v3: NumsPort's twenty, then the count kept on port `20`. -/
def nums3OutPorts (w : List Bool) (ncar capT V : ℕ) (v : ThrNumVals) : Fin 21 → List Bool := fun i =>
  if h : i.val < 20 then numsOutPorts w ncar capT v ⟨i.val, h⟩ else List.replicate V true

theorem nums3Out_low (w : List Bool) (ncar capT V : ℕ) (v : ThrNumVals) (i : Fin 20) :
    nums3OutPorts w ncar capT V v ⟨i.val, by omega⟩ = numsOutPorts w ncar capT v i := by
  unfold nums3OutPorts
  rw [dif_pos i.isLt]

theorem nums3Out_val (w : List Bool) (ncar capT V : ℕ) (v : ThrNumVals) (k : Fin 14) :
    nums3OutPorts w ncar capT V v ⟨k.val + 3, by omega⟩ = List.replicate (v.get k) true := by
  rw [nums3Out_low w ncar capT V v ⟨k.val + 3, by omega⟩]
  exact numsOutPorts_val w ncar capT v k

theorem nums3Out_count (w : List Bool) (ncar capT V : ℕ) (v : ThrNumVals) :
    nums3OutPorts w ncar capT V v ⟨20, by omega⟩ = List.replicate V true := by
  unfold nums3OutPorts
  rw [dif_neg (by decide)]

end NearCubicWires.WireExponent3_5.PrimThrW.Nums3
