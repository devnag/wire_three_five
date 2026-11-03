import Proof.Wire_3_5.Primitive.Writers.DataRun
import Proof.Wire_3_5.Primitive.Writers.ReqBridge
import Proof.Wire_3_5.Primitive.SeedFix.TabThr

/-! # PA (d): the THR per-call data stage, interface (THR's `Data.data_step`)

P3:3049-3050 ("One-sided scores may be computed directly at a sampled row in polynomial time") and P3:3068-3084
(lem:primitive: a call reads its circuits, carriers and translation): a THR call's evaluators read the tuple's retained
bottoms as ONE gate table `gatesW h (tupleG Cs)` (`thrTableM a`, `a = 1 … 4`) and each carrier's doubled atoms
as `gatesW h (maskGates X)` (`carTableM`), with the pool's slice lengths (`Records.thrSlices`: the carriers, then the
tuple's occurrences). This file states the stage built once for the THR cells and the G3 (`GateThrWriterAt`):

* `thrCounts` (the carriers' sizes, then `|tupleG Cs|`);
* **`ThrDataStage`**: a machine on `Data`'s layout which, from the framed THR request word
  `reqW n true (thrCodes Cs) (carrier codes) tl` (`ReqBridge.reqW_thrReq`: `= (thrReq …).word ++ sfx` at
  `tl = natListWord translation ++ sfx`), `1^n`, `1^L`, `1^W`, runs within `cost` steps (`PolyBounded` in
  `K + n + L + W`, `K` bounding the codes' bit lengths, as `thrTableCost*_poly`)
  to a bank with `dataWord (thrCounts …)` on the output stream, the request kept, the tuple's table on `tabS` and each
  carrier's table on its slot's stream `3` (as `Data.data_step`), an unfilled carrier slot's stream `3` blank.

Paper quantities of the main type: the tuple's gate table `gatesW h (tupleG Cs)`, the carriers' tables, and the THR
pool's slice lengths. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data

/-- **The THR call's counts**: the carriers' sizes, then the tuple's bottom-occurrence count (the THR pool's slice
lengths up to the carriers' doubling, `Records.thrSlices`). -/
def thrCounts {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) :
    List ℕ :=
  carriers.map (·.length) ++ [(PrimT.ThrTab.tupleG Cs).length]

/-- **The THR per-call data stage** (interface): the machine, the tuple table's stream, the cost with its polynomial
bound, and the run from the THR request (the analogue of `Data.data_step`). -/
structure ThrDataStage where
  s : ℕ
  M : Machine (DS + 2 + DR + 1) s
  tabS : Fin (DS + 1)
  cost : ∀ {n : ℕ} (a' : ℕ), (Fin a' → NormalizedThresholdThresholdCircuit n) → List (Stars.Carrier n) → ℕ → ℕ → ℕ
  Cc : ℕ
  Dc : ℕ
  cost_le : ∀ {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (L W K : ℕ), 1 ≤ a' → a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ L) →
    (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) →
    (∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ K) →
    (∀ X ∈ carriers, natBitLength X.code ≤ K) → 2 ≤ n + L →
    ValidatorPolynomialDomination.PolyBounded (cost a' Cs carriers L W) (K + n + L + W) Cc Dc
  run : ∀ {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl : List Bool) (L W : ℕ), 1 ≤ a' → a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ L) →
    (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) → 2 ≤ n + L →
    natBitLength n + 1 ≤ 2 * W + 2 → 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2 →
    2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2 →
    (∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2) →
    (∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2) →
    2 * (unaryList (thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2 →
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ),
      Step M (cost a' Cs carriers L W) (fun _ => 0)
        (Fin.addCases (rawIn (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) n L W)
          (fun _ : Fin 1 => List.replicate 0 false))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape sOUT) = dataWord (thrCounts Cs carriers) ∧
      tout (sTape sIN) =
        RepairOrdinary.frame (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      tout (sTape tabS) = FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = []

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
