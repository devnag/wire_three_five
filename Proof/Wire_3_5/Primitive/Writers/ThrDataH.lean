import Proof.Wire_3_5.Primitive.Writers.ThrBigS
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4

/-! # c4 THR block, the THR stage's data stage and hash bits at one call

P3:2543-2558, 2596-2604 (the THR call's numbers, computed once per call) and P3:2331-2333 (the fixed hash's bits): the
two premises of `thr_call_run` about the stage's input `thrReq.word ++ hbF`:
* **`thr_hd`**: the v4 data stage (`ThrData.ThrDataStage4.run3`) on the THR writer's input (the request parse absorbs
  the hash suffix in its free tail, `ReqBridge.reqW_thrReq`), the data word `hashNums ++ thrCounts`;
* **`thr_hxe`**: the hash bits' program (`ThrHB.hbX_spec`) marks `hbF` on its stream from the same input.

Paper quantities of the main types: the THR call's data word and its fixed hash's bits. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars

/-- **The THR data stage at one call** (the v4, `run3`), on the THR writer's input `thrReq.word ++ hbF`. -/
theorem thr_hd {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
    (S : ThrData.ThrDataStage4 alg Dexp capT) (P : StarParams) {a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n)) (translation : List ℕ)
    (hbF : List Bool) (L W : ℕ) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ P.n + L) (hcN : natBitLength P.n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcu : 2 * (Data.unaryList (ThrData.hashNums P Cs carriers alg Dexp (capT P.n) ++ ThrData.thrCounts Cs carriers)).length
      + 2 ≤ 2 * W + 2)
    (hd26 : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hneed : S.need P.n ≤ 2 * W + 2) :
    ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ) (J : Fin S.x3 → List Bool),
      Step S.M3 (S.cost3 a Cs carriers L W) (fun _ => 0)
        (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := S.x3) (motive := fun _ => List Bool)
          (Fin.addCases (Data.rawIn ((thrReq P.n a ha Cs carriers translation).word ++ hbF) P.n L W)
            (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := Data.DS + 2 + Data.DR + 1) (n := S.x3) (motive := fun _ => List Bool)
          (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J) ∧
      tout (sTape Data.sOUT) = Data.dataWord (ThrData.hashNums P Cs carriers alg Dexp (capT P.n) ++
        ThrData.thrCounts Cs carriers) ∧
      tout (sTape Data.sIN) = frame ((thrReq P.n a ha Cs carriers translation).word ++ hbF) := by
  rw [← ReqBridge.reqW_thrReq ha Cs carriers translation hbF]
  obtain ⟨tout, m, J, hst, -, hO, hI, -⟩ := S.run3 P Cs carriers (RepairRepresentation.natListWord translation ++ hbF)
    L W ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu hd26 hneed
  exact ⟨tout, m, J, hst, hO, hI⟩

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
