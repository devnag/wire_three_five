import Proof.Wire_3_5.Primitive.SeedFix.C4HkH

/-! # The HASH stage, part 9: the stage's run

"Greedily choose a child with no larger value [...] the printed decisions are the fixed hash's bits" (P3:2327-2336);
the THR writer's input `req.word ++ frame hashBits`. **`hashLay_run`**: from any HASH setup run to a
C4H-a `HBank2` bank (whose kept words hold the Hb ruler `1^{T2 + s_h}` and `1^{T2}`), the HASH stage (`C4Wrap.wrapM`:
the setup and the pre-loop stage, the docked decision loop of a `HashFamAt2` family, the docked finisher) ends with
`frame (w ++ frame bits)` on port `2`, `bits` the family's decisions, within any budget above its `wrapCost`.

Paper quantity of the main type: the HASH stage's output `frame (w ++ frame bits)` (the THR writer's input). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- The HASH stage's pre-loop setup: the setup, then the pre-loop stage. -/
noncomputable def setupH {x s0 : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (M0 : Machine (3 + x) s0)
    (hkT : Fin 94 → Fin (3 + x)) (off : ℕ) (hr : off + 12 ≤ 3 + x) (n : ℕ) :=
  Composition.machine M0 (preZ off hr hkT n ⟨L.gRR.val, by have := L.gRR.isLt; omega⟩)

/-- **The HASH stage's run.** -/
theorem hashLay_run {x s0 c0 : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (A : C4Iface.AsmStage)
    (wa : RepairRepresentation.WilliamsAlgorithm) (PRE POST : List Bool) (KW : Fin 94 → List Bool)
    (q uu W sh : ℕ) (bits : List Bool) (hF : HashFamAt2 A wa PRE POST KW q uu W sh bits)
    (M0 : Machine (3 + x) s0) (w v : List Bool) (B : Fin (3 + x) → List Bool)
    (h0 : Step M0 c0 (fun _ => 0) (SeedFixTypes.stageIn x w v) (fun _ => 0) B)
    (ρ : ℕ) (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x)) (off : ℕ)
    (hB : HBank2 L hLx B w v PRE POST KW q uu ρ hkT hqT off) (T2 : ℕ)
    (hKL : KW ⟨23, by omega⟩ = List.replicate (T2 + sh) true) (hKT : KW ⟨16, by omega⟩ = List.replicate T2 true)
    (hRc : hF.F.cellCost + 1 ≤ 2 ^ ρ)
    (hroom : off + 12 + (hF.F.T + 1 + 1 + 1) + (2 + 2 + 0 + 1) ≤ 3 + x) (Bd : ℕ)
    (hBd : wrapCost (c0 + 1 + (2 * preCost w T2 sh + 2 + 1 + (2 * 2 ^ ρ + 4))) hF.F (2 ^ ρ) (finCost w bits) + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run ⟨x, _, wrapM (setupH L hLx M0 hkT off (by omega) (hF.F.T + 1 + 1 + 1)) hF.F (off + 12)
      (by omega) (hashExt L hLx A wa hkT hqT off (by omega) hF.F.T) finM (off + 12 + (hF.F.T + 1 + 1 + 1)) hroom
      (finExtH off (by omega))⟩ Bd w v (frame (w ++ frame bits)) := by
  obtain ⟨B2, s2, hP⟩ := pre_run off (by omega) hkT L hLx B w v PRE POST KW q uu ρ hqT hB T2 sh hKL hKT
    (hF.F.T + 1 + 1 + 1) (by omega)
  obtain ⟨tout, hf, hout⟩ := fin_spec.2 w bits
  have r := C4Wrap.wrap_run (setupH L hLx M0 hkT off (by omega) (hF.F.T + 1 + 1 + 1)) w v B2 (Step.seq h0 s2) hF.F
    (2 ^ ρ) (2 ^ ρ + 1) (off + 12) (by omega) (hashExt L hLx A wa hkT hqT off (by omega) hF.F.T)
    (hash_entry L hLx A wa PRE POST KW q uu W sh bits hF B w v ρ hkT hqT off hB (by omega) (by omega) B2 hP hRc)
    finM _ tout hf (off + 12 + (hF.F.T + 1 + 1 + 1)) hroom (finExtH off (by omega)) fiO
    (hash_fin L hLx A wa PRE POST KW q uu W sh bits hF B w v ρ hkT hqT off hB (by omega) (by omega) B2 hP hroom) Bd hBd
  rw [hout] at r
  exact r

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
