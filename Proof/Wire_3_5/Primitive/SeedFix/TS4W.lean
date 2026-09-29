import Proof.Wire_3_5.Primitive.SeedFix.TS4L

/-! # thrStage4U, part 16: **`thrStage4U : ∀ l, ThrStage4U l`**

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231 (the THR call's numbers, computed once per call), P3:3083-3086 (the named
carriers), P3:3425-3430 (the THR filter's cap `B_T`), P3:3071-3091 ("the preprocessing … runs in time polynomial in
`n`") and P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`"): at every call family of the gate, the v4 data
stage is PA's v2 stage plus `m3M` on `x3 = thrStageRoom (gate0 l F).alg` extra tapes; its time `cost3G` and W6's
capacity need `needT` are polynomial, the degrees fixed by the literals, the coefficients by `c_r`:

* `fuel_le` (the run's fuel within `cost3G`), **`run3G`** (`ThrDataStage4.run3` at the gate);
* **`stage4At`** (the family's `ThrDataStage4`, `x3 := W6.thrStageRoom (gate0 l F).alg`), `stage4At_x3`;
* **`thrStage4U : ∀ l, ThrData.ThrStage4U l`** (degree `max (DcG l) (NDeg l)`, coefficient `CcG l c_r + NCoef l c_r`).

Paper quantities of the main type: the data word `dataWord (hashNums … ++ thrCounts Cs carriers)`, its cost and W6's
capacity need, both polynomial. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer

variable (l : Literals)

/-- The run's fuel (the hash writer within `19W + 4`) is within `cost3G`. -/
theorem fuel_le (cr : ℕ) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (L W : ℕ) (hs : List ℕ) (hq : qhCost hs ≤ 19 * W + 4) :
    2 * m3Fuel (W6.litAlg l) 1 cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) Cs carriers L W hs + 2 + 1 ≤
      cost3G l cr Cs carriers L W := by
  unfold m3Fuel cost3G; omega

theorem unary_len_left (a b : List ℕ) : (unaryList a).length ≤ (unaryList (a ++ b)).length := by
  rw [W6.unaryList_append, List.length_append]; omega

/-- **`ThrDataStage4.run3` at the gate** (`alg = litAlg l`, `D = 1`, the THR cap `capTOf c_r n …`). -/
theorem run3G (cr : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ P.n + L) (hcN : natBitLength P.n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList (hashNums P Cs carriers (W6.litAlg l) 1 (capTOf cr P.n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)) ++ thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hneed : needT l cr P.n ≤ 2 * W + 2) :
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ) (J : Fin (t4X (W6.litAlg l)) → List Bool),
      Step (m3M (W6.litAlg l) 1 cr (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)) (cost3G l cr Cs carriers L W) (fun _ => 0)
        (Fin.addCases (m := DS + 2 + DR + 1) (n := t4X (W6.litAlg l)) (motive := fun _ => List Bool)
          (Fin.addCases (rawIn (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => [])) (fun _ => 0)
        (Fin.addCases (m := DS + 2 + DR + 1) (n := t4X (W6.litAlg l)) (motive := fun _ => List Bool)
          (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J) ∧
      (∀ j, (J j).length ≤ cost3G l cr Cs carriers L W) ∧
      tout (sTape sOUT) = dataWord (hashNums P Cs carriers (W6.litAlg l) 1 (capTOf cr P.n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)) ++ thrCounts Cs carriers) ∧
      tout (sTape sIN) = RepairOrdinary.frame (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      tout (sTape (sSym 0 3)) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = [] := by
  have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
  have hml : (carriers.map Stars.Carrier.code).length = carriers.length := List.length_map _
  have hKb : ∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ W := fun c hc => by
    have h := hcx c hc
    rw [PrimAsm.ParseNat.natWord_length] at h
    omega
  have hN0 := p0need_of l cr P.n W (ReqBridge.thrCodes Cs).length (carriers.map Stars.Carrier.code).length
    (by omega) (by omega) hneed
  have hn1 : 1 ≤ P.n := by have := P.two_le_r; have := P.four_r_le_n; omega
  have hc1 : 1 ≤ (capTOf cr P.n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)) := capTL_pos l cr P.n
  have hok : PrimThrW.TopFront2.TF2Ok Cs (carriers.map Stars.Carrier.code) (W + (P.n + 1) ^ 26) := by
    refine ⟨by omega, by omega, by omega, by rw [hml]; omega, fun x hx => ?_, fun y hy => ?_⟩
    · have := hcx x hx; omega
    · have := hcy y hy; omega
  have hW : W6.needW (W6.litAlg l) 1 (P.n + (capTOf cr P.n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l))) ≤ W + (P.n + 1) ^ 26 := needW_of l cr P.n W hneed
  have hq : qhCost (hashNums P Cs carriers (W6.litAlg l) 1 (capTOf cr P.n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l))) ≤ 19 * W + 4 := by
    refine qh_le _ W ?_
    have := unary_len_left (hashNums P Cs carriers (W6.litAlg l) 1 (capTOf cr P.n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l))) (thrCounts Cs carriers)
    omega
  have hf := fuel_le l cr Cs carriers L W _ hq
  refine (m3_run (W6.litAlg l) 1 cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) P Cs carriers tl L W ha hk
    hL hLX h2 hcN hcA hcK hcx hcy hcu hd hKb hN0 hn1 hc1 hok hW).elim fun tout h => h.elim fun m h' => h'.elim
    fun J hJ => ?_
  exact ⟨tout, m, J, hJ.1.enlarge (le_trans (Nat.le_succ _) hf), fun j => (hJ.2.1 j).trans hf, hJ.2.2⟩

/-- **The v4 data stage at one call family of the gate** (`x3 = thrStageRoom (gate0 l F).alg`). -/
noncomputable def stage4At (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
      (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap) where
  toThrDataStage2 := ThrData.thrDataStage2
  x3 := W6.thrStageRoom (gate0 l F).alg
  s3 := _
  M3 := m3M (W6.litAlg l) 1 F.cr (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)
  cost3 := fun a' Cs carriers L W => cost3G l F.cr Cs carriers L W
  Cc3 := CcG l F.cr
  Dc3 := DcG l
  cost3_le := fun Cs carriers L W K ha hk hL hLX hK hKX h2 =>
    cost3G_le l F.cr Cs carriers L W K ha hk hL hLX hK hKX h2
  need := needT l F.cr
  Kn := NCoef l F.cr
  Dn := NDeg l
  need_le := needT_le l F.cr
  run3 := run3G l F.cr

/-- **`thrStage4U`: the v4 data stage at every call family of the gate, uniform constants** (the degree
`max (DcG l) (NDeg l)` fixed by the literals, the coefficient `CcG l c_r + NCoef l c_r` by `F`). -/
noncomputable def thrStage4U : ∀ l, ThrData.ThrStage4U l := fun l _ =>
  ⟨max (DcG l) (NDeg l), ⟨0, 0, 0, 0, 0, 0, 0, 0⟩, 0, fun F _ _ _ =>
    ⟨CcG l F.cr + NCoef l F.cr, fun kclk coef A a ha => ⟨stage4At l F kclk coef A a ha, le_refl _, le_refl _⟩⟩⟩

end NearCubicWires.WireExponent3_5.PrimT.TS4
