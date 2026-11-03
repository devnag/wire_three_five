import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThr
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrBBase


noncomputable section
set_option maxRecDepth 4096


/-! # G3, the THR gate-frame writer, part 2: the budget and the writer at every call

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050), within the
preprocessing class (`prim:runtime`, P3:3105-3115). G2's fill count (`CvS`, `DvS`: `needW` covers the THR codes' bits
and the tuple's occurrence count too) and G2's cost shape, with the THR data stage (`ThrDataStage2`) for the SYM
stage:

* `occ_len_le`, `tupleG_len_le` (the tuple's occurrences are at most its circuits' description bits);
  `thr_call_facts`, `thr_data_hyps` (the THR stage's hypotheses from `I.Call`);
* `pool_bounds3` (the THR pool and the three slots' widths are at most `3·DC`, `one_tape_support`);
* `DCn3`, `costN3`, `cost_le3`, `pb_costN3` (`gtC D`, `gtD D`);
* **`gateThrAt D hD`**: `GeoIface2.GateThrWriterAt l F E_G c_G kclk coef A a ha` under `gtD D ≤ E_G.Apre`,
  `gtC D·2^(gtD D) ≤ c_G` (the stage instance `D`, its tuple table on `sSym 0 3`).

Paper quantity of the main type: C3a's gate field of the THR call's pool (P3:1655-1664) within the preprocessing
class. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4GateSym
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.SupplierPipeline
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces NearCubicWires.ValidatorPolynomialDomination

/-! ## The tuple's occurrences -/

/-! ## The THR stage's hypotheses at a call -/

section Data

/-! ## The THR pool's size and the slots' widths -/

end Data

/-! ## The THR writer's steps -/

/-! ## The THR writer at every THR call -/

section Ready
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem thr_call_facts (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (h : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) :
    carriers.length ≤ 2 ∧ (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) ∧ (∀ X ∈ carriers, X.WithinEnvelope 26) := by
  obtain ⟨_, hcar, hdesc, hcount, _, _, _⟩ := h
  exact ⟨hcount, fun i => hdesc i, hcar⟩

/-- **The THR gate-frame writer's run at every THR call of the family**, within the preprocessing class. -/
theorem gt_ready (D : PrimAsm.ThrData.ThrDataStage2) (hD : D.tabS = PrimAsm.Data.sSym 0 3)
    (hA : gtD D ≤ EG.Apre) (hc : gtC D * 2 ^ gtD D ≤ cG) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    PrimAsm.WriterIfaceJ.WriterRun (mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).M
      (cG * classBound EG .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
        (((gate0 l F).budget kclk coef A a ha).psiOf n))
      (mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).inS
      (mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).outS
      (thrReq n a' ha' Cs carriers translation).word
      (C4Geo.gateField (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)) := by
  refine stage_run (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS) _ _ _ ?_
  obtain ⟨hk, hd, he⟩ := thr_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation hcall
  have hn : 1 ≤ n := by
    have h1 := hs.2.1
    have h2 := hs.2.2.1
    omega
  obtain ⟨hL, hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu, hK, hKX⟩ :=
    thr_data_hyps Cs carriers ha' hk hd he (UnaryCalc.value DvS CvS n) (needW_le n)
  have hword : PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation) = (thrReq n a' ha' Cs carriers translation).word := by
    have := PrimAsm.ReqBridge.reqW_thrReq ha' Cs carriers translation []
    simpa using this
  rw [← hword]
  refine gt_run D hD DvS CvS _ ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers _ ha' hk _ rfl
    hL hLX h2 hcN hcA hcK hcx hcy hcu ?_
  obtain ⟨hP, hH⟩ := pool_bounds3 D hD ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
    (RepairRepresentation.natListWord translation) _ _ ha' hk hL hLX h2 hcN hcA hcK hcx hcy hcu
  have hDC := D.cost_le Cs carriers (UnaryCalc.value DvS CvS n) (UnaryCalc.value DvS CvS n)
    (UnaryCalc.value DvS CvS n) ha' hk hL hLX hK hKX h2
  have hwl : (PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation)).length ≤ PrimAsm.CallSize.wordBound 26 26 2 n := by
    rw [hword]
    exact PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha _ hcall
  have c1 := cost_le3 D _ n _ _ _ hwl (by unfold DCn3; exact hDC) hP hH
  have c2 := costN3_le D n
  have c3 := pre_class_le EG (gtC D) (gtD D) cG n (((gate0 l F).budget kclk coef A a ha).kOf n)
    (((gate0 l F).budget kclk coef A a ha).psiOf n) hn hA hc
  exact le_trans c1 (le_trans c2 c3)

/-- **The THR gate-frame writer** (`GeoIface2.GateThrWriterAt`): the machine `gtM D DvS CvS`, from
`frame (thrReq …).word` to C3a's gate field of the THR call's pool, at every call of the family (`a' = 0` included). -/
noncomputable def gateThrAt (D : PrimAsm.ThrData.ThrDataStage2) (hD : D.tabS = PrimAsm.Data.sSym 0 3)
    (hA : gtD D ≤ EG.Apre) (hc : gtC D * 2 ^ gtD D ≤ cG) :
    GeoIface2.GateThrWriterAt l F EG cG kclk coef A a ha :=
  ⟨mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS), fun n a' ha' Cs carriers translation hcall hs =>
    gt_ready l F EG cG kclk coef A a ha D hD hA hc n a' ha' Cs carriers translation hcall hs⟩

end Ready

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym

end
