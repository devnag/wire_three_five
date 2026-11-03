import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymR
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Primitive.Writers.SymDataCost
import Proof.Wire_3_5.Primitive.Writers.ReqBridge
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Proof.MachineModel.OrdinaryMatrixPacketCapacityCost
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymBBase


noncomputable section
set_option maxRecDepth 4096


/-! # G2, the SYM gate-frame writer, part 4: the budget and the writer at every call

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050), and the call's
preprocessing is polynomial in `n` (`prim:runtime`, P3:3105-3115). This part fixes the writer's fill count and bounds its
steps at every SYM call of the gate's family:

* `needW`, the fill count's coefficient and degree `CvS`, `DvS` (`needW_le`: `W = CvS·(n+1)^DvS` covers the codes'
  bits and the envelopes, PA's `CallSize`); `sym_call_facts`, `sym_data_hyps` (PA's data stage's hypotheses from
  `I.Call`);
* `pool_bounds`: the pool's size and the slots' widths are at most `6·DC` (the tables are written within the data
  stage's `DC` steps, `one_tape_support`);
* `cost_le`, `pb_costN`: the writer's steps are at most `costN n`, polynomially bounded (`gsC`, `gsD`);
* `pre_class_le`: `gsC·(n+1)^gsD ≤ c_G·classBound E_G .preprocessing n k ψ` once `gsD ≤ E_G.Apre`,
  `gsC·2^gsD ≤ c_G`;
* **`gateSymAt`**: `GeoIface2.GateSymWriterAt l F E_G c_G kclk coef A a ha` (the machine `gsM DvS CvS`).

Paper quantity of the main type: C3a's gate field of the call's pool (P3:1655-1664) within the preprocessing class. -/

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

/-! ## Monotone costs -/

/-! ## The fill count -/

/-! ## The data stage's hypotheses at a call -/

section Data

/-! ## The pool's size and the slots' widths -/

end Data

/-! ## The writer's steps -/

/-! ## The writer at every SYM call -/

section Ready
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem sym_call_facts (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (h : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation)) :
    carriers.length ≤ 2 ∧ (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) ∧ (∀ X ∈ carriers, X.WithinEnvelope 26) := by
  obtain ⟨_, hcar, hdesc, hcount, _, _, _⟩ := h
  exact ⟨hcount, fun i => hdesc i, hcar⟩

/-- **The SYM gate-frame writer's run at every SYM call of the family**, within the preprocessing class. -/
theorem gs_ready (hA : gsD ≤ EG.Apre) (hc : gsC * 2 ^ gsD ≤ cG) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    PrimAsm.WriterIfaceJ.WriterRun (mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).M
      (cG * classBound EG .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
        (((gate0 l F).budget kclk coef A a ha).psiOf n))
      (mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).inS
      (mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).outS
      (symReq n a' ha' Cs carriers translation).word (C4Geo.gateField (PrimAsm.Records.symPool Cs carriers)) := by
  refine stage_run (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS) _ _ _ ?_
  obtain ⟨hk, hd, he⟩ := sym_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation hcall
  have hn : 1 ≤ n := by
    have h1 := hs.2.1
    have h2 := hs.2.2.1
    omega
  obtain ⟨hL, hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu, hK, hKX⟩ :=
    sym_data_hyps Cs carriers ha' hk hd he (UnaryCalc.value DvS CvS n) (needW_le n)
  have hword := PrimAsm.ReqBridge.reqW_symReq ha' Cs carriers translation
  rw [← hword]
  refine gs_run DvS CvS _ n a' Cs carriers _ ha' hk _ rfl hL hLX h2 hcN hcA hcK hcx hcy hcu ?_
  obtain ⟨hP, hH⟩ := pool_bounds Cs carriers (RepairRepresentation.natListWord translation) _ _ ha' hk hL hLX h2
    hcN hcA hcK hcx hcy hcu
  have hDC := PrimAsm.Data.coreCost_poly Cs carriers (UnaryCalc.value DvS CvS n) (UnaryCalc.value DvS CvS n)
    (UnaryCalc.value DvS CvS n) ha' hk hL hLX hK hKX h2
  have hwl : (PrimAsm.Data.reqW n false (PrimAsm.Data.symCodes a' Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation)).length ≤ PrimAsm.CallSize.wordBound 26 26 2 n := by
    rw [hword]
    exact PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha _ hcall
  have c1 := cost_le _ n _ _ _ hwl (by unfold DCn; exact hDC) hP hH
  have c2 := costN_le n
  have c3 := pre_class_le EG gsC gsD cG n (((gate0 l F).budget kclk coef A a ha).kOf n)
    (((gate0 l F).budget kclk coef A a ha).psiOf n) hn hA hc
  omega

/-- **The SYM gate-frame writer** (`GeoIface2.GateSymWriterAt`): the machine `gsM DvS CvS`, from
`frame (symReq …).word` to C3a's gate field of the call's pool, at every call of the family. -/
noncomputable def gateSymAt (hA : gsD ≤ EG.Apre) (hc : gsC * 2 ^ gsD ≤ cG) :
    GeoIface2.GateSymWriterAt l F EG cG kclk coef A a ha :=
  ⟨mkStage (gsM DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS), fun n a' ha' Cs carriers translation hcall hs =>
    gs_ready l F EG cG kclk coef A a ha hA hc n a' ha' Cs carriers translation hcall hs⟩

end Ready

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym

end
