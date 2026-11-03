import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4HkI
import Proof.Wire_3_5.FinalPass.HashFree2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashFree
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4HkJBase


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH stage, part 10: one stage for every THR call, and its run at a call

"Greedily choose a child with no larger value [...] the printed decisions are the fixed hash's bits" (P3:2327-2336).
The HASH stage's machine does not depend on the call: its loop is the loop of the proof-free family `famUH A wa`
(`C4Hf.chFamH`'s machine fields depend only on C6's assembler and the printer's algorithm; `hash_uniform`, by `rfl`), so
one `Stage3` (**`hashStageU`**) serves every call. **`hash_call_run`**: at a THR call, with the free numbers
(`HashFreeOk2`: `HashEAt` and `caps_ge`) and any setup run to a C4H-a `HBank2` bank at the call's words, the stage
ends with `frame (thrIn …)` (the THR writer's input) within any budget above its steps.

* `famUH`, `hashStageU`, `hash_uniform`, **`hash_call_run`**.

Paper quantity of the main type: the THR writer's input `req.word ++ frame hashBits` at a call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

section Call
variable (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
  (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The HASH stage at one THR call**, within any budget above its steps, from any setup run to an `HBank2` bank at
the call's words. -/
theorem hash_call_run {x s0 c0 : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (M0 : Machine (3 + x) s0)
    (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x)) (off : ℕ)
    (hroom : off + 12 + ((famUH UnionMachine.TailAsm.asmStage wa).T + 1 + 1 + 1) + (2 + 2 + 0 + 1) ≤ 3 + x)
    (n a2 : ℕ) (ha2 : a2 ≤ 4) (Cs : Fin a2 → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a2 ha2 Cs carriers translation)) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (E4 : Cost.Envelope) (B : Fin (3 + x) → List Bool)
    (h0 : Step M0 c0 (fun _ => 0) (SeedFixTypes.stageIn x (thrReq n a2 ha2 Cs carriers translation).word (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)) (fun _ => 0) B)
    (hB : C4H.HBank2 L hLx B (thrReq n a2 ha2 Cs carriers translation).word (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (C4Child.pre (gate0 l F).alg (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 5) 0)) (C4Child.post (gate0 l F).alg (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 5) 0)) (C4H.hb0 (C4H.hbX (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (FinalPass.HashFr.capsOf ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 1)) 0 0))
      (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 5) 0).P.Q (2 ^ (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 5) 0).dRow * 2 ^ (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 5) 0).dRow) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 6) hkT hqT off)
    (Bd : ℕ)
    (hBd : wrapCost (c0 + 1 + (2 * preCost (thrReq n a2 ha2 Cs carriers translation).word (2 * (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t) (2 * (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t * (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0) + 2 + 1 + (2 * 2 ^ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 6 + 4))) (C4Hf.hashFamCall (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation UnionMachine.TailAsm.asmStage wa (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 5) 0) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 rfl rfl rfl (FinalPass.HashFr.capsOf ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 1)) E4 (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) (H.Kc n) (H.Kch n) (H.caps_ge kclk coef A a ha n a2 ha2 Cs carriers translation hcall hs) (H.side kclk coef A a ha n a2 ha2 Cs carriers translation hcall hs)).F
      (2 ^ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 6) (finCost (thrReq n a2 ha2 Cs carriers translation).word (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs) (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs) (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))) + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run (hashStageU L hLx M0 wa hkT hqT off hroom) Bd (thrReq n a2 ha2 Cs carriers translation).word (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (frame (SeedFixTypes.thrIn l F kclk coef A a ha n a2 ha2 Cs carriers translation hs)) :=
  hashLay_run L hLx UnionMachine.TailAsm.asmStage wa _ _ _ _ _ _ _ _ (C4Hf.hashFamCall (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation UnionMachine.TailAsm.asmStage wa (PrimAsm.ThrFam.thrR0 (callInputs l F kclk coef A a ha) hs Cs carriers translation ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 4) (H.dF (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 5) 0) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 2) 0 rfl rfl rfl (FinalPass.HashFr.capsOf ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 1)) E4 (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) (H.Kc n) (H.Kch n) (H.caps_ge kclk coef A a ha n a2 ha2 Cs carriers translation hcall hs) (H.side kclk coef A a ha n a2 ha2 Cs carriers translation hcall hs)) M0 (thrReq n a2 ha2 Cs carriers translation).word (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) B h0 ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) 6) hkT hqT off hB
    (2 * (C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t) (C4Hk.hb0_ruler _) (C4Hk.hb0_two _) (H.side kclk coef A a ha n a2 ha2 Cs carriers translation hcall hs).2.2.2.2.2.1 hroom Bd hBd

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4Hk

end
