import Lean
import Proof.Wire_3_5.FinalPass.S5TJoinBase
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.S5TJoin2Base


noncomputable section
set_option maxRecDepth 4096


/-! # S5-THR, part 34: the front's THR words at a request (P3:3083-3086, 3170-3181)

At a THR request the front's words `frontWordsOfW` on slots `8 … 15` are S2's call words and numbers of
`thrCallOf` (`thrWords`, `thrNums`); at a SYM request they are empty. The final pass's input is the call's word then
its seed word: at a THR request `reqW n true (thrCodes Cs) (carrier codes) (translation ++ seedWord)`
(`ReqBridge.reqW_thrReq`), and the seed word ends with the fixed hash's bits `frame (ofFn thrHashBits)`.

* `thr_w0`, `thr_wpay`, `thr_w5`, `thr_w6`, `thr_w7`, `sym_w` (the slot words); `fpIn_word`, `fpIn_split`.

Paper quantities of the main types: THR slots `8 … 15` (`thrWords`, `thrNums`, S2's reads), the final pass's input
word (the request's word and its seed word, P3:3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline

section Words

end Words

section Input
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
  (n a' : ℕ) (ha' : a' ≤ 4) (carriers : List (Stars.Carrier n)) (translation : List ℕ)

/-- **The final pass's input at a THR request** is the data stage's request word. -/
theorem fpIn_thr (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩) :
    PlanFP.fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hc⟩ =
      PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
        (RepairRepresentation.natListWord translation ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg
          ⟨n, .thr, a', ha', Cs, carriers, translation⟩) :=
  (PrimAsm.ReqBridge.reqW_thrReq ha' Cs carriers translation _).symm

/-- **The final pass's input at a THR request ends with the fixed hash's bits.** -/
theorem fpIn_thr_split (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    PlanFP.fpIn l F kclk coef A a ha ⟨⟨n, .thr, a', ha', Cs, carriers, translation⟩, hc⟩ =
      ((⟨n, .thr, a', ha', Cs, carriers, translation⟩ : PrimRequest).word ++
        FinalPass.Sample.sampleWord (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
          (List.ofFn fun j => (((SeedFix.thrCallSample (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers
            translation).S j).1.val, ((SeedFix.thrCallSample (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs
            carriers translation).S j).2.val))) ++
      frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
        (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
        ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
        (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
        (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
        (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
        (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers))) := by
  show _ ++ seedWord _ _ _ = _
  simp only [seedWord, dif_pos hs, List.append_assoc]

/-- **The final pass's input at a SYM request** is the data stage's request word (mode bit `false`). -/
theorem fpIn_sym (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) :
    PlanFP.fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hc⟩ =
      PrimAsm.Data.reqW n false (PrimAsm.Codec.codeList ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
        (PrimAsm.Codec.carrierCodes ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
        (RepairRepresentation.natListWord translation ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg
          ⟨n, .sym, a', ha', Cs, carriers, translation⟩) :=
  (PrimAsm.ReqBridge.reqW_word ⟨n, .sym, a', ha', Cs, carriers, translation⟩ _).symm

end Input

end NearCubicWires.WireExponent3_5.FinalPass.S5T

end
