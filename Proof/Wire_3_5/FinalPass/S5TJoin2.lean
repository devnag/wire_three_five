import Proof.Wire_3_5.FinalPass.S5TJoin

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
variable {kc : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (Sw : SymWords)
  (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
  (translation : List ℕ)

theorem thr_w0 (hs : I.StarAt n) :
    frontWordsOfW I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨8, by omega⟩ =
      (if a' = 0 then [] else FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) := by
  simp only [frontWordsOfW, dif_pos hs]
  rfl

theorem thr_wpay (hs : I.StarAt n) (m : ℕ) (h1 : 1 ≤ m) (h4 : m ≤ 4) :
    frontWordsOfW I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨8 + m, by omega⟩ =
      (if h : m - 1 < a' then PrimThrW.TopFront.payOf alg (Cs ⟨m - 1, h⟩) else []) := by
  simp only [frontWordsOfW, dif_pos hs, show ¬ (8 + m < 8) by omega, dite_false, show 8 + m < 15 by omega, dite_true]
  unfold thrWords
  simp only [thrCallOf, show 8 + m - 8 = m by omega, show m ≠ 0 by omega, if_false]
  by_cases h : m - 1 < a'
  · rw [dif_pos ⟨h, h4⟩, dif_pos h]; rfl
  · rw [dif_neg (fun e => h e.1), dif_neg h, if_pos h4]

theorem thr_w5 (hs : I.StarAt n) :
    frontWordsOfW I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨13, by omega⟩ =
      PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (Primitive.thrCutoff (I.starParams n hs) Cs alg
        (Primitive.thrCallDen alg I hs Cs))) := by
  simp only [frontWordsOfW, dif_pos hs, show ¬ (13 < 8) by omega, dite_false, show 13 < 15 by omega, dite_true]
  unfold thrWords
  simp only [thrCallOf, show (13 - 8 : ℕ) = 5 by rfl, show (5 : ℕ) ≠ 0 by omega, if_false,
    show ¬ ((5 : ℕ) ≤ 4) by omega, and_false, dite_false, if_true]

theorem thr_w6 (hs : I.StarAt n) :
    frontWordsOfW I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨14, by omega⟩ =
      ListEval.levelWord
        (Primitive.thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg
          (Primitive.thrCallDen alg I hs Cs) (Primitive.thrCallE alg I hs Cs carriers)
          (Primitive.thrCallT alg I hs Cs carriers) (Primitive.thrCallJ alg I hs Cs carriers)).M
        (Primitive.thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg
          (Primitive.thrCallDen alg I hs Cs) (Primitive.thrCallE alg I hs Cs carriers)
          (Primitive.thrCallT alg I hs Cs carriers) (Primitive.thrCallJ alg I hs Cs carriers)).J
        (Primitive.thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg
          (Primitive.thrCallDen alg I hs Cs) (Primitive.thrCallE alg I hs Cs carriers)
          (Primitive.thrCallT alg I hs Cs carriers) (Primitive.thrCallJ alg I hs Cs carriers)).W
        (ListEval.rowsOf (MajorantBits.dataBits
          (Primitive.thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg
            (Primitive.thrCallDen alg I hs Cs) (Primitive.thrCallE alg I hs Cs carriers)
            (Primitive.thrCallT alg I hs Cs carriers) (Primitive.thrCallJ alg I hs Cs carriers))
          (FinalPass.thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
            (I.filterParams .thr n) alg (Primitive.thrCallDen alg I hs Cs) (Primitive.thrCallE alg I hs Cs carriers)
            (Primitive.thrCallT alg I hs Cs carriers) (Primitive.thrCallJ alg I hs Cs carriers)))
          (Primitive.thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg
            (Primitive.thrCallDen alg I hs Cs) (Primitive.thrCallE alg I hs Cs carriers)
            (Primitive.thrCallT alg I hs Cs carriers) (Primitive.thrCallJ alg I hs Cs carriers)).M) := by
  simp only [frontWordsOfW, dif_pos hs, show ¬ (14 < 8) by omega, dite_false, show 14 < 15 by omega, dite_true]
  unfold thrWords
  simp only [thrCallOf, show (14 - 8 : ℕ) = 6 by rfl, show (6 : ℕ) ≠ 0 by omega, if_false,
    show ¬ ((6 : ℕ) ≤ 4) by omega, and_false, dite_false, show (6 : ℕ) ≠ 5 by omega]
  rfl

theorem thr_w7 (hs : I.StarAt n) :
    frontWordsOfW I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨15, by omega⟩ =
      PrimAsm.Data.unaryList [a', Fintype.card (Primitive.ThrEq (I.starParams n hs) Cs alg),
        Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs),
        (Primitive.thrOccs (I.starParams n hs) Cs).length] := by
  simp only [frontWordsOfW, dif_pos hs, show ¬ (15 < 8) by omega, dite_false, show ¬ (15 < 15) by omega, if_true]
  rfl

theorem sym_w (Cs' : Fin a' → NormalizedSymmetricThresholdCircuit n) (k : Fin (17 + Sw.nw)) (h8 : 8 ≤ k.val)
    (h16 : k.val < 16) : frontWordsOfW I alg Sw ⟨n, .sym, a', ha', Cs', carriers, translation⟩ k = [] := by
  simp only [frontWordsOfW]
  split_ifs <;> first | rfl | omega

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
