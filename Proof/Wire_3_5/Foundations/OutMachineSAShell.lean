import Lean
import Proof.Wire_3_5.Foundations.OutMachineJoinW
import Proof.Wire_3_5.Foundations.OutMachineCarGen
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineCarIface
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Foundations.OutMachineSAShellBase


noncomputable section
set_option maxRecDepth 4096


/-! # SA's shell: S4's words 0–3 from their writers

S4's first four words at a request (`frontWordsW2 … (s4SlotA k)`, P3:3044-3048, 3170-3181): the offset word, the
sample word, the two carrier tables. SA is the join of three writers:

* **`slot0Ws`**, **`slot1Ws`** (the offset's and the sample's word families; `slot0Ws_eq`: the offset word
  `frameP (List.ofFn (C4Geo.offset P σ)) ++ [false]` at the call's star parameters and translation);
* `carF`, **`carSub l`** (`carPhaseJ l` at words 0–1, the carrier tables; `fw_car`: they are S4's words 2–3);
* **`saWords`** (the joined family is S4's words 0–3), **`saOf2`**, **`saOf`**-to-be:
  `saOf2 slot0 slot1 := ((slot0.join slot1).join (carSub l)).congrWs (saWords l) : S4WordsMAJ l`.

Paper quantity of the main type: S4's words (the offset, the sample, the carrier tables; P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Finish

variable (l : Literals)

/-- **S4's word 0 (the offset) as a one-word family** (SA's slot 0; the writer). -/
noncomputable def slot0Ws (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (_ : Fin 1) : List Bool :=
  frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA 0)

/-- **S4's word 1 (the sample) as a one-word family** (SA's slot 1). -/
noncomputable def slot1Ws (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (_ : Fin 1) : List Bool :=
  frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA 1)

/-- A call's star hypotheses hold (the `Call` field). -/
theorem starAt {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} (r : FReq l F kclk coef A a ha) :
    (callInputs l F kclk coef A a ha).StarAt r.1.n := r.2.2.2.2.2.2.1

/-- **The offset word**: slot 0 is `frameP (List.ofFn (C4Geo.offset P σ)) ++ [false]` at the call's star parameters
`P` and its translation `σ`. -/
theorem slot0Ws_eq (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (k : Fin 1) :
    slot0Ws l F kclk coef A a ha r k =
      frameP (List.ofFn (PrimT.C4Geo.offset ((callInputs l F kclk coef A a ha).starParams r.1.n (starAt l r))
        (((callInputs l F kclk coef A a ha).starParams r.1.n (starAt l r)).translationOfCodes r.1.translation))) ++
        [false] := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  cases mode <;>
  · simp only [slot0Ws, frontWordsW2, frontWordsOfW2, dif_pos hs]
    rfl

/-- **The carrier tables' writer** (`carPhaseJ l` at words `0`, `1`). -/
noncomputable def carSub : CoreWordsMJ l 2 fun F kclk coef A a ha r k => Car.carWords l F kclk coef A a ha r (carF k) :=
  (CarGen.carPhaseJ l).sub carF

/-- **The carrier tables are S4's words 2–3.** -/
theorem fw_car (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (j : Fin 2) :
    Car.carWords l F kclk coef A a ha r (carF j) =
      frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA ⟨2 + j.val, by omega⟩) := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  match j with
  | ⟨0, _⟩ =>
    cases mode <;>
    · simp only [frontWordsW2, frontWordsOfW2, dif_pos hs]
      rfl
  | ⟨1, _⟩ =>
    cases mode <;>
    · simp only [frontWordsW2, frontWordsOfW2, dif_pos hs]
      rfl

/-- **The joined family is S4's words 0–3.** -/
theorem saWords (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (k : Fin (1 + 1 + 2)) :
    Fin.append (Fin.append (slot0Ws l F kclk coef A a ha r) (slot1Ws l F kclk coef A a ha r))
        (fun j => Car.carWords l F kclk coef A a ha r (carF j)) k =
      frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA k) := by
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => exact fw_car l F kclk coef A a ha r 0
  | ⟨3, _⟩ => exact fw_car l F kclk coef A a ha r 1

/-- **SA from its slot writers**: the offset's writer, the sample's writer, the carrier tables. -/
noncomputable def saOf2 (slot0 : CoreWordsMJ l 1 (slot0Ws l)) (slot1 : CoreWordsMJ l 1 (slot1Ws l)) : S4WordsMAJ l :=
  ((slot0.join slot1).join (carSub l)).congrWs (saWords l)

end NearCubicWires.WireExponent3_5.FinalPass.Out.SA

end
