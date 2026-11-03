import Lean
import Proof.Wire_3_5.FinalPass.SymF5
import Proof.Wire_3_5.FinalPass.SWParts
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase


noncomputable section
set_option maxRecDepth 4096


/-! # SWf (the SYM words writer's flat tables), part 11: the flat part's words at a SYM request

At a SYM request `r = ⟨n, sym, a', Cs, carriers, …⟩` of a call family (on-star, `PrimitiveInputs.Call`), the SYM slots
`24 … 27` of the front's exit (`SWParts.swWs l 8 4`, the words of `SWfT l`) are the list seeds' flat tables of the
call's flat list `symListParams I n a' Cs carriers` at the population lengths `|symGates C_c|` (`0` past the tuple):
the `tablesJ (symCallOf …) c`, i.e. `flatWord`.

* `symPl r`, `symL r c` (the flat list and the population lengths at a request, `⟨0,0,0⟩`/`0` at THR);
* **`swf_words`**: `swWs l 8 4 _ F … r c = flatWord (symPl r) (symL r c)` at every SYM request.

Paper quantity of the main type: the SYM call word `4·2 + c` (the flat tables of circuit `c`, list:flatten
P3:1508-1520, P3:3170-3178) at the request. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.PrimAsm.Plan

section Req
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The call's flat list at a SYM request (`⟨0, 0, 0⟩` at THR). -/
noncomputable def symPl (r : FReq l F kclk coef A a ha) : FlatListParams :=
  match r.1 with
  | ⟨n, .sym, a', _, Cs, carriers, _⟩ => symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers
  | ⟨_, .thr, _, _, _, _, _⟩ => ⟨0, 0, 0⟩

/-- Circuit `c`'s population length at a SYM request: `|symGates C_c|`, `0` past the tuple (and at THR). -/
noncomputable def symL (r : FReq l F kclk coef A a ha) (c : Fin 4) : ℕ :=
  match r.1 with
  | ⟨_, .sym, a', _, Cs, _, _⟩ => if h : c.val < a' then (Stars.symGates (Cs ⟨c.val, h⟩)).length else 0
  | ⟨_, .thr, _, _, _, _, _⟩ => 0

/-- **The flat part's words at a SYM request.** -/
theorem swf_words (r : FReq l F kclk coef A a ha) (hm : r.1.mode = .sym) (c : Fin 4) :
    SWParts.swWs l 8 4 (by norm_num) F kclk coef A a ha r c = flatWord (symPl l F kclk coef A a ha r) (symL l F kclk coef A a ha r c) := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  cases mode with
  | thr => exact absurd hm (by simp)
  | sym =>
    have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
    unfold SWParts.swWs frontWordsW2 frontWordsOfW2
    simp only [dif_pos hs]
    rw [dif_neg (by simp only [symSlot]; omega), if_neg (by simp only [symSlot]; omega),
      dif_pos (by simp only [symSlot, sw0_nw]; omega)]
    show PrimT.S3.symWords (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) _ = _
    refine (congrArg (PrimT.S3.symWords (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers))
      (Fin.ext ?_ : _ = PrimT.S3.wIdx 2 c)).trans ?_
    · simp only [symSlot, PrimT.S3.wIdx]
      omega
    · rw [PrimT.S3.symWords_idx]
      show PrimT.S3.tablesJ (symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) c = _
      rw [flatWord_tablesJ]
      congr 1
      unfold PrimT.S3.gatesJ symL
      dsimp only [symCallOf]
      split_ifs <;> rfl

end Req

end NearCubicWires.WireExponent3_5.FinalPass.SymF

end
