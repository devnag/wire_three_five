import Lean
import Proof.Wire_3_5.Foundations.OutMachineJoinG
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase


noncomputable section
set_option maxRecDepth 4096


/-! # The SYM words writer by parts (root #262; P3:1508-1520, 3170-3178)

The core half's SYM slots `16 … 32` of `frontWordsW2` (the `symWords`, word `4t + j` of kind `t` for circuit `j`,
then the unary list of the `symNums`) are written by five SYM-guarded writers (X6's `GuardedWordsMJ`, guard
`r.1.mode = .sym`), one per kind:

* **`SWgT l`**: the gate tables (`symSlot 0 … 3`, slots `16 … 19`); **`SWtT l`**: the framed top tables (`20 … 23`);
  **`SWfT l`**: the list seeds' flat tables (`24 … 27`); **`SWlT l`**: the stage-5 templates (`28 … 31`);
  **`SWnT l`**: the numbers' unary list (`32`); their words `swWs l o m` (the slots `symSlot (o + k)`);
* **`swOf : SWgT l → SWtT l → SWfT l → SWlT l → SWnT l → SymWordsMJ l`**: X6's `GuardedWordsMJ.join` four times,
  `congrWs` onto `frontWordsW2 … (symSlot k)` (the joined words ARE the slots in order, `swWs_append`), then
  `SymWordsMJ.ofG`.

Paper quantity of the main type: the SYM evaluator's call words and numbers (the `symWords`, `symNums`) at the SYM
slots of the front's exit. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SWParts
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Seams

variable (l : Literals)

/-- The SYM guard. -/
abbrev symG : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Prop :=
  fun _ _ _ _ _ _ r => r.1.mode = .sym

/-- The SYM slots `symSlot (o + k)`, `k < m`. -/
noncomputable def swWs (o m : ℕ) (h : o + m ≤ 17) :
    ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool :=
  fun F kclk coef A a ha r k => frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot ⟨o + k.val, by omega⟩)

/-- **The gate tables' writer** (slots `16 … 19`). -/
abbrev SWgT := GuardedWordsMJ l (symG l) 4 (swWs l 0 4 (by norm_num))
/-- **The top tables' writer** (slots `20 … 23`). -/
abbrev SWtT := GuardedWordsMJ l (symG l) 4 (swWs l 4 4 (by norm_num))
/-- **The flat tables' writer** (slots `24 … 27`). -/
abbrev SWfT := GuardedWordsMJ l (symG l) 4 (swWs l 8 4 (by norm_num))
/-- **The templates' writer** (slots `28 … 31`). -/
abbrev SWlT := GuardedWordsMJ l (symG l) 4 (swWs l 12 4 (by norm_num))
/-- **The numbers' writer** (slot `32`). -/
abbrev SWnT := GuardedWordsMJ l (symG l) 1 (swWs l 16 1 (by norm_num))

/-- The five parts' words, appended, are the SYM slots in order. -/
theorem swWs_append (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (k : Fin 17) :
    Fin.append (Fin.append (Fin.append (Fin.append (swWs l 0 4 (by norm_num) F kclk coef A a ha r)
      (swWs l 4 4 (by norm_num) F kclk coef A a ha r)) (swWs l 8 4 (by norm_num) F kclk coef A a ha r))
      (swWs l 12 4 (by norm_num) F kclk coef A a ha r)) (swWs l 16 1 (by norm_num) F kclk coef A a ha r) k =
    frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot k) := by
  fin_cases k <;> rfl

variable {l}

/-- **The SYM words writer from its five parts.** -/
noncomputable def swOf (Pg : SWgT l) (Pt : SWtT l) (Pf : SWfT l) (Pl : SWlT l) (Pn : SWnT l) : SymWordsMJ l :=
  SymWordsMJ.ofG ((((Pg.join Pt).join Pf).join Pl).join Pn |>.congrWs fun F kclk coef A a ha r _ k =>
    swWs_append l F kclk coef A a ha r k)

end NearCubicWires.WireExponent3_5.FinalPass.SWParts

end
