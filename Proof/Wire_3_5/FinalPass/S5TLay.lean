import Proof.Wire_3_5.FinalPass.S5TParse

/-! # S5-THR, part 6: the THR half's register-program layout (P3:3170-3181)

One register-program layout (`WM (nsL D x6 xt) nrL`) carries the whole THR half; the docked raw machines run on
blocks of its streams (`DockW.dockS`), their shared ports mapped onto the streams that hold the shared words:

* streams `0` the input `frame fpIn`; `1 … 8` the THR slots `8 … 15`; `9` the template, `10` the count `1^W`, `11`
  the fill's marker tape, `12 … 12+D` the powers (the prelude, `preFs`); `13+D …` 32 scratch streams;
* the prep block (`p0Map`: its request on `0`, its fill count on scratch stream `0`), W6's block (`w6Map`: port `0` on
  the input, ports `1`, `2`, `20` on the prep's outputs `|carriers|`, `cap_T`, `V`, port `17` on slot `13`), the
  front end's block (`tfMap`: port `0` on the input, port `1` on `V`, ports `2 … 5` on slots `9 … 12`), the data
  stage's block (`tdMap`: its request on the input, its table `tabS` on slot `8`);
* **`preFs_inj`**, **`p0Map_inj`**, **`w6Map_inj`**, **`tfMap_inj`**, **`tdMap_inj`**, and the block values.

Paper quantity: none (the machine's tape layout; the consumers' types carry the paper's words). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T

section Lay
variable (D x6 xt : ℕ)

/-- The prep's tapes (`LNS 0 + 2 + LNR + 1`). -/
abbrev P0T : ℕ := 675
/-- PA's data stage's tapes (`DS + 2 + DR + 1`). -/
abbrev TDT : ℕ := 9902

/-- The prep's block. -/
def p0B : ℕ := 45 + D
/-- W6's block. -/
def w6B : ℕ := p0B D + 675
/-- The front end's block. -/
def tfB : ℕ := w6B D + (21 + x6)
/-- The data stage's block. -/
def tdB : ℕ := tfB D x6 + (10 + xt)
/-- The layout's last stream index. -/
def nsL : ℕ := tdB D x6 xt + 9902
/-- The layout's register count. -/
abbrev nrL : ℕ := 128

theorem nsL_ge : 45 + D + 675 + (21 + x6) + (10 + xt) + 9902 ≤ nsL D x6 xt := by
  unfold nsL tdB tfB w6B p0B; omega

/-- The input. -/
def sIn : Fin (nsL D x6 xt + 1) := ⟨0, by omega⟩
/-- THR slot `8 + k`. -/
def sSlot (k : Fin 8) : Fin (nsL D x6 xt + 1) := ⟨1 + k.val, by have := nsL_ge D x6 xt; have := k.isLt; omega⟩
/-- The template. -/
def sTm : Fin (nsL D x6 xt + 1) := ⟨9, by have := nsL_ge D x6 xt; omega⟩
/-- The count `1^W`. -/
def sCt : Fin (nsL D x6 xt + 1) := ⟨10, by have := nsL_ge D x6 xt; omega⟩
/-- Scratch stream `i < 32`. -/
def sMisc (i : Fin 32) : Fin (nsL D x6 xt + 1) := ⟨13 + D + i.val, by have := nsL_ge D x6 xt; have := i.isLt; omega⟩

/-- The prep's tapes on the layout: its request on the input, its fill count on scratch stream `0`. -/
def p0Map (j : Fin P0T) : Fin (nsL D x6 xt + 1) :=
  if j.val = 0 then sIn D x6 xt else if j.val = 2 then sMisc D x6 xt 0
  else ⟨p0B D + j.val, by have := nsL_ge D x6 xt; have : j.val < 675 := j.isLt; unfold p0B; omega⟩

theorem p0Map_val (j : Fin P0T) :
    (p0Map D x6 xt j).val = if j.val = 0 then 0 else if j.val = 2 then 13 + D else p0B D + j.val := by
  unfold p0Map; split_ifs <;> rfl

theorem p0Map_inj : Function.Injective (p0Map D x6 xt) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [p0Map_val] at h'
  unfold p0B at h'
  apply Fin.ext
  split_ifs at h' <;> omega

/-- W6's tapes on the layout: port `0` on the input, ports `1`, `2`, `20` on the prep's outputs, port `17` on slot
`13`. -/
def w6Map (j : Fin (21 + x6)) : Fin (nsL D x6 xt + 1) :=
  if j.val = 0 then sIn D x6 xt
  else if j.val = 1 then ⟨p0B D + 4, by have := nsL_ge D x6 xt; unfold p0B; omega⟩
  else if j.val = 2 then ⟨p0B D + 5, by have := nsL_ge D x6 xt; unfold p0B; omega⟩
  else if j.val = 20 then ⟨p0B D + 6, by have := nsL_ge D x6 xt; unfold p0B; omega⟩
  else if j.val = 17 then sSlot D x6 xt 5
  else ⟨w6B D + j.val, by have := nsL_ge D x6 xt; have := j.isLt; unfold w6B p0B; omega⟩

theorem w6Map_val (j : Fin (21 + x6)) :
    (w6Map D x6 xt j).val = if j.val = 0 then 0 else if j.val = 1 then p0B D + 4 else if j.val = 2 then p0B D + 5
      else if j.val = 20 then p0B D + 6 else if j.val = 17 then 6 else w6B D + j.val := by
  unfold w6Map; split_ifs <;> rfl

theorem w6Map_inj : Function.Injective (w6Map D x6 xt) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [w6Map_val] at h'
  unfold w6B p0B at h'
  apply Fin.ext
  split_ifs at h' <;> omega

/-- The front end's tapes on the layout: port `0` on the input, port `1` on `V`, ports `2 … 5` on slots `9 … 12`. -/
def tfMap (j : Fin (10 + xt)) : Fin (nsL D x6 xt + 1) :=
  if j.val = 0 then sIn D x6 xt
  else if j.val = 1 then ⟨p0B D + 6, by have := nsL_ge D x6 xt; unfold p0B; omega⟩
  else if j.val ≤ 5 then ⟨j.val, by have := nsL_ge D x6 xt; omega⟩
  else ⟨tfB D x6 + j.val, by have := nsL_ge D x6 xt; have := j.isLt; unfold tfB w6B p0B; omega⟩

theorem tfMap_val (j : Fin (10 + xt)) :
    (tfMap D x6 xt j).val = if j.val = 0 then 0 else if j.val = 1 then p0B D + 6 else if j.val ≤ 5 then j.val
      else tfB D x6 + j.val := by
  unfold tfMap; split_ifs <;> rfl

theorem tfMap_inj : Function.Injective (tfMap D x6 xt) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [tfMap_val] at h'
  unfold tfB w6B p0B at h'
  apply Fin.ext
  split_ifs at h' <;> omega

/-- The data stage's tapes on the layout: its request on the input, its table `tabS` (tape `18`) on slot `8`. -/
def tdMap (j : Fin TDT) : Fin (nsL D x6 xt + 1) :=
  if j.val = 0 then sIn D x6 xt else if j.val = 18 then sSlot D x6 xt 0
  else ⟨tdB D x6 xt + j.val, by have : j.val < 9902 := j.isLt; unfold nsL; omega⟩

theorem tdMap_val (j : Fin TDT) :
    (tdMap D x6 xt j).val = if j.val = 0 then 0 else if j.val = 18 then 1 else tdB D x6 xt + j.val := by
  unfold tdMap; split_ifs <;> rfl

theorem tdMap_inj : Function.Injective (tdMap D x6 xt) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [tdMap_val] at h'
  unfold tdB tfB w6B p0B at h'
  apply Fin.ext
  split_ifs at h' <;> omega

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.S5T
