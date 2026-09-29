import Proof.Wire_3_5.FinalPass.S5TPre6

/-! # S5-THR, part 22: the named streams and registers of the THR half (P3:3170-3181)

On the THR half's layout `WM (nsL D x6 xt) nrL` (`S5TLay`):

* `xsN j` (the powers `12 + j`), `sPad` (the padded template, scratch stream `8`), **`fs2`** (the padded prelude's
  streams: input, template, padded template, the unused stream `10` for the count (it lands on the scrub's driver),
  the powers), `fs2_inj`, `fs2_0`;
* `wP j` (W6's port `j` on its block), **`tailSN`** (the tail's nineteen streams), `tailSN_inj`;
* `pR` (the parse's registers `0 … 6`), **`tailRg`** (the tail's forty registers: `10 … 48`, and `3` = the tuple size
  from the parse), `tailRg_inj`.

Paper quantity: none (the machine's layout; the consumers' types carry the paper's words). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T

section Lay2
variable (D x6 xt : ℕ)

/-- The power `xs j` on stream `12 + j`. -/
def xsN (j : ℕ) : Fin (nsL D x6 xt + 1) :=
  if h : j ≤ D then ⟨12 + j, by have := nsL_ge D x6 xt; omega⟩ else ⟨0, by omega⟩

theorem xsN_val (j : ℕ) (hj : j ≤ D) : (xsN D x6 xt j).val = 12 + j := by unfold xsN; rw [dif_pos hj]

/-- The padded template: scratch stream `8`. -/
def sPad : Fin (nsL D x6 xt + 1) := sMisc D x6 xt 8

/-- **The padded prelude's streams**: input, template, padded template, the count's unused stream, the powers. -/
def fs2 (k : Fin (D + 5)) : Fin (nsL D x6 xt + 1) :=
  if k.val = 0 then sIn D x6 xt else if k.val = 1 then sTm D x6 xt else if k.val = 2 then sPad D x6 xt
  else if k.val = 3 then sCt D x6 xt else ⟨8 + k.val, by have := nsL_ge D x6 xt; have := k.isLt; omega⟩

theorem fs2_val (k : Fin (D + 5)) :
    (fs2 D x6 xt k).val = if k.val = 0 then 0 else if k.val = 1 then 9 else if k.val = 2 then 21 + D
      else if k.val = 3 then 10 else 8 + k.val := by
  unfold fs2 sPad sMisc sTm sCt sIn; split_ifs <;> simp <;> omega

theorem fs2_inj : Function.Injective (fs2 D x6 xt) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [fs2_val] at h'
  have := a.isLt; have := b.isLt
  apply Fin.ext
  split_ifs at h' <;> omega

theorem fs2_0 : fs2 D x6 xt (sI2 D) = 0 := by unfold fs2 sI2 sIn; simp

theorem fs2_xs (j : ℕ) (hj : j ≤ D) : fs2 D x6 xt (sxs2 D j) = xsN D x6 xt j := by
  apply Fin.ext; rw [fs2_val, sxs2_val D j hj, xsN_val D x6 xt j hj]; split_ifs <;> omega

/-- The tail's stream values as `α k + β k · D`: input `0`, template `9`, W6's ports `3, 8, 9, 12, 13, 15, 18, 19`
(`w6B D + j = 720 + j + D`), scratch `1 … 7` (`13 + D + i`), slots `14`, `15` (`7`, `8`). -/
def tailA : Fin 19 → ℕ := ![0, 9, 723, 728, 729, 732, 733, 735, 738, 739, 14, 15, 16, 17, 18, 19, 20, 7, 8]

/-- The `D`-coefficient of the tail's stream values. -/
def tailB : Fin 19 → ℕ := ![0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0]

theorem tailB_le : ∀ k, tailB k ≤ 1 := by decide
theorem tailA_lo : ∀ k, tailB k = 0 → tailA k < 14 := by decide
theorem tailA_hi : ∀ k, tailB k = 1 → 14 ≤ tailA k := by decide
theorem tailAB_inj : ∀ a b, tailB a = tailB b → tailA a = tailA b → a = b := by decide

/-- The tail's stream values. -/
def tailSV (k : Fin 19) : ℕ := tailA k + tailB k * D

theorem tailSV_inj {a b : Fin 19} (h : tailSV D a = tailSV D b) : a = b := by
  unfold tailSV at h
  have h1 := tailB_le a
  have h2 := tailB_le b
  by_cases hab : tailB a = tailB b
  · exact tailAB_inj a b hab (by rw [hab] at h; omega)
  · exfalso
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with ha | ha <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with hb | hb
    · exact hab (by rw [ha, hb])
    · have := tailA_lo a ha; have := tailA_hi b hb; rw [ha, hb] at h; omega
    · have := tailA_hi a ha; have := tailA_lo b hb; rw [ha, hb] at h; omega
    · exact hab (by rw [ha, hb])

theorem tailSV_lt (k : Fin 19) : tailSV D k < nsL D x6 xt + 1 := by
  have := nsL_ge D x6 xt
  have h1 := tailB_le k
  have h2 : tailA k ≤ 739 := by revert k; decide
  unfold tailSV
  have : tailB k * D ≤ D := by nlinarith
  omega

/-- **The tail's nineteen streams** on the layout. -/
def tailSN : Fin 19 ↪ Fin (nsL D x6 xt + 1) :=
  ⟨fun k => ⟨tailSV D k, tailSV_lt D x6 xt k⟩, fun _ _ h => tailSV_inj D (congrArg Fin.val h)⟩

/-- The parse's registers `0 … 6`. -/
def pR : PReg nrL := ⟨fun j => ⟨j.val, by have := j.isLt; show j.val < 128; omega⟩,
  fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- **The tail's forty registers**: `10 … 48`, and register `3` (the tuple size from the parse) last. -/
def tailRg : Fin 40 ↪ Fin nrL :=
  ⟨fun k => if k.val < 39 then ⟨10 + k.val, by have := k.isLt; show 10 + k.val < 128; omega⟩
    else ⟨3, by show 3 < 128; omega⟩, fun a b h => by
    have h' := congrArg Fin.val h
    have := a.isLt; have := b.isLt
    apply Fin.ext
    dsimp only at h'
    split_ifs at h' <;> simp at h' <;> omega⟩

theorem tailRg_val (k : Fin 40) : (tailRg k).val = if k.val < 39 then 10 + k.val else 3 := by
  unfold tailRg; dsimp only [Function.Embedding.coeFn_mk]; split <;> rfl

end Lay2

end NearCubicWires.WireExponent3_5.FinalPass.S5T
