import Proof.Wire_3_5.UnionMachine.FrontAtomCopy
import Proof.Wire_3_5.UnionMachine.FrontAtomTail
import Proof.Wire_3_5.UnionMachine.FrontAtomDecoder
import Proof.Wire_3_5.UnionMachine.FrontLoopKit
import Proof.Amplification.RecoveryScratchErase

/-! # C6 front, U1b: the atom loop's tapes

The atom loop's `1703 + 11` tapes: v8's decoder bank first (`dm`), then `0` the guess rest, `1` the copy's cell, `2–4`
the copy's registers `PG PT K`, `5` the loop's condition, `6–7` the verdict's registers `J BAD`, `8` the ruler `1^H`,
`9–10` the erasers' capacity tapes. The decoder's private tapes (every tape but the raw, template, output, driver and
policy tapes) are enumerated by `priv`. Main declarations: the slot maps `dm sm cm tm em pm` with injectivity, `priv`
with `priv_pub` / `priv_surj`. Paper quantity: none (the layout of the atom loop). -/

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLayout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

abbrev AT : ℕ := 1703 + 11

/-- The decoder's tapes. -/
def dm (i : Fin 1703) : Fin AT := Fin.castAdd 11 i
/-- The loop's own tapes. -/
def sm (k : Fin 11) : Fin AT := Fin.natAdd 1703 k

theorem dm_inj : Function.Injective dm := fun a b h => by simpa [dm] using h
theorem sm_inj : Function.Injective sm := fun a b h => by simpa [sm] using h
theorem dm_ne_sm (i : Fin 1703) (k : Fin 11) : dm i ≠ sm k := by
  intro h; have := congrArg Fin.val h; simp [dm, sm] at this; omega

/-- The decoder's public tapes (restored or extended by a pass). -/
def isPub (i : Fin 1703) : Bool :=
  i.val == 1 || i.val == 1674 || i.val == 1688 || i.val == 1694 || i.val == 1698 || i.val == 1699

/-- The private tapes, in order. -/
def priv (k : Fin 1697) : Fin 1703 :=
  ⟨if k.val < 1 then k.val else if k.val < 1673 then k.val + 1 else if k.val < 1686 then k.val + 2
    else if k.val < 1691 then k.val + 3 else if k.val < 1694 then k.val + 4 else k.val + 6,
    by have := k.isLt; split_ifs <;> omega⟩

theorem priv_inj : Function.Injective priv := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [priv] at hv
  apply Fin.ext
  have := a.isLt; have := b.isLt
  split_ifs at hv <;> omega

theorem priv_pub (k : Fin 1697) : isPub (priv k) = false := by
  have := k.isLt
  simp only [isPub, priv, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  split_ifs <;> omega

theorem priv_surj (i : Fin 1703) (h : isPub i = false) : ∃ k, priv k = i := by
  simp only [isPub, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  have := i.isLt
  refine ⟨⟨if i.val < 1 then i.val else if i.val < 1674 then i.val - 1 else if i.val < 1688 then i.val - 2
    else if i.val < 1694 then i.val - 3 else if i.val < 1698 then i.val - 4 else i.val - 6,
    by split_ifs <;> omega⟩, ?_⟩
  apply Fin.ext
  simp only [priv]
  split_ifs <;> omega

/-- The copy's tapes (C5's layout: rest, cell, decoder raw tape, `PG PT K`). -/
def cm : Fin 6 → Fin AT := ![sm 0, sm 1, dm 1, sm 2, sm 3, sm 4]
/-- The verdict's tapes (flag, condition, `J BAD`). -/
def tm : Fin 4 → Fin AT := ![dm 1700, sm 5, sm 6, sm 7]
/-- The private eraser's tapes (the private tapes, the ruler `1^H`, its capacity tape). -/
def em (x : Fin (1697 + 1 + 1)) : Fin AT :=
  if h : x.val < 1697 then dm (priv ⟨x.val, h⟩) else if x.val = 1697 then sm 8 else sm 9

theorem em_priv (k : Fin 1697) : em (Fin.castAdd 1 (Fin.castAdd 1 k)) = dm (priv k) := by
  simp [em, k.isLt]

theorem em_ruler : em (Fin.castAdd 1 (Fin.natAdd 1697 (0 : Fin 1))) = sm 8 := by simp [em]
theorem em_cap : em (Fin.natAdd (1697 + 1) (0 : Fin 1)) = sm 9 := by simp [em]

/-- The raw tape's eraser (the raw tape, the driver `1^P` as its ruler, its capacity tape). -/
def pm : Fin 3 → Fin AT := ![dm 1, dm 1694, sm 10]

theorem cm_inj : Function.Injective cm := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [cm, dm, sm, AT] at this)

theorem tm_inj : Function.Injective tm := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [tm, dm, sm, AT] at this)

theorem pm_inj : Function.Injective pm := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := congrArg Fin.val h; simp [pm, dm, sm, AT] at this)

theorem em_val (x : Fin (1697 + 1 + 1)) :
    (em x).val = if h : x.val < 1697 then (priv ⟨x.val, h⟩).val else if x.val = 1697 then 1711 else 1712 := by
  unfold em; split_ifs <;> simp [dm, sm]

theorem em_inj : Function.Injective em := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [em_val, em_val] at hv
  have ha := a.isLt; have hb := b.isLt
  apply Fin.ext
  split_ifs at hv with h1 h2 h3 h4 h5 h6 <;> first
    | (have := congrArg Fin.val (priv_inj (Fin.ext hv)); simpa using this)
    | (have := (priv ⟨a.val, h1⟩).isLt; omega)
    | (have := (priv ⟨b.val, h3⟩).isLt; omega)
    | omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLayout
