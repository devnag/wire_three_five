import Proof.Wire_3_5.FinalPass.DigsLink1
import Proof.Wire_3_5.Primitive.ThresholdWriter.EqRead

/-! # `DigsW`'s body, part 16: the program's data from the circuits (P3:2543-2551)

Per circuit `i < a'` (ℕ-indexed, `0` / `[]` beyond `a'`): `Sd i = |supp_i|`, `md i = |children_i|`, the payload's
content `cDd i`, and for a child index `kk i`: the skipped integers `zsd` (the first `kk i` children's weights and
targets), the selected child's weights `wsd` and target `td`, the rest `restd`. `cDd_eq` is the decomposition the
program navigates (`EqRead.payOf_eq`, `exactWord_eq`). Main declarations: `ysOf`, `Sd`, `md`, `cDd`, `zsd`, `wsd`,
`td`, `restd`, **`cDd_eq`**, `zsd_len`, `wsd_len`, `payOf_cDd`. Paper quantities: the circuits' retained tops,
children and selected children. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline

/-- A child's integers in word order: its weights, then its target. -/
def ysOf {k : ℕ} (ch : ExactThresholdGate k) : List ℤ := List.ofFn ch.weight ++ [ch.target]

theorem exactWord_ys {k : ℕ} (ch : ExactThresholdGate k) : exactWord ch = (ysOf ch).flatMap intWord := by
  rw [PrimThrW.EqRead.exactWord_eq, ysOf, List.flatMap_append]; simp

theorem ysOf_len_flat {k : ℕ} : ∀ l : List (ExactThresholdGate k), (l.flatMap ysOf).length = l.length * (k + 1)
  | [] => by simp
  | ch :: l => by
    rw [List.flatMap_cons, List.length_append, ysOf_len_flat l, List.length_cons, ysOf]; simp; ring

section Data
variable {q a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit q) (alg : DecompositionAlgorithm)

/-- `|supp_i|`. -/
def Sd (i : ℕ) : ℕ := if h : i < a' then (Cs ⟨i, h⟩).top.support.card else 0

/-- `|children_i|`. -/
def md (i : ℕ) : ℕ := if h : i < a' then (ThresholdRows.children alg (Cs ⟨i, h⟩)).length else 0

/-- Circuit `i`'s payload content. -/
def cDd (i : ℕ) : List Bool :=
  if h : i < a' then natWord (Cs ⟨i, h⟩).top.support.card ++ (natWord (ThresholdRows.children alg (Cs ⟨i, h⟩)).length ++
    (ThresholdRows.children alg (Cs ⟨i, h⟩)).flatMap exactWord) else []

/-- The integers of the children before the selected one. -/
def zsd (kk : ℕ → ℕ) (i : ℕ) : List ℤ :=
  if h : i < a' then ((ThresholdRows.children alg (Cs ⟨i, h⟩)).take (kk i)).flatMap ysOf else []

/-- The selected child's weights. -/
def wsd (kk : ℕ → ℕ) (i : ℕ) : List ℤ :=
  if h : i < a' then (((ThresholdRows.children alg (Cs ⟨i, h⟩))[kk i]?).map fun ch => List.ofFn ch.weight).getD []
  else []

/-- The selected child's target. -/
def td (kk : ℕ → ℕ) (i : ℕ) : ℤ :=
  if h : i < a' then (((ThresholdRows.children alg (Cs ⟨i, h⟩))[kk i]?).map fun ch => ch.target).getD 0 else 0

/-- The children after the selected one. -/
def restd (kk : ℕ → ℕ) (i : ℕ) : List Bool :=
  if h : i < a' then ((ThresholdRows.children alg (Cs ⟨i, h⟩)).drop (kk i + 1)).flatMap exactWord else []

theorem payOf_cDd (i : ℕ) (h : i < a') : PrimThrW.TopFront.payOf alg (Cs ⟨i, h⟩) = frame (cDd Cs alg i) := by
  rw [PrimThrW.EqRead.payOf_eq, cDd, dif_pos h]

theorem cDd_eq (kk : ℕ → ℕ) (i : ℕ) (h : i < a') (hk : kk i < md Cs alg i) :
    cDd Cs alg i = natWord (Sd Cs i) ++ (natWord (md Cs alg i) ++ ((zsd Cs alg kk i).flatMap intWord ++
      ((wsd Cs alg kk i ++ [td Cs alg kk i]).flatMap intWord ++ restd Cs alg kk i))) := by
  unfold cDd Sd md zsd wsd td restd at *
  rw [dif_pos h] at hk
  simp only [dif_pos h]
  obtain ⟨l, hl⟩ : ∃ l, l = ThresholdRows.children alg (Cs ⟨i, h⟩) := ⟨_, rfl⟩
  rw [← hl] at hk ⊢
  have hsplit : l = l.take (kk i) ++ l[kk i] :: l.drop (kk i + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  rw [List.getElem?_eq_getElem hk]
  simp only [Option.map_some, Option.getD_some]
  congr 2
  conv_lhs => rw [hsplit]
  rw [List.flatMap_append, List.flatMap_cons, List.flatMap_assoc]
  simp only [← exactWord_ys]
  rw [exactWord_ys l[kk i], ysOf]

theorem zsd_len (kk : ℕ → ℕ) (i : ℕ) (h : i < a') (hk : kk i ≤ md Cs alg i) :
    (zsd Cs alg kk i).length = kk i * (Sd Cs i + 1) := by
  unfold zsd Sd md at *
  rw [dif_pos h] at hk ⊢
  rw [dif_pos h, ysOf_len_flat, List.length_take_of_le hk]

theorem wsd_len (kk : ℕ → ℕ) (i : ℕ) (h : i < a') (hk : kk i < md Cs alg i) :
    (wsd Cs alg kk i).length = Sd Cs i := by
  unfold wsd Sd md at *
  rw [dif_pos h] at hk ⊢
  rw [dif_pos h, List.getElem?_eq_getElem hk]
  simp

end Data

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
