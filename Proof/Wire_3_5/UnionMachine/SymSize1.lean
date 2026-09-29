import Proof.Wire_3_5.Primitive.SeedFix.S3Big12
import Proof.Wire_3_5.FinalPass.ThrSz3

/-! # hS, part 1: S3's call size below `600·Y⁴` from atom bounds `≤ Y`

S3's call words (`symWords`: the gate tables, the framed top tables, the list seeds' flat tables, the stage-5
templates) and numbers (`symNums`) are products of at most four atoms of the call — the arity, the bottom-gate lists,
their table width `tabH`, the top tables, the walk length `t`, the levels `J + 1`, the windows `W_j`, the population
`M`, the list-seed count `|FlatSeed|` (P3:3170-3178, list:flatten P3:1508-1520). With every atom `≤ Y`:

* `AtomsY k Y` (the hypotheses), `pows`, `tabLen_le`, `templ_le`, **`word_le`** (`≤ 16Y⁴`), **`num_le`**
  (`≤ 16Y⁴`), **`symSize_le`** (`S3.symSize k ≤ 600Y⁴`).

Paper quantity of the main type: the SYM per-point evaluator's input size (P3:3176-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SymSize
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall)

/-- **The call's atoms below `Y`.** -/
structure AtomsY (k : SymCall) (Y : ℕ) : Prop where
  one : 1 ≤ Y
  n : k.P.n + 1 ≤ Y
  G : ∀ j, (gatesJ k j).length ≤ Y
  H : ∀ j, PrimT.tabH (gatesJ k j) ≤ Y
  top : ∀ j, (topJ k j).length ≤ Y
  walk : k.Pl.walkLen ≤ Y
  J : k.Pl.base.J + 1 ≤ Y
  W : ∀ i, k.Pl.base.W i ≤ Y
  M : k.Pl.M ≤ Y
  FS : Fintype.card k.Pl.FlatSeed ≤ Y

theorem pows (Y : ℕ) (hY : 1 ≤ Y) : Y ≤ Y ^ 2 ∧ Y ^ 2 ≤ Y ^ 3 ∧ Y ^ 3 ≤ Y ^ 4 := by
  refine ⟨?_, Nat.pow_le_pow_right hY (by norm_num), Nat.pow_le_pow_right hY (by norm_num)⟩
  calc Y = Y ^ 1 := (pow_one _).symm
    _ ≤ Y ^ 2 := Nat.pow_le_pow_right hY (by norm_num)

section Generic
variable {k : SymCall} {Y : ℕ}

theorem tabLen_le (h : AtomsY k Y) (j : Fin 4) : tabLen k j ≤ 5 * Y ^ 3 := by
  obtain ⟨p12, p23, p34⟩ := pows Y h.one
  have hw := h.walk
  have hJ := h.J
  have hG := h.G j
  unfold tabLen
  rw [flatTable_len]
  have a : 1 + (k.Pl.base.J + 1) * (2 * (gatesJ k j).length + 1) ≤ 1 + Y * (2 * Y + 1) :=
    Nat.add_le_add_left (Nat.mul_le_mul hJ (by omega)) _
  have b : k.Pl.walkLen * (1 + (k.Pl.base.J + 1) * (2 * (gatesJ k j).length + 1)) ≤ Y * (1 + Y * (2 * Y + 1)) :=
    Nat.mul_le_mul hw a
  have e : Y * (1 + Y * (2 * Y + 1)) = 2 * Y ^ 3 + Y ^ 2 + Y := by ring
  rw [e] at b
  have := h.one
  omega

theorem templ_le (h : AtomsY k Y) (j : Fin 4) : (templJ k j).length ≤ 14 * Y ^ 4 := by
  obtain ⟨p12, p23, p34⟩ := pows Y h.one
  have hl := ThrSz.levelWord_le k.Pl.M k.Pl.base.J k.Pl.base.W (fun _ => List.replicate (gatesJ k j).length false)
    Y (gatesJ k j).length h.W (fun _ => by rw [List.length_replicate])
  have hJ := h.J
  have hG := h.G j
  have hM := h.M
  have a : (k.Pl.base.J + 1) * (5 * Y + 5 + (gatesJ k j).length) ≤ Y * (6 * Y + 5) :=
    Nat.mul_le_mul hJ (by omega)
  have e : Y * (6 * Y + 5) = 6 * Y ^ 2 + 5 * Y := by ring
  rw [e] at a
  have := h.one
  show (ListEval.levelWord k.Pl.M k.Pl.base.J k.Pl.base.W
    (fun _ => List.replicate (gatesJ k j).length false)).length ≤ _
  omega

/-- **Every call word is below `16Y⁴`.** -/
theorem word_le (h : AtomsY k Y) (t j : Fin 4) : (wordOf k t j).length ≤ 16 * Y ^ 4 := by
  obtain ⟨p12, p23, p34⟩ := pows Y h.one
  have h1 := h.one
  unfold wordOf
  split_ifs with h0 h1' h2
  · rw [gatesW_length]
    have hn := h.n
    have hG := h.G j
    have hH := h.H j
    have a : 1 + (k.P.n + 1) * (2 * (2 * PrimT.tabH (gatesJ k j) + 1)) ≤ 1 + Y * (2 * (2 * Y + 1)) :=
      Nat.add_le_add_left (Nat.mul_le_mul hn (Nat.mul_le_mul_left 2 (by omega))) _
    have b := Nat.mul_le_mul hG a
    have e : Y * (1 + Y * (2 * (2 * Y + 1))) = 4 * Y ^ 3 + 2 * Y ^ 2 + Y := by ring
    rw [e] at b
    omega
  · rw [frame_len]
    have := h.top j
    omega
  · rw [tablesJ_len]
    have b := Nat.mul_le_mul h.FS (tabLen_le h j)
    have e : Y * (5 * Y ^ 3) = 5 * Y ^ 4 := by ring
    rw [e] at b
    omega
  · have := templ_le h j
    omega

/-- **Every call number is below `16Y⁴`.** -/
theorem num_le (h : AtomsY k Y) (i : Fin 18) : symNums k i ≤ 16 * Y ^ 4 := by
  obtain ⟨p12, p23, p34⟩ := pows Y h.one
  have h1 := h.one
  unfold symNums
  split_ifs with h0 h1'
  · have := k.ha
    omega
  · have := h.FS
    omega
  · unfold numOf
    split_ifs with g0 g1 g2
    · have := h.G ⟨(i.val - 2) % 4, by omega⟩
      omega
    · have := h.H ⟨(i.val - 2) % 4, by omega⟩
      omega
    · have := tabLen_le h ⟨(i.val - 2) % 4, by omega⟩
      omega
    · have := templ_le h ⟨(i.val - 2) % 4, by omega⟩
      omega

/-- **S3's call size below `600Y⁴`.** -/
theorem symSize_le (h : AtomsY k Y) : symSize k ≤ 600 * Y ^ 4 := by
  obtain ⟨p12, p23, p34⟩ := pows Y h.one
  have hw : ∑ i, (symWords k i).length ≤ 16 * (16 * Y ^ 4) := by
    calc ∑ i, (symWords k i).length ≤ ∑ _i : Fin 16, 16 * Y ^ 4 :=
          Finset.sum_le_sum (fun i _ => by unfold symWords; exact word_le h _ _)
      _ = 16 * (16 * Y ^ 4) := by simp
  have hs : ∑ i, symNums k i ≤ 18 * (16 * Y ^ 4) := by
    calc ∑ i, symNums k i ≤ ∑ _i : Fin 18, 16 * Y ^ 4 := Finset.sum_le_sum (fun i _ => num_le h i)
      _ = 18 * (16 * Y ^ 4) := by simp
  have hn := h.n
  unfold symSize
  omega

end Generic

end NearCubicWires.WireExponent3_5.UnionMachine.SymSize
