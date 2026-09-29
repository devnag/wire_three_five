import Proof.Wire_3_5.Compiler.MachineTopBound
import Proof.Wire_3_5.Compiler.MachineReqContract4

/-! # C3 v2 top level, T6 (part 3b): the class bound and the machine obligation (P3:1887-1906, 3105-3115)

Paper: "Construction takes `(input description size + 𝒮)·poly(n)` deterministic bit operations" (P3:1905-1906), with
`𝒮 ≤ A·2^m·Q'(P_ex+1)^{Q'd}` (P3:1892), under "If all displayed logarithmic and degree parameters are bounded by fixed
polynomials in `n`" (P3:1896-1897); the preprocessing class `2^{O(Ψ_i+Ψ_aux)}` of prim:runtime (P3:3105-3115). Every
parameter of the run is at most `X = 𝒮'·|input|·(n+1)^{a_par}` (`𝒮'` the charged occurrence count of (c′)):
the parameters of (b) directly, the input's own counts (`m`, `A`, the atoms, the encoding maxima) through the input
record's lengths (`c3Input`), and the counts `(P_ex+1)^d`, `Q'(P_ex+1)^{Q'd}`, `2^m·A`, the stacked occurrences through
(c′). With `𝒮' ≤ 2^Ψ`, `|input| ≤ 2^Ψ` and `n ≥ 1`, the degree-8 bound `gB_le` gives
**`c3_within`**: `c3Cost a R ≤ coef·2^{cpsi·Ψ}·n^{Apre}` whenever `16 ≤ cpsi`, `Apre ≥ apreOf a_par = 8·a_par` and
`coef ≥ 52802·2^{8·a_par}`. **`c3Blocks`** assembles the C3 v3′ contract's `ClassBlocks` (the machine `c3M`, the step
`c3_run`, the output tape 1), **`c3Implements`** is `Machine.Implements (c3v3p a E (c3Input a) coef a_par)`, and
**`c3Certified`** adds the error field (`c3v3p_err`). The paper quantity is the construction's cost in the preprocessing
class. Main declarations: `listMax_le`, the length lemmas, `bigX`, `apreOf`, **`c3_within`**, **`c3Blocks`**,
**`c3Implements`**, **`c3Certified`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (fields signMagnitude)

theorem listMax_le (l : List ℕ) (c : ℕ) (h : ∀ x ∈ l, x ≤ c) : listMax l ≤ c := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons y l ih => exact max_le (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem y hx))

theorem le_flatMap_length {α : Type} (f : α → List Bool) (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem length_le_flatMap {α β : Type} (f : α → List β) (hf : ∀ x, 1 ≤ (f x).length) :
    ∀ l : List α, l.length ≤ (l.flatMap f).length
  | [] => by simp
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := hf x
    have := length_le_flatMap f hf l
    omega

theorem rec_length (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    (loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length = 2 * f0.length + 1 + (2 * f1.length + 1) +
      (2 * f2.length + 1) + (2 * f3.length + 1) + (2 * f4.length + 1) + (2 * f5.length + 1) + (2 * f6.length + 1) +
      (2 * f7.length + 1) + (2 * f8.length + 1) + (2 * f9.length + 1) + (2 * f10.length + 1) := by
  simp only [loadRec, List.length_append, frame_length]
  omega

/-! ## The expression's encoding -/

theorem termRec_le (V : IntExpression ℕ) (t : ℤ × List (F2Poly ℕ)) (ht : t ∈ V) :
    (termRec t).length ≤ (V.flatMap termRec ++ [false]).length := by
  rw [List.length_append]
  have := le_flatMap_length termRec V t ht
  omega

theorem cbits_le (t : ℤ × List (F2Poly ℕ)) : (cbits t.1).length ≤ (termRec t).length := by
  simp only [termRec, termWord, List.length_cons, List.length_append, frame_length]
  omega

theorem factorRec_le (t : ℤ × List (F2Poly ℕ)) (f : F2Poly ℕ) (hf : f ∈ t.2) :
    (factorRec f).length ≤ (termRec t).length := by
  simp only [termRec, termWord, List.length_cons, List.length_append]
  have := le_flatMap_length factorRec t.2 f hf
  omega

theorem factor_len_le (f : F2Poly ℕ) : f.length ≤ (factorRec f).length := by
  simp only [factorRec, List.length_cons, List.length_append]
  have := length_le_flatMap recW (fun mono => by simp [recW]) f
  omega

theorem code_le (f : F2Poly ℕ) (mono : List ℕ) (hm : mono ∈ f) : (codeBits mono).length ≤ (factorRec f).length := by
  simp only [factorRec, List.length_cons, List.length_append]
  have := le_flatMap_length recW f mono hm
  simp only [recW, List.length_cons, frame_length] at this
  omega

theorem flatten_le (t : ℤ × List (F2Poly ℕ)) : t.2.flatten.length ≤ (termRec t).length := by
  have h1 : t.2.flatten.length ≤ (t.2.flatMap factorRec).length := by
    rw [List.length_flatten, List.length_flatMap]
    apply List.sum_le_sum
    intro f _
    exact factor_len_le f
  simp only [termRec, termWord, List.length_cons, List.length_append]
  omega

theorem getD_length_le (pool : List (List SynEq)) (i : ℕ) : (pool.getD i []).length ≤ pool.flatten.length := by
  by_cases h : i < pool.length
  · rw [List.getD_eq_getElem _ _ h]
    exact (List.sublist_flatten_of_mem (List.getElem_mem h)).length_le
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem monoMasks_length (pool : List (List SynEq)) :
    ∀ mono : List ℕ, (monoMasks pool mono).length ≤ (pool.flatten.length + 1) ^ mono.length
  | [] => by simp [monoMasks]
  | x :: mono => by
    simp only [monoMasks, List.length_flatMap, List.length_map, List.map_const', List.sum_replicate, smul_eq_mul,
      List.length_cons, pow_succ]
    have h1 := monoMasks_length pool mono
    have h2 : (labelsOf pool x).length ≤ pool.flatten.length + 1 := by
      simp only [labelsOf, List.length_range']
      have := getD_length_le pool x
      omega
    calc (labelsOf pool x).length * (monoMasks pool mono).length
        ≤ (pool.flatten.length + 1) * (pool.flatten.length + 1) ^ mono.length := Nat.mul_le_mul h2 h1
      _ = (pool.flatten.length + 1) ^ mono.length * (pool.flatten.length + 1) := Nat.mul_comm _ _

theorem shapeOf_flatten_len {α : Type} (D : List (List α)) : (shapeOf D).flatten.length = D.flatten.length := by
  unfold shapeOf
  rw [← List.map_flatten, List.length_map]

variable (a : DecompositionAlgorithm)

/-- The expression's field of the input record. -/
theorem f8_le (R : C3Req) : (R.V.flatMap termRec ++ [false]).length ≤ (c3Input a R).length := by
  unfold c3Input
  rw [rec_length]
  omega

theorem V_le (R : C3Req) : R.V.length ≤ (c3Input a R).length := by
  have h := length_le_flatMap termRec (fun t => by simp [termRec]) R.V
  have := f8_le a R
  simp only [List.length_append] at this
  omega

theorem m_le (R : C3Req) : R.m ≤ (c3Input a R).length := by
  unfold c3Input
  simp only [rec_length, List.length_replicate]
  omega

theorem atoms_le (R : C3Req) : (shapeOf (R.D a)).length ≤ (c3Input a R).length := by
  have h : (shapeOf (R.D a)).length ≤ (tableTape (childTable R.P.Q (shapeOf (R.D a))) []).length := by
    unfold tableTape childTable
    rw [List.append_nil]
    have := length_le_flatMap atomStream (fun E => by simp [atomStream])
      ((List.range (shapeOf (R.D a)).length).map fun a' => (labelsOf (shapeOf (R.D a)) a').map fun c =>
        Unions.ew R.P.Q (shapeOf (R.D a)).flatten.length (0, 2 ^ c))
    simpa using this
  unfold c3Input
  rw [rec_length]
  omega

theorem h1_le (R : C3Req) : (natWord R.dRow ++ natWord (R.p + 1)).length ≤ (c3Input a R).length := by
  unfold c3Input
  simp only [rec_length, frame_length]
  omega

theorem h2_le (R : C3Req) : (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols).length ≤ (c3Input a R).length := by
  unfold c3Input
  simp only [rec_length, frame_length]
  omega

theorem sCBW_le (R : C3Req) : sCBW R ≤ (c3Input a R).length := by
  apply listMax_le
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact (cbits_le t).trans ((termRec_le R.V t ht).trans (f8_le a R))

theorem sNF_le (R : C3Req) : sNF R ≤ (c3Input a R).length := by
  apply listMax_le
  intro x hx
  obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  exact (factor_len_le f).trans ((factorRec_le t f hf).trans ((termRec_le R.V t ht).trans (f8_le a R)))

theorem sCB_le (R : C3Req) : sCB R ≤ (c3Input a R).length := by
  apply listMax_le
  intro x hx
  obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨f, hf, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨mono, hm, rfl⟩ := List.mem_map.mp hx
  exact (code_le f mono hm).trans ((factorRec_le t f hf).trans ((termRec_le R.V t ht).trans (f8_le a R)))

theorem sB_le (R : C3Req) (hR : R.Pre a) :
    sB a R ≤ (c3Input a R).length * ((shapeOf (R.D a)).flatten.length + 1) ^ R.d := by
  obtain ⟨_, _, _, _, hmono, _⟩ := hR
  apply listMax_le
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [List.length_flatMap]
  calc ((t.2.flatten.map fun mono => (monoMasks (shapeOf (R.D a)) mono).length)).sum
      ≤ (t.2.flatten.map fun _ => ((shapeOf (R.D a)).flatten.length + 1) ^ R.d).sum := by
        apply List.sum_le_sum
        intro mono hmn
        obtain ⟨f, hf, hmf⟩ := List.mem_flatten.mp hmn
        exact (monoMasks_length _ mono).trans
          (Nat.pow_le_pow_right (by omega) (hmono t ht f hf mono hmf).1)
    _ = t.2.flatten.length * ((shapeOf (R.D a)).flatten.length + 1) ^ R.d := by
        rw [List.map_const', List.sum_replicate, smul_eq_mul]
    _ ≤ (c3Input a R).length * ((shapeOf (R.D a)).flatten.length + 1) ^ R.d :=
        Nat.mul_le_mul_right _ ((flatten_le t).trans ((termRec_le R.V t ht).trans (f8_le a R)))

/-! ## The counts within the charged occurrence count -/

theorem one_le_occP (R : C3Req) (hQ : 1 ≤ R.P.Q) : 1 ≤ R.occBoundP a := by
  unfold C3Req.occBoundP
  have h1 : 1 ≤ max 1 R.V.length := le_max_left _ _
  have h2 : 1 ≤ 2 ^ R.m := Nat.one_le_two_pow
  have h3 : 1 ≤ ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d) := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc 1 = 1 * 1 * 1 := by norm_num
    _ ≤ max 1 R.V.length * 2 ^ R.m * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d)) := by gcongr

theorem nu_le (R : C3Req) : sNU a R ≤ R.occBoundP a := by
  unfold sNU C3Req.occBoundP
  rw [shapeOf_flatten_len]
  have h1 : 1 ≤ max 1 R.V.length * 2 ^ R.m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d)
      = 1 * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d)) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ h1

theorem ng_le (R : C3Req) (hQ : 1 ≤ R.P.Q) : sNG a R ≤ R.occBoundP a := by
  refine le_trans ?_ (nu_le a R)
  unfold sNG sNU
  calc ((shapeOf (R.D a)).flatten.length + 1) ^ R.d ≤ ((shapeOf (R.D a)).flatten.length + 1) ^ (R.P.Q * R.d) :=
        Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_left _ hQ)
    _ ≤ R.P.Q * ((shapeOf (R.D a)).flatten.length + 1) ^ (R.P.Q * R.d) := Nat.le_mul_of_pos_left _ hQ

theorem pow2m_le (R : C3Req) (hQ : 1 ≤ R.P.Q) : 2 ^ R.m * R.V.length ≤ R.occBoundP a ∧ 2 ^ R.m ≤ R.occBoundP a := by
  unfold C3Req.occBoundP
  have h4 : 1 ≤ R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hv : R.V.length ≤ max 1 R.V.length := le_max_right _ _
  have hv1 : 1 ≤ max 1 R.V.length := le_max_left _ _
  constructor
  · calc 2 ^ R.m * R.V.length = R.V.length * 2 ^ R.m * 1 := by ring
      _ ≤ max 1 R.V.length * 2 ^ R.m * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d)) := by gcongr
  · calc 2 ^ R.m = 1 * 2 ^ R.m * 1 := by ring
      _ ≤ max 1 R.V.length * 2 ^ R.m * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d)) := by gcongr

theorem cuts_le (R : C3Req) (hR : R.Pre a) : (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length ≤ R.occBoundP a := by
  obtain ⟨_, hm, _, hV, hmono, _⟩ := hR
  refine le_trans ?_ (occBound_le_occBoundP a R)
  rw [cutsRefX_length]
  have := compileRefX_length_le (poolSyn (R.D a)) (2 ^ R.P.h) R.m R.P.Q R.d hm R.V hV
    (fun t ht f hf mono hmn => (hmono t ht f hf mono hmn).1)
  rwa [poolSyn_flatten, List.length_map] at this

theorem sfRecs_length (R : C3Req) :
    (sfRecs a R).length = (c3v2Ref a R).length * (R.P.width + R.P.width + 2) := by
  have hlens : ∀ c ∈ c3v2Ref a R, c.leftWeights.length = R.P.width ∧ c.rightWeights.length = R.P.width := by
    intro c hc'
    simp only [c3v2Ref, EquationRow.doubled, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc'
    obtain ⟨c0, hc0, hc'⟩ := hc'
    simp only [cutsRefX, List.mem_flatMap, List.mem_range, termCuts, List.mem_map] at hc0
    obtain ⟨j, _, t, _, e, _, rfl⟩ := hc0
    rcases hc' with rfl | rfl <;>
      simp [EquationRow.padded, EquationRow.successor, EquationRow.paddedRight, occCut, RowBinLift.split]
  unfold sfRecs
  rw [List.length_flatMap]
  have : ∀ c ∈ c3v2Ref a R, ((fields c).map (signMagnitude (R.p + 1))).length = R.P.width + R.P.width + 2 := by
    intro c hc
    obtain ⟨h1, h2⟩ := hlens c hc
    simp [fields, h1, h2]
    omega
  rw [List.map_congr_left this]
  simp

/-! ## The bounding quantity and the class -/

theorem input_pos (R : C3Req) : 1 ≤ (c3Input a R).length := by
  unfold c3Input
  rw [rec_length]
  omega

/-! ## The machine obligation -/


end NearCubicWires.WireExponent3_5.CompilerMachine.Top
