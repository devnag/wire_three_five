import Proof.Wire_3_5.Foundations.S0

/-! # `alg:polarization`: exact product-to-parity conversion (P3:1830-1856), and the polarization stage of
`alg:compiler` (P3:1918-1923)

Realizes "For an integer `t ≥ 1` and bits `b_1,…,b_t`, with repetitions allowed,
`2^{t−1}∏_{i=1}^t b_i = Σ_{∅≠J⊆[t]} (−1)^{|J|−1} ⊕_{j∈J} b_j`. If every `b_i` is an `𝔽₂` polynomial of degree at most
`d` in a common atom pool, every parity on the right has degree at most `d`" (P3:1832-1843), and its use in the proof
of `alg:compiler`: "Multiply the expression by `2^{m−1}`. For a nonconstant term of length `t_ν`,
Lemma alg:polarization replaces its product by at most `2^{t_ν}−1` parities, with integer coefficient multiplier
`2^{m−t_ν}`. A constant term instead has multiplier `2^{m−1}`. Thus there are at most `A2^m` Boolean polynomials, all of
degree at most `d`" (P3:1918-1923).

`J` ranges over the sub-lists of positions (`List.sublists'`), so repeated bits are allowed; the empty sub-list is kept
(its parity is `0`, so its term vanishes), which gives at most `2^{t_ν}` parities per term.

Main declarations (on the S0 types `F2Poly`, `IntExpression`): `xorAll`, `chi`; **`polarization`** (the identity);
`F2Poly.eval_append`, `F2Poly.eval_flatten`; **`polarize m V`** (the ref) with **`polarize_value`**
(`Σ w·[p] = 2^{m−1}·V` exactly, when every term has at most `m` factors), `polarize_length_le` (`≤ A·2^m`) and
`polarize_degree_le` (every parity has degree `≤ d`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-- The parity of a list of bits. -/
def xorAll : List Bool → Bool
  | [] => false
  | b :: l => xor b (xorAll l)

/-- The spin `χ(b) = 1 − 2b` (P3:1846). -/
def chi (b : Bool) : ℤ := 1 - 2 * bitZ b

theorem two_bitZ_xorAll (l : List Bool) : 2 * bitZ (xorAll l) = 1 - (l.map chi).prod := by
  induction l with
  | nil => simp [xorAll, bitZ]
  | cons b l ih =>
    simp only [xorAll, List.map_cons, List.prod_cons]
    have hl : (l.map chi).prod = 1 - 2 * bitZ (xorAll l) := by linarith
    rw [hl]
    cases b <;> cases xorAll l <;> simp [chi, bitZ]

theorem sum_map_neg' {β : Type} (l : List β) (f : β → ℤ) : (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- `Σ_{J ⊆ l} (−1)^{|J|} ∏_{j∈J} f j = ∏_{x∈l} (1 − f x)`, over the sub-lists of positions. -/
theorem sum_sublists'_signed_prod {β : Type} (l : List β) (f : β → ℤ) :
    (l.sublists'.map fun J => (-1) ^ J.length * (J.map f).prod).sum = (l.map fun x => 1 - f x).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sublists'_cons, List.map_append, List.sum_append, List.map_map, List.map_cons, List.prod_cons, ← ih]
    have : ((l.sublists'.map ((fun J => (-1) ^ J.length * (J.map f).prod) ∘ List.cons a))) =
        l.sublists'.map fun J => -f a * ((-1) ^ J.length * (J.map f).prod) := by
      apply List.map_congr_left
      intro J _
      simp only [Function.comp, List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      ring
    rw [this, List.sum_map_mul_left]; ring

/-- `Σ_{J ⊆ l} (−1)^{|J|} = 0` for a nonempty list. -/
theorem sum_sublists'_signed {β : Type} (a : β) (l : List β) :
    ((a :: l).sublists'.map fun J => ((-1 : ℤ) ^ J.length)).sum = 0 := by
  rw [List.sublists'_cons, List.map_append, List.sum_append, List.map_map]
  have : ((l.sublists'.map ((fun J => ((-1 : ℤ) ^ J.length)) ∘ List.cons a))) =
      l.sublists'.map fun J => -((-1 : ℤ) ^ J.length) := by
    apply List.map_congr_left
    intro J _
    simp [Function.comp, pow_succ]
  rw [this, sum_map_neg']; ring

theorem prod_one_sub_chi {β : Type} (l : List β) (f : β → Bool) :
    (l.map fun x => 1 - chi (f x)).prod = 2 ^ l.length * (l.map fun x => bitZ (f x)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [ih]
    simp only [chi, pow_succ]
    ring

/-- **`alg:polarization`** (P3:1832-1836): for a nonempty list (repetitions allowed) and bits `f`,
`2^{t−1}∏ f = Σ_{J ⊆ [t]} −(−1)^{|J|} ⊕_{j∈J} f j` (the empty `J` contributes `0`). -/
theorem polarization {β : Type} (l : List β) (f : β → Bool) (hl : l ≠ []) :
    2 ^ (l.length - 1) * (l.map fun x => bitZ (f x)).prod =
      (l.sublists'.map fun J => -(-1 : ℤ) ^ J.length * bitZ (xorAll (J.map f))).sum := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  have hterm : ∀ J : List β, 2 * (-(-1 : ℤ) ^ J.length * bitZ (xorAll (J.map f))) =
      -((-1 : ℤ) ^ J.length) + (-1 : ℤ) ^ J.length * (J.map fun x => chi (f x)).prod := by
    intro J
    have := two_bitZ_xorAll (J.map f)
    rw [List.map_map, show (chi ∘ f) = (fun x => chi (f x)) from rfl] at this
    linear_combination (-(-1 : ℤ) ^ J.length) * this
  have h2 : 2 * ((a :: l').sublists'.map fun J => -(-1 : ℤ) ^ J.length * bitZ (xorAll (J.map f))).sum =
      2 ^ (a :: l').length * ((a :: l').map fun x => bitZ (f x)).prod := by
    rw [← List.sum_map_mul_left, List.map_congr_left (fun J _ => hterm J), List.sum_map_add, sum_map_neg',
      sum_sublists'_signed a l', neg_zero, zero_add, sum_sublists'_signed_prod, prod_one_sub_chi]
  have hpow : (2 : ℤ) ^ (a :: l').length = 2 * 2 ^ ((a :: l').length - 1) := by
    rw [← pow_succ']; congr 1
  rw [hpow] at h2
  linarith

/-! ## Polynomials -/

theorem foldl_xor_init {β : Type} (f : β → Bool) (l : List β) (a b : Bool) :
    l.foldl (fun acc m => xor acc (f m)) (xor a b) = xor a (l.foldl (fun acc m => xor acc (f m)) b) := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, Bool.xor_assoc, ih]

theorem F2Poly.eval_append {Atom : Type} (p q : F2Poly Atom) (ρ : Atom → Bool) :
    F2Poly.eval (p ++ q) ρ = xor (F2Poly.eval p ρ) (F2Poly.eval q ρ) := by
  unfold F2Poly.eval
  rw [List.foldl_append]
  have := foldl_xor_init (fun m => m.all ρ) q (List.foldl (fun acc m => xor acc (m.all ρ)) false p) false
  simpa using this

theorem F2Poly.eval_flatten {Atom : Type} (J : List (F2Poly Atom)) (ρ : Atom → Bool) :
    F2Poly.eval J.flatten ρ = xorAll (J.map fun p => F2Poly.eval p ρ) := by
  induction J with
  | nil => rfl
  | cons p J ih => rw [List.flatten_cons, F2Poly.eval_append, ih]; rfl

/-- One term `c·∏ p_j` of an explicit integer expression, multiplied by `2^{m−1}`, as signed parities (P3:1918-1922):
a constant term keeps the constant-one polynomial with multiplier `2^{m−1}`; a term of length `t ≥ 1` becomes
`c·2^{m−t}·(−(−1)^{|J|})·[⊕_{j∈J} p_j]` over the sub-lists `J`. -/
def polarizeTerm {Atom : Type} (m : ℕ) (c : ℤ) (ps : List (F2Poly Atom)) : List (ℤ × F2Poly Atom) :=
  if ps = [] then [(2 ^ (m - 1) * c, [[]])]
  else ps.sublists'.map fun J => (c * 2 ^ (m - ps.length) * -(-1 : ℤ) ^ J.length, J.flatten)

/-- **The polarization stage** of `alg:compiler` (P3:1918-1923): an explicit integer expression, times `2^{m−1}`, as a
list of signed `𝔽₂` polynomials. -/
def polarize {Atom : Type} (m : ℕ) (V : IntExpression Atom) : List (ℤ × F2Poly Atom) :=
  V.flatMap fun t => polarizeTerm m t.1 t.2

/-- The value of a list of signed polynomials. -/
def signedValue {Atom : Type} (L : List (ℤ × F2Poly Atom)) (ρ : Atom → Bool) : ℤ :=
  (L.map fun w => w.1 * bitZ (F2Poly.eval w.2 ρ)).sum

theorem signedValue_append {Atom : Type} (L L' : List (ℤ × F2Poly Atom)) (ρ : Atom → Bool) :
    signedValue (L ++ L') ρ = signedValue L ρ + signedValue L' ρ := by
  simp [signedValue, List.sum_append]

theorem polarizeTerm_value {Atom : Type} (m : ℕ) (hm : 1 ≤ m) (c : ℤ) (ps : List (F2Poly Atom))
    (hps : ps.length ≤ m) (ρ : Atom → Bool) :
    signedValue (polarizeTerm m c ps) ρ = 2 ^ (m - 1) * (c * (ps.map fun p => bitZ (F2Poly.eval p ρ)).prod) := by
  unfold polarizeTerm
  split_ifs with h
  · subst h
    simp [signedValue, F2Poly.eval, bitZ]
  · have hb := polarization ps (fun p => F2Poly.eval p ρ) h
    unfold signedValue
    rw [List.map_map]
    have hterm : ∀ J : List (F2Poly Atom),
        ((fun w : ℤ × F2Poly Atom => w.1 * bitZ (F2Poly.eval w.2 ρ)) ∘
          fun J => (c * 2 ^ (m - ps.length) * -(-1 : ℤ) ^ J.length, J.flatten)) J =
        c * 2 ^ (m - ps.length) * (-(-1 : ℤ) ^ J.length * bitZ (xorAll (J.map fun p => F2Poly.eval p ρ))) := by
      intro J
      simp only [Function.comp, F2Poly.eval_flatten]
      ring
    rw [List.map_congr_left (fun J _ => hterm J), List.sum_map_mul_left, ← hb]
    have hlen : 1 ≤ ps.length := List.length_pos_iff.mpr h
    have hpow : (2 : ℤ) ^ (m - ps.length) * 2 ^ (ps.length - 1) = 2 ^ (m - 1) := by
      rw [← pow_add]; congr 1; omega
    calc c * 2 ^ (m - ps.length) * (2 ^ (ps.length - 1) * (ps.map fun p => bitZ (F2Poly.eval p ρ)).prod)
        = (2 ^ (m - ps.length) * 2 ^ (ps.length - 1)) * (c * (ps.map fun p => bitZ (F2Poly.eval p ρ)).prod) := by
          ring
      _ = 2 ^ (m - 1) * (c * (ps.map fun p => bitZ (F2Poly.eval p ρ)).prod) := by rw [hpow]

/-- **The polarized expression has the value `2^{m−1}V`**, exactly, when every term has at most `m ≥ 1` factors. -/
theorem polarize_value {Atom : Type} (m : ℕ) (hm : 1 ≤ m) (V : IntExpression Atom)
    (hV : ∀ t ∈ V, t.2.length ≤ m) (ρ : Atom → Bool) :
    signedValue (polarize m V) ρ = 2 ^ (m - 1) * IntExpression.eval V ρ := by
  induction V with
  | nil => simp [polarize, signedValue, IntExpression.eval]
  | cons t V ih =>
    simp only [polarize, List.flatMap_cons] at ih ⊢
    rw [signedValue_append, polarizeTerm_value m hm t.1 t.2 (hV t (List.mem_cons_self)) ρ,
      ih (fun t' ht' => hV t' (List.mem_cons_of_mem _ ht'))]
    simp only [IntExpression.eval, List.map_cons, List.sum_cons]
    ring

/-- At most `2^m` signed polynomials per term: `|polarize m V| ≤ A·2^m` (P3:1922). -/
theorem polarize_length_le {Atom : Type} (m : ℕ) (V : IntExpression Atom) (hV : ∀ t ∈ V, t.2.length ≤ m) :
    (polarize m V).length ≤ V.length * 2 ^ m := by
  induction V with
  | nil => simp [polarize]
  | cons t V ih =>
    simp only [polarize, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have h1 : (polarizeTerm m t.1 t.2).length ≤ 2 ^ m := by
      unfold polarizeTerm
      split_ifs
      · simp; exact Nat.one_le_two_pow
      · rw [List.length_map, List.length_sublists']
        exact Nat.pow_le_pow_right (by norm_num) (hV t List.mem_cons_self)
    have := ih (fun t' ht' => hV t' (List.mem_cons_of_mem _ ht'))
    nlinarith

/-- Every monomial of every polarized polynomial is a monomial of one of the factors (so the degree stays `≤ d`,
P3:1837-1838, 1923). -/
theorem polarize_mono_mem {Atom : Type} (m : ℕ) (V : IntExpression Atom) (w : ℤ × F2Poly Atom)
    (hw : w ∈ polarize m V) (mono : List Atom) (hmono : mono ∈ w.2) :
    mono = [] ∨ ∃ t ∈ V, ∃ p ∈ t.2, mono ∈ p := by
  simp only [polarize, List.mem_flatMap] at hw
  obtain ⟨t, ht, hw⟩ := hw
  unfold polarizeTerm at hw
  split_ifs at hw with h
  · simp only [List.mem_singleton] at hw
    subst hw
    left; simpa using hmono
  · simp only [List.mem_map] at hw
    obtain ⟨J, hJ, rfl⟩ := hw
    right
    simp only [List.mem_flatten] at hmono
    obtain ⟨p, hp, hm⟩ := hmono
    exact ⟨t, ht, p, (List.mem_sublists'.mp hJ).subset hp, hm⟩

end NearCubicWires.WireExponent3_5.Compiler
