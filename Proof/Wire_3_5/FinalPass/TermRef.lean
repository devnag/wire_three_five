import Proof.Wire_3_5.FinalPass.PopBridge
import Proof.Wire_3_5.FinalPass.Sym

/-! # Final pass, stage 8: the symmetric-top sample term from the corners (P3:2449-2494, 3170-3178)

At one sampled pair the SYM term of the printed value is `M(e,x)·R̂_{e'}(c,u,v)` (`symValueBits`), where the reported
conjunction is `row:sym-reported` (P3:2489-2494): `R̂ = Π_j g_j(A_j(u) + B_j(v) + t_j^+ − t_j^−)` at the reported
states. With unit weights (`symScore`) the one-sided score of circuit `j` is `A_j(u) + B_j(v) = #[T_i(c+u)] − #[T(c)] +
#[T_i(c+v)]`, a function of the circuit's CORNER word alone (the same word that gives its residual populations,
`popBits`). This module gives the term in the form a machine computes it:
- `cnt k X`: the number of gate occurrences whose corner `k` is one;
- `termOk X top t⁺ t⁻`: `g(#1 − #3 + #2 + [t⁺] − [t⁻])`, with the reports clamped to `{0,…,m}` (`clampState`) and
  `g` the top table extended by zero (`symLookupFn`);
- **`termOk_eq`**: `termOk` on circuit `C`'s corner word is `C`'s factor of `row:sym-reported`;
- **`symRhat_eq_terms`**: `R̂` is the conjunction of the circuits' `termOk`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Term
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Rows
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop NearCubicWires.WireExponent3_5.Lists

/-! ## Counts on the corner word -/

/-- The number of groups (of four corners) whose corner `k` is one. -/
def cnt (k : Fin 4) : List Bool → ℕ
  | a :: b :: c :: d :: rest => (if ![a, b, c, d] k then 1 else 0) + cnt k rest
  | _ => 0

/-- The number of groups. -/
def groups : List Bool → ℕ
  | _ :: _ :: _ :: _ :: rest => groups rest + 1
  | _ => 0

/-- The report clamped to `{0,…,m}` (`clampState`). -/
def clampN (m t : ℕ) : ℕ := if t ≤ m then t else 0

/-- **The circuit's factor from its corners**: `g(#1 − #3 + #2 + [t⁺] − [t⁻])`, `g` the table extended by zero. -/
def termOk (X top : List Bool) (tp tm : ℕ) : Bool :=
  let s : ℤ := (cnt 1 X : ℤ) - cnt 3 X + cnt 2 X + clampN (groups X) tp - clampN (groups X) tm
  decide (0 ≤ s) && top.getD s.toNat false

/-! ## The corner word of a gate list -/

theorem cnt_cornerWord {n : ℕ} (k : Fin 4) (Ts : List (BitInput n → Bool)) (c u v : BitInput n) :
    cnt k (cornerWord Ts c u v) = (Ts.filter fun T => corners T c u v k).length := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih =>
    have e : cornerWord (T :: Ts) c u v =
        corners T c u v 0 :: corners T c u v 1 :: corners T c u v 2 :: corners T c u v 3 :: cornerWord Ts c u v := by
      simp [cornerWord, List.ofFn_succ]
    rw [e, cnt, ih, List.filter_cons]
    have hk : (![corners T c u v 0, corners T c u v 1, corners T c u v 2, corners T c u v 3] : Fin 4 → Bool) k =
        corners T c u v k := by rw [← fin4_fun_eq]
    rw [hk]
    split <;> simp_all [Nat.add_comm]

theorem groups_cornerWord {n : ℕ} (Ts : List (BitInput n → Bool)) (c u v : BitInput n) :
    groups (cornerWord Ts c u v) = Ts.length := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih =>
    have e : cornerWord (T :: Ts) c u v =
        corners T c u v 0 :: corners T c u v 1 :: corners T c u v 2 :: corners T c u v 3 :: cornerWord Ts c u v := by
      simp [cornerWord, List.ofFn_succ]
    rw [e, groups, ih, List.length_cons]

/-! ## The factor of `row:sym-reported` -/

theorem clampN_eq (m t : ℕ) : clampN m t = (clampState m t : ℕ) := by
  unfold clampN clampState; split <;> rfl

/-- Close an integer identity over Boolean cases. -/
macro "bool_ring" : tactic => `(tactic| (simp [bitZ] <;> ring))

theorem rowLeft_unit {n : ℕ} (G : List (NormalizedThresholdGate n)) (c u : BitInput n) :
    rowLeft (0 : ℤ) (unitGates G) c u =
      ((G.filter fun g => g.eval (xorInput c u)).length : ℤ) - (G.filter fun g => g.eval c).length := by
  unfold rowLeft unitGates
  induction G with
  | nil => simp
  | cons g G ih =>
    simp only [List.map_cons, List.sum_cons, zero_add] at ih ⊢
    rw [ih]
    simp only [List.filter_cons]
    cases g.eval (xorInput c u) <;> cases g.eval c <;> bool_ring

theorem rowRight_unit {n : ℕ} (G : List (NormalizedThresholdGate n)) (c v : BitInput n) :
    rowRight (unitGates G) c v = ((G.filter fun g => g.eval (xorInput c v)).length : ℤ) := by
  unfold rowRight unitGates
  induction G with
  | nil => simp
  | cons g G ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [List.filter_cons]
    cases g.eval (xorInput c v) <;> bool_ring

theorem cnt_gates {n : ℕ} (k : Fin 4) (G : List (NormalizedThresholdGate n)) (c u v : BitInput n) :
    cnt k (cornerWord (G.map fun g => g.eval) c u v) = (G.filter fun g => corners g.eval c u v k).length := by
  rw [cnt_cornerWord, List.filter_map, List.length_map]; rfl

/-- **The circuit's factor from its corners** is `g_C(A_C(u) + B_C(v) + [t⁺] − [t⁻])` (row:sym-reported). -/
theorem termOk_eq {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (c u v : BitInput n) (tp tm : ℕ) :
    termOk (cornerWord ((symGates C).map fun g => g.eval) c u v) (List.ofFn C.top) tp tm =
      symLookupFn C (symLeftScore C c u + symRightScore C c v + ((clampState C.bottomCount tp : ℕ) : ℤ) -
        ((clampState C.bottomCount tm : ℕ) : ℤ)) := by
  have hg : groups (cornerWord ((symGates C).map fun g => g.eval) c u v) = C.bottomCount := by
    rw [groups_cornerWord, List.length_map, length_symGates]
  unfold termOk symLeftScore symRightScore
  rw [hg, rowLeft_unit, rowRight_unit, cnt_gates, cnt_gates, cnt_gates, clampN_eq, clampN_eq]
  have e1 : ∀ g : NormalizedThresholdGate n, corners g.eval c u v 1 = g.eval (xorInput c u) := fun _ => rfl
  have e2 : ∀ g : NormalizedThresholdGate n, corners g.eval c u v 2 = g.eval (xorInput c v) := fun _ => rfl
  have e3 : ∀ g : NormalizedThresholdGate n, corners g.eval c u v 3 = g.eval c := fun _ => rfl
  simp only [e1, e2, e3]
  generalize ((symGates C).filter fun g => g.eval (xorInput c u)).length = n1
  generalize ((symGates C).filter fun g => g.eval (xorInput c v)).length = n2
  generalize ((symGates C).filter fun g => g.eval c).length = n3
  generalize ((clampState C.bottomCount tp : ℕ)) = cp
  generalize ((clampState C.bottomCount tm : ℕ)) = cm
  have hs : ((n1 : ℤ) - n3 + n2 + cp - cm) = (n1 : ℤ) - n3 + n2 + cp - cm := rfl
  generalize hS : ((n1 : ℤ) - n3 + n2 + cp - cm) = S
  unfold symLookupFn
  by_cases h0 : 0 ≤ S
  · rw [decide_eq_true h0, Bool.true_and]
    by_cases hm : S.toNat ≤ C.bottomCount
    · rw [dif_pos ⟨h0, hm⟩, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    · rw [dif_neg (fun h => hm h.2), List.getD_eq_default _ _ (by simp; omega)]
  · rw [decide_eq_false h0, Bool.false_and, dif_neg (fun h => h0 h.1)]

/-! ## The reported conjunction from the corners -/

section Sym
variable (P : StarParams) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (Pl : FlatListParams)

/-- The corner word of circuit `j` at the sampled pair. -/
def cornersOf (c : BitInput P.n) (u v : P.Errors) (j : Fin a) : List Bool :=
  cornerWord ((symGates (Cs j)).map fun g => g.eval) c (P.errorVector P.leftBlock u) (P.errorVector P.rightBlock v)

/-- **`R̂` is the conjunction of the circuits' factors**, each from its corner word and its lists' reports. -/
theorem symRhatFast_eq_terms (el : Pl.FlatSeed) (c : BitInput P.n) (u v : P.Errors) :
    symRhatFast P Cs Pl el c u v = (List.finRange a).all fun j =>
      termOk (cornersOf P Cs c u v j) (List.ofFn (Cs j).top) (symRepFast P Cs Pl el c u v j).1
        (symRepFast P Cs Pl el c u v j).2 := by
  unfold symRhatFast symReported
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, List.all_eq_true]
  have e : ∀ j : Fin a, termOk (cornersOf P Cs c u v j) (List.ofFn (Cs j).top) (symRepFast P Cs Pl el c u v j).1
      (symRepFast P Cs Pl el c u v j).2 = symG P Cs j (symScore P Cs c u v j +
        symShift (symM P Cs) (symReportState (symM P Cs) (symRepFast P Cs Pl el c u v)) j) := by
    intro j
    unfold cornersOf
    rw [termOk_eq]
    unfold symG symScore symShift symReportState symM
    congr 1
    ring
  constructor
  · intro h j _; rw [e]; exact h j
  · intro h j; rw [← e]; exact h j (List.mem_finRange j)

/-- The residual populations of circuit `j` are stage 3's bits on its corner word. -/
theorem symZp_eq_pop (c : BitInput P.n) (u v : P.Errors) (j : Fin a) :
    symZp P Cs c u v j = popBits true (cornersOf P Cs c u v j) := by
  unfold symZp cornersOf plusBits
  rw [(popBits_cornerWord _ _ _ _).1, List.map_map]
  rfl

theorem symZm_eq_pop (c : BitInput P.n) (u v : P.Errors) (j : Fin a) :
    symZm P Cs c u v j = popBits false (cornersOf P Cs c u v j) := by
  unfold symZm cornersOf minusBits
  rw [(popBits_cornerWord _ _ _ _).2, List.map_map]
  rfl

end Sym

end NearCubicWires.WireExponent3_5.FinalPass.Term
