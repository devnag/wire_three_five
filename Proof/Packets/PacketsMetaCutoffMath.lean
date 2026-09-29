import Proof.Assembly.Production

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMeta.CutoffMath
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ThresholdAlignedEnvelope
open scoped BigOperators

/-! ## The definitions the machine proof is written against -/

abbrev Rec := ℕ × ℕ × ℕ

def childRec {n : ℕ} (g : ExactThresholdGate n) : Rec :=
  (((List.ofFn g.weight).map Int.natAbs).sum, g.target.toNat, (-g.target).toNat)

def recMag (x : Rec) : ℕ := x.1 + x.2.1 + x.2.2

def horner (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + b * horner b ds

def selMag (s : List Rec) : ℕ :=
  horner ((s.map recMag).sum + 1) (s.map (·.1)) +
    Int.natAbs ((horner ((s.map recMag).sum + 1) (s.map (·.2.1)) : ℤ) -
      (horner ((s.map recMag).sum + 1) (s.map (·.2.2)) : ℤ))

def tables (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    List (List Rec) :=
  r.circuits.map (fun c => (ThresholdRows.children a c).map childRec) ++
    List.replicate (4 - r.circuits.length) [((0 : ℕ), (0 : ℕ), (0 : ℕ))]

def T (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i : ℕ) :
    List Rec := (tables a r).getD i []

def nestedSum (T0 T1 T2 T3 : List Rec) (f : List Rec → ℕ) : ℕ :=
  (T0.map fun x0 => (T1.map fun x1 => (T2.map fun x2 => (T3.map fun x3 =>
    f [x0, x1, x2, x3]).sum).sum).sum).sum

/-! ## Generic list sums over a product of lists -/

/-- The sum of `g` over the cartesian product of `Ls` (first list outermost). -/
def secSum {α : Type} : List (List α) → (List α → ℕ) → ℕ
  | [], g => g []
  | L :: Ls, g => (L.map fun x => secSum Ls (fun s => g (x :: s))).sum

theorem secSum_four {α : Type} (T0 T1 T2 T3 : List α) (f : List α → ℕ) :
    secSum [T0, T1, T2, T3] f =
      (T0.map fun x0 => (T1.map fun x1 => (T2.map fun x2 => (T3.map fun x3 =>
        f [x0, x1, x2, x3]).sum).sum).sum).sum := rfl

theorem secSum_pad {α : Type} (z : α) (m : ℕ) : ∀ (Ls : List (List α)) (g : List α → ℕ),
    secSum (Ls ++ List.replicate m [z]) g = secSum Ls (fun s => g (s ++ List.replicate m z))
  | [], g => by
    simp only [List.nil_append, secSum]
    induction m generalizing g with
    | zero => rfl
    | succ m ih =>
      simp only [List.replicate_succ, secSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      rw [ih]
  | L :: Ls, g => by
    simp only [List.cons_append, secSum]
    congr 1
    apply List.map_congr_left
    intro x _
    rw [secSum_pad z m Ls]

theorem secSum_one {α : Type} : ∀ (Ls : List (List α)),
    secSum Ls (fun _ => 1) = (Ls.map List.length).prod
  | [] => rfl
  | L :: Ls => by
    simp only [secSum, List.map_cons, List.prod_cons]
    rw [secSum_one Ls]
    simp [List.sum_replicate, List.map_const']

/-- A sum over a dependent pi type over `Fin k` is the product-list sum. -/
theorem pi_sum {α : Type} : ∀ (k : ℕ) (n : Fin k → ℕ) (rec : (i : Fin k) → Fin (n i) → α)
    (g : List α → ℕ),
    (∑ sel : ((i : Fin k) → Fin (n i)), g (List.ofFn fun i => rec i (sel i))) =
      secSum (List.ofFn fun i => List.ofFn (rec i)) g
  | 0, n, rec, g => by
    simp only [List.ofFn_zero, secSum]
    rw [Fintype.sum_unique]
  | k + 1, n, rec, g => by
    rw [← (Fin.consEquiv (fun i => Fin (n i))).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, secSum]
    rw [List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro j _
    exact pi_sum k (fun i => n i.succ) (fun i => rec i.succ) (fun s => g (rec 0 j :: s))

/-! ## Horner and the padding record -/

theorem horner_ofFn (b : ℕ) : ∀ {n : ℕ} (d : Fin n → ℕ),
    horner b (List.ofFn d) = ∑ i : Fin n, b ^ i.val * d i
  | 0, d => by simp [horner]
  | n + 1, d => by
    rw [List.ofFn_succ, horner, horner_ofFn b (fun i => d i.succ), Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem horner_zeros (b m : ℕ) : horner b (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, horner, ih]

theorem horner_pad (b m : ℕ) : ∀ l : List ℕ, horner b (l ++ List.replicate m 0) = horner b l
  | [] => by rw [List.nil_append, horner_zeros]; rfl
  | d :: l => by simp only [List.cons_append, horner, horner_pad b m l]

theorem selMag_pad (s : List Rec) (m : ℕ) :
    selMag (s ++ List.replicate m ((0 : ℕ), (0 : ℕ), (0 : ℕ))) = selMag s := by
  have hm : ((s ++ List.replicate m ((0 : ℕ), (0 : ℕ), (0 : ℕ))).map recMag).sum = (s.map recMag).sum := by
    simp [List.map_append, List.map_replicate, recMag, List.sum_replicate]
  have h1 : (s ++ List.replicate m ((0 : ℕ), (0 : ℕ), (0 : ℕ))).map (·.1) = s.map (·.1) ++ List.replicate m 0 := by
    simp [List.map_append, List.map_replicate]
  have h2 : (s ++ List.replicate m ((0 : ℕ), (0 : ℕ), (0 : ℕ))).map (·.2.1) =
      s.map (·.2.1) ++ List.replicate m 0 := by
    simp [List.map_append, List.map_replicate]
  have h3 : (s ++ List.replicate m ((0 : ℕ), (0 : ℕ), (0 : ℕ))).map (·.2.2) =
      s.map (·.2.2) ++ List.replicate m 0 := by
    simp [List.map_append, List.map_replicate]
  unfold selMag
  rw [hm, h1, h2, h3, horner_pad, horner_pad, horner_pad]

/-! ## One child record -/

theorem childRec_fst {n : ℕ} (g : ExactThresholdGate n) :
    (childRec g).1 = ∑ x, (g.weight x).natAbs := by
  simp [childRec, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem recMag_childRec {n : ℕ} (g : ExactThresholdGate n) : recMag (childRec g) = childMagnitude g := by
  have h := Int.toNat_add_toNat_neg_eq_natAbs g.target
  unfold recMag
  rw [childRec_fst]
  unfold childMagnitude
  simp only [childRec]
  omega

theorem childRec_target {n : ℕ} (g : ExactThresholdGate n) :
    ((childRec g).2.1 : ℤ) - ((childRec g).2.2 : ℤ) = g.target := by
  simp only [childRec]
  exact Int.toNat_sub_toNat_neg g.target

/-! ## Disjoint supports: the absolute value of the sum is the sum of absolute values -/

theorem natAbs_sum_disjoint {ι : Type} [Fintype ι] (f : ι → ℤ)
    (h : ∀ i j, i ≠ j → f i = 0 ∨ f j = 0) : (∑ i, f i).natAbs = ∑ i, (f i).natAbs := by
  by_cases hz : ∀ i, f i = 0
  · simp [hz]
  · rw [not_forall] at hz
    obtain ⟨i, hi⟩ := hz
    have h1 : ∑ j, f j = f i :=
      Finset.sum_eq_single i (fun j _ hj => (h j i hj).resolve_right hi) (by simp)
    have h2 : ∑ j, (f j).natAbs = (f i).natAbs :=
      Finset.sum_eq_single i (fun j _ hj => by rw [(h j i hj).resolve_right hi]; rfl) (by simp)
    rw [h1, h2]

theorem embeddedWeight_ne_zero {Local Global : Type} [Fintype Local] [DecidableEq Global]
    (e : Local ↪ Global) (w : Local → ℤ) (idx : Global) (h : embeddedWeight e w idx ≠ 0) :
    ∃ x, e x = idx := by
  by_contra hn
  rw [not_exists] at hn
  apply h
  unfold embeddedWeight
  apply Finset.sum_eq_zero
  intro x _
  exact if_neg (hn x)

theorem embeddedWeight_natAbs_sum {Local Global : Type} [Fintype Local] [Fintype Global]
    [DecidableEq Global] (e : Local ↪ Global) (w : Local → ℤ) :
    ∑ idx, (embeddedWeight e w idx).natAbs = ∑ x, (w x).natAbs := by
  have hpt : ∀ idx, (embeddedWeight e w idx).natAbs =
      ∑ x, if e x = idx then (w x).natAbs else 0 := by
    intro idx
    unfold embeddedWeight
    rw [natAbs_sum_disjoint]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    · intro x y hxy
      by_cases hx : e x = idx
      · right
        exact if_neg (fun hy => hxy (e.injective (hx.trans hy.symm)))
      · left
        exact if_neg hx
  simp_rw [hpt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_ite_eq]
  simp

def start (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i : Fin r.circuits.length) :=
  ((r.circuits.take i.val).flatMap thresholdCircuitOccurrences).length

theorem embedding_val (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i : Fin r.circuits.length)
    (j : Fin (r.circuits.get i).top.support.card) :
    (thresholdCircuitEmbedding r i j).val = start r i + j.val := rfl

theorem end_le (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i j : Fin r.circuits.length)
    (hij : i.val < j.val) : start r i + (r.circuits.get i).top.support.card ≤ start r j := by
  have h := ((List.take_sublist_take_left (l := r.circuits) (show i.val + 1 ≤ j.val by omega)).flatMap
    thresholdCircuitOccurrences).length_le
  rw [List.take_succ_eq_append_getElem i.isLt] at h
  simpa only [List.flatMap_append, List.flatMap_singleton, List.length_append, thresholdCircuitOccurrences,
    List.length_ofFn, List.get_eq_getElem, start] using h

theorem embedding_ne (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (i j : Fin r.circuits.length)
    (hi : i ≠ j) (x : Fin (r.circuits.get i).top.support.card) (y : Fin (r.circuits.get j).top.support.card) :
    thresholdCircuitEmbedding r i x ≠ thresholdCircuitEmbedding r j y := by
  intro he
  have hv := congrArg Fin.val he
  rw [embedding_val, embedding_val] at hv
  have hx := x.isLt
  have hy := y.isLt
  have hne : i.val ≠ j.val := by intro h; exact hi (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hb := end_le r i j h; omega
  · have hb := end_le r j i h; omega

theorem stack_weights {Carrier : Type} (base : Int) {n : Nat} (es : Fin n → LabelledEquation Carrier)
    (x : Carrier) :
    (stackEquations base (List.ofFn es)).weights x = ∑ i : Fin n, base ^ i.val * (es i).weights x := by
  induction n with
  | zero => simp [stackEquations]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    change (es 0).weights x + base * (stackEquations base (List.ofFn (fun i : Fin n => es i.succ))).weights x = _
    rw [ih, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ, pow_succ]
    ring

theorem stack_targets {Carrier : Type} (base : Int) {n : Nat} (es : Fin n → LabelledEquation Carrier) :
    (stackEquations base (List.ofFn es)).target = ∑ i : Fin n, base ^ i.val * (es i).target := by
  induction n with
  | zero => simp [stackEquations]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    change (es 0).target + base * (stackEquations base (List.ofFn (fun i : Fin n => es i.succ))).target = _
    rw [ih, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, one_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ, pow_succ]
    ring

theorem canonical_base (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) :
    equationListBase (ThresholdRows.equations a r sel) =
      ((∑ i : Fin r.circuits.length,
        childMagnitude ((ThresholdRows.children a (r.circuits.get i)).get (sel i))) + 1 : Nat) := by
  unfold equationListBase ThresholdRows.equations
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, thresholdChildEquation_magnitudeBound]

theorem canonical_target (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) :
    (ThresholdRows.equation a r sel).target =
      ∑ i : Fin r.circuits.length, equationListBase (ThresholdRows.equations a r sel) ^ i.val *
        ((ThresholdRows.children a (r.circuits.get i)).get (sel i)).target := by
  unfold ThresholdRows.equation canonicalEquationStack ThresholdRows.equations
  exact stack_targets _ _

theorem ofFn_get_map {α β : Type} (l : List α) (f : α → β) :
    List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
  have h : (fun i : Fin l.length => f (l.get i)) = f ∘ l.get := rfl
  rw [h, ← List.map_ofFn, List.ofFn_get]

/-! ## One selection: the stacked equation's magnitude envelope is `selMag` -/

section Selection
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- The selected child of circuit `i`. -/
abbrev child (sel : ThresholdRows.Selection a r) (i : Fin r.circuits.length) :=
  (ThresholdRows.children a (r.circuits.get i)).get (sel i)

theorem stack_weight_eq (sel : ThresholdRows.Selection a r) (idx : Fin (thresholdFourfoldOccurrences r).length) :
    (ThresholdRows.equation a r sel).weights idx =
      ∑ i : Fin r.circuits.length, equationListBase (ThresholdRows.equations a r sel) ^ i.val *
        (thresholdChildEquation r i (child a r sel i)).weights idx := by
  unfold ThresholdRows.equation canonicalEquationStack
  conv_lhs => rw [show ThresholdRows.equations a r sel = List.ofFn (fun i : Fin r.circuits.length =>
    thresholdChildEquation r i (child a r sel i)) from rfl]
  rw [stack_weights]
  rfl

theorem child_disjoint (sel : ThresholdRows.Selection a r) (idx : Fin (thresholdFourfoldOccurrences r).length)
    (i j : Fin r.circuits.length) (hij : i ≠ j) :
    (thresholdChildEquation r i (child a r sel i)).weights idx = 0 ∨
      (thresholdChildEquation r j (child a r sel j)).weights idx = 0 := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hi, hj⟩ := hc
  obtain ⟨x, hx⟩ := embeddedWeight_ne_zero (thresholdCircuitEmbedding r i) (child a r sel i).weight idx hi
  obtain ⟨y, hy⟩ := embeddedWeight_ne_zero (thresholdCircuitEmbedding r j) (child a r sel j).weight idx hj
  exact embedding_ne r i j hij x y (hx.trans hy.symm)

theorem weights_natAbs_sum (sel : ThresholdRows.Selection a r) (base : ℕ)
    (hb : equationListBase (ThresholdRows.equations a r sel) = (base : ℤ)) :
    ∑ idx, ((ThresholdRows.equation a r sel).weights idx).natAbs =
      ∑ i : Fin r.circuits.length, base ^ i.val * (childRec (child a r sel i)).1 := by
  have hpt : ∀ idx, ((ThresholdRows.equation a r sel).weights idx).natAbs =
      ∑ i : Fin r.circuits.length, base ^ i.val *
        ((thresholdChildEquation r i (child a r sel i)).weights idx).natAbs := by
    intro idx
    rw [stack_weight_eq, hb, natAbs_sum_disjoint]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    · intro i j hij
      rcases child_disjoint a r sel idx i j hij with h | h
      · left; rw [h, mul_zero]
      · right; rw [h, mul_zero]
  simp_rw [hpt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, childRec_fst]
  congr 1
  exact embeddedWeight_natAbs_sum (thresholdCircuitEmbedding r i) (child a r sel i).weight

/-- The records of one selection, in circuit order. -/
def selRecs (sel : ThresholdRows.Selection a r) : List Rec :=
  List.ofFn fun i : Fin r.circuits.length => childRec (child a r sel i)

theorem selRecs_base (sel : ThresholdRows.Selection a r) :
    ((selRecs a r sel).map recMag).sum + 1 =
      (∑ i : Fin r.circuits.length, childMagnitude (child a r sel i)) + 1 := by
  simp only [selRecs, List.map_ofFn, List.sum_ofFn, Function.comp_def, recMag_childRec]

theorem magnitude_eq_selMag (sel : ThresholdRows.Selection a r) :
    equationMagnitudeBound (ThresholdRows.equation a r sel) = selMag (selRecs a r sel) := by
  set base := (∑ i : Fin r.circuits.length, childMagnitude (child a r sel i)) + 1 with hbase
  have hb : equationListBase (ThresholdRows.equations a r sel) = (base : ℤ) :=
    canonical_base a r sel
  have ht := canonical_target a r sel
  rw [hb] at ht
  unfold equationMagnitudeBound selMag
  rw [selRecs_base, ← hbase, weights_natAbs_sum a r sel base hb, ht]
  have e1 : (selRecs a r sel).map (·.1) = List.ofFn fun i : Fin r.circuits.length => (childRec (child a r sel i)).1 := by
    simp [selRecs, List.map_ofFn, Function.comp_def]
  have e2 : (selRecs a r sel).map (·.2.1) =
      List.ofFn fun i : Fin r.circuits.length => (childRec (child a r sel i)).2.1 := by
    simp [selRecs, List.map_ofFn, Function.comp_def]
  have e3 : (selRecs a r sel).map (·.2.2) =
      List.ofFn fun i : Fin r.circuits.length => (childRec (child a r sel i)).2.2 := by
    simp [selRecs, List.map_ofFn, Function.comp_def]
  rw [e1, e2, e3, horner_ofFn, horner_ofFn, horner_ofFn]
  congr 1
  congr 1
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_sub, childRec_target]

end Selection

/-! ## The family: `family_eq` and `card_eq` -/

theorem tables_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit) :
    tables a r = (List.ofFn fun i : Fin r.circuits.length =>
      List.ofFn fun j : Fin (ThresholdRows.children a (r.circuits.get i)).length =>
        childRec ((ThresholdRows.children a (r.circuits.get i)).get j)) ++
      List.replicate (4 - r.circuits.length) [((0 : ℕ), (0 : ℕ), (0 : ℕ))] := by
  unfold tables
  congr 1
  rw [← ofFn_get_map r.circuits (fun c => (ThresholdRows.children a c).map childRec)]
  congr 1
  funext i
  exact (ofFn_get_map _ childRec).symm

theorem tables_length (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (h4 : r.circuits.length ≤ 4) : (tables a r).length = 4 := by
  simp [tables]
  omega

theorem tables_four (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (h4 : r.circuits.length ≤ 4) : tables a r = [T a r 0, T a r 1, T a r 2, T a r 3] := by
  have hl := tables_length a r h4
  unfold T
  generalize tables a r = l at hl ⊢
  match l, hl with
  | [x0, x1, x2, x3], _ => rfl

theorem secSum_tables (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (g : List Rec → ℕ) :
    (∑ sel : ThresholdRows.Selection a r, g (selRecs a r sel ++
        List.replicate (4 - r.circuits.length) ((0 : ℕ), (0 : ℕ), (0 : ℕ)))) =
      secSum (tables a r) g := by
  rw [tables_eq, secSum_pad]
  exact pi_sum r.circuits.length (fun i => (ThresholdRows.children a (r.circuits.get i)).length)
    (fun i j => childRec ((ThresholdRows.children a (r.circuits.get i)).get j))
    (fun s => g (s ++ List.replicate (4 - r.circuits.length) ((0 : ℕ), (0 : ℕ), (0 : ℕ))))

/-- **The family magnitude envelope as the machine's nested sum.** -/
theorem family_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (h4 : r.circuits.length ≤ 4) :
    familyMagnitudeBound (ThresholdRows.equation a r) =
      nestedSum (T a r 0) (T a r 1) (T a r 2) (T a r 3) selMag := by
  unfold familyMagnitudeBound nestedSum
  rw [← secSum_four, ← tables_four a r h4, ← secSum_tables]
  apply Finset.sum_congr rfl
  intro sel _
  rw [selMag_pad, magnitude_eq_selMag]

/-- **The number of child selections is the product of the four table lengths.** -/
theorem card_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (h4 : r.circuits.length ≤ 4) :
    Fintype.card (ThresholdRows.Selection a r) =
      (T a r 0).length * (T a r 1).length * (T a r 2).length * (T a r 3).length := by
  rw [Fintype.card_eq_sum_ones]
  have h := secSum_tables a r (fun _ => 1)
  rw [h, secSum_one, tables_four a r h4]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.mul_one]
  ring

/-! ## Size facts from the request's own `topWord` -/

section Size
open PCJd4d1d9d7d1fa4313_Production

theorem topWord_thr (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) :
    Request.topWord a (.thr r four L target) = r.circuits.flatMap (fun c =>
      RepairOrdinary.frame (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))) := rfl

theorem circuit_word_le (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (c : NormalizedThresholdThresholdCircuit r.q)
    (hc : c ∈ r.circuits) :
    (exactListWord (ThresholdRows.children a c)).length ≤
      (Request.topWord a (.thr r four L target)).length := by
  rw [topWord_thr, List.length_flatMap]
  have h1 : (RepairOrdinary.frame (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))).length ≤
      (r.circuits.map (fun c => (RepairOrdinary.frame
        (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))).length)).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have h2 := RepairOrdinary.frame_length (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))
  rw [List.length_append] at h2
  omega

theorem mem_tables (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (l : List Rec) (hl : l ∈ tables a r) :
    (∃ c ∈ r.circuits, l = (ThresholdRows.children a c).map childRec) ∨
      l = [((0 : ℕ), (0 : ℕ), (0 : ℕ))] := by
  unfold tables at hl
  rcases List.mem_append.mp hl with h | h
  · left
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    exact ⟨c, hc, rfl⟩
  · right
    exact List.eq_of_mem_replicate h

theorem mem_T (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (i : ℕ) : T a r i = [] ∨ T a r i ∈ tables a r := by
  unfold T
  rw [List.getD_eq_getElem?_getD]
  cases h : (tables a r)[i]? with
  | none => left; rfl
  | some l =>
    right
    exact List.mem_of_getElem? h

theorem T_length_le (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (i : ℕ) :
    (T a r i).length ≤ (Request.topWord a (.thr r four L target)).length + 1 := by
  rcases mem_T a r i with h | h
  · rw [h]; simp
  · rcases mem_tables a r _ h with ⟨c, hc, he⟩ | he
    · rw [he, List.length_map]
      have h1 := DecompositionSource.children_le_output (ThresholdRows.children a c)
      have h2 := circuit_word_le a r four L target c hc
      omega
    · rw [he]; simp

theorem childMagnitude_lt {n : ℕ} (gs : List (ExactThresholdGate n)) (g : ExactThresholdGate n)
    (hg : g ∈ gs) : childMagnitude g < 2 ^ (exactListWord gs).length := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  have h1 := RowCachedEquation.equation_magnitude gs[k]
  have h2 := RowCachedCoordinateBounds.child_bytes gs k hk
  have he : equationMagnitudeBound (RowCachedEquation.equation gs[k]) = childMagnitude gs[k] := rfl
  rw [he] at h1
  exact h1.trans_le (Nat.pow_le_pow_right (by decide) h2)

theorem rec_lt (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (i : ℕ) (x : Rec) (hx : x ∈ T a r i) :
    recMag x < 2 ^ (Request.topWord a (.thr r four L target)).length := by
  rcases mem_T a r i with h | h
  · rw [h] at hx; simp at hx
  · rcases mem_tables a r _ h with ⟨c, hc, he⟩ | he
    · rw [he] at hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      rw [recMag_childRec]
      exact (childMagnitude_lt _ g hg).trans_le
        (Nat.pow_le_pow_right (by decide) (circuit_word_le a r four L target c hc))
    · rw [he] at hx
      rw [List.mem_singleton.mp hx]
      simp [recMag]

end Size

end NearCubicWires.PacketsMeta.CutoffMath

