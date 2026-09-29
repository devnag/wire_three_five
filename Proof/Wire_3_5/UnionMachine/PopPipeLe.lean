import Proof.Wire_3_5.Primitive.Writers.SymLeafIface

/-! # The POP pipeline's cost is polynomial times `2^{O(e)}`

The POP row of the flat list prints the population's expression: its capacities (`popR`, `popCp`, the Route B)
carry the counting capacity `(8L+2)^{3·lbP}` of the row's factor prints, and the row's evaluation runs the walk's
`2^t` truth-table rows (`t = walkLen = 2⌊e/4⌋+1`; `ListMachine.Row.popRowCost_le`). Every other piece of
`PopPipe.popPipeBound` is polynomial in the capacity, the list's numbers and the slice.
* the block length (`blockC_len_le`: `2·|block| + 2 ≤ blF …`, hence C2's `StateOk` at Route B's capacities by `PopCap.popStates_okB`);
* the row record's length (`rec_len_le`: setup fields, the constant term, at most `M + 1` states of `2t` blocks);
* the uniform bookkeeping `PB f` (`f ≤ C·(Y·2^e)^k` for constants `C, k`), closed under `+`, `·`, powers, `-`,
  `/`, `max`; every atom of the bound (the list's numbers, `(8L+2)^{3·lbP} ≤ Y`, `2^t ≤ 2·2^e`, the slice's
  labels, the record's length, the row's cost) is `PB`, and `c6pb` decomposes the explicit cost expression;
* **`popPipe_le : PrimAsm.SymLeaf.PopPipeLe`** (the consumer statement).

Paper quantity of the main type: the POP unit's running time (list:flatten P3:1491-1498, row:sym P3:2477-2496) at the
error exponent `e` (P3:2210-2211). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PopPipeLe
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm

/-! ## Numbers -/

theorem clog_le (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem ceilSqrt_le (v : ℕ) : CanonicalFourfoldRowProgram.natCeilSqrt v ≤ v + 1 := by
  unfold CanonicalFourfoldRowProgram.natCeilSqrt
  have := Nat.sqrt_le_self v
  simp only
  split_ifs <;> omega

theorem ceil_div_le (S a : ℕ) (ha : 1 ≤ a) : (S + a - 1) / a ≤ S := by
  have : (S + a - 1) / a < S + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have h1 : S ≤ S * a := Nat.le_mul_of_pos_right S ha
    have e : (S + 1) * a = S * a + a := by ring
    omega
  omega

theorem winAt_le (S J j : ℕ) : LevelW.winAt S J j ≤ S + 64 := by
  unfold LevelW.winAt
  split_ifs
  · omega
  · have := ceil_div_le S (2 ^ (j / 3)) Nat.one_le_two_pow; omega

theorem sum_range_le (n B : ℕ) (f : ℕ → ℕ) (h : ∀ j < n, f j ≤ B) : ∑ j ∈ Finset.range n, f j ≤ n * B := by
  calc ∑ j ∈ Finset.range n, f j ≤ ∑ _j ∈ Finset.range n, B :=
        Finset.sum_le_sum fun j hj => h j (Finset.mem_range.mp hj)
    _ = n * B := by simp

theorem lbSumF_le (S J : ℕ) : PopParams.lbSumF S J ≤ J * (4 * (S + 64)) := by
  unfold PopParams.lbSumF
  exact sum_range_le J _ _ fun j _ => by have := winAt_le S J j; omega

theorem lwSumF_le (S J L : ℕ) : PopParams.lwSumF S J L ≤ (J + 1) * (5 * (S + 64) + L + 6) := by
  unfold PopParams.lwSumF
  refine sum_range_le (J + 1) _ _ fun j _ => ?_
  have hw := winAt_le S J j
  have hp := LevelW.pow_clog_le (2 * LevelW.winAt S J j + 1) (by omega)
  omega

theorem two_pow_ge (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-! ## The visit factor's block -/

section Block
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW

theorem pieceA_len (Lp d : ℕ) : (pieceA Lp d).length = 32 * Lp + 4 * d + 60 := by
  unfold pieceA
  simp only [List.length_append, reps_length, m2, m3, List.length_cons, List.length_nil]
  ring

theorem pieceB_len (labs : List ℕ) (cap1 : ℕ) :
    (pieceB labs cap1).length = (labs.flatMap labE).length + 4 * cap1 + 10 := by
  unfold pieceB
  simp only [List.length_append, reps_length, m2, List.length_cons, List.length_nil]
  ring

theorem m2_flat_len (l : List Bool) : (l.flatMap m2).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.flatMap_cons, List.length_append, ih, m2, List.length_cons, List.length_nil]; ring

theorem labSum_ge' (labs : List ℕ) : 5 + 10 * labs.length ≤ labSum labs := by
  have := labSum_ge labs; unfold labSum; omega

/-- **The block of a visit factor fits the block bound `blF`.** -/
theorem blockC_len_le (Pl : FlatListParams) (e : Pl.FlatSeed) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ)
    (k : Fin Pl.walkLen) (hlen : labs.length = 4 * L) (hs : s ≤ Pl.M) :
    2 * (blockC (visitData Pl e k) L s sgn neg labs).length + 2 ≤
      PopNums.blF L (3 * PopLink.lbP Pl) (PopLink.capP Pl L) (labSum labs) (labs.flatMap labE).length
        (PopSetup.popLw Pl L) Pl.M := by
  have e1 := PopRec.blockE_eq (visitData Pl e k) L s sgn neg labs
  have hl := congrArg List.length e1
  rw [RepairOrdinary.Streaming.marks_length, List.length_cons, PopBlockW.blockE_length, pieceA_len, pieceB_len,
    PopBlockW.pieceP_length] at hl
  have hc1 : cap1C L labs = labSum labs := by
    unfold cap1C
    have h1 : labCost (4 * L) labs = labSum labs := by rw [← hlen]; exact labCost_eq labs
    have h2 := labSum_ge' labs
    rw [h1]; exact max_eq_right (by omega)
  have hlv : ((FinalPass.ListEval.levelWord (visitData Pl e k).M (visitData Pl e k).J (visitData Pl e k).W
      (FinalPass.ListEval.rowsOf (visitData Pl e k) L)).flatMap m2).length =
      4 * (PopParams.lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J L + Pl.base.M + 2) := by
    rw [m2_flat_len]
    have := PopParams.levelWord_length Pl.base L (FinalPass.ListEval.rowsOf (visitData Pl e k) L)
      (fun j _ => by simp [FinalPass.ListEval.rowsOf])
    rw [show (visitData Pl e k).M = Pl.base.M from rfl, show (visitData Pl e k).J = Pl.base.J from rfl,
      show (visitData Pl e k).W = Pl.base.W from rfl, this]
  have hcap : capC (visitData Pl e k) L = PopLink.capP Pl L := PopLink.capC_visit Pl e L k
  rw [hc1, hlv, hcap, PopLink.listBound_visit] at hl
  unfold PopNums.blF PopSetup.popLw
  have hM : Pl.base.M = Pl.M := rfl
  omega

end Block

/-! ## The slice's labels -/

section Labs
open NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- The slice's labels are at most `popMlab` (Emit's `sliceLabs_le` at `j = Lg = L`). -/
theorem sliceLabs_le_mlab (r4 G off L : ℕ) : ∀ lab ∈ sliceLabs r4 G off L, lab ≤ PopSetup.popMlab r4 G off L :=
  Emit.sliceLabs_le r4 G off L (PopSetup.popMlab r4 G off L) le_rfl L le_rfl

end Labs

/-! ## The POP row's cost, by C2's bound -/

section Row
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **C2's side conditions hold at Route B's capacities** (`popStates_okB` with the block bound). -/
theorem popStates_ok (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1))
    (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length) :
    ∀ st ∈ popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s,
      StateOk Pl.walkLen (PopSetup.popR Pl r4 G off L) (PopSetup.popCp Pl r4 G off L) st := by
  have hlen := Emit.sliceLabs_length r4 G off L
  exact PopCap.popStates_okB Pl e L sgn (sliceLabs r4 G off L) hlabs hlen (PopSetup.popMlab r4 G off L)
    (sliceLabs_le_mlab r4 G off L) _ (fun s' k neg => blockC_len_le Pl e L s'.val sgn neg _ k hlen (Nat.le_of_lt_succ s'.isLt)) s

/-- **The POP row's cost** at most `2^t · 128 · (|record| + 1)^3` (C2's `popRowCost_le`). -/
theorem rowCost_le (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1))
    (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length) :
    popRowCost Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) (PopSetup.popR Pl r4 G off L)
        (PopSetup.popR Pl r4 G off L + 1) (PopSetup.popCp Pl r4 G off L) (oneWC Pl s)
        (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s) ≤
      2 ^ Pl.walkLen * (128 * ((popRowRec Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen)
        (PopSetup.popR Pl r4 G off L) (PopSetup.popR Pl r4 G off L + 1) (PopSetup.popCp Pl r4 G off L) (oneWC Pl s)
        (popStates Pl e L sgn (sliceLabs r4 G off L) hlabs s)).length + 1) ^ 3) :=
  popRowCost_le _ _ _ _ _ _ _ (popStates_ok Pl e L r4 G off sgn s hlabs)

end Row

/-! ## The row record's length -/

section RecLen
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.RepairOrdinary (frame frame_length)

theorem len_flatMap_le' {α β : Type} (l : List α) (f : α → List β) (B : ℕ) (h : ∀ x ∈ l, (f x).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have e : (l.length + 1) * B = l.length * B + B := by ring
    omega

theorem fields_len (u n θ R L cap : ℕ) :
    (fieldsWord (setupFields u n θ R L cap)).length ≤ 2 * R + 2 * L + 8 * n + 2 * θ + 2 * cap + 20 := by
  rw [setupFields_eq]
  simp [fieldsWord, frame_length]
  omega

theorem oneWC_len (Pl : FlatListParams) (s : Fin (Pl.M + 1)) : (oneWC Pl s).length ≤ 4 * Pl.walkLen + 7 := by
  unfold oneWC popOne
  split_ifs
  · have h4 : ∀ f ∈ List.replicate Pl.walkLen ([[]] : List (List ℕ)), (true :: Rec.polyWord f).length ≤ 4 := by
      intro f hf
      rw [List.eq_of_mem_replicate hf]
      decide
    have := len_flatMap_le' _ _ 4 h4
    rw [List.length_replicate] at this
    have h5 := PopCap.coefWord_pm 1 (Or.inl rfl)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, Rec.termWord,
      List.length_append, List.length_singleton, List.length_nil, h5]
    omega
  · simp

theorem storeRec_len {F : EvalFam} (xs : List (FSpec F)) (B : ℕ) (h : ∀ x ∈ xs, x.block.length + 1 ≤ B) :
    (storeRec xs).length ≤ xs.length * B + 1 := by
  unfold storeRec
  rw [List.length_append, List.length_singleton]
  have := len_flatMap_le' xs (fun x => true :: x.block) B (fun x hx => by
    rw [List.length_cons]; exact h x hx)
  omega

/-- **The POP row record's length**: the setup fields, the constant term, and at most `M + 1` states of `2t`
blocks, each block within `blF`. -/
theorem rec_len_le (Pl : FlatListParams) (e : Pl.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ)
    (hlabs : 4 * L ≤ labs.length) (hlen : labs.length = 4 * L) (s : Fin (Pl.M + 1)) (θ R L' c' : ℕ) :
    (popRowRec Pl.walkLen θ R L' c' (oneWC Pl s) (popStates Pl e L sgn labs hlabs s)).length ≤
      2 * R + 2 * L' + 16 * Pl.walkLen + 2 * θ + 2 * c' + 40 + (Pl.M + 1) * (2 * Pl.walkLen *
        PopNums.blF L (3 * PopLink.lbP Pl) (PopLink.capP Pl L) (labSum labs) (labs.flatMap labE).length
          (PopSetup.popLw Pl L) Pl.M + 13) := by
  generalize hBL : PopNums.blF L (3 * PopLink.lbP Pl) (PopLink.capP Pl L) (labSum labs) (labs.flatMap labE).length
    (PopSetup.popLw Pl L) Pl.M = BL
  unfold popRowRec popRec
  have h0 : (fieldsWord (setupFields (negFam F35).t Pl.walkLen θ R L' c')).length ≤
      2 * R + 2 * L' + 8 * Pl.walkLen + 2 * θ + 2 * c' + 20 := fields_len _ _ _ _ _ _
  have h1 := oneWC_len Pl s
  have hl : (popStates Pl e L sgn labs hlabs s).length ≤ Pl.M + 1 := by
    rw [popStates_eq, List.length_map]
    unfold statesC
    split_ifs <;> simp
  have hb : ∀ st ∈ popStates Pl e L sgn labs hlabs s, (srec st).length ≤ 2 * Pl.walkLen * BL + 13 := by
    intro st hst
    rw [popStates_eq] at hst
    obtain ⟨⟨c, s'⟩, hcs, rfl⟩ := List.mem_map.mp hst
    have hc : c = 1 ∨ c = -1 := by
      unfold statesC at hcs
      split_ifs at hcs
      · obtain ⟨i, _, hi⟩ := List.mem_map.mp hcs
        exact Or.inr (Prod.mk.inj hi).1.symm
      · exact Or.inl (Prod.mk.inj (List.mem_singleton.mp hcs)).1
    have hst2 := storeRec_len (visitFs Pl e L sgn labs hlabs s') BL (fun x hx => by
      obtain ⟨k, neg, rfl⟩ := mem_visitFs Pl e L sgn labs hlabs s' x hx
      rw [visitSpec_block]
      have := blockC_len_le Pl e L s'.val sgn neg labs k hlen (Nat.le_of_lt_succ s'.isLt)
      rw [hBL] at this
      omega)
    rw [visitFs_length] at hst2
    simp only [srec, stateRec, List.length_cons, List.length_append, frame_length, PopCap.coefWord_pm c hc]
    omega
  have h2 := len_flatMap_le' _ srec _ hb
  have h3 : (popStates Pl e L sgn labs hlabs s).length * (2 * Pl.walkLen * BL + 13) ≤
      (Pl.M + 1) * (2 * Pl.walkLen * BL + 13) := Nat.mul_le_mul_right _ hl
  simp only [List.length_append, frame_length, List.length_singleton]
  omega

end RecLen

/-! ## Polynomial bookkeeping over the pipeline's parameters -/

section PB
open NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- The POP pipeline's parameters (the binders of `PopPipeLe`). -/
structure Pr where
  cap : ℕ
  Pl : FlatListParams
  e : Pl.FlatSeed
  L : ℕ
  r4 : ℕ
  G : ℕ
  off : ℕ
  sgn : Bool
  s : Fin (Pl.M + 1)
  hlabs : 4 * L ≤ (sliceLabs r4 G off L).length

/-- The polynomial base `Y`. -/
def Yp (p : Pr) : ℕ := p.cap + p.Pl.M + p.Pl.B + p.Pl.errExp + p.L + p.r4 + p.G + p.off +
  Fintype.card p.Pl.FlatSeed + (8 * p.L + 2) ^ (3 * PopLink.lbP p.Pl + 1) + 2

/-- The bound's base `Y · 2^e`. -/
def Bp (p : Pr) : ℕ := Yp p * 2 ^ p.Pl.errExp

theorem Bp_pos (p : Pr) : 1 ≤ Bp p := by
  have h1 : 1 ≤ Yp p := by unfold Yp; omega
  exact Nat.mul_le_mul h1 Nat.one_le_two_pow

theorem Y_le_Bp (p : Pr) : Yp p ≤ Bp p := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

/-- `f` is at most `C · (Y·2^e)^k`, uniformly in the parameters. -/
def PB (f : Pr → ℕ) : Prop := ∃ C k : ℕ, ∀ p, f p ≤ C * Bp p ^ k

theorem PB.const (c : ℕ) : PB fun _ => c := ⟨c, 0, fun p => by simp⟩

theorem PB.add {f g : Pr → ℕ} (hf : PB f) (hg : PB g) : PB fun p => f p + g p := by
  obtain ⟨C1, k1, h1⟩ := hf
  obtain ⟨C2, k2, h2⟩ := hg
  refine ⟨C1 + C2, max k1 k2, fun p => ?_⟩
  have hb := Bp_pos p
  have e1 := Nat.mul_le_mul_left C1 (Nat.pow_le_pow_right hb (le_max_left k1 k2))
  have e2 := Nat.mul_le_mul_left C2 (Nat.pow_le_pow_right hb (le_max_right k1 k2))
  have := h1 p
  have := h2 p
  show f p + g p ≤ _
  rw [Nat.add_mul]
  omega

theorem PB.mul {f g : Pr → ℕ} (hf : PB f) (hg : PB g) : PB fun p => f p * g p := by
  obtain ⟨C1, k1, h1⟩ := hf
  obtain ⟨C2, k2, h2⟩ := hg
  refine ⟨C1 * C2, k1 + k2, fun p => ?_⟩
  calc f p * g p ≤ (C1 * Bp p ^ k1) * (C2 * Bp p ^ k2) := Nat.mul_le_mul (h1 p) (h2 p)
    _ = C1 * C2 * Bp p ^ (k1 + k2) := by rw [pow_add]; ring

theorem PB.pow {f : Pr → ℕ} (hf : PB f) (n : ℕ) : PB fun p => f p ^ n := by
  obtain ⟨C, k, h⟩ := hf
  refine ⟨C ^ n, k * n, fun p => ?_⟩
  calc f p ^ n ≤ (C * Bp p ^ k) ^ n := Nat.pow_le_pow_left (h p) n
    _ = C ^ n * Bp p ^ (k * n) := by rw [mul_pow, pow_mul]

theorem PB.mono {f g : Pr → ℕ} (hg : PB g) (h : ∀ p, f p ≤ g p) : PB f := by
  obtain ⟨C, k, hc⟩ := hg
  exact ⟨C, k, fun p => (h p).trans (hc p)⟩

theorem PB.sub {f : Pr → ℕ} (hf : PB f) (g : Pr → ℕ) : PB fun p => f p - g p :=
  hf.mono fun _ => Nat.sub_le _ _

theorem PB.div {f : Pr → ℕ} (hf : PB f) (g : Pr → ℕ) : PB fun p => f p / g p :=
  hf.mono fun _ => Nat.div_le_self _ _

theorem PB.max {f g : Pr → ℕ} (hf : PB f) (hg : PB g) : PB fun p => max (f p) (g p) :=
  (hf.add hg).mono fun _ => by omega

theorem PB.ofY {f : Pr → ℕ} (h : ∀ p, f p ≤ Yp p) : PB f :=
  ⟨1, 1, fun p => by rw [pow_one, one_mul]; exact (h p).trans (Y_le_Bp p)⟩

/-- Decompose sums, products, powers, truncated differences, quotients and maxima down to bounded atoms. -/
syntax "c6pb" : tactic
macro_rules
  | `(tactic| c6pb) => `(tactic| first
      | with_reducible assumption
      | with_reducible exact PB.const _
      | ((with_reducible refine PB.add ?_ ?_) <;> c6pb)
      | ((with_reducible refine PB.mul ?_ ?_) <;> c6pb)
      | ((with_reducible refine PB.pow ?_ _) <;> c6pb)
      | ((with_reducible refine PB.sub ?_ _) <;> c6pb)
      | ((with_reducible refine PB.div ?_ _) <;> c6pb)
      | ((with_reducible refine PB.max ?_ ?_) <;> c6pb)
      | ((refine PB.pow ?_ _) <;> c6pb))

end PB

/-! ## The pipeline's bound -/

section Pipe
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW
open NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires.RepairOrdinary (frame frame_length)

theorem costL_le {k : ℕ} (cap : ℕ) (os : List (Arith.AOp k)) :
    Arith.costL cap os ≤ os.length * (30 * (cap + 1) * (cap + 1)) + Arith.costL 0 os := by
  induction os with
  | nil => simp [Arith.costL]
  | cons o os ih =>
    have ho : o.cost cap ≤ 30 * (cap + 1) * (cap + 1) + o.cost 0 := by
      cases o <;> simp only [Arith.AOp.cost] <;> omega
    simp only [Arith.costL, List.length_cons]
    have e : (os.length + 1) * (30 * (cap + 1) * (cap + 1)) =
        os.length * (30 * (cap + 1) * (cap + 1)) + 30 * (cap + 1) * (cap + 1) := by ring
    omega

/-- **The POP pipeline's cost bound is polynomial in `Y · 2^e`.** -/
theorem pb_pipe : PB fun p => PopPipe.popPipeBound p.cap p.Pl p.e p.L p.r4 p.G p.off (popMlab p.r4 p.G p.off p.L)
    (popLw p.Pl p.L) (popR p.Pl p.r4 p.G p.off p.L) (popCp p.Pl p.r4 p.G p.off p.L) (popRW p.Pl) (popRW p.Pl)
    p.sgn p.s p.hlabs := by
  have aC : PB fun p => p.cap := PB.ofY fun p => by unfold Yp; omega
  have aM : PB fun p => p.Pl.M := PB.ofY fun p => by unfold Yp; omega
  have aM' : PB fun p => p.Pl.base.M := aM
  have aB : PB fun p => p.Pl.B := PB.ofY fun p => by unfold Yp; omega
  have aE : PB fun p => p.Pl.errExp := PB.ofY fun p => by unfold Yp; omega
  have aL : PB fun p => p.L := PB.ofY fun p => by unfold Yp; omega
  have aR4 : PB fun p => p.r4 := PB.ofY fun p => by unfold Yp; omega
  have aG : PB fun p => p.G := PB.ofY fun p => by unfold Yp; omega
  have aO : PB fun p => p.off := PB.ofY fun p => by unfold Yp; omega
  have aLb : PB fun p => lbP p.Pl := PB.ofY fun p => by
    have h1 := two_pow_ge (3 * lbP p.Pl + 1)
    have h2 : 2 ^ (3 * lbP p.Pl + 1) ≤ (8 * p.L + 2) ^ (3 * lbP p.Pl + 1) := Nat.pow_le_pow_left (by omega) _
    unfold Yp; omega
  have aX : PB fun p => (8 * p.L + 2) ^ (3 * lbP p.Pl) := PB.ofY fun p => by
    have h2 : (8 * p.L + 2) ^ (3 * lbP p.Pl) ≤ (8 * p.L + 2) ^ (3 * lbP p.Pl + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    unfold Yp; omega
  have aS : PB fun p => CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * p.Pl.base.B) :=
    PB.mono (g := fun p => 4096 * p.Pl.B + 1) (by c6pb) fun p => by
      have := ceilSqrt_le (64 ^ 2 * p.Pl.base.B)
      have e : 64 ^ 2 * p.Pl.base.B = 4096 * p.Pl.B := by show 64 ^ 2 * p.Pl.B = _; norm_num
      omega
  have aJ : PB fun p => p.Pl.base.J := PB.mono (g := fun p => p.Pl.B + 9) (by c6pb) fun p => by
    show Nat.clog 2 p.Pl.B + 9 ≤ _
    have := clog_le p.Pl.B
    omega
  have aRk : PB fun p => p.Pl.base.rank := PB.mono (g := fun p => p.Pl.B + 9 + p.Pl.M) (by c6pb) fun p => by
    show max (Nat.clog 2 p.Pl.B + 9) (Nat.clog 2 p.Pl.M) ≤ _
    have := clog_le p.Pl.B
    have := clog_le p.Pl.M
    omega
  have aSd : PB fun p => FinalPass.Flat.sideB p.Pl.base.rank :=
    PB.mono (g := fun p => 2 * p.Pl.base.rank + 1) (by c6pb) fun p => by
      show (2 * p.Pl.base.rank + (p.Pl.base.rank - 1) + 1) / 2 ≤ _
      omega
  have aW : PB fun p => p.Pl.walkLen := PB.mono (g := fun p => p.Pl.errExp + 1) (by c6pb) fun p => by
    show 2 * (p.Pl.errExp / 4) + 1 ≤ _
    omega
  have aT : PB fun p => SupplierWalk.majorityThreshold p.Pl.walkLen := PB.mono aW fun p => by
    show (p.Pl.walkLen + 1) / 2 ≤ _
    omega
  have aPw : PB fun p => 2 ^ p.Pl.walkLen := ⟨2, 1, fun p => by
    have h1 : 2 ^ p.Pl.walkLen ≤ 2 ^ (p.Pl.errExp + 1) :=
      Nat.pow_le_pow_right (by omega) (by show 2 * (p.Pl.errExp / 4) + 1 ≤ _; omega)
    have h2 : 2 ^ p.Pl.errExp ≤ Bp p := Nat.le_mul_of_pos_left _ (by unfold Yp; omega)
    rw [pow_succ] at h1
    show 2 ^ p.Pl.walkLen ≤ 2 * Bp p ^ 1
    rw [pow_one]
    omega⟩
  have aLw : PB fun p => PopParams.lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * p.Pl.base.B))
      p.Pl.base.J p.L :=
    PB.mono (g := fun p => (p.Pl.base.J + 1) *
        (5 * (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * p.Pl.base.B) + 64) + p.L + 6))
      (by c6pb) fun p => lwSumF_le _ _ _
  have aLs : PB fun p => PopParams.lbSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * p.Pl.base.B))
      p.Pl.base.J :=
    PB.mono (g := fun p => p.Pl.base.J * (4 * (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * p.Pl.base.B) + 64)))
      (by c6pb) fun p => lbSumF_le _ _
  have aCp : PB fun p => capP p.Pl p.L :=
    PB.mono (g := fun p => 4 * (PopParams.lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * p.Pl.base.B))
        p.Pl.base.J p.L + p.Pl.M + 2 + p.L + 1)) (by c6pb) fun p => by
      unfold capP FinalPass.ListEval.capOf
      rw [PopParams.levelWord_length p.Pl.base p.L _ (fun j _ => by simp)]
      exact le_rfl
  have aMl : PB fun p => popMlab p.r4 p.G p.off p.L := by
    simp only [popMlab]
    c6pb
  have aLab : PB fun p => labSum (sliceLabs p.r4 p.G p.off p.L) :=
    PB.mono (g := fun p => 5 + 4 * p.L * (2 * popMlab p.r4 p.G p.off p.L + 10)) (by c6pb) fun p => by
      unfold labSum
      have := List.sum_le_card_nsmul ((sliceLabs p.r4 p.G p.off p.L).map fun lab => 2 * lab + 10)
        (2 * popMlab p.r4 p.G p.off p.L + 10) (by
          intro x hx
          obtain ⟨lab, hl, rfl⟩ := List.mem_map.mp hx
          have := sliceLabs_le_mlab p.r4 p.G p.off p.L lab hl
          omega)
      simp only [List.length_map, smul_eq_mul, Emit.sliceLabs_length] at this
      omega
  have aLL : PB fun p => ((sliceLabs p.r4 p.G p.off p.L).flatMap labE).length :=
    PB.mono (g := fun p => 4 * p.L * (4 * popMlab p.r4 p.G p.off p.L + 4)) (by c6pb) fun p => by
      have := len_flatMap_le' (sliceLabs p.r4 p.G p.off p.L) labE (4 * popMlab p.r4 p.G p.off p.L + 4) (by
        intro lab hl
        have := sliceLabs_le_mlab p.r4 p.G p.off p.L lab hl
        simp only [labE, List.length_append, reps_length, m2, List.length_cons, List.length_nil]
        omega)
      rwa [Emit.sliceLabs_length] at this
  have aCn : PB fun p => Arith.costL p.cap PopNums.numOps := PB.mono (by c6pb) fun p => costL_le p.cap _
  have aCv : PB fun p => Arith.costL p.cap PopCellNum.vOps := PB.mono (by c6pb) fun p => costL_le p.cap _
  have aRec : PB fun p => (popRowRec p.Pl.walkLen (SupplierWalk.majorityThreshold p.Pl.walkLen)
      (popR p.Pl p.r4 p.G p.off p.L) (popR p.Pl p.r4 p.G p.off p.L + 1) (popCp p.Pl p.r4 p.G p.off p.L)
      (oneWC p.Pl p.s) (popStates p.Pl p.e p.L p.sgn (sliceLabs p.r4 p.G p.off p.L) p.hlabs p.s)).length := by
    refine PB.mono ?_ fun p => rec_len_le p.Pl p.e p.L p.sgn _ p.hlabs (Emit.sliceLabs_length _ _ _ _) p.s _ _ _ _
    simp only [popR, popCp, popLw, popMlab, popCAP, popLL, PopCap.popKc, PopCap.popCapB, PopCap.popPW, PopNums.blF]
    c6pb
  have aFr : PB fun p => (frame (popRowRec p.Pl.walkLen (SupplierWalk.majorityThreshold p.Pl.walkLen)
      (popR p.Pl p.r4 p.G p.off p.L) (popR p.Pl p.r4 p.G p.off p.L + 1) (popCp p.Pl p.r4 p.G p.off p.L)
      (oneWC p.Pl p.s) (popStates p.Pl p.e p.L p.sgn (sliceLabs p.r4 p.G p.off p.L) p.hlabs p.s))).length :=
    PB.mono (by c6pb) fun p => (frame_length _).le
  have aPrc : PB fun p => popRowCost p.Pl.walkLen (SupplierWalk.majorityThreshold p.Pl.walkLen)
      (popR p.Pl p.r4 p.G p.off p.L) (popR p.Pl p.r4 p.G p.off p.L + 1) (popCp p.Pl p.r4 p.G p.off p.L)
      (oneWC p.Pl p.s) (popStates p.Pl p.e p.L p.sgn (sliceLabs p.r4 p.G p.off p.L) p.hlabs p.s) :=
    PB.mono (by c6pb) fun p => rowCost_le p.Pl p.e p.L p.r4 p.G p.off p.sgn p.s p.hlabs
  have aR : PB fun p => popR p.Pl p.r4 p.G p.off p.L := by
    simp only [popR, popLw, popMlab, popCAP, popLL, PopCap.popKc, PopNums.blF]
    c6pb
  have aCP : PB fun p => popCp p.Pl p.r4 p.G p.off p.L := by
    simp only [popCp, popMlab, PopCap.popCapB, PopCap.popPW]
    c6pb
  simp only [PopPipe.popPipeBound, PrimT.WalkBank.walkBankCost, FinalPass.Flat.bodyCostL, FinalPass.Flat.lastCostL,
    FinalPass.Flat.visitLCost, FinalPass.Flat.mkSeedCost, FinalPass.Flat.mkEPCost, FinalPass.Flat.mkBWCost,
    FinalPass.Flat.levelCost, FinalPass.Flat.rowStepCost, FinalPass.Filt.selTCost, FinalPass.Filt.selStepCost,
    PopCellW.popCellBound, PopCellNum.numABound, PopCellNum.numBBound, PopRecW.popRecBound, PopRecW.setupBound,
    PopRecW.oneBound, PopRecW.statesBound, PopRecW.stateBound, PopRecW.visitsBound, PopBlockW.blockBound,
    PopBlockW.dataBound, LevelWordW.lvWordBound, LevelWordW.lvBodyBound, LevelW.phBound, PopParams.lvlBound,
    UnaryPow.sq, labsCost, gateCost, labCost1, popMlab, popLw, popRW]
  c6pb

end Pipe

/-! ## The deliverable -/

/-- **The POP pipeline bound**: the POP pipeline runs within `Kp · Y^Dp · 2^{Dp·e}`. -/
theorem popPipe_le : PrimAsm.SymLeaf.PopPipeLe := by
  obtain ⟨C, k, h⟩ := pb_pipe
  refine ⟨C, k, fun cap Pl e L r4 G off sgn s hlabs => ?_⟩
  have h1 := h ⟨cap, Pl, e, L, r4, G, off, sgn, s, hlabs⟩
  have e1 : Bp ⟨cap, Pl, e, L, r4, G, off, sgn, s, hlabs⟩ ^ k = (cap + Pl.M + Pl.B + Pl.errExp + L + r4 + G + off +
      Fintype.card Pl.FlatSeed + (8 * L + 2) ^ (3 * PopLink.lbP Pl + 1) + 2) ^ k * 2 ^ (k * Pl.errExp) := by
    simp only [Bp, Yp]
    rw [mul_pow, ← pow_mul, Nat.mul_comm Pl.errExp k]
  rw [e1, ← Nat.mul_assoc] at h1
  exact h1

end NearCubicWires.WireExponent3_5.UnionMachine.PopPipeLe
