import Proof.Wire_3_5.Compiler.MachineReqFits
import Proof.Wire_3_5.Compiler.MachinePolyTerm

/-! # C3 v2: the compiler stages' contract, emitting the printer's request (P3:1874-1955, 1707-1738, 3105-3115)

Realizes the five-field unit (`Machine.MachineContract`) of the compiler stages of `alg:compiler` with the base
printer's input as the output: "There is an explicit signed separated-equation expression congruent to `2^{m−1}V(z)`
modulo `2^{Q'}`, with at most `𝒮 ≤ A 2^m Q'(P_ex+1)^{Q'd}` occurrences. Each occurrence stacks at most `Q'd` original
exact equations and has a coefficient of `O(b+m+Q')` bits" (P3:1886-1893), printed through "the two successor cuts
`1[E_i=0] = 1[E_i≥0] − 1[E_i≥1]`" (P3:1728-1731), in the additive class `2^{O(Ψ)}` (P3:3108, 3112-3114).

The request is C3a's pool request (the dense pool `densePool`), the padded expression over the pool
atoms, `m`, `d`, the printer instance (the row bits and the columns of `φ`) and the field width `p`. The
output is the base printer's `MatrixScoreBatch.Request` word; the reference is
`doubled false (cutsRefX …)`. The error field names the printer's table: there is a request `r` with this word, and at
every row and column its weighted-dominance table is `2^{m−1}·V` modulo `2^{Q'}`, where atom `i·G + gi` is the value
of gate `gi` at the pulled-back point of flip `i` (the pool's meaning, `densePool_exact`), and `r` has at most
`2·A·2^m·Q'(P_ex+1)^{Q'd}` cuts.

The P/N range of C3a's word (1) is an explicit precondition (`PNFit`, the instruction on MC6): the pool stream
writes every field part in `h` bits, and this contract is the consumer that reads them as the dense fields.

Main declarations: `C3Req`, `C3Req.D`, `C3Req.occBound`, `atomVal`, `PNFit`, `C3Req.Pre`, `reqWord`, `c3v2Ref`,
`mkReq`, **`c3v2`**, **`c3v2_err`**, **`c3v2_not_nil`**; lemmas `cutsRefX_length`, `poolSyn_flatten`,
`poolExact_atomVal`, `cols_getD`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Req
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.SupplierPipeline NearCubicWires.RepairRepresentation NearCubicWires.SupplierPrinter
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut Request leftScore rightScore weight cutWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- The C3 v2 request: C3a's pool request `P` (the dense pool, its P/N width `h` and the lift precision `Q'`), the
expression `V` over the pool atoms, the factor count `m`, the degree `d`, the printer's row bits `dRow` and the columns
of `φ`, the field width `p` of the stacked cuts, the star width `k` and the load `ψ`. -/
structure C3Req where
  P : PoolReq
  V : IntExpression ℕ
  m : ℕ
  d : ℕ
  dRow : ℕ
  cols : List ℕ
  p : ℕ
  k : ℕ
  psi : ℕ

variable (a : DecompositionAlgorithm)

/-- The dense pool of the request (C3a's reference). -/
def C3Req.D (R : C3Req) : List (List (ExactThresholdGate (R.P.width + R.P.width))) :=
  densePool a R.P.gates R.P.side R.P.width R.P.flips

/-- The occurrence bound `A·2^m·Q'·(P_ex+1)^{Q'd}` (alg:eq-occurrences, P3:1887-1888). -/
def C3Req.occBound (R : C3Req) : ℕ :=
  R.V.length * 2 ^ R.m * (R.P.Q * ((R.D a).flatten.length + 1) ^ (R.P.Q * R.d))

theorem gates_pos (F G x : ℕ) (hx : x < F * G) : 0 < G := by
  rcases Nat.eq_zero_or_pos G with h | h
  · rw [h, Nat.mul_zero] at hx; omega
  · exact h

/-- **The truth of pool atom `x`** at the center assignment `(a_L, a_R)`: gate `x mod G` at the pulled-back point of
flip pattern `x / G`; atoms beyond the pool are false. -/
def atomVal (R : PoolReq) (aL aR x : ℕ) : Bool :=
  if hx : x < R.flips.length * R.gates.length then
    (R.gates[x % R.gates.length]'(Nat.mod_lt _ (gates_pos _ _ _ hx))).gate.eval
      (pullPoint R.side (R.flips[x / R.gates.length]'((Nat.div_lt_iff_lt_mul (gates_pos _ _ _ hx)).mpr hx)) aL aR)
  else false

/-- **The P/N range of C3a's word (1)**: every field part of every pool child is below `2^h`, so the pool stream's
`h`-bit words carry the dense fields (`fieldPN_value`). -/
def PNFit (R : PoolReq) : Prop :=
  ∀ fe ∈ poolChildren a R.gates R.flips, ∀ q, q ≤ R.width + R.width →
    (fieldPN R.side fe.1 R.width fe.2 q).1 < 2 ^ R.h ∧ (fieldPN R.side fe.1 R.width fe.2 q).2 < 2 ^ R.h

/-- The admissible requests: C3a's precondition, `m, Q' ≥ 1`, every term has exactly `m` factors, monomials of at
most `d` atoms of the pool, the pool's P/N range and magnitudes within `h` bits, the stacked fields within `p` bits
(`h·Q'·d ≤ p`, `|c|·2^{Q'} ≤ 2^p`), the printer instance (`width ≤ 2·dRow`, `dRow` columns of `width` bits), and the
printer's gate budget `(2·𝒮)² ≤ ⌈U^{0.1}⌉` (alg:eq-budget, P3:1897-1900). -/
def C3Req.Pre (R : C3Req) : Prop :=
  R.P.Pre ∧ 1 ≤ R.m ∧ 1 ≤ R.P.Q ∧ Padded R.m R.V ∧
    (∀ t ∈ R.V, ∀ f ∈ t.2, ∀ mono ∈ f, mono.length ≤ R.d ∧ ∀ x ∈ mono, x < R.P.flips.length * R.P.gates.length) ∧
    PNFit a R.P ∧ DenseFit R.P.h (R.D a) ∧
    R.P.h * R.P.Q * R.d ≤ R.p ∧ (∀ t ∈ R.V, t.1.natAbs * 2 ^ R.P.Q ≤ 2 ^ R.p) ∧
    R.P.width ≤ 2 * R.dRow ∧ R.cols.length = R.dRow ∧ (∀ c ∈ R.cols, c < 2 ^ R.P.width) ∧
    (2 * R.occBound a) * (2 * R.occBound a) ≤ rectangularInnerDimension (2 ^ R.dRow)

/-- The printer's request word (`MatrixScoreBatch.word`) of the given fields. -/
def reqWord (dRow p width : ℕ) (cols : List ℕ) (cs : List Cut) : List Bool :=
  (natWord dRow ++ natWord p ++ natWord cs.length ++ natWord width ++ MatrixScorePhi.columnsWord width cols) ++
    cs.flatMap (cutWord p)

/-- **The reference**: the stacked cuts in the machine's order, each doubled into its two successor cuts. -/
def c3v2Ref (R : C3Req) : List Cut :=
  EquationRow.doubled false (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V)

/-- The request with the given cuts (its invariants as hypotheses). -/
def mkReq (R : C3Req) (cs : List Cut) (hw : R.P.width ≤ 2 * R.dRow)
    (hcf : ∀ j, j < R.dRow → R.cols.getD j 0 < 2 ^ R.P.width)
    (hl : ∀ c ∈ cs, c.leftWeights.length = R.P.width ∧ c.rightWeights.length = R.P.width)
    (hf : ∀ c ∈ cs, EquationRow.Fits (R.p + 1) c)
    (hg : cs.length * cs.length ≤ rectangularInnerDimension (2 ^ R.dRow)) : Request where
  d := R.dRow
  p := R.p + 1
  cuts := cs
  width := R.P.width
  column := fun j => R.cols.getD j 0
  widthLe := hw
  columnFits := hcf
  lengths := hl
  fits := hf
  gateSquare := hg

/-- **The C3 v2 contract**: the compiler stages emit the base printer's request. -/
def c3v2 (E : Envelope) (inputWord : C3Req → List Bool) (coef : ℕ) : MachineContract E where
  Req := C3Req
  input := inputWord
  pre := fun R => R.Pre a ∧ (inputWord R).length ≤ 2 ^ R.psi
  Out := List Cut × C3Req
  ref := fun R => (c3v2Ref a R, R)
  encode := fun o => reqWord o.2.dRow (o.2.p + 1) o.2.P.width o.2.cols o.1
  cls := .preprocessing
  q := fun R => R.P.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef
  /- alg:compiler (P3:1886-1890) through the printer (P3:1728-1737): the word is a request's word, and at every row
  and column its table is `2^{m−1}·V` modulo `2^{Q'}`, with at most `2·A·2^m·Q'(P_ex+1)^{Q'd}` cuts. -/
  errSpec := fun R o => ∃ r : Request, MatrixScoreBatch.word r = reqWord o.2.dRow (o.2.p + 1) o.2.P.width o.2.cols o.1 ∧
    r.cuts = o.1 ∧ r.d = R.dRow ∧ r.p = R.p + 1 ∧ r.width = R.P.width ∧ r.cols = R.cols ∧
    r.Gates ≤ 2 * R.occBound a ∧
    ∀ row col : Fin r.U, weightedDominance (leftScore r) (rightScore r) (weight r) row col ≡
      2 ^ (R.m - 1) * IntExpression.eval R.V (atomVal R.P (r.phi row.val) (r.phi col.val)) [ZMOD (2 : ℤ) ^ R.P.Q]

/-! ## The error field of the reference -/

theorem cutsRefX_length {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) (H : ℤ) (m Q : ℕ)
    (V : IntExpression ℕ) : (cutsRefX D H m Q V).length = (compileRefX (poolSyn D) H m Q V).length := by
  unfold cutsRefX compileRefX
  simp only [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro j _
  congr 1
  apply List.map_congr_left
  intro t _
  unfold termCuts termOcc
  rw [List.length_map, List.length_map, oddMasksM_congr (shapeOf D) (poolSyn D) (shape_poolSyn D)]

theorem poolSyn_flatten {w : ℕ} (D : List (List (ExactThresholdGate (w + w)))) :
    (poolSyn D).flatten = D.flatten.map synOf := by
  unfold poolSyn
  rw [List.map_flatten]

theorem cols_getD (l : List ℕ) : (List.range l.length).map (fun j => l.getD j 0) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ h2

/-- **The pool is exact at every center assignment** for the atom truths `atomVal` (from `densePool_exact`). -/
theorem poolExact_atomVal (R : PoolReq) (hR : R.Pre) (aL aR : ℕ) :
    PoolExact (poolSyn (densePool a R.gates R.side R.width R.flips)) aL aR (atomVal R aL aR) := by
  obtain ⟨_, _, hL, hRr⟩ := hR
  intro x
  rw [poolSyn, getD_map_map, List.map_map]
  have hfun : ((fun e => bitZ (decide (e.value aL aR = 0))) ∘ synOf) =
      fun e : ExactThresholdGate (R.width + R.width) => if e.eval (centerInput R.width aL aR) then (1 : ℤ) else 0 := by
    funext e
    simp only [Function.comp]
    rw [← eqOf_holds, synOf_value]
    by_cases hd : (eqOf e).difference (RowBinLift.assignment aL aR) = 0
    · simp [bitZ, LabelledEquation.Holds, hd]
    · simp [bitZ, LabelledEquation.Holds, hd]
  rw [hfun]
  by_cases hx : x < R.flips.length * R.gates.length
  · have hG := gates_pos _ _ _ hx
    have hi : x / R.gates.length < R.flips.length := (Nat.div_lt_iff_lt_mul hG).mpr hx
    have hg : x % R.gates.length < R.gates.length := Nat.mod_lt _ hG
    have hex := densePool_exact a R.gates R.side R.width R.flips aL aR hL hRr _ _ hi hg
    rw [Nat.div_add_mod' x R.gates.length] at hex
    rw [← hex]
    simp only [atomVal, dif_pos hx, bitZ]
  · have hlen := densePool_length a R.gates R.side R.width R.flips
    rw [List.getD_eq_default _ _ (by omega)]
    simp [atomVal, dif_neg hx, bitZ]

/-- **The error field holds for the reference** on every admissible request (the `Certified.err` field of C3 v2). -/
theorem c3v2_err (E : Envelope) (inputWord : C3Req → List Bool) (coef : ℕ) :
    ∀ R, (c3v2 a E inputWord coef).pre R →
      (c3v2 a E inputWord coef).errSpec R ((c3v2 a E inputWord coef).ref R) := by
  rintro R ⟨⟨hP, hm, hQ, hV, hmono, _, hD, hp, hc, hw, hcl, hcf, hbud⟩, _⟩
  set D := R.D a with hDdef
  set H : ℤ := 2 ^ R.P.h
  set cs := cutsRefX D H R.m R.P.Q R.V
  have hlenle : cs.length ≤ R.occBound a := by
    rw [cutsRefX_length]
    have := compileRefX_length_le (poolSyn D) H R.m R.P.Q R.d hm R.V hV (fun t ht f hf mono hmn => (hmono t ht f hf mono hmn).1)
    rwa [poolSyn_flatten, List.length_map] at this
  have hfits : ∀ c ∈ cs, EquationRow.Fits R.p c := by
    intro c hc'
    simp only [cs, cutsRefX, List.mem_flatMap, List.mem_range, termCuts, List.mem_map] at hc'
    obtain ⟨j, _, t, ht, e, he, rfl⟩ := hc'
    refine occCut_fits D R.P.h R.P.Q R.d R.p hQ hD hp (t.1 * 2 ^ 0) (-(-1 : ℤ) ^ (selectBits t.2 j).length) ?_
      (by simpa using hc t ht) _ ?_ e he
    · rw [Int.natAbs_neg, Int.natAbs_pow]
      simp
    · intro mono hmn
      obtain ⟨f, hf, hmf⟩ := List.mem_flatten.mp hmn
      exact (hmono t ht f ((Poly.selectBits_sublist t.2 j).subset hf) mono hmf).1
  have hlens : ∀ c ∈ EquationRow.doubled false cs,
      c.leftWeights.length = R.P.width ∧ c.rightWeights.length = R.P.width := by
    intro c hc'
    simp only [EquationRow.doubled, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc'
    obtain ⟨c0, hc0, hc'⟩ := hc'
    simp only [cs, cutsRefX, List.mem_flatMap, List.mem_range, termCuts, List.mem_map] at hc0
    obtain ⟨j, _, t, _, e, _, rfl⟩ := hc0
    rcases hc' with rfl | rfl <;>
      simp [EquationRow.padded, EquationRow.successor, EquationRow.paddedRight, occCut, RowBinLift.split]
  have hfit2 : ∀ c ∈ EquationRow.doubled false cs, EquationRow.Fits (R.p + 1) c := by
    intro c hc'
    simp only [EquationRow.doubled, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc'
    obtain ⟨c0, hc0, hc'⟩ := hc'
    have hf := EquationRow.padded_fits false R.p c0 (hfits c0 hc0)
    rcases hc' with rfl | rfl
    · exact EquationRow.fits_widen R.p _ hf
    · exact EquationRow.successor_fits R.p _ hf
  have hcf' : ∀ j, j < R.dRow → R.cols.getD j 0 < 2 ^ R.P.width := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hcf _ (List.getElem_mem _)
  have hg : (EquationRow.doubled false cs).length * (EquationRow.doubled false cs).length ≤
      rectangularInnerDimension (2 ^ R.dRow) := by
    rw [EquationRow.doubled_length]
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlenle) (Nat.mul_le_mul_left 2 hlenle)).trans hbud
  refine ⟨mkReq R (EquationRow.doubled false cs) hw hcf' hlens hfit2 hg, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show MatrixScoreBatch.word _ = _
    unfold MatrixScoreBatch.word MatrixScoreBatch.header reqWord
    have hcols : (mkReq R (EquationRow.doubled false cs) hw hcf' hlens hfit2 hg).cols = R.cols := by
      show (List.range R.dRow).map (fun j => R.cols.getD j 0) = R.cols
      rw [← hcl]
      exact cols_getD R.cols
    rw [hcols]
    rfl
  · show (List.range R.dRow).map (fun j => R.cols.getD j 0) = R.cols
    rw [← hcl]
    exact cols_getD R.cols
  · show (EquationRow.doubled false cs).length ≤ 2 * R.occBound a
    rw [EquationRow.doubled_length]
    omega
  · intro row col
    rw [table_doubled _ cs rfl row col, ← occTable_cutsRefX]
    refine compileRefX_modEq (poolSyn D) H (H - 1) (by omega) R.m R.P.Q hm R.V hV _ _ ?_ _
      (poolExact_atomVal a R.P hP _ _)
    intro e he
    rw [poolSyn_flatten] at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact synOf_abs_le R.P.h x (hD x hx) _ _


end NearCubicWires.WireExponent3_5.CompilerMachine.Req
