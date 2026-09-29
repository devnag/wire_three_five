import Proof.Wire_3_5.FinalPass.SdCtr2

/-! # S4 (the seeds phase), part 12: the loop over the centers (P3:1206-1216, 3044-3048)

"At each of the columns [centers], evaluate the reported lookup at these `Q` pairs" (P3:3046-3048): for a filter
seed `e`, the body visits every cell center `c = centerAt P σ row col` (the center writer into `tC`), runs the loop
over the sampled pairs there (`sLoop`), and rewinds the pairs' word. The loop state is relative to the loop's entry
state `ωR0` (its static facts `CStat`): `CInvB` (every kept stream as at entry, the heads, the registers but the two
flags, the numerator `frame (binary W a)`, the point's and center's streams formatted, `CarOK`, the scratch blank).
`KeptC`, `CStat`, `CInvB` (insensitive to the counters' words and flags: `cInvB_sets`, `cInvB_setv`), and the
evaluator's environment at a center `PtEnvC`.

Paper quantity of the main type: `Σ_c Σ_ℓ M(e, x_{c,ℓ})·Σ R̂(x_{c,ℓ})` at a filter seed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decCost decWord digitsOf)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)

section Lay
variable {nw nn nsc nrs : ℕ}

/-- The streams the center loop keeps: the sample loop's kept streams but the center and the two counters. -/
def KeptC (i : Fin (bns nw nsc + 1)) : Prop := Kept i ∧ i ≠ tC ∧ i ≠ tRow ∧ i ≠ tCol

/-- **The center loop's static facts** at its entry state `ωR0`. -/
structure CStat (cap : ℕ) (FP : GapParams) {n : ℕ} (carriers : List (Stars.Carrier n)) (P : StarParams)
    (σT : P.Translation) {N : ℕ} (ps : List (Fin N × Fin N)) (s bb h tl : ℕ) (ωR0 : BS nw nn nsc nrs) : Prop where
  Sp : ωR0.st tSp = [true]
  Thr : ωR0.st tThr = ListEval.unary (SupplierWalk.majorityThreshold FP.walkLen)
  sh : ∀ i, ωR0.sh i = 0
  ms : ∀ (j : ℕ) (hj : j < 14), ωR0.val (brg (122 + j) (by omega)) = 0
  cap2 : 2 ≤ cap
  M : ∀ k, ωR0.val (rM k) = 0
  Pf : ∀ k : Fin 2, ωR0.val (rP k) = if k.val < carriers.length then 1 else 0
  acc : ωR0.val rAcc = 0
  ac : ωR0.val rAc = 0
  dec : ∀ q : Fin 12, ωR0.val (frD q) = ![s, bb, h, tl, 0, 0, 0, 0, 0, 0, 0, 0] q
  off : ωR0.st (ctrS 0) = frameP (List.ofFn (offset P σT)) ++ [false]
  cB : ωR0.val (ctrR 0) = P.b
  cS : ωR0.val (ctrR 1) = P.s
  cH : ωR0.val (ctrR 2) = P.r / 2
  cL : ωR0.val (ctrR 3) = hL P
  cR : ωR0.val (ctrR 4) = P.n - P.r * P.b - hL P
  cZ : ∀ i : Fin 26, 5 ≤ i.val → ωR0.val (ctrR i) = 0
  I : ωR0.st tI = sw (s * h) ps
  cnt : ∀ b : Bool, ωR0.val (cC b) = 0 ∧ ωR0.val (cK b) = 0

/-- **The center loop's common state** at accumulator `a`. -/
structure CInvB (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n))
    (W a : ℕ) (ωR0 ω : BS nw nn nsc nrs) : Prop where
  st : ∀ i, KeptC i → ω.st i = ωR0.st i
  sh : ω.sh = ωR0.sh
  val : ∀ q, q ≠ cF false → q ≠ cF true → ω.val q = ωR0.val q
  cell : ω.cell = ωR0.cell
  Nw : ω.st tN = frame (binary W a)
  U : ∃ Y : List Bool, ω.st tU = frameP Y ++ [false] ∧ Y.length = n
  V : ∃ Y : List Bool, ω.st tV = frameP Y ++ [false] ∧ Y.length = n
  C : ∃ Y : List Bool, ω.st tC = frameP Y ++ [false] ∧ Y.length = n
  car : ∀ (k : Fin 2) (h : k.val < carriers.length), CarOK cap FP e (carriers.get ⟨k.val, h⟩) k ω
  sc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false

/-- **The evaluator's environment at a center**: as `PtEnv`, relative to the center loop's entry state. -/
structure PtEnvC {n : ℕ} (c u v : BitInput n) (ωR0 ω : BS nw nn nsc nrs) : Prop where
  st : ∀ i, KeptC i → ω.st i = ωR0.st i
  C : ω.st tC = frame (List.ofFn c)
  U : ω.st tU = frame (List.ofFn u)
  V : ω.st tV = frame (List.ofFn v)
  sh : ∀ i, i ≠ tI → ω.sh i = ωR0.sh i
  val : ∀ q, q ≠ rgX → q ≠ rM 0 → q ≠ rM 1 → q ≠ cF false → q ≠ cF true → ω.val q = ωR0.val q
  cell : ω.cell = ωR0.cell
  sc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false

theorem kept_C : Kept (tC : Fin (bns nw nsc + 1)) := kept_bst 1 _ (by omega) (by omega) (by omega) (by omega) (by omega)
theorem kept_Row : Kept (tRow : Fin (bns nw nsc + 1)) :=
  kept_bst 25 _ (by omega) (by omega) (by omega) (by omega) (by omega)
theorem kept_Col : Kept (tCol : Fin (bns nw nsc + 1)) :=
  kept_bst 26 _ (by omega) (by omega) (by omega) (by omega) (by omega)

/-- A counter's stream: off the numerator, the halves, the center, the carriers' streams, the scratch. -/
theorem cT_facts (row : Bool) :
    (cT row : Fin (bns nw nsc + 1)) ≠ tN ∧ (cT row : Fin (bns nw nsc + 1)) ≠ tU ∧
      (cT row : Fin (bns nw nsc + 1)) ≠ tV ∧ (cT row : Fin (bns nw nsc + 1)) ≠ tC ∧ ¬ IsSc (cT row : Fin (bns nw nsc + 1)) ∧
      (∀ (j : ℕ) (hj : j < 47), ((8 ≤ j ∧ j < 18) ∨ j = 32 ∨ j = 33) → bst j hj ≠ (cT row : Fin (bns nw nsc + 1))) ∧
      (∀ i, KeptC i → i ≠ (cT row : Fin (bns nw nsc + 1))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj hj' => ?_, fun i hi => ?_⟩
  · simp only [cT, tN]; apply bst_ne; split <;> omega
  · simp only [cT, tU]; apply bst_ne; split <;> omega
  · simp only [cT, tV]; apply bst_ne; split <;> omega
  · simp only [cT, tC]; apply bst_ne; split <;> omega
  · simp only [IsSc, cT, bst]; split <;> omega
  · simp only [cT]; apply bst_ne; split <;> omega
  · cases row
    · exact hi.2.2.2
    · exact hi.2.2.1

theorem cInvB_sets (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (W a : ℕ)
    (ωR0 ω : BS nw nn nsc nrs) (row : Bool) (s : List Bool) (h : CInvB cap FP e carriers W a ωR0 ω) :
    CInvB cap FP e carriers W a ωR0 (ω.sets (cT row) s) := by
  obtain ⟨hN, hU, hV, hC, hS, hM, hK⟩ := cT_facts (nw := nw) (nsc := nsc) row
  have ne : ∀ i, i ≠ cT row → (ω.sets (cT row) s).st i = ω.st i := fun i hi => by
    simp only [WState.sets_st]; rw [Function.update_of_ne hi]
  obtain ⟨YU, hYU, hlU⟩ := h.U
  obtain ⟨YV, hYV, hlV⟩ := h.V
  obtain ⟨YC, hYC, hlC⟩ := h.C
  exact ⟨fun i hi => by rw [ne i (hK i hi)]; exact h.st i hi, by simp only [WState.sets_sh]; exact h.sh,
    fun q h1 h2 => by simp only [WState.sets_val]; exact h.val q h1 h2, h.cell,
    by rw [ne tN (Ne.symm hN)]; exact h.Nw, ⟨YU, by rw [ne tU (Ne.symm hU)]; exact hYU, hlU⟩,
    ⟨YV, by rw [ne tV (Ne.symm hV)]; exact hYV, hlV⟩, ⟨YC, by rw [ne tC (Ne.symm hC)]; exact hYC, hlC⟩,
    fun k hk => carOK_tr cap FP e _ k (h.car k hk) (fun j hj hj' => ne _ (hM j hj hj')),
    fun i hi b hb => by rw [ne i (fun e => hS (e ▸ hi))] at hb; exact h.sc i hi b hb⟩

theorem cInvB_setv (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (W a : ℕ)
    (ωR0 ω : BS nw nn nsc nrs) (row : Bool) (v : ℕ) (h : CInvB cap FP e carriers W a ωR0 ω) :
    CInvB cap FP e carriers W a ωR0 (ω.setv (cF row) v) :=
  ⟨h.st, h.sh, fun q h1 h2 => by
      rw [wsetv_val_ne _ _ (show q ≠ cF row by cases row <;> assumption)]; exact h.val q h1 h2,
    h.cell, h.Nw, h.U, h.V, h.C, fun k hk => carOK_tr cap FP e _ k (h.car k hk) (fun _ _ _ => rfl), h.sc⟩

end Lay

end NearCubicWires.WireExponent3_5.FinalPass.Sd
