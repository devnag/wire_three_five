import Proof.Wire_3_5.FinalPass.SdDec

/-! # S4 (the seeds phase), part 8: one sampled pair (P3:3044-3053, 3170-3178)

"At each column, evaluate the reported lookup at these `Q` pairs" (P3:3046-3048): for a fixed center `c` and filter
seed `e`, the loop runs over the sampled pairs `(a, b)` on word `1` (`sw kh ps`: per pair both indices framed in
`kh`-bit binary, then `0`): stage 0 decodes `a` into `tU` and `b` into `tV` (`decB`), and the per-point step adds
`[mask]·V(a, b)` to the numerator. The loop state `SInv` is relative to the loop's entry state `ωR` (its static facts
`SStat`); the evaluator is a hypothesis at every pair from any state meeting `PtEnv`. **`sIter_spec`**: one pair,
the numerator gains `sTerm (a, b) = [carF 0 ∧ carF 1]·V(a, b)`, `SInv` at the next pair. **`sLoop_spec`**: the loop
`sLoop E` over all the pairs on `tI` adds `sSum ps = Σ_{(a,b) ∈ ps} sTerm (a, b)`.

Paper quantity of the main type: `Σ_ℓ M(e, x_ℓ)·Σ R̂(x_ℓ)` over the sampled pairs at a center. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decCost decWord digitsOf binary_length'')
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

/-- **The sampled pairs' word**: per pair both indices framed in `kh`-bit binary, then `0`. -/
def sw {N : ℕ} (kh : ℕ) (ps : List (Fin N × Fin N)) : List Bool :=
  ps.flatMap (fun ab => frame (binary kh ab.1) ++ frame (binary kh ab.2)) ++ [false]

theorem sw_cons {N : ℕ} (kh : ℕ) (a b : Fin N) (ps : List (Fin N × Fin N)) :
    sw kh ((a, b) :: ps) = frameP (binary kh a) ++ false :: (frameP (binary kh b) ++ false :: sw kh ps) := by
  simp [sw, frame_eq_frameP]

theorem drop_frame (X R : List Bool) : (frameP X ++ false :: R).drop (2 * X.length + 1) = R := by
  rw [show frameP X ++ false :: R = (frameP X ++ [false]) ++ R by simp, List.drop_left' (by simp)]

section Lay
variable {nw nn nsc nrs : ℕ}

theorem decOut_st_ne (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) (i : Fin (bns nw nsc + 1))
    (hi : i ≠ tO right) : (decOut right s bb h tl k p ω).st i = ω.st i := by
  simp only [decOut, WState.setv_st, WState.seth_st, WState.sets_st]
  rw [Function.update_of_ne hi]

theorem decOut_st_O (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) :
    (decOut right s bb h tl k p ω).st (tO right) =
      frameP (decWord bb h tl right (digitsOf s h (binary (s * h) k))) ++ [false] := by
  simp [decOut]

theorem decOut_sh_ne (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) (i : Fin (bns nw nsc + 1))
    (hi : i ≠ tI) : (decOut right s bb h tl k p ω).sh i = ω.sh i := by
  simp only [decOut, WState.setv_sh, WState.seth_sh, WState.sets_sh]
  rw [Function.update_of_ne hi]

theorem decOut_sh_I (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) :
    (decOut right s bb h tl k p ω).sh tI = p + 2 * (s * h) + 1 := by
  simp [decOut]

theorem decOut_val_ne (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) (q : Fin (bnr nn nrs))
    (hq : q ≠ rgX) : (decOut right s bb h tl k p ω).val q = ω.val q := by
  simp only [decOut, WState.setv_val, WState.seth_val, WState.sets_val]
  rw [Function.update_of_ne hq]

theorem decOut_val_X (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) :
    (decOut right s bb h tl k p ω).val rgX = p + 2 * (s * h) + 1 := by
  simp [decOut]

theorem decOut_cell (right : Bool) (s bb h tl k p : ℕ) (ω : BS nw nn nsc nrs) :
    (decOut right s bb h tl k p ω).cell = ω.cell := rfl

/-- The carriers' streams agree. -/
theorem carOK_tr (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (X : Stars.Carrier n) (k : Fin 2)
    {ω ω' : BS nw nn nsc nrs} (hc : CarOK cap FP e X k ω)
    (h : ∀ (j : ℕ) (hj : j < 47), ((8 ≤ j ∧ j < 18) ∨ j = 32 ∨ j = 33) → ω'.st (bst j hj) = ω.st (bst j hj)) :
    CarOK cap FP e X k ω' := by
  have := k.isLt
  obtain ⟨A, B, ys, h1, h2, h3, h4⟩ := hc.acc
  exact ⟨by rw [show tG k = bst (32 + k.val) _ from rfl, h _ _ (by omega)]; exact hc.G,
    ⟨A, B, ys, by rw [show tPos k = bst (10 + 4 * k.val) _ from rfl, h _ _ (by omega)]; exact h1,
      by rw [show tNeg k = bst (11 + 4 * k.val) _ from rfl, h _ _ (by omega)]; exact h2,
      by rw [show tX k = bst (12 + 4 * k.val) _ from rfl, h _ _ (by omega)]; exact h3, h4⟩,
    by rw [show tZ k = bst (13 + 4 * k.val) _ from rfl, h _ _ (by omega)]; exact hc.Z,
    by rw [show tT k = bst (8 + k.val) _ from rfl, h _ _ (by omega)]; exact hc.T, hc.cap⟩

/-- The streams a sample loop keeps: all but the numerator, the point's halves, the carriers' accumulators and
corner words, and the evaluators' scratch. -/
def Kept (i : Fin (bns nw nsc + 1)) : Prop :=
  i ≠ tN ∧ i ≠ tU ∧ i ≠ tV ∧ (∀ k : Fin 2, i ≠ tPos k ∧ i ≠ tNeg k ∧ i ≠ tX k) ∧ ¬ IsSc i

/-- A fixed stream off the numerator, the halves, the carriers' accumulators and corner words, and the scratch, is
kept. -/
theorem kept_bst (j : ℕ) (hj : j < 47) (h0 : j ≠ 0) (h2 : j ≠ 2) (h3 : j ≠ 3) (hm : j < 10 ∨ 18 ≤ j)
    (hs : j < 18 ∨ 25 ≤ j) : Kept (bst j hj : Fin (bns nw nsc + 1)) :=
  ⟨by simp only [tN]; apply bst_ne; omega, by simp only [tU]; apply bst_ne; omega,
    by simp only [tV]; apply bst_ne; omega,
    fun k => by
      have := k.isLt
      exact ⟨by simp only [tPos]; apply bst_ne; omega, by simp only [tNeg]; apply bst_ne; omega,
        by simp only [tX]; apply bst_ne; omega⟩,
    by simp only [IsSc, bst]; omega⟩

/-- **The sample loop's static facts** at its entry state `ωR`. -/
structure SStat (cap : ℕ) (FP : GapParams) {n : ℕ} (carriers : List (Stars.Carrier n)) (c : BitInput n)
    (s bb h tl : ℕ) (ωR : BS nw nn nsc nrs) : Prop where
  C : ωR.st tC = frame (List.ofFn c)
  Sp : ωR.st tSp = [true]
  Thr : ωR.st tThr = ListEval.unary (SupplierWalk.majorityThreshold FP.walkLen)
  sh : ∀ i, i ≠ tI → ωR.sh i = 0
  ms : ∀ (j : ℕ) (hj : j < 14), ωR.val (brg (122 + j) (by omega)) = 0
  cap2 : 2 ≤ cap
  M : ∀ k, ωR.val (rM k) = 0
  P : ∀ k : Fin 2, ωR.val (rP k) = if k.val < carriers.length then 1 else 0
  acc : ωR.val rAcc = 0
  ac : ωR.val rAc = 0
  dec : ∀ q : Fin 12, q ≠ 9 → ωR.val (frD q) = ![s, bb, h, tl, 0, 0, 0, 0, 0, 0, 0, 0] q

/-- **The sample loop's state** with `rest` pairs to go, the numerator `x`, `tI`'s head at `p`. -/
structure SInv (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) {N : ℕ}
    (kh W x p : ℕ) (rest : List (Fin N × Fin N)) (ωR ω : BS nw nn nsc nrs) : Prop where
  st : ∀ i, Kept i → ω.st i = ωR.st i
  sh : ∀ i, i ≠ tI → ω.sh i = ωR.sh i
  shI : ω.sh tI = p
  val : ∀ q, q ≠ rgX → ω.val q = ωR.val q
  X : ω.val rgX = p
  cell : ω.cell = ωR.cell
  Nw : ω.st tN = frame (binary W x)
  U : ∃ Y : List Bool, ω.st tU = frameP Y ++ [false] ∧ Y.length = n
  V : ∃ Y : List Bool, ω.st tV = frameP Y ++ [false] ∧ Y.length = n
  car : ∀ (k : Fin 2) (h : k.val < carriers.length), CarOK cap FP e (carriers.get ⟨k.val, h⟩) k ω
  sc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false
  I : (ω.st tI).drop p = sw kh rest

/-- **The evaluator's environment** at the point `(u, v)`. -/
structure PtEnv {n : ℕ} (u v : BitInput n) (ωR ω : BS nw nn nsc nrs) : Prop where
  st : ∀ i, Kept i → ω.st i = ωR.st i
  U : ω.st tU = frame (List.ofFn u)
  V : ω.st tV = frame (List.ofFn v)
  sh : ∀ i, i ≠ tI → ω.sh i = ωR.sh i
  val : ∀ q, q ≠ rgX → q ≠ rM 0 → q ≠ rM 1 → ω.val q = ωR.val q
  cell : ω.cell = ωR.cell
  sc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false

end Lay

/-! ## One pair -/

variable (E : SymPtEval2)

/-- **One sampled pair**: its halves decoded, then the per-point step. -/
noncomputable def sBody : BP E.nw E.nn E.nsc E.nrs := .seq (decB false) (.seq (decB true) (ptStep E))

/-- One pair's cost at a value bound `V`. -/
def sCost (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (s bb h tl nE V T : ℕ) : ℕ :=
  decCost s bb h tl + 1 + (decCost s bb h tl + 1 + ptCost FP e carriers nE V T)

/-- The pair's term: the mask's two factors at the decoded halves times the value. -/
def sTerm (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (c : BitInput n) {N : ℕ}
    (eu ev : Fin N → BitInput n) (Vf : Fin N → Fin N → ℕ) (ab : Fin N × Fin N) : ℕ :=
  (carF FP e carriers c (eu ab.1) (ev ab.2) 0 && carF FP e carriers c (eu ab.1) (ev ab.2) 1).toNat * Vf ab.1 ab.2

theorem sIter_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n))
    (c : BitInput n) {N : ℕ} (eu ev : Fin N → BitInput n) (Vf : Fin N → Fin N → ℕ) (s bb h tl W T nE Vm : ℕ)
    (ωR : BS E.nw E.nn E.nsc E.nrs) (hR : SStat cap FP carriers c s bb h tl ωR)
    (hbs : bb + 1 = 2 ^ s) (hn : h * bb + h * bb + tl = n)
    (hdl : ∀ a : Fin N, decWord bb h tl false (digitsOf s h (binary (s * h) a)) = List.ofFn (eu a))
    (hdr : ∀ b : Fin N, decWord bb h tl true (digitsOf s h (binary (s * h) b)) = List.ofFn (ev b))
    (hev : ∀ (a b : Fin N) (ω₀ : BS E.nw E.nn E.nsc E.nrs), PtEnv (eu a) (ev b) ωR ω₀ →
      ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ nE ∧ EvOut (Vf a b) ω₀ ω₁)
    (hVm : ∀ a b, Vf a b ≤ Vm) (hVc : Vm ≤ cap) (hcapT : 2 * T + 2 < cap)
    (hcs : 2 * 2 ^ s ≤ cap ∧ s ≤ cap ∧ 2 * n ≤ cap ∧ bb ≤ cap ∧ h ≤ cap ∧ tl ≤ cap)
    (x p : ℕ) (a b : Fin N) (rest : List (Fin N × Fin N)) (ω : BS E.nw E.nn E.nsc E.nrs)
    (hI : SInv cap FP e carriers (s * h) W x p ((a, b) :: rest) ωR ω)
    (hp : p + 2 * (2 * (s * h) + 1) ≤ cap)
    (hx : x + sTerm FP e carriers c eu ev Vf (a, b) < 2 ^ W)
    (hT : x + sTerm FP e carriers c eu ev Vf (a, b) < 2 ^ T) :
    ∃ ω', WExec cap (sBody E) ω ω' (sCost FP e carriers s bb h tl nE Vm T) ∧
      SInv cap FP e carriers (s * h) W (x + sTerm FP e carriers c eu ev Vf (a, b)) (p + 2 * (2 * (s * h) + 1)) rest
        ωR ω' := by
  have hUV : (tU : Fin (bns E.nw E.nsc + 1)) ≠ tV := by simp only [tU, tV]; apply bst_ne; omega
  have hIU : (tI : Fin (bns E.nw E.nsc + 1)) ≠ tU := by simp only [tI, tU]; apply bst_ne; omega
  have hIV : (tI : Fin (bns E.nw E.nsc + 1)) ≠ tV := by simp only [tI, tV]; apply bst_ne; omega
  have tOf : (tO false : Fin (bns E.nw E.nsc + 1)) = tU := rfl
  have tOt : (tO true : Fin (bns E.nw E.nsc + 1)) = tV := rfl
  have hfr : ∀ q : Fin 12, q ≠ 9 → (frD q : Fin (bnr E.nn E.nrs)) ≠ rgX := fun q hq h =>
    hq (frD_inj (h.trans (rfl : (rgX : Fin (bnr E.nn E.nrs)) = frD 9)))
  have hla := binary_length'' (s * h) a
  have hlb := binary_length'' (s * h) b
  obtain ⟨YU, hYU, hYUl⟩ := hI.U
  obtain ⟨YV, hYV, hYVl⟩ := hI.V
  have hdrop := hI.I
  rw [sw_cons] at hdrop
  -- the left half
  have e1 := decB_spec cap false s bb h tl a p YU (frameP (binary (s * h) b) ++ false :: sw (s * h) rest) ω hbs hdrop
    hI.shI (by rw [tOf]; exact hYU) (by rw [hYUl]; omega)
    (by rw [tOf, hI.sh tU hIU.symm]; exact hR.sh tU hIU.symm)
    (fun q => by
      by_cases hq : q = 9
      · subst hq; rw [show frD 9 = (rgX : Fin (bnr E.nn E.nrs)) from rfl, hI.X]; simp
      · rw [hI.val _ (hfr q hq), hR.dec q hq]; fin_cases q <;> simp_all)
    hcs.1 hcs.2.1 (by omega) (by rw [hYUl]; exact hcs.2.2.1) hcs.2.2.2.1 hcs.2.2.2.2.1 hcs.2.2.2.2.2
  obtain ⟨ω1, h1⟩ : ∃ ω1, ω1 = decOut false s bb h tl a p ω := ⟨_, rfl⟩
  rw [← h1] at e1
  have h1I : ω1.st tI = ω.st tI := by rw [h1, decOut_st_ne _ _ _ _ _ _ _ _ _ (by rw [tOf]; exact hIU)]
  -- the right half
  have hdrop1 : (ω1.st tI).drop (p + 2 * (s * h) + 1) = frameP (binary (s * h) b) ++ false :: sw (s * h) rest := by
    rw [h1I, show p + 2 * (s * h) + 1 = p + (2 * (binary (s * h) a).length + 1) by rw [hla]; ring, ← List.drop_drop,
      hdrop, drop_frame]
  have e2 := decB_spec cap true s bb h tl b (p + 2 * (s * h) + 1) YV (sw (s * h) rest) ω1 hbs hdrop1
    (by rw [h1, decOut_sh_I]) (by rw [tOt, h1, decOut_st_ne _ _ _ _ _ _ _ _ _ (by rw [tOf]; exact hUV.symm)]; exact hYV)
    (by rw [hYVl]; omega)
    (by rw [tOt, h1, decOut_sh_ne _ _ _ _ _ _ _ _ _ hIV.symm, hI.sh tV hIV.symm]; exact hR.sh tV hIV.symm)
    (fun q => by
      by_cases hq : q = 9
      · subst hq; rw [show frD 9 = (rgX : Fin (bnr E.nn E.nrs)) from rfl, h1, decOut_val_X]; simp
      · rw [h1, decOut_val_ne _ _ _ _ _ _ _ _ _ (hfr q hq), hI.val _ (hfr q hq), hR.dec q hq]
        fin_cases q <;> simp_all)
    hcs.1 hcs.2.1 (by omega) (by rw [hYVl]; exact hcs.2.2.1) hcs.2.2.2.1 hcs.2.2.2.2.1 hcs.2.2.2.2.2
  obtain ⟨ω2, h2⟩ : ∃ ω2, ω2 = decOut true s bb h tl b (p + 2 * (s * h) + 1) ω1 := ⟨_, rfl⟩
  rw [← h2] at e2
  -- facts about ω2
  have st2 : ∀ i, i ≠ tU → i ≠ tV → ω2.st i = ω.st i := fun i hu hv => by
    rw [h2, decOut_st_ne _ _ _ _ _ _ _ _ _ (by rw [tOt]; exact hv), h1,
      decOut_st_ne _ _ _ _ _ _ _ _ _ (by rw [tOf]; exact hu)]
  have sh2 : ∀ i, i ≠ tI → ω2.sh i = ω.sh i := fun i hi => by
    rw [h2, decOut_sh_ne _ _ _ _ _ _ _ _ _ hi, h1, decOut_sh_ne _ _ _ _ _ _ _ _ _ hi]
  have val2 : ∀ q, q ≠ rgX → ω2.val q = ω.val q := fun q hq => by
    rw [h2, decOut_val_ne _ _ _ _ _ _ _ _ _ hq, h1, decOut_val_ne _ _ _ _ _ _ _ _ _ hq]
  have U2 : ω2.st tU = frame (List.ofFn (eu a)) := by
    rw [h2, decOut_st_ne _ _ _ _ _ _ _ _ _ (by rw [tOt]; exact hUV), h1, ← tOf, decOut_st_O, hdl, frame_eq_frameP]
  have V2 : ω2.st tV = frame (List.ofFn (ev b)) := by
    rw [h2, ← tOt, decOut_st_O, hdr, frame_eq_frameP]
  have hkeep : ∀ i, Kept i → ω2.st i = ωR.st i := fun i hk => by
    rw [st2 i hk.2.1 hk.2.2.1]; exact hI.st i hk
  have hRsh : ∀ i, i ≠ tI → ω2.sh i = ωR.sh i := fun i hi => by rw [sh2 i hi]; exact hI.sh i hi
  have hRv : ∀ q, q ≠ rgX → ω2.val q = ωR.val q := fun q hq => by rw [val2 q hq]; exact hI.val q hq
  have hms : ∀ (j : ℕ) (hj : j < 14), (brg (122 + j) (by omega) : Fin (bnr E.nn E.nrs)) ≠ rgX := fun j hj => by
    simp only [rgX]; apply brg_ne; omega
  have hsc2 : ∀ i, IsSc i → ∀ b ∈ ω2.st i, b = false := fun i hi b hb => by
    have hu : i ≠ tU := fun h => by subst h; simp only [IsSc, tU, bst] at hi; omega
    have hv : i ≠ tV := fun h => by subst h; simp only [IsSc, tV, bst] at hi; omega
    rw [st2 i hu hv] at hb
    exact hI.sc i hi b hb
  -- the point's step
  have hcom : MaskCom cap FP c (eu a) (ev b) ω2 :=
    ⟨by rw [show tC = bst 1 _ from rfl, hkeep _ (kept_bst 1 _ (by omega) (by omega) (by omega) (by omega)
          (by omega))]; exact hR.C,
      U2, V2,
      by rw [show tSp = bst 4 _ from rfl, hkeep _ (kept_bst 4 _ (by omega) (by omega) (by omega) (by omega)
          (by omega))]; exact hR.Sp,
      by rw [show tThr = bst 36 _ from rfl, hkeep _ (kept_bst 36 _ (by omega) (by omega) (by omega) (by omega)
          (by omega))]; exact hR.Thr,
      fun i hi => by rw [hRsh i hi]; exact hR.sh i hi,
      fun j hj => by rw [hRv _ (hms j hj)]; exact hR.ms j hj, hR.cap2⟩
  have hcar : ∀ (k : Fin 2) (hk : k.val < carriers.length), CarOK cap FP e (carriers.get ⟨k.val, hk⟩) k ω2 :=
    fun k hk => carOK_tr cap FP e _ k (hI.car k hk) (fun j hj hj' => st2 _
      (by simp only [tU]; apply bst_ne; omega) (by simp only [tV]; apply bst_ne; omega))
  have hacR : (rAc : Fin (bnr E.nn E.nrs)) ≠ rgX := by simp only [rAc, rgX]; apply brg_ne; omega
  have haR : (rAcc : Fin (bnr E.nn E.nrs)) ≠ rgX := by simp only [rAcc, rgX]; apply brg_ne; omega
  have hmR : ∀ k : Fin 2, (rM k : Fin (bnr E.nn E.nrs)) ≠ rgX := fun k => by
    have := k.isLt; simp only [rM, rgX]; apply brg_ne; omega
  have hpR : ∀ k : Fin 2, (rP k : Fin (bnr E.nn E.nrs)) ≠ rgX := fun k => by
    have := k.isLt; simp only [rP, rgX]; apply brg_ne; omega
  have hNU : (tN : Fin (bns E.nw E.nsc + 1)) ≠ tU := by simp only [tN, tU]; apply bst_ne; omega
  have hNV : (tN : Fin (bns E.nw E.nsc + 1)) ≠ tV := by simp only [tN, tV]; apply bst_ne; omega
  have hN2 : ω2.st tN = frame (binary W x) := by
    rw [st2 tN hNU hNV]; exact hI.Nw
  have hmk : ∀ i : Fin (bns E.nw E.nsc + 1), IsSc i → ∀ k : Fin 2, i ≠ tPos k ∧ i ≠ tNeg k ∧ i ≠ tX k := fun i hi k => by
    have := k.isLt
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> (subst h; simp only [IsSc, tPos, tNeg, tX, bst] at hi; omega)
  have hUm : ∀ k : Fin 2, (tU : Fin (bns E.nw E.nsc + 1)) ≠ tPos k ∧ (tU : Fin (bns E.nw E.nsc + 1)) ≠ tNeg k ∧ (tU : Fin (bns E.nw E.nsc + 1)) ≠ tX k :=
      fun k => by
    have := k.isLt
    exact ⟨by simp only [tU, tPos]; apply bst_ne; omega, by simp only [tU, tNeg]; apply bst_ne; omega,
      by simp only [tU, tX]; apply bst_ne; omega⟩
  have hVm' : ∀ k : Fin 2, (tV : Fin (bns E.nw E.nsc + 1)) ≠ tPos k ∧ (tV : Fin (bns E.nw E.nsc + 1)) ≠ tNeg k ∧ (tV : Fin (bns E.nw E.nsc + 1)) ≠ tX k :=
      fun k => by
    have := k.isLt
    exact ⟨by simp only [tV, tPos]; apply bst_ne; omega, by simp only [tV, tNeg]; apply bst_ne; omega,
      by simp only [tV, tX]; apply bst_ne; omega⟩
  obtain ⟨ω3, e3, n3, _, k3, v3, s3, c3, o3, sc3⟩ := ptStep_spec E cap FP e carriers c (eu a) (ev b) W T x
    (Vf a b) nE ω2 hcom hcar (fun k => by rw [hRv _ (hmR k)]; exact hR.M k)
    (fun k => by rw [hRv _ (hpR k)]; exact hR.P k) hN2 (by rw [hRv _ haR]; exact hR.acc)
    (by rw [hRv _ hacR]; exact hR.ac) hsc2
    (fun ω₀ hs hc hst hv => hev a b ω₀ ⟨fun i hk => by rw [hst i hk.2.2.2.1]; exact hkeep i hk,
      by rw [hst tU hUm]; exact U2, by rw [hst tV hVm']; exact V2,
      fun i hi => by rw [hs]; exact hRsh i hi,
      fun q hq h0 h1' => by rw [hv q h0 h1']; exact hRv q hq,
      by rw [hc, h2, decOut_cell, h1, decOut_cell]; exact hI.cell,
      fun i hi b hb => by rw [hst i (hmk i hi)] at hb; exact hsc2 i hi b hb⟩)
    hx hT ((hVm a b).trans hVc) hcapT
  have hIk : Kept (tI : Fin (bns E.nw E.nsc + 1)) := kept_bst 31 _ (by omega) (by omega) (by omega) (by omega)
    (by omega)
  refine ⟨ω3, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) ?_, ⟨fun i hk => ?_, fun i hi => ?_, ?_, fun q hq => ?_, ?_,
    ?_, n3, ?_, ?_, k3, sc3, ?_⟩⟩
  · unfold sCost
    have : ptCost FP e carriers nE (Vf a b) T ≤ ptCost FP e carriers nE Vm T := by
      unfold ptCost
      have := Nat.mul_le_mul_right (incCost T + 4) (hVm a b)
      omega
    omega
  · rw [o3 i hk.1 hk.2.2.2.1 hk.2.2.2.2]; exact hkeep i hk
  · rw [s3]; exact hRsh i hi
  · rw [s3, h2, decOut_sh_I]; ring
  · rw [v3]; exact hRv q hq
  · rw [v3, h2, decOut_val_X]; ring
  · rw [c3, h2, decOut_cell, h1, decOut_cell]; exact hI.cell
  · refine ⟨List.ofFn (eu a), ?_, by simp⟩
    rw [o3 tU hNU.symm hUm (by simp only [IsSc, tU, bst]; omega), U2, frame_eq_frameP]
  · refine ⟨List.ofFn (ev b), ?_, by simp⟩
    rw [o3 tV hNV.symm hVm' (by simp only [IsSc, tV, bst]; omega), V2, frame_eq_frameP]
  · rw [o3 tI hIk.1 hIk.2.2.2.1 hIk.2.2.2.2, st2 tI hIU hIV,
      show p + 2 * (2 * (s * h) + 1) = p + (2 * (binary (s * h) a).length + 1) +
        (2 * (binary (s * h) b).length + 1) by rw [hla, hlb]; ring,
      ← List.drop_drop (i := 2 * (binary (s * h) b).length + 1) (j := p + (2 * (binary (s * h) a).length + 1)),
      ← List.drop_drop (i := 2 * (binary (s * h) a).length + 1) (j := p), hdrop, drop_frame, drop_frame]

/-! ## All the pairs -/

/-- **The loop over the sampled pairs.** -/
noncomputable def sLoop : BP E.nw E.nn E.nsc E.nrs := .whs tI (sBody E)

/-- The pairs' sum. -/
def sSum (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n)) (c : BitInput n) {N : ℕ}
    (eu ev : Fin N → BitInput n) (Vf : Fin N → Fin N → ℕ) (ps : List (Fin N × Fin N)) : ℕ :=
  (ps.map (sTerm FP e carriers c eu ev Vf)).sum

theorem wbit_tI {nw nn nsc nrs : ℕ} (ω : BS nw nn nsc nrs) (p : ℕ) (hp : ω.sh tI = p) (l : List Bool)
    (hl : (ω.st tI).drop p = l) : wbit ω tI = l.getD 0 false := by
  unfold wbit
  have e := ListEval.readTapeBit_drop (ω.st tI) p 0
  simp only [Nat.add_zero] at e
  rw [hp, e, hl]
  rfl

theorem sLoop_spec (cap : ℕ) (FP : GapParams) (e : GapSeed FP) {n : ℕ} (carriers : List (Stars.Carrier n))
    (c : BitInput n) {N : ℕ} (eu ev : Fin N → BitInput n) (Vf : Fin N → Fin N → ℕ) (s bb h tl W T nE Vm : ℕ)
    (ωR : BS E.nw E.nn E.nsc E.nrs) (hR : SStat cap FP carriers c s bb h tl ωR)
    (hbs : bb + 1 = 2 ^ s) (hn : h * bb + h * bb + tl = n) (hkh : 1 ≤ s * h)
    (hdl : ∀ a : Fin N, decWord bb h tl false (digitsOf s h (binary (s * h) a)) = List.ofFn (eu a))
    (hdr : ∀ b : Fin N, decWord bb h tl true (digitsOf s h (binary (s * h) b)) = List.ofFn (ev b))
    (hev : ∀ (a b : Fin N) (ω₀ : BS E.nw E.nn E.nsc E.nrs), PtEnv (eu a) (ev b) ωR ω₀ →
      ∃ ω₁, WExec cap (evalD E) ω₀ ω₁ nE ∧ EvOut (Vf a b) ω₀ ω₁)
    (hVm : ∀ a b, Vf a b ≤ Vm) (hVc : Vm ≤ cap) (hcapT : 2 * T + 2 < cap)
    (hcs : 2 * 2 ^ s ≤ cap ∧ s ≤ cap ∧ 2 * n ≤ cap ∧ bb ≤ cap ∧ h ≤ cap ∧ tl ≤ cap) :
    ∀ (rest : List (Fin N × Fin N)) (x p : ℕ) (ω : BS E.nw E.nn E.nsc E.nrs),
      SInv cap FP e carriers (s * h) W x p rest ωR ω →
      p + rest.length * (2 * (2 * (s * h) + 1)) ≤ cap →
      x + sSum FP e carriers c eu ev Vf rest < 2 ^ W → x + sSum FP e carriers c eu ev Vf rest < 2 ^ T →
      ∃ ω', WExec cap (sLoop E) ω ω' (rest.length * (sCost FP e carriers s bb h tl nE Vm T + 2) + 1) ∧
        SInv cap FP e carriers (s * h) W (x + sSum FP e carriers c eu ev Vf rest)
          (p + rest.length * (2 * (2 * (s * h) + 1))) ([] : List (Fin N × Fin N)) ωR ω'
  | [], x, p, ω, hI, _, _, _ => by
    refine ⟨ω, WExec.mono (WExec.whsF ?_) (by simp), ?_⟩
    · rw [wbit_tI ω p hI.shI _ hI.I]
      rfl
    · simpa [sSum] using hI
  | (a, b) :: rest, x, p, ω, hI, hp, hx, hT => by
    have hsum : sSum FP e carriers c eu ev Vf ((a, b) :: rest) =
        sTerm FP e carriers c eu ev Vf (a, b) + sSum FP e carriers c eu ev Vf rest := by
      simp [sSum]
    rw [hsum] at hx hT
    have hlen : ((a, b) :: rest).length = rest.length + 1 := rfl
    rw [hlen] at hp
    obtain ⟨ω1, e1, h1⟩ := sIter_spec E cap FP e carriers c eu ev Vf s bb h tl W T nE Vm ωR hR hbs hn hdl hdr hev hVm
      hVc hcapT hcs x p a b rest ω hI (by nlinarith) (by omega) (by omega)
    obtain ⟨ω', e', h'⟩ := sLoop_spec cap FP e carriers c eu ev Vf s bb h tl W T nE Vm ωR hR hbs hn hkh hdl hdr hev
      hVm hVc hcapT hcs rest _ _ ω1 h1 (by nlinarith) (by omega) (by omega)
    have hbit : wbit ω tI = true := by
      rw [wbit_tI ω p hI.shI _ hI.I, sw_cons]
      obtain ⟨k, hk⟩ : ∃ k, s * h = k + 1 := ⟨s * h - 1, by omega⟩
      rw [hk]
      simp [SignedSortKey.binary, frameP]
    refine ⟨ω', WExec.mono (WExec.whsT hbit e1 e') ?_, ?_⟩
    · rw [hlen, Nat.add_mul, Nat.one_mul]
      omega
    · have eq1 : x + sSum FP e carriers c eu ev Vf ((a, b) :: rest) =
          x + sTerm FP e carriers c eu ev Vf (a, b) + sSum FP e carriers c eu ev Vf rest := by
        rw [hsum]; ring
      have eq2 : p + ((a, b) :: rest).length * (2 * (2 * (s * h) + 1)) =
          p + 2 * (2 * (s * h) + 1) + rest.length * (2 * (2 * (s * h) + 1)) := by
        rw [hlen]; ring
      rw [eq1, eq2]
      exact h'

end NearCubicWires.WireExponent3_5.FinalPass.Sd
