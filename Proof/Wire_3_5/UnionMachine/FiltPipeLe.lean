import Proof.Wire_3_5.Primitive.Writers.BudgetIface2

/-! # The FILTER pipeline's cost is polynomial with an exponent linear in `e`

The regular filter's FILTER row prints `(4L+1)^{filtDeg}` monomials, `filtDeg = 384·walkLen + 1` with
`walkLen = 2⌊e/4⌋ + 1` (P3:2063-2101, the walk of length `O(e)`; `FiltRec.filtDeg_filterTable`); every other piece
of `FiltPipe.filtPipeBound` is polynomial in the parameters (`2^{fieldBits} ≤ 32·(2len+1)`, the rulers
`O(len + cap)`, the table `walkLen·(256L + 258) + 1`, the slice's labels `≤ off + L + (r4+4)G`).
* the pieces, each at most `c·M^k` for `M` a fixed multiple of `Y = len + cap + e + L + r4 + G + off + 2`;
* **`filtPipe_bound`**: `filtPipeBound … ≤ K_f·Y^{1540}·(L+2)^{1540(e+1)}` at the setup's rulers, the polynomial
  part of absolute degree (`r4`, `G`, `off` enter only through the labels), the exponential part the FILTER row's;
* **`filtPipe_le2 : BudgetIface.FiltPipeLe2`** (the consumer statement).

Paper quantity of the main type: the FILTER unit's running time at the error exponent `e` (P3:2063-2101, 2210-2211). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FiltPipeLe
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters

/-! ## Logarithms -/

theorem clog_le (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := by
  rcases Nat.lt_or_ge 1 n with h | h
  · have hc : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) h
    have := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h
    rw [Nat.pred_eq_sub_one] at this
    have e : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have : Nat.clog 2 n = 0 := Nat.clog_of_right_le_one h 2
    rw [this]; simp

/-! ## The parameters -/

section Params
variable (P : GapParams)

theorem fb_le : P.fieldBits ≤ P.len + 4 := by
  unfold GapParams.fieldBits; have := clog_le P.len; omega

theorem pow_fb_le : 2 ^ P.fieldBits ≤ 16 * (2 * P.len + 1) := by
  unfold GapParams.fieldBits
  rw [pow_add]; have := pow_clog_le P.len; norm_num; omega

theorem pb_le : P.prefixBits ≤ 32 * P.cap := by
  unfold GapParams.prefixBits; exact clog_le _

theorem lb_le : P.labelBits ≤ 32 * P.cap + P.len := by
  unfold GapParams.labelBits
  have := pb_le P; have := clog_le P.len
  exact max_le (by omega) (by omega)

theorem walkLen_le : P.walkLen ≤ P.errExp + 1 := by
  unfold GapParams.walkLen; omega

theorem wOf_le : FinalPass.Filt.wOf P.fieldBits P.labelBits ≤ 2 * (P.len + 4) + 3 * (32 * P.cap + P.len) := by
  unfold FinalPass.Filt.wOf
  have := fb_le P; have := lb_le P
  omega

end Params

/-! ## Polynomial pieces: monotone, then at one bound `M` -/

section Poly
open NearCubicWires.WireExponent3_5.FinalPass.Filt

theorem pows (M : ℕ) (h : 1 ≤ M) : 1 ≤ M ∧ M ≤ M ^ 2 ∧ M ^ 2 ≤ M ^ 3 ∧ M ^ 3 ≤ M ^ 4 := by
  refine ⟨h, ?_, ?_, ?_⟩
  · nlinarith
  · rw [pow_succ]; nlinarith [Nat.one_le_pow 2 M h]
  · rw [pow_succ]; nlinarith [Nat.one_le_pow 3 M h]

theorem copyCost_mono {m lb a L m' lb' a' L' : ℕ} (h1 : m ≤ m') (h2 : lb ≤ lb') (h3 : a ≤ a') (h4 : L ≤ L') :
    copyCost m lb a L ≤ copyCost m' lb' a' L' := by
  unfold copyCost kStepCost mulCost selTCost selStepCost FinalPass.Tm.mulStepCost
  gcongr

theorem copyCost_at (M : ℕ) (hM : 1 ≤ M) : copyCost M M M M ≤ 20000 * M ^ 3 := by
  unfold copyCost kStepCost mulCost selTCost selStepCost FinalPass.Tm.mulStepCost
  obtain ⟨p1, p2, p3, -⟩ := pows M hM
  nlinarith

theorem visitZCost_mono {m lb a L n m' lb' a' L' n' : ℕ} (h1 : m ≤ m') (h2 : lb ≤ lb') (h3 : a ≤ a') (h4 : L ≤ L')
    (h5 : n ≤ n') : visitZCost m lb a L n ≤ visitZCost m' lb' a' L' n' := by
  unfold visitZCost visitCost copiesCost
  have hc := copyCost_mono h1 h2 h3 h4
  unfold wOf
  gcongr

theorem visitZCost_at (M n : ℕ) (hM : 1 ≤ M) (hn : n ≤ 128) : visitZCost M M M M n ≤ 4000000 * M ^ 3 := by
  unfold visitZCost visitCost copiesCost wOf
  have hc := copyCost_at M hM
  obtain ⟨p1, p2, p3, -⟩ := pows M hM
  have e1 : n * (copyCost M M M M + 3) ≤ 128 * (20000 * M ^ 3 + 3) := Nat.mul_le_mul hn (by omega)
  have e2 : (2 * M + M + (M - 1) + M) * n ≤ (5 * M) * 128 := Nat.mul_le_mul (by omega) hn
  omega

end Poly

section Poly2
open NearCubicWires.WireExponent3_5.FinalPass.Filt

theorem bodyCost_le (m lb a L R M : ℕ) (hM : 1 ≤ M) (h1 : m ≤ M) (h2 : lb ≤ M) (h3 : a ≤ M) (h4 : L ≤ M)
    (h5 : R ≤ M) : bodyCost m lb a L 128 R ≤ 5000000 * M ^ 3 := by
  unfold bodyCost
  have v := visitZCost_mono (n := 128) (n' := 128) h1 h2 h3 h4 le_rfl
  have va := visitZCost_at M 128 hM le_rfl
  have hw : wOf m lb * 128 ≤ (5 * M) * 128 := Nat.mul_le_mul (by unfold wOf; omega) le_rfl
  obtain ⟨p1, p2, p3, -⟩ := pows M hM
  omega

theorem lastCost_le (m lb a L n M : ℕ) (hM : 1 ≤ M) (h1 : m ≤ M) (h2 : lb ≤ M) (h3 : a ≤ M) (h4 : L ≤ M)
    (h5 : n ≤ M) : lastCost m lb a L 128 n ≤ 6000000 * M ^ 3 := by
  unfold lastCost
  have v := visitZCost_mono (n := 128) (n' := 128) h1 h2 h3 h4 le_rfl
  have va := visitZCost_at M 128 hM le_rfl
  obtain ⟨p1, p2, p3, -⟩ := pows M hM
  have e1 : n * (128 * (2 * L + 2) + 2) ≤ M * (128 * (2 * M + 2) + 2) := Nat.mul_le_mul h5 (by omega)
  have e2 : M * (128 * (2 * M + 2) + 2) ≤ 258 * M ^ 2 + 256 * M ^ 2 := by nlinarith
  omega

theorem labsCost_mono {r4 G off Lg r4' G' off' Lg' : ℕ} (h1 : r4 ≤ r4') (h2 : G ≤ G') (h3 : off ≤ off') (h4 : Lg ≤ Lg') :
    PrimAsm.Emit.labsCost r4 G off Lg ≤ PrimAsm.Emit.labsCost r4' G' off' Lg' := by
  unfold PrimAsm.Emit.labsCost PrimAsm.Emit.gateCost PrimAsm.Emit.labCost1
  gcongr

theorem labsCost_at (M : ℕ) (hM : 1 ≤ M) : PrimAsm.Emit.labsCost M M M M ≤ 10000 * M ^ 3 := by
  unfold PrimAsm.Emit.labsCost PrimAsm.Emit.gateCost PrimAsm.Emit.labCost1
  obtain ⟨p1, p2, p3, -⟩ := pows M hM
  nlinarith

theorem loadCost_eq (ws : List (List Bool)) :
    ListMachine.Row.loadCost ws = 2 * (ws.map List.length).sum + 2 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [ListMachine.Row.loadCost, ih]; ring

end Poly2

section Words
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec

theorem labE_length (lab : ℕ) : (labE lab).length = 4 * lab + 4 := by
  simp [labE, PrimAsm.FiltRecW.reps_length, m2]; ring

theorem labsE_len (labs : List ℕ) : (labs.flatMap labE).length = 4 * labs.sum + 4 * labs.length := by
  induction labs with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.length_append, ih, labE_length, List.sum_cons, List.length_cons]; ring

theorem m2s_len (tw : List Bool) : (tw.flatMap m2).length = 4 * tw.length := by
  induction tw with
  | nil => rfl
  | cons b t ih => rw [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp [m2]; ring

theorem filtEmit_length (Lp d cap1 thr c : ℕ) (tw : List Bool) (labs : List ℕ) :
    (filtEmit Lp d cap1 thr c tw labs).length ≤
      200 + 48 * Lp + 4 * d + 4 * labs.sum + 4 * labs.length + 4 * cap1 + 4 * tw.length + 4 * thr + 32 * c := by
  simp only [filtEmit, List.length_append, PrimAsm.FiltRecW.reps_length, labsE_len, m2s_len]
  simp only [m2, m3, List.length_cons, List.length_nil]
  omega

end Words

section Fields
open NearCubicWires.WireExponent3_5.ListMachine

theorem atomCodes_len (labs : List ℕ) : (labs.flatMap Rec.atomCode).length = labs.sum + labs.length := by
  induction labs with
  | nil => rfl
  | cons l ls ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.sum_cons, List.length_cons]; simp [Rec.atomCode]; ring

theorem factorFields_sum (L d cap1 thr c : ℕ) (labs : List ℕ) (tbl : List (List (List Bool))) (sgn : Bool) :
    ((Row.factorFields L d labs cap1 0 (FinalPass.Filt.stage37Data tbl thr sgn c)).map List.length).sum ≤
      8 * L + d + labs.sum + labs.length + cap1 + (FinalPass.Filt.tableWord tbl).length + thr + 8 * c + 30 ∧
    (Row.factorFields L d labs cap1 0 (FinalPass.Filt.stage37Data tbl thr sgn c)).length = 24 := by
  constructor
  · simp only [Row.factorFields, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.ofFn_succ, List.ofFn_zero, RepairOrdinary.frame_length, Print.xsAt_length, List.length_replicate,
      List.length_cons, List.length_nil, List.length_append, Row.labelWord, atomCodes_len]
    simp [FinalPass.Filt.stage37Data, FinalPass.ListEval.unary]
    omega
  · simp [Row.factorFields]

end Fields

/-! ## The whole pipeline -/

section Main
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.RepairOrdinary (frame)

theorem labSum_eq (labs : List ℕ) : labSum labs = 5 + 2 * labs.sum + 10 * labs.length := by
  unfold labSum
  induction labs with
  | nil => rfl
  | cons l ls ih => simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem sum_le_of (labs : List ℕ) (B : ℕ) (h : ∀ l ∈ labs, l ≤ B) : labs.sum ≤ labs.length * B := by
  induction labs with
  | nil => simp
  | cons l ls ih =>
    simp only [List.sum_cons, List.length_cons]
    have h1 := h l List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem l hx))
    nlinarith

/-- The constants of the bound. -/
def K1 : ℕ := 100000000
def K2 : ℕ := 100000000
def K3 : ℕ := putCost filterPre + putCost filterSuf + 100

/-- The parameters' bounds at `M = 30000·Y`. -/
structure Atoms (P : GapParams) (L r4 G off Y M : ℕ) : Prop where
  hY2 : 2 ≤ Y
  hYM : Y ≤ M
  hM : 1 ≤ M
  big : 1000 ≤ M
  fb : P.fieldBits ≤ M
  lb : P.labelBits ≤ M
  pb : P.prefixBits ≤ M
  hL : L ≤ M
  RW : PrimAsm.FiltSetup.rulerW P ≤ M
  W : wOf P.fieldBits P.labelBits * 128 ≤ M
  e4 : 2 * (P.errExp / 4) ≤ M
  wl : P.walkLen ≤ M
  hr4 : r4 ≤ Y
  hG : G ≤ Y
  hoff : off ≤ Y
  sq : 3 * (Y * Y) + 2 * Y ≤ M * M
  hLY : L ≤ Y
  fbY : 2 ^ P.fieldBits ≤ 32 * Y

theorem atoms (P : GapParams) (L r4 G off : ℕ) :
    Atoms P L r4 G off (P.len + P.cap + P.errExp + L + r4 + G + off + 2)
      (30000 * (P.len + P.cap + P.errExp + L + r4 + G + off + 2)) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = P.len + P.cap + P.errExp + L + r4 + G + off + 2 := ⟨_, rfl⟩
  rw [← hY]
  have hfb := fb_le P
  have hlb := lb_le P
  have hpb := pb_le P
  have hwOf := wOf_le P
  have hwl := walkLen_le P
  have hp := pow_fb_le P
  have hY2 : 2 ≤ Y := by omega
  have h1 : Y * Y ≤ (30000 * Y) * (30000 * Y) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 2 * Y ≤ Y * Y := Nat.mul_le_mul_right Y hY2
  refine ⟨hY2, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_, by omega, by omega⟩
  · unfold PrimAsm.FiltSetup.rulerW; omega
  · have e1 : (30000 * Y) * (30000 * Y) = 900000000 * (Y * Y) := by ring
    omega

theorem partAD (P : GapParams) (L r4 G off Y M : ℕ) (a : Atoms P L r4 G off Y M) :
    PrimAsm.Modulus.modCost P.fieldBits + 1 + PrimT.tauCost P.fieldBits + 1 +
      PrimT.WalkBank.walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4))
        (PrimAsm.FiltSetup.rulerW P) (PrimAsm.FiltSetup.rulerW P) + 1 +
      (2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 (PrimAsm.FiltSetup.rulerW P) + 3) +
        3 + 1 + lastCost P.fieldBits P.labelBits P.prefixBits L 128 (2 * (P.errExp / 4))) ≤ 50000000 * M ^ 4 := by
  obtain ⟨p1, p2, p3, p4⟩ := pows M a.hM
  have hbig := a.big
  have hA : PrimAsm.Modulus.modCost P.fieldBits ≤ 300000 * M ^ 3 := by
    unfold PrimAsm.Modulus.modCost
    have h1 : 1 ≤ P.fieldBits := by unfold GapParams.fieldBits; omega
    have hs := GF2.searchCost_le P.fieldBits P.fieldBits h1 le_rfl
    have hp2 : 2 ^ (2 * P.fieldBits) ≤ (32 * Y) * (32 * Y) := by
      rw [pow_mul', sq]; exact Nat.mul_le_mul a.fbY a.fbY
    have h3 : 2 ^ (2 * P.fieldBits) * P.fieldBits ^ 1 ≤ ((32 * Y) * (32 * Y)) * M := by
      rw [pow_one]; exact Nat.mul_le_mul hp2 a.fb
    have h4 : ((32 * Y) * (32 * Y)) * M ≤ 1024 * M ^ 3 := by
      have hYY : Y * Y ≤ M * M := Nat.mul_le_mul a.hYM a.hYM
      have e1 : ((32 * Y) * (32 * Y)) * M = 1024 * ((Y * Y) * M) := by ring
      have e2 : M ^ 3 = (M * M) * M := by ring
      rw [e1, e2]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hYY)
    have h5 : GF2.searchCost P.fieldBits ≤ 200 * (1024 * M ^ 3) := hs.trans (Nat.mul_le_mul_left 200 (h3.trans h4))
    have := a.fb
    omega
  have hB : PrimT.tauCost P.fieldBits ≤ 4000 * M ^ 4 := by
    have := PrimT.tauCost_le P.fieldBits
    have h2 : (P.fieldBits + 1) ^ 4 ≤ (2 * M) ^ 4 := Nat.pow_le_pow_left (by have := a.fb; have := a.hM; omega) 4
    have h3 : (2 * M) ^ 4 = 16 * M ^ 4 := by ring
    omega
  have hC : PrimT.WalkBank.walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4))
      (PrimAsm.FiltSetup.rulerW P) (PrimAsm.FiltSetup.rulerW P) ≤ 30000000 * M ^ 2 := by
    unfold PrimT.WalkBank.walkBankCost
    have h1 : 160 * (2 * (P.errExp / 4)) + 2 * (wOf P.fieldBits P.labelBits * 128) + PrimAsm.FiltSetup.rulerW P +
        PrimAsm.FiltSetup.rulerW P + 2 ≤ 170 * M := by have := a.e4; have := a.W; have := a.RW; have := a.hM; omega
    have h2 := Nat.pow_le_pow_left h1 2
    have h3 : (170 * M) ^ 2 = 28900 * M ^ 2 := by ring
    omega
  have hD1 := bodyCost_le P.fieldBits P.labelBits P.prefixBits L (PrimAsm.FiltSetup.rulerW P) M a.hM a.fb a.lb a.pb a.hL
    a.RW
  have hD2 := lastCost_le P.fieldBits P.labelBits P.prefixBits L (2 * (P.errExp / 4)) M a.hM a.fb a.lb a.pb a.hL a.e4
  have hD : 2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 (PrimAsm.FiltSetup.rulerW P) + 3)
      ≤ 6000000 * M ^ 4 := by
    have h1 := Nat.mul_le_mul a.e4 (show bodyCost P.fieldBits P.labelBits P.prefixBits L 128
      (PrimAsm.FiltSetup.rulerW P) + 3 ≤ 5000000 * M ^ 3 + 3 by omega)
    have h5 : M * (5000000 * M ^ 3 + 3) ≤ 6000000 * M ^ 4 := by
      have e1 : M * (5000000 * M ^ 3 + 3) = 5000000 * M ^ 4 + 3 * M := by ring
      have h6 : M ≤ M ^ 4 := p2.trans (p3.trans p4)
      omega
    omega
  have h24 : M ^ 2 ≤ M ^ 4 := p3.trans p4
  omega

theorem labs_facts (L r4 G off Y M : ℕ) (hL : L ≤ M) (hr4 : r4 + 4 ≤ 3 * Y) (hG : G ≤ Y) (hoff : off ≤ Y)
    (hsq : 3 * (Y * Y) + 2 * Y ≤ M * M) (hYM : Y ≤ M) (hLY : L ≤ Y) (hM : 1 ≤ M) :
    (sliceLabs r4 G off L).length = 4 * L ∧ (sliceLabs r4 G off L).sum ≤ 4 * M ^ 3 ∧
      labSum (sliceLabs r4 G off L) ≤ 20 * M ^ 3 + 40 * M := by
  have hll : (sliceLabs r4 G off L).length = 4 * L := sliceLabs_length r4 G off L
  have hlabB : ∀ l ∈ sliceLabs r4 G off L, l ≤ M ^ 2 := by
    have hB0 : off + L + (r4 + 4) * G ≤ M ^ 2 := by
      have h1 : (r4 + 4) * G ≤ 3 * (Y * Y) := by
        have h0 := Nat.mul_le_mul hr4 hG
        have e0 : 3 * Y * Y = 3 * (Y * Y) := by ring
        omega
      have e1 : M ^ 2 = M * M := by ring
      omega
    exact sliceLabs_le r4 G off L (M ^ 2) hB0 L le_rfl
  have hsum : (sliceLabs r4 G off L).sum ≤ 4 * M ^ 3 := by
    have h1 := sum_le_of (sliceLabs r4 G off L) (M ^ 2) hlabB
    rw [hll] at h1
    have h2 : 4 * L * M ^ 2 ≤ 4 * M * M ^ 2 := Nat.mul_le_mul_right _ (by omega)
    have e1 : 4 * M * M ^ 2 = 4 * M ^ 3 := by ring
    omega
  obtain ⟨p1, p2, p3, p4⟩ := pows M hM
  refine ⟨hll, hsum, ?_⟩
  rw [labSum_eq, hll]; omega

theorem nums (P : GapParams) (e : GapSeed P) (L r4 G off Y M : ℕ) (a : Atoms P L r4 G off Y M) :
    filtDeg (filterTable P e L) ≤ 385 * M ∧ (tableWord (filterTable P e L)).length ≤ 515 * M ^ 2 ∧
      cap37 (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L ≤ 520 * M ^ 2 ∧
      SupplierWalk.majorityThreshold P.walkLen ≤ M ∧ (sliceLabs r4 G off L).length = 4 * L ∧
      (sliceLabs r4 G off L).sum ≤ 4 * M ^ 3 ∧ cap1C L (sliceLabs r4 G off L) ≤ 20 * M ^ 3 + 40 * M ∧
      labSum (sliceLabs r4 G off L) ≤ 20 * M ^ 3 + 40 * M ∧
      labCost (4 * L) (sliceLabs r4 G off L) ≤ 20 * M ^ 3 + 40 * M := by
  obtain ⟨p1, p2, p3, p4⟩ := pows M a.hM
  have hbig := a.big
  obtain ⟨hll, hsum, hls⟩ := labs_facts L r4 G off Y M a.hL (by have := a.hr4; have := a.hY2; omega) a.hG a.hoff
    a.sq a.hYM a.hLY a.hM
  have hwL : P.walkLen * (256 * L + 258) ≤ 514 * M ^ 2 := by
    have h1 := Nat.mul_le_mul a.wl (show 256 * L + 258 ≤ 514 * M by have := a.hL; have := a.hM; omega)
    have e1 : M * (514 * M) = 514 * M ^ 2 := by ring
    omega
  have hthr : SupplierWalk.majorityThreshold P.walkLen ≤ M := by
    unfold SupplierWalk.majorityThreshold; have := a.wl; have := a.hM; omega
  refine ⟨?_, ?_, ?_, hthr, hll, hsum, ?_, hls, ?_⟩
  · rw [filtDeg_filterTable P e L]; have := a.wl; omega
  · rw [tableWord_length P e L]; omega
  · rw [cap37_filterTable P e L _]; have := a.hL; omega
  · rw [cap1C_eq L _ hll]; exact hls
  · rw [← hll, labCost_eq]; exact hls

theorem partEF (P : GapParams) (e : GapSeed P) (L r4 G off Y M : ℕ) (a : Atoms P L r4 G off Y M) :
    PrimAsm.FiltRecW.filtBound (4 * L) (filtDeg (filterTable P e L)) (SupplierWalk.majorityThreshold P.walkLen)
      (cap37 (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L) (tableWord (filterTable P e L)).length
      (labSum (sliceLabs r4 G off L)) r4 G off L + 1 +
      (5 * (frame (filtRecC (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L true
        (sliceLabs r4 G off L))).length + 1) ≤ 10000000 * M ^ 3 := by
  obtain ⟨p1, p2, p3, p4⟩ := pows M a.hM
  have hbig := a.big
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, -⟩ := nums P e L r4 G off Y M a
  have hE1 := labsCost_mono (show r4 ≤ M by have := a.hr4; have := a.hYM; omega)
    (show G ≤ M by have := a.hG; have := a.hYM; omega) (show off ≤ M by have := a.hoff; have := a.hYM; omega) a.hL
  have hE2 := labsCost_at M a.hM
  have hE : PrimAsm.FiltRecW.filtBound (4 * L) (filtDeg (filterTable P e L))
      (SupplierWalk.majorityThreshold P.walkLen)
      (cap37 (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L) (tableWord (filterTable P e L)).length
      (labSum (sliceLabs r4 G off L)) r4 G off L ≤ 3000000 * M ^ 3 := by
    unfold PrimAsm.FiltRecW.filtBound
    have := a.hL
    omega
  have hF : (frame (filtRecC (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L true
      (sliceLabs r4 G off L))).length ≤ 100000 * M ^ 3 := by
    rw [filtEmit_eq]
    refine (filtEmit_length _ _ _ _ _ _ _).trans ?_
    have := a.hL
    omega
  omega

theorem partG (P : GapParams) (e : GapSeed P) (L r4 G off Y M : ℕ) (a : Atoms P L r4 G off Y M) :
    filtCostC (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L true (sliceLabs r4 G off L) ≤
      putCost filterPre + putCost filterSuf + 1000000 * M ^ 3 +
        (4 * L + 1) ^ (filtDeg (filterTable P e L)) * 2 ^ (filtDeg (filterTable P e L)) * (1000000 * M ^ 3) + 10 := by
  obtain ⟨p1, p2, p3, p4⟩ := pows M a.hM
  have hbig := a.big
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := nums P e L r4 G off Y M a
  have hF : (frame (filtRecC (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L true
      (sliceLabs r4 G off L))).length ≤ 100000 * M ^ 3 := by
    rw [filtEmit_eq]
    refine (filtEmit_length _ _ _ _ _ _ _).trans ?_
    have := a.hL
    omega
  obtain ⟨hff, hffl⟩ := factorFields_sum (4 * L) (filtDeg (filterTable P e L)) (cap1C L (sliceLabs r4 G off L))
    (SupplierWalk.majorityThreshold P.walkLen)
    (cap37 (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L) (sliceLabs r4 G off L)
    (filterTable P e L) true
  have hG1 : loadCost (factorFields (4 * L) (filtDeg (filterTable P e L)) (sliceLabs r4 G off L)
      (cap1C L (sliceLabs r4 G off L)) 0 (stage37Data (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) true
        (cap37 (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L))) ≤ 100000 * M ^ 3 := by
    rw [loadCost_eq, hffl]
    have := a.hL
    omega
  have hG2 : stage37Cost (tableWord (filterTable P e L)).length (SupplierWalk.majorityThreshold P.walkLen) L + 1 + 1 +
      2 * labCost (4 * L) (sliceLabs r4 G off L) + 100 * (4 * L + 1) ^ 2 ≤ 1000000 * M ^ 3 := by
    unfold stage37Cost cost7 FinalPass.Pop.passCost
    have h1 : (4 * L + 1) ^ 2 ≤ (5 * M) ^ 2 := Nat.pow_le_pow_left (by have := a.hL; have := a.hM; omega) 2
    have h2 : (5 * M) ^ 2 = 25 * M ^ 2 := by ring
    have := a.hL
    omega
  unfold filtCostC
  have hr : (filtRecC (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L true
      (sliceLabs r4 G off L)).length ≤ 100000 * M ^ 3 := by
    have := RepairOrdinary.frame_length (filtRecC (filterTable P e L) (SupplierWalk.majorityThreshold P.walkLen) L
      true (sliceLabs r4 G off L))
    omega
  have hm := Nat.mul_le_mul_left ((4 * L + 1) ^ (filtDeg (filterTable P e L)) * 2 ^ (filtDeg (filterTable P e L))) hG2
  omega

theorem expo (P : GapParams) (e : GapSeed P) (L : ℕ) :
    (4 * L + 1) ^ (filtDeg (filterTable P e L)) * 2 ^ (filtDeg (filterTable P e L)) ≤
      (L + 2) ^ (1540 * (P.errExp + 1)) := by
  rw [← mul_pow]
  have hfd : filtDeg (filterTable P e L) = 384 * P.walkLen + 1 := filtDeg_filterTable P e L
  have h8 : (4 * L + 1) * 2 ≤ (L + 2) ^ 4 := by
    have e1 : (L + 2) ^ 4 = (L + 2) * (L + 2) ^ 3 := by ring
    have h83 : 8 ≤ (L + 2) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (L + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h84 : (L + 2) * 8 ≤ (L + 2) ^ 4 := by rw [e1]; exact Nat.mul_le_mul_left _ h83
    omega
  calc ((4 * L + 1) * 2) ^ (filtDeg (filterTable P e L)) ≤ ((L + 2) ^ 4) ^ (filtDeg (filterTable P e L)) :=
        Nat.pow_le_pow_left h8 _
    _ = (L + 2) ^ (4 * filtDeg (filterTable P e L)) := by rw [← pow_mul]
    _ ≤ (L + 2) ^ (1540 * (P.errExp + 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        rw [hfd]; unfold GapParams.walkLen; omega

/-- **The FILTER pipeline's cost bound**: polynomial of absolute degree in the parameters, times the FILTER row's
`(L+2)^{1540(e+1)}`. -/
theorem filtPipe_bound (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ) :
    PrimAsm.FiltPipe.filtPipeBound P e L r4 G off (PrimAsm.FiltSetup.rulerW P) (PrimAsm.FiltSetup.rulerW P) ≤
      (K1 * 30000 ^ 4 + K2 * 30000 ^ 3 + K3) * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ 1540 *
        (L + 2) ^ (1540 * (P.errExp + 1)) := by
  have a := atoms P L r4 G off
  obtain ⟨Y, hY⟩ : ∃ Y, Y = P.len + P.cap + P.errExp + L + r4 + G + off + 2 := ⟨_, rfl⟩
  rw [← hY] at a ⊢
  obtain ⟨M, hMd⟩ : ∃ M, M = 30000 * Y := ⟨_, rfl⟩
  rw [← hMd] at a
  have hAD := partAD P L r4 G off Y M a
  have hEF := partEF P e L r4 G off Y M a
  have hG := partG P e L r4 G off Y M a
  have hX := expo P e L
  unfold PrimAsm.FiltPipe.filtPipeBound
  generalize (4 * L + 1) ^ (filtDeg (filterTable P e L)) * 2 ^ (filtDeg (filterTable P e L)) = BT at hG hX
  obtain ⟨p1, p2, p3, p4⟩ := pows M a.hM
  have hbig := a.big
  have hY1 : 1 ≤ Y := by have := a.hY2; omega
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (L + 2) ^ (1540 * (P.errExp + 1)) := ⟨_, rfl⟩
  rw [← hZ] at hX ⊢
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨D, hD⟩ : ∃ D, D = 1540 := ⟨_, rfl⟩
  rw [← hD]
  have hW1 : 1 ≤ Y ^ D := Nat.one_le_pow D Y (by omega)
  have hM4 : M ^ 4 ≤ 810000000000000000 * Y ^ D := by
    have e1 : M ^ 4 = 810000000000000000 * Y ^ 4 := by rw [hMd]; ring
    rw [e1]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega))
  have hM3 : M ^ 3 ≤ 27000000000000 * Y ^ D := by
    have e1 : M ^ 3 = 27000000000000 * Y ^ 3 := by rw [hMd]; ring
    rw [e1]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega))
  -- the polynomial part and the FILTER row's part, as multiples of `W · Z`, `W = Y^1540`
  generalize Y ^ D = W at hW1 hM4 hM3 ⊢
  have hWZ : W ≤ W * Z := Nat.le_mul_of_pos_right _ hZ1
  have hbig : BT * (1000000 * M ^ 3) ≤ 1000000 * 27000000000000 * (W * Z) := by
    calc BT * (1000000 * M ^ 3) ≤ Z * (1000000 * (27000000000000 * W)) :=
          Nat.mul_le_mul hX (Nat.mul_le_mul_left _ hM3)
      _ = 1000000 * 27000000000000 * (W * Z) := by ring
  have hK3 : putCost filterPre + putCost filterSuf + 100 ≤ (putCost filterPre + putCost filterSuf + 100) * (W * Z) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) (by omega))
  have hc4 : (30000 : ℕ) ^ 4 = 810000000000000000 := by norm_num
  have hc3 : (30000 : ℕ) ^ 3 = 27000000000000 := by norm_num
  unfold K1 K2 K3
  rw [hc4, hc3]
  have h34 : M ^ 3 ≤ M ^ 4 := p4
  have hZM : 70000000 * M ^ 4 ≤ 100000000 * 810000000000000000 * (W * Z) := by
    have h1 := Nat.mul_le_mul_left 70000000 (hM4.trans (Nat.mul_le_mul_left _ hWZ))
    have h2 : 70000000 * (810000000000000000 * (W * Z)) ≤ 100000000 * 810000000000000000 * (W * Z) := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (by norm_num)
    omega
  have hbig2 : 1000000 * 27000000000000 * (W * Z) ≤ 100000000 * 27000000000000 * (W * Z) :=
    Nat.mul_le_mul_right _ (by norm_num)
  have hdist : (100000000 * 810000000000000000 + 100000000 * 27000000000000 +
      (putCost filterPre + putCost filterSuf + 100)) * W * Z = 100000000 * 810000000000000000 * (W * Z) +
      100000000 * 27000000000000 * (W * Z) + (putCost filterPre + putCost filterSuf + 100) * (W * Z) := by ring
  rw [hdist]
  omega

/-- **`FiltPipeLe2` in the consumer's shape.** -/
theorem filtPipe_le2_pre : ∃ Kf Df : ℕ, ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
    PrimAsm.FiltPipe.filtPipeBound P e L r4 G off (PrimAsm.FiltSetup.rulerW P) (PrimAsm.FiltSetup.rulerW P) ≤
      Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ Df * (L + 2) ^ (Df * (P.errExp + 1)) :=
  ⟨K1 * 30000 ^ 4 + K2 * 30000 ^ 3 + K3, 1540, fun P e L r4 G off _ => filtPipe_bound P e L r4 G off⟩

end Main

/-- ** (d2): the FILTER pipeline's cost bound in the writers' form.** -/
theorem filtPipe_le2 : PrimAsm.BudgetIface.FiltPipeLe2 := filtPipe_le2_pre

end NearCubicWires.WireExponent3_5.UnionMachine.FiltPipeLe
