import Proof.Wire_3_5.Primitive.Writers.SparseNum

/-! # C6 front, the capacity writer: `1^{capQ q}` and `1^{RQ q}` as unary streams

The loop's bank needs registers of capacity `cap = capQ q = (32·coef+1)·2^{q−⌊k/4⌋}·(q+1)^{A_main}`, scratch of `R = RQ q =
1000(q+6)·cap` blanks, a driver `1^R` and a log `0^{R+1}` (`Plan.bankA`). These are far beyond any register of a small
word program, so the writer builds them as unary STREAMS, sentinel first (`U d = 0 1^d`), bit-driven (no counter reaches
`cap`): a copy loop (`cpLoop`), the sentinel rewind (`rewU`), the seek (`seekEnd`), append (`appS`), in-place doubling
(`dblS`), `2^m` by `m` doublings (`powS`), and `C` appended copies (`repS`).

Paper quantity of the main type: the loop's capacities `cap`, `R` (P3:3797-3811 via), in unary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCapW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Unary streams -/

/-- A unary stream: the sentinel `0`, then `d` ones. -/
def U (d : ℕ) : List Bool := false :: List.replicate d true

/-- Write `k` ones from position `h`. -/
def wrOnes : List Bool → ℕ → ℕ → List Bool
  | l, _, 0 => l
  | l, h, k + 1 => wrOnes (writeTapeBit l h true) (h + 1) k

theorem write_rep_true : ∀ (e h : ℕ), h ≤ e →
    writeTapeBit (List.replicate e true) h true = List.replicate (max e (h + 1)) true
  | 0, 0, _ => by simp [writeTapeBit]
  | e + 1, 0, _ => by
    rw [List.replicate_succ]
    simp only [writeTapeBit]
    rw [max_eq_left (by omega), List.replicate_succ]
  | e + 1, h + 1, hh => by
    rw [List.replicate_succ]
    simp only [writeTapeBit]
    rw [write_rep_true e h (by omega), show max (e + 1) (h + 1 + 1) = max e (h + 1) + 1 by omega, List.replicate_succ]
  | 0, h + 1, hh => by omega

theorem write_U (e h : ℕ) (h1 : 1 ≤ h) (h2 : h ≤ e + 1) : writeTapeBit (U e) h true = U (max e h) := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  unfold U
  simp only [writeTapeBit]
  rw [write_rep_true e h' (by omega)]

theorem wrOnes_U : ∀ (d e h : ℕ), 1 ≤ h → h ≤ e + 1 → wrOnes (U e) h d = U (max e (h - 1 + d))
  | 0, e, h, h1, h2 => by simp only [wrOnes]; rw [max_eq_left (by omega)]
  | d + 1, e, h, h1, h2 => by
    simp only [wrOnes]
    rw [write_U e h h1 h2, wrOnes_U d (max e h) (h + 1) (by omega) (by omega)]
    congr 1
    omega

theorem read_U_pos (d j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ d) : readTapeBit (U d) j = true := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold U readTapeBit
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, show j' < d by omega]

theorem read_U_zero (d : ℕ) : readTapeBit (U d) 0 = false := by
  unfold U readTapeBit; simp

theorem read_U_end (d j : ℕ) (h : d + 1 ≤ j) : readTapeBit (U d) j = false := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold U readTapeBit
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, show ¬ j' < d by omega]

/-! ## The loops -/

section Loops
variable {ns nr : ℕ} (cap : ℕ)

theorem wst_eq {σ τ : WState ns nr} (h1 : ∀ i, σ.sh i = τ.sh i) (h2 : ∀ i, σ.st i = τ.st i) (h3 : σ.val = τ.val)
    (h4 : σ.cell = τ.cell) : σ = τ := WState.eq (funext h1) (funext h2) h3 h4

/-- The copy body: write `1` on `b`, advance `b` and `a`. -/
def cpBody (a b : Fin (ns + 1)) : WM ns nr := .seq (.wr b true) (.seq (.fwd b) (.fwd a))

/-- **The copy loop**: while `a` reads `1`. -/
def cpLoop (a b : Fin (ns + 1)) : WM ns nr := .whs a (cpBody a b)

/-- The state after `k` copy steps. -/
def cpState (a b : Fin (ns + 1)) (σ : WState ns nr) (k : ℕ) : WState ns nr :=
  ((σ.sets b (wrOnes (σ.st b) (σ.sh b) k)).seth b (σ.sh b + k)).seth a (σ.sh a + k)

theorem cpLoop_spec (a b : Fin (ns + 1)) (hab : a ≠ b) : ∀ (k : ℕ) (σ : WState ns nr),
    (∀ j < k, readTapeBit (σ.st a) (σ.sh a + j) = true) → readTapeBit (σ.st a) (σ.sh a + k) = false →
    WExec cap (cpLoop a b) σ (cpState a b σ k) (7 * k + 1)
  | 0, σ, _, hstop => by
    have h := WExec.whsF (cap := cap) (P := cpBody a b) (i := a) (σ := σ) (by simpa [wbit] using hstop)
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hia : i = a
      · subst hia; simp [cpState, Function.update_apply]
      · by_cases hib : i = b
        · subst hib; simp [cpState, Function.update_apply, hia]
        · simp [cpState, Function.update_apply, hia, hib]
    · intro i
      by_cases hib : i = b
      · subst hib; simp [cpState, wrOnes, Function.update_apply]
      · simp [cpState, Function.update_apply, hib]
    · rfl
    · rfl
  | k + 1, σ, hrun, hstop => by
    have hba : b ≠ a := fun h => hab h.symm
    have h0 := hrun 0 (by omega)
    set σ1 : WState ns nr := ((σ.sets b (writeTapeBit (σ.st b) (σ.sh b) true)).seth b (σ.sh b + 1)).seth a
      (σ.sh a + 1) with hσ1
    have hbody : WExec cap (cpBody a b) σ σ1 5 := by
      have e1 := WExec.wr (cap := cap) b true σ
      have e2 := WExec.fwd (cap := cap) b (σ.sets b (writeTapeBit (σ.st b) (σ.sh b) true))
      have e3 := WExec.fwd (cap := cap) a ((σ.sets b (writeTapeBit (σ.st b) (σ.sh b) true)).seth b
        ((σ.sets b (writeTapeBit (σ.st b) (σ.sh b) true)).sh b + 1))
      refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
      simp only [σ1, WState.seth_sh, WState.sets_sh, Function.update_of_ne hab]
    have s1a : σ1.st a = σ.st a := by simp [σ1, Function.update_of_ne hab]
    have h1a : σ1.sh a = σ.sh a + 1 := by simp [σ1]
    have s1b : σ1.st b = writeTapeBit (σ.st b) (σ.sh b) true := by simp [σ1]
    have h1b : σ1.sh b = σ.sh b + 1 := by simp [σ1, Function.update_of_ne hba]
    have ih := cpLoop_spec a b hab k σ1 (fun j hj => by
        rw [s1a, h1a, show σ.sh a + 1 + j = σ.sh a + (j + 1) by omega]; exact hrun (j + 1) (by omega))
      (by rw [s1a, h1a, show σ.sh a + 1 + k = σ.sh a + (k + 1) by omega]; exact hstop)
    have h := WExec.whsT (cap := cap) (i := a) (by simpa [wbit] using h0) hbody ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i
      by_cases hia : i = a
      · subst hia; simp [cpState, σ1, Function.update_apply, hab]; omega
      · by_cases hib : i = b
        · subst hib; simp [cpState, σ1, Function.update_apply, hia]; omega
        · simp [cpState, σ1, Function.update_apply, hia, hib]
    · intro i
      by_cases hib : i = b
      · subst hib; simp [cpState, σ1, Function.update_apply, wrOnes, hab, hba]
      · simp [cpState, σ1, Function.update_apply, hib]
    · rfl
    · rfl

end Loops

/-! ## Rewinds, seeks, appends -/

section Moves
variable {ns nr : ℕ} (cap : ℕ)

theorem bwdLoop (a : Fin (ns + 1)) : ∀ (k : ℕ) (σ : WState ns nr), σ.sh a = k →
    (∀ j, 1 ≤ j → j ≤ k → readTapeBit (σ.st a) j = true) → readTapeBit (σ.st a) 0 = false →
    WExec cap (.whs a (.bwd a)) σ (σ.seth a 0) (3 * k + 1)
  | 0, σ, hk, _, h0 => by
    have h := WExec.whsF (cap := cap) (P := .bwd a) (i := a) (σ := σ) (by simpa [wbit, hk] using h0)
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = a
      · subst hi; simp [hk]
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · rfl
    · rfl
  | k + 1, σ, hk, hrun, h0 => by
    have hb := WExec.bwd (cap := cap) a σ
    have ih := bwdLoop a k (σ.seth a (σ.sh a - 1)) (by simp [hk]) (fun j h1 h2 => by
        simpa using hrun j h1 (by omega)) (by simpa using h0)
    have h := WExec.whsT (cap := cap) (i := a) (P := .bwd a) (by simpa [wbit, hk] using hrun (k + 1) (by omega) le_rfl)
      hb ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = a
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · rfl
    · rfl

/-- **The sentinel rewind**: back to the first cell after the sentinel. -/
def rewU (a : Fin (ns + 1)) : WM ns nr := .seq (.bwd a) (.seq (.whs a (.bwd a)) (.fwd a))

theorem rewU_spec (a : Fin (ns + 1)) (σ : WState ns nr) (d h : ℕ) (hst : σ.st a = U d) (hh : σ.sh a = h)
    (h1 : 1 ≤ h) (h2 : h ≤ d + 1) : WExec cap (rewU a) σ (σ.seth a 1) (3 * h + 2) := by
  have e1 := WExec.bwd (cap := cap) a σ
  have e2 := bwdLoop cap a (h - 1) (σ.seth a (σ.sh a - 1)) (by simp [hh]) (fun j hj1 hj2 => by
      simp only [WState.seth_st, hst]; exact read_U_pos d j hj1 (by omega)) (by simp [hst, read_U_zero])
  have e3 := WExec.fwd (cap := cap) a ((σ.seth a (σ.sh a - 1)).seth a 0)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply wst_eq
  · intro i; by_cases hi : i = a
    · subst hi; simp
    · simp [Function.update_apply, hi]
  · intro i; rfl
  · rfl
  · rfl

theorem fwdLoop (a : Fin (ns + 1)) : ∀ (k : ℕ) (σ : WState ns nr),
    (∀ j < k, readTapeBit (σ.st a) (σ.sh a + j) = true) → readTapeBit (σ.st a) (σ.sh a + k) = false →
    WExec cap (.whs a (.fwd a)) σ (σ.seth a (σ.sh a + k)) (3 * k + 1)
  | 0, σ, _, hstop => by
    have h := WExec.whsF (cap := cap) (P := .fwd a) (i := a) (σ := σ) (by simpa [wbit] using hstop)
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = a
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · rfl
    · rfl
  | k + 1, σ, hrun, hstop => by
    have hf := WExec.fwd (cap := cap) a σ
    have ih := fwdLoop a k (σ.seth a (σ.sh a + 1)) (fun j hj => by
        simpa [show σ.sh a + 1 + j = σ.sh a + (j + 1) by omega] using hrun (j + 1) (by omega))
      (by simpa [show σ.sh a + 1 + k = σ.sh a + (k + 1) by omega] using hstop)
    have h := WExec.whsT (cap := cap) (i := a) (P := .fwd a) (by simpa [wbit] using hrun 0 (by omega)) hf ih
    refine WExec.cast cap h ?_ (by omega)
    apply wst_eq
    · intro i; by_cases hi : i = a
      · subst hi; simp; omega
      · simp [Function.update_apply, hi]
    · intro i; rfl
    · rfl
    · rfl

/-- **The seek**: to the first cell past the ones. -/
def seekEnd (a : Fin (ns + 1)) : WM ns nr := .whs a (.fwd a)

theorem seekEnd_spec (a : Fin (ns + 1)) (σ : WState ns nr) (d h : ℕ) (hst : σ.st a = U d) (hh : σ.sh a = h)
    (h1 : 1 ≤ h) (h2 : h ≤ d + 1) : WExec cap (seekEnd a) σ (σ.seth a (d + 1)) (3 * (d + 1 - h) + 1) := by
  have e := fwdLoop cap a (d + 1 - h) σ (fun j hj => by rw [hst, hh]; exact read_U_pos d _ (by omega) (by omega))
    (by rw [hst, hh]; exact read_U_end d _ (by omega))
  rw [hh, show h + (d + 1 - h) = d + 1 by omega] at e
  exact e

/-- **Append** the ones of `a` at `b`'s head, then rewind `a`. -/
def appS (a b : Fin (ns + 1)) : WM ns nr := .seq (cpLoop a b) (rewU a)

theorem appS_spec (a b : Fin (ns + 1)) (hab : a ≠ b) (σ : WState ns nr) (d e h : ℕ) (ha : σ.st a = U d)
    (hah : σ.sh a = 1) (hb : σ.st b = U e) (hbh : σ.sh b = h) (h1 : 1 ≤ h) (h2 : h ≤ e + 1) :
    WExec cap (appS a b) σ (((σ.sets b (U (max e (h - 1 + d)))).seth b (h + d)).seth a 1) (10 * d + 7) := by
  have hba : b ≠ a := fun x => hab x.symm
  have e1 := cpLoop_spec cap a b hab d σ (fun j hj => by rw [ha, hah]; exact read_U_pos d _ (by omega) (by omega))
    (by rw [ha, hah]; exact read_U_end d _ (by omega))
  have hcs_a : (cpState a b σ d).st a = U d := by simp [cpState, Function.update_of_ne hab, ha]
  have hcs_ah : (cpState a b σ d).sh a = d + 1 := by simp [cpState, hah]; omega
  have e2 := rewU_spec cap a (cpState a b σ d) d (d + 1) hcs_a hcs_ah (by omega) le_rfl
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply wst_eq
  · intro i
    by_cases hi : i = a
    · subst hi; simp [cpState, Function.update_apply]
    · by_cases hib : i = b
      · subst hib; simp [cpState, Function.update_apply, hi, hbh]
      · simp [cpState, Function.update_apply, hi, hib]
  · intro i
    by_cases hib : i = b
    · subst hib; simp [cpState, Function.update_apply, hb, hbh, wrOnes_U d e h h1 h2]
    · simp [cpState, Function.update_apply, hib]
  · rfl
  · rfl

end Moves

/-! ## Doubling, powers of two, repeated appends -/

section Pow
variable {ns nr : ℕ} (cap : ℕ)

/-- **In-place doubling** of `a` (with the helper `b`). -/
def dblS (a b : Fin (ns + 1)) : WM ns nr :=
  .seq (appS a b) (.seq (rewU b) (.seq (seekEnd a) (.seq (appS b a) (rewU a))))

theorem dblS_spec (a b : Fin (ns + 1)) (hab : a ≠ b) (σ : WState ns nr) (d e : ℕ) (ha : σ.st a = U d)
    (hah : σ.sh a = 1) (hb : σ.st b = U e) (hbh : σ.sh b = 1) (hed : e ≤ d) :
    WExec cap (dblS a b) σ ((((σ.sets a (U (2 * d))).sets b (U d)).seth a 1).seth b 1) (32 * d + 29) := by
  have hba : b ≠ a := fun x => hab x.symm
  have s1 := appS_spec cap a b hab σ d e 1 ha hah hb hbh le_rfl (by omega)
  rw [show max e (1 - 1 + d) = d by omega] at s1
  set σ1 := ((σ.sets b (U d)).seth b (1 + d)).seth a 1 with hσ1
  have s2 := rewU_spec cap b σ1 d (1 + d) (by simp [σ1]) (by simp [σ1, Function.update_of_ne hba]) (by omega)
    (by omega)
  set σ2 := σ1.seth b 1 with hσ2
  have s3 := seekEnd_spec cap a σ2 d 1 (by simp [σ2, σ1, Function.update_of_ne hab, ha])
    (by simp [σ2, σ1, Function.update_apply, hab])
    le_rfl (by omega)
  set σ3 := σ2.seth a (d + 1) with hσ3
  have s4 := appS_spec cap b a hba σ3 d d (d + 1) (by simp [σ3, σ2, σ1]) (by simp [σ3, σ2, σ1,
    Function.update_of_ne hba]) (by simp [σ3, σ2, σ1, Function.update_of_ne hab, ha]) (by simp [σ3]) (by omega)
    le_rfl
  rw [show max d (d + 1 - 1 + d) = 2 * d by omega] at s4
  set σ4 := ((σ3.sets a (U (2 * d))).seth a (d + 1 + d)).seth b 1 with hσ4
  have s5 := rewU_spec cap a σ4 (2 * d) (d + 1 + d) (by simp [σ4]) (by simp [σ4, Function.update_of_ne hab])
    (by omega) (by omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (by omega)
  apply wst_eq
  · intro i
    by_cases hi : i = a
    · subst hi; simp [σ4, σ3, σ2, σ1, Function.update_apply, hab]
    · by_cases hib : i = b
      · subst hib; simp [σ4, σ3, σ2, σ1, Function.update_apply, hi]
      · simp [σ4, σ3, σ2, σ1, Function.update_apply, hi, hib]
  · intro i
    by_cases hi : i = a
    · subst hi; simp [σ4, σ3, σ2, σ1, Function.update_apply, hab]
    · by_cases hib : i = b
      · subst hib; simp [σ4, σ3, σ2, σ1, Function.update_apply, hi]
      · simp [σ4, σ3, σ2, σ1, Function.update_apply, hi, hib]
  · rfl
  · rfl

/-- **`2^m` doublings**: `m` rounds of `dblS`, counted down in the register `rM`. -/
def powS (rM : Fin nr) (a b : Fin (ns + 1)) : WM ns nr := .whr rM (.seq (.dec rM) (dblS a b))

theorem powS_spec (rM : Fin nr) (a b : Fin (ns + 1)) (hab : a ≠ b) : ∀ (m : ℕ) (σ : WState ns nr) (d e : ℕ),
    σ.val rM = m → m ≤ cap → σ.st a = U d → σ.sh a = 1 → σ.st b = U e → σ.sh b = 1 → e ≤ d →
    ∃ e' : ℕ, WExec cap (powS rM a b) σ
      (((((σ.sets a (U (d * 2 ^ m))).sets b (U e')).seth a 1).seth b 1).setv rM 0)
      (32 * (d * 2 ^ m) + 33 * m + 1 - 32 * d)
  | 0, σ, d, e, hm, _, ha, hah, hb, hbh, _ => by
    refine ⟨e, ?_⟩
    have h := WExec.whrF (cap := cap) (P := .seq (.dec rM) (dblS a b)) (r := rM) (σ := σ) hm
    refine WExec.cast cap h ?_ (by simp)
    apply wst_eq
    · intro i
      by_cases hi : i = a
      · subst hi; simp [Function.update_apply, hah, hab]
      · by_cases hib : i = b
        · subst hib; simp [Function.update_apply, hi, hbh]
        · simp [Function.update_apply, hi, hib]
    · intro i
      by_cases hi : i = a
      · subst hi; simp [Function.update_apply, ha, hab]
      · by_cases hib : i = b
        · subst hib; simp [Function.update_apply, hi, hb]
        · simp [Function.update_apply, hi, hib]
    · funext r; by_cases hr : r = rM
      · subst hr; simp [hm]
      · simp [Function.update_apply, hr]
    · rfl
  | m + 1, σ, d, e, hm, hmc, ha, hah, hb, hbh, hed => by
    have hdec := WExec.dec (cap := cap) rM σ (by omega)
    set σ0 := σ.setv rM (σ.val rM - 1) with hσ0
    have hd := dblS_spec cap a b hab σ0 d e (by simp [σ0, ha]) (by simp [σ0, hah]) (by simp [σ0, hb])
      (by simp [σ0, hbh]) hed
    set σ1 := (((σ0.sets a (U (2 * d))).sets b (U d)).seth a 1).seth b 1 with hσ1
    have hab' : b ≠ a := fun x => hab x.symm
    obtain ⟨e', ih⟩ := powS_spec rM a b hab m σ1 (2 * d) d (by simp [σ1, σ0, hm]) (by omega)
      (by simp [σ1, Function.update_of_ne hab]) (by simp [σ1, Function.update_of_ne hab])
      (by simp [σ1]) (by simp [σ1]) (by omega)
    refine ⟨e', ?_⟩
    have h := WExec.whrT (cap := cap) (r := rM) (by omega) (WExec.seq hdec hd) ih
    have hp : d * 2 ^ (m + 1) = 2 * d * 2 ^ m := by ring
    have hle : 2 * d ≤ 2 * d * 2 ^ m := Nat.le_mul_of_pos_right _ (by positivity)
    refine WExec.cast cap h ?_ (by rw [hp]; omega)
    apply wst_eq
    · intro i
      by_cases hi : i = a
      · subst hi; simp [σ1, σ0, Function.update_apply, hab]
      · by_cases hib : i = b
        · subst hib; simp [σ1, σ0, Function.update_apply, hi]
        · simp [σ1, σ0, Function.update_apply, hi, hib]
    · intro i
      by_cases hi : i = a
      · subst hi; simp [σ1, σ0, Function.update_apply, hab, hp]
      · by_cases hib : i = b
        · subst hib; simp [σ1, σ0, Function.update_apply, hi]
        · simp [σ1, σ0, Function.update_apply, hi, hib]
    · funext r; by_cases hr : r = rM
      · subst hr; simp [σ1, σ0]
      · simp [σ1, σ0, Function.update_apply, hr]
    · rfl

/-- **`C` appended copies** of `a` at `c`, counted down in `rC`. -/
def repS (rC : Fin nr) (a c : Fin (ns + 1)) : WM ns nr := .whr rC (.seq (.dec rC) (appS a c))

theorem repS_spec (rC : Fin nr) (a c : Fin (ns + 1)) (hac : a ≠ c) (d : ℕ) : ∀ (C : ℕ) (σ : WState ns nr) (e : ℕ),
    σ.val rC = C → C ≤ cap → σ.st a = U d → σ.sh a = 1 → σ.st c = U e → σ.sh c = e + 1 →
    WExec cap (repS rC a c) σ (((σ.sets c (U (e + C * d))).seth c (e + C * d + 1)).setv rC 0) (C * (10 * d + 11) + 1)
  | 0, σ, e, hC, _, ha, hah, hc, hch => by
    have h := WExec.whrF (cap := cap) (P := .seq (.dec rC) (appS a c)) (r := rC) (σ := σ) hC
    refine WExec.cast cap h ?_ (by simp)
    apply wst_eq
    · intro i; by_cases hi : i = c
      · subst hi; simp [hch]
      · simp [Function.update_apply, hi]
    · intro i; by_cases hi : i = c
      · subst hi; simp [hc]
      · simp [Function.update_apply, hi]
    · funext r; by_cases hr : r = rC
      · subst hr; simp [hC]
      · simp [Function.update_apply, hr]
    · rfl
  | C + 1, σ, e, hC, hCc, ha, hah, hc, hch => by
    have hca : c ≠ a := fun x => hac x.symm
    have hdec := WExec.dec (cap := cap) rC σ (by omega)
    set σ0 := σ.setv rC (σ.val rC - 1) with hσ0
    have hap := appS_spec cap a c hac σ0 d e (e + 1) (by simp [σ0, ha]) (by simp [σ0, hah]) (by simp [σ0, hc])
      (by simp [σ0, hch]) (by omega) le_rfl
    rw [show max e (e + 1 - 1 + d) = e + d by omega] at hap
    set σ1 := ((σ0.sets c (U (e + d))).seth c (e + 1 + d)).seth a 1 with hσ1
    have ih := repS_spec rC a c hac d C σ1 (e + d) (by simp [σ1, σ0, hC]) (by omega)
      (by simp [σ1, Function.update_of_ne hac, σ0, ha]) (by simp [σ1]) (by simp [σ1])
      (by simp [σ1, Function.update_of_ne hca]; omega)
    have h := WExec.whrT (cap := cap) (r := rC) (by omega) (WExec.seq hdec hap) ih
    refine WExec.cast cap h ?_ (by ring_nf; omega)
    apply wst_eq
    · intro i
      by_cases hi : i = c
      · subst hi; simp [σ1, σ0, Function.update_apply, hca]; ring
      · by_cases hia : i = a
        · subst hia; simp [σ1, σ0, Function.update_apply, hi, hah]
        · simp [σ1, σ0, Function.update_apply, hi, hia]
    · intro i
      by_cases hi : i = c
      · subst hi; simp [σ1, σ0, Function.update_apply]; ring_nf
      · simp [σ1, σ0, Function.update_apply, hi]
    · funext r; by_cases hr : r = rC
      · subst hr; simp [σ1, σ0]
      · simp [σ1, σ0, Function.update_apply, hr]
    · rfl

end Pow

/-! ## The register phase: `m = q − ⌊k/4⌋`, `c = (q+1)^A·K`, `f = (q+6)·1000` -/

section Regs
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryPow NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
variable {ns nr : ℕ} (cap : ℕ)

theorem div1 (R : Fin 9 ↪ Fin nr) (a b : ℕ) (σ : WState ns nr) (ha0 : σ.val (R 0) = a) (hb0 : σ.val (R 1) = b)
    (hq0 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (h5 : σ.val (R 5) = 0)
    (h6 : σ.val (R 6) = 0) (h7 : σ.val (R 7) = 0) (hb1 : 1 ≤ b) (hcap : a + b ≤ cap) :
    WExec cap (divW R) σ ((σ.setv (R 0) (a % b)).setv (R 2) (a / b)) (2 * UnaryPow.sq cap) := by
  have h := divW_spec cap R σ (by rw [hb0]; exact hb1) h3 h4 h5 h6 h7 (by rw [ha0]; omega) (by rw [hb0]; omega)
    (by rw [hq0, ha0]; omega) (by omega)
  rw [ha0, hb0, hq0, Nat.zero_add] at h
  refine WExec.mono h ?_
  unfold UnaryPow.sq
  have h1 : a + 2 ≤ cap + 2 := by omega
  have h2 : 90 * a + 90 * b + 60 ≤ 90 * (cap + 2) := by omega
  calc (a + 2) * (90 * a + 90 * b + 60) ≤ (cap + 2) * (90 * (cap + 2)) := Nat.mul_le_mul h1 h2
    _ ≤ 2 * (200 * (cap + 2) * (cap + 2)) := by nlinarith

theorem sub1 (R : Fin 4 ↪ Fin nr) (a b : ℕ) (σ : WState ns nr) (ha0 : σ.val (R 0) = a) (hb0 : σ.val (R 1) = b)
    (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (ha : a ≤ cap) (hb : b ≤ cap) :
    WExec cap (subW R) σ (σ.setv (R 0) (a - b)) (UnaryPow.sq cap) := by
  have h := subW_spec cap R σ h2 h3 (by rw [ha0]; exact ha) (by rw [hb0]; exact hb)
  rw [ha0, hb0] at h
  have hs := lin_le_sq cap
  exact WExec.mono h (by omega)

theorem incNv (r : Fin nr) (v c : ℕ) (σ : WState ns nr) (hr : σ.val r = v) (hc : v + c ≤ cap) (hc6 : c ≤ 100) :
    WExec cap (StarNums.incN r c) σ (σ.setv r (v + c)) (UnaryPow.sq cap) := by
  have h := StarNums.incN_spec cap r c σ (by rw [hr]; exact hc)
  rw [hr] at h
  have hs := sq_ge cap
  exact WExec.mono h (by omega)

theorem rs_le' (P : Shared.StarParams) : P.r * P.s ≤ P.n := by
  have h2s : 2 ^ P.s ≤ P.n / P.r + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have hslt : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  have hrq : P.r * (P.n / P.r) ≤ P.n := Nat.mul_div_le P.n P.r
  exact le_trans (Nat.mul_le_mul_left _ (by omega)) hrq

/-- The star parameters at `n = q`, `r = rowBr c_r q`. -/
def starP (cr q : ℕ) (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) : Shared.StarParams :=
  ⟨q, Ledger.rowBr cr q, Ledger.rowBr_even cr q, Ledger.two_le_rowBr hcr q, h4⟩

theorem starP_k (cr q : ℕ) (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) :
    (starP cr q hcr h4).k = Cost.starWidth (Ledger.rowBr cr q) q := rfl

theorem star1 (cr q : ℕ) (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) (S : Fin 20 ↪ Fin nr) (σ : WState ns nr)
    (hn : σ.val (S 0) = q) (hz : ∀ i : Fin 20, i ≠ 0 → σ.val (S i) = 0) (hcap : 4 * (q + 3) + 2 * cr + 20 ≤ cap) :
    WExec cap (StarNums.starNumsM cr 0 S) σ (StarNums.starOut σ S (starP cr q hcr h4) 0) (3 * UnaryPow.sq cap) := by
  have h := StarNums.starNums_spec cap cr 0 S (starP cr q hcr h4) rfl σ hn hz (by simp [starP]; omega)
  refine WExec.mono h ?_
  unfold StarNums.starCost UnaryPow.sq
  simp only [starP]
  nlinarith

def SB : Fin 20 ↪ Fin 48 := ⟨![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19], by decide⟩
def dvE : Fin 9 ↪ Fin 48 := ⟨![21, 22, 23, 24, 25, 26, 27, 28, 29], by decide⟩
def sbE : Fin 4 ↪ Fin 48 := ⟨![30, 23, 31, 32], by decide⟩
def pwE : Fin 5 ↪ Fin 48 := ⟨![33, 34, 35, 36, 37], by decide⟩
def mcE : Fin 5 ↪ Fin 48 := ⟨![34, 38, 39, 35, 36], by decide⟩
def mfE : Fin 5 ↪ Fin 48 := ⟨![40, 41, 42, 35, 36], by decide⟩
@[simp] theorem SB_apply (i : Fin 20) :
    SB i = ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] i := rfl
@[simp] theorem dvE_apply (i : Fin 9) : dvE i = ![21, 22, 23, 24, 25, 26, 27, 28, 29] i := rfl
@[simp] theorem sbE_apply (i : Fin 4) : sbE i = ![30, 23, 31, 32] i := rfl
@[simp] theorem pwE_apply (i : Fin 5) : pwE i = ![33, 34, 35, 36, 37] i := rfl
@[simp] theorem mcE_apply (i : Fin 5) : mcE i = ![34, 38, 39, 35, 36] i := rfl
@[simp] theorem mfE_apply (i : Fin 5) : mfE i = ![40, 41, 42, 35, 36] i := rfl

theorem SB_zero (i : Fin 20) (hi : i ≠ 0) : SB i ≠ 0 := by
  fin_cases i <;> simp_all

theorem SB_val (j : Fin 20) : (SB j).val = j.val := by fin_cases j <;> rfl

/-- The star block's exit leaves every register off the block's outputs. -/
theorem starOut_off (G : Fin 48 ↪ Fin nr) (σ : WState ns nr) (P : Shared.StarParams) (fe : ℕ) (r : Fin nr)
    (hr : ∀ j : Fin 20, r ≠ G (SB j)) : (StarNums.starOut σ (SB.trans G) P fe).val r = σ.val r := by
  have hupd : ∀ (f : Fin nr → ℕ) (j : Fin 20) (v : ℕ), Function.update f (G (SB j)) v r = f r :=
    fun f j v => Function.update_of_ne (hr j) v f
  simp only [StarNums.starOut, WState.setv_val, Function.Embedding.trans_apply, hupd]

/-- Phase 1: the star numbers, then `k/4`. -/
def P1 (cr : ℕ) (G : Fin 48 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.starNumsM cr 0 (SB.trans G)) (.seq (FinalPass.Hash4.wcopyR (G 9) (G 21) (G 43))
  (.seq (StarNums.incN (G 22) 4) (divW (dvE.trans G))))

noncomputable def p1Out (cr : ℕ) (G : Fin 48 ↪ Fin nr) (σ : WState ns nr) (q : ℕ) (hcr : 1 ≤ cr)
    (h4 : 4 * Ledger.rowBr cr q ≤ q) : WState ns nr :=
  ((((StarNums.starOut σ (SB.trans G) (starP cr q hcr h4) 0).setv (G 21) (Cost.starWidth (Ledger.rowBr cr q) q)).setv
    (G 22) 4).setv (G 21) (Cost.starWidth (Ledger.rowBr cr q) q % 4)).setv (G 23) (Cost.starWidth (Ledger.rowBr cr q) q / 4)

theorem G_ne_SB (G : Fin 48 ↪ Fin nr) (i : Fin 48) (hi : 20 ≤ i.val) (j : Fin 20) : G i ≠ G (SB j) := by
  intro h
  have := congrArg Fin.val (G.injective h)
  rw [SB_val] at this
  omega

theorem P1_spec (cr : ℕ) (G : Fin 48 ↪ Fin nr) (σ : WState ns nr) (q : ℕ) (hq : σ.val (G 0) = q)
    (hz : ∀ i : Fin 48, i ≠ 0 → σ.val (G i) = 0) (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q)
    (hcap : 4 * (q + 3) + 2 * cr + 20 ≤ cap) :
    WExec cap (P1 cr G) σ (p1Out cr G σ q hcr h4) (10 * UnaryPow.sq cap) := by
  have hk : Cost.starWidth (Ledger.rowBr cr q) q ≤ q := rs_le' (starP cr q hcr h4)
  have hs := sq_ge cap
  set k := Cost.starWidth (Ledger.rowBr cr q) q with hkdef
  set σ1 := StarNums.starOut σ (SB.trans G) (starP cr q hcr h4) 0 with hσ1
  have z1 : ∀ i : Fin 48, 20 ≤ i.val → σ1.val (G i) = σ.val (G i) := fun i hi =>
    starOut_off G σ _ 0 (G i) (fun j => G_ne_SB G i hi j)
  have s1 := star1 cap cr q hcr h4 (SB.trans G) σ (by simpa using hq) (fun i hi => by
    simp only [Function.Embedding.trans_apply]; exact hz _ (SB_zero i hi)) (by omega)
  have k1 : σ1.val (G 9) = k := by
    simp only [σ1, StarNums.starOut, WState.setv_val, Function.Embedding.trans_apply, SB_apply]
    simp [Function.update_apply, starP_k, hkdef]
  have s2 := copy1 cap (G 9) (G 21) (G 43) (by simp) (by simp) (by simp) k σ1 k1
    (by rw [z1 21 (by decide)]; exact hz 21 (by decide)) (by rw [z1 43 (by decide)]; exact hz 43 (by decide))
    (by omega)
  have s3 := incN0 cap (G 22) 4 (σ1.setv (G 21) k) (by
    rw [WState.setv_val, Function.update_of_ne (G.injective.ne (by decide)), z1 22 (by decide)]
    exact hz 22 (by decide)) (by omega)
  have s4 := div1 cap (dvE.trans G) k 4 ((σ1.setv (G 21) k).setv (G 22) 4) (by simp) (by simp)
    (by simp [Function.update_apply, z1, hz]) (by simp [Function.update_apply, z1, hz])
    (by simp [Function.update_apply, z1, hz]) (by simp [Function.update_apply, z1, hz])
    (by simp [Function.update_apply, z1, hz]) (by simp [Function.update_apply, z1, hz]) (by norm_num) (by omega)
  simp only [Function.Embedding.trans_apply, dvE_apply, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons] at s4
  unfold P1
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega)

/-- Phase 2: `m = q − k/4` in `G 30`. -/
def P2 (G : Fin 48 ↪ Fin nr) : WM ns nr := .seq (FinalPass.Hash4.wcopyR (G 0) (G 30) (G 43)) (subW (sbE.trans G))

theorem P2_spec (G : Fin 48 ↪ Fin nr) (σ : WState ns nr) (q k4 : ℕ) (hq : σ.val (G 0) = q) (hk : σ.val (G 23) = k4)
    (h30 : σ.val (G 30) = 0) (h31 : σ.val (G 31) = 0) (h32 : σ.val (G 32) = 0) (h43 : σ.val (G 43) = 0)
    (hkq : k4 ≤ q) (hcap : q ≤ cap) :
    WExec cap (P2 G) σ ((σ.setv (G 30) q).setv (G 30) (q - k4)) (3 * UnaryPow.sq cap) := by
  have hs := sq_ge cap
  have s1 := copy1 cap (G 0) (G 30) (G 43) (by simp) (by simp) (by simp) q σ hq h30 h43 hcap
  have s2 := sub1 cap (sbE.trans G) q k4 (σ.setv (G 30) q) (by simp) (by simp [Function.update_apply, hk])
    (by simp [Function.update_apply, h31]) (by simp [Function.update_apply, h32]) (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, sbE_apply, Matrix.cons_val_zero] at s2
  unfold P2
  exact WExec.mono (WExec.seq s1 s2) (by omega)

/-- Phase 3: `c = (q+1)^A·K` in `G 39`. -/
def P3 (K A : ℕ) (G : Fin 48 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (G 0) (G 33) (G 43)) (.seq (.inc (G 33))
  (.seq (powConstW (pwE.trans G) A) (.seq (StarNums.incN (G 38) K) (mulAddW (mcE.trans G)))))

theorem P3_spec (K A : ℕ) (G : Fin 48 ↪ Fin nr) (σ : WState ns nr) (q : ℕ) (hq : σ.val (G 0) = q)
    (hz : ∀ i : Fin 48, 33 ≤ i.val → i.val ≤ 39 → σ.val (G i) = 0) (h43 : σ.val (G 43) = 0) (hK : 1 ≤ K)
    (hcap : K * (q + 1) ^ A + q + 2 ≤ cap) :
    WExec cap (P3 K A G) σ (((((σ.setv (G 33) q).setv (G 33) (q + 1)).setv (G 34) ((q + 1) ^ A)).setv (G 38) K).setv
      (G 39) (0 + (q + 1) ^ A * K)) ((4 * A + 12) * UnaryPow.sq cap) := by
  have hX : (q + 1) ^ A ≤ K * (q + 1) ^ A := Nat.le_mul_of_pos_left _ (by omega)
  have hKX : K ≤ K * (q + 1) ^ A := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
  have hXK : (q + 1) ^ A * K ≤ cap := by rw [Nat.mul_comm]; omega
  have hc1 : 1 ≤ cap := by omega
  have hs := sq_ge cap
  have z : ∀ i : Fin 48, 33 ≤ i.val → i.val ≤ 39 → σ.val (G i) = 0 := hz
  have s1 := copy1 cap (G 0) (G 33) (G 43) (by simp) (by simp) (by simp) q σ hq (z 33 (by decide) (by decide)) h43
    (by omega)
  have s2 := inc1 cap (G 33) q (σ.setv (G 33) q) (by simp) (by omega)
  have s3 := pow1 cap (pwE.trans G) (q + 1) A ((σ.setv (G 33) q).setv (G 33) (q + 1)) (by simp)
    (by simp [Function.update_apply, z 34 (by decide) (by decide)])
    (by simp [Function.update_apply, z 35 (by decide) (by decide)])
    (by simp [Function.update_apply, z 36 (by decide) (by decide)])
    (by simp [Function.update_apply, z 37 (by decide) (by decide)]) hc1 (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, pwE_apply, Matrix.cons_val_one, Matrix.head_cons] at s3
  have s4 := incN0 cap (G 38) K (((σ.setv (G 33) q).setv (G 33) (q + 1)).setv (G 34) ((q + 1) ^ A))
    (by simp [Function.update_apply, z 38 (by decide) (by decide)]) (by omega)
  have s5 := mulAdd1 cap (mcE.trans G) ((q + 1) ^ A) K 0
    ((((σ.setv (G 33) q).setv (G 33) (q + 1)).setv (G 34) ((q + 1) ^ A)).setv (G 38) K) (by simp) (by simp)
    (by simp [Function.update_apply, z 39 (by decide) (by decide)])
    (by simp [Function.update_apply, z 35 (by decide) (by decide)])
    (by simp [Function.update_apply, z 36 (by decide) (by decide)]) (by omega) (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, mcE_apply, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at s5
  unfold P3
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_
  have e : (A + 1) * (4 * UnaryPow.sq cap) = 4 * A * UnaryPow.sq cap + 4 * UnaryPow.sq cap := by ring
  have e2 : (4 * A + 12) * UnaryPow.sq cap = 4 * A * UnaryPow.sq cap + 12 * UnaryPow.sq cap := by ring
  omega

/-- Phase 4: `f = (q+6)·1000` in `G 42`. -/
def P4 (G : Fin 48 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (G 0) (G 40) (G 43)) (.seq (StarNums.incN (G 40) 6)
  (.seq (StarNums.incN (G 41) 1000) (mulAddW (mfE.trans G))))

theorem P4_spec (G : Fin 48 ↪ Fin nr) (σ : WState ns nr) (q : ℕ) (hq : σ.val (G 0) = q)
    (hz : ∀ i : Fin 48, 40 ≤ i.val → i.val ≤ 43 → σ.val (G i) = 0) (h35 : σ.val (G 35) = 0) (h36 : σ.val (G 36) = 0)
    (hcap : 1000 * (q + 7) ≤ cap) :
    WExec cap (P4 G) σ ((((σ.setv (G 40) q).setv (G 40) (q + 6)).setv (G 41) 1000).setv (G 42) (0 + (q + 6) * 1000))
      (8 * UnaryPow.sq cap) := by
  have hs := sq_ge cap
  have s1 := copy1 cap (G 0) (G 40) (G 43) (by simp) (by simp) (by simp) q σ hq (hz 40 (by decide) (by decide))
    (hz 43 (by decide) (by decide)) (by omega)
  have s2 := incNv cap (G 40) q 6 (σ.setv (G 40) q) (by simp) (by omega) (by norm_num)
  have s3 := incN0 cap (G 41) 1000 ((σ.setv (G 40) q).setv (G 40) (q + 6))
    (by simp [Function.update_apply, hz 41 (by decide) (by decide)]) (by omega)
  have s4 := mulAdd1 cap (mfE.trans G) (q + 6) 1000 0 (((σ.setv (G 40) q).setv (G 40) (q + 6)).setv (G 41) 1000)
    (by simp) (by simp) (by simp [Function.update_apply, hz 42 (by decide) (by decide)])
    (by simp [Function.update_apply, h35]) (by simp [Function.update_apply, h36]) (by omega) (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, mfE_apply, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at s4
  unfold P4
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega)

/-- **The register phase.** -/
def capRegs (cr K A : ℕ) (G : Fin 48 ↪ Fin nr) : WM ns nr := .seq (P1 cr G) (.seq (P2 G) (.seq (P3 K A G) (P4 G)))

theorem upd_ne {α : Type} [DecidableEq α] (f : α → ℕ) {a b : α} (v : ℕ) (h : b ≠ a) : Function.update f a v b = f b :=
  Function.update_of_ne h v f

theorem capRegs_spec (cr K A : ℕ) (G : Fin 48 ↪ Fin nr) (σ : WState ns nr) (q : ℕ) (hq : σ.val (G 0) = q)
    (hz : ∀ i : Fin 48, i ≠ 0 → σ.val (G i) = 0) (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) (hK : 1 ≤ K)
    (hcap : K * (q + 1) ^ A + 1000 * (q + 7) + 2 * cr + 100 ≤ cap) :
    ∃ τ : WState ns nr, WExec cap (capRegs cr K A G) σ τ ((4 * A + 40) * UnaryPow.sq cap) ∧
      τ.val (G 30) = q - Cost.starWidth (Ledger.rowBr cr q) q / 4 ∧ τ.val (G 39) = (q + 1) ^ A * K ∧
      τ.val (G 42) = (q + 6) * 1000 ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      ∀ r, (∀ i, G i ≠ r) → τ.val r = σ.val r := by
  have hk : Cost.starWidth (Ledger.rowBr cr q) q ≤ q := rs_le' (starP cr q hcr h4)
  have hs := sq_ge cap
  set k := Cost.starWidth (Ledger.rowBr cr q) q with hkdef
  have e1 := P1_spec cap cr G σ q hq hz hcr h4 (by omega)
  set σ1 := p1Out cr G σ q hcr h4 with hσ1
  have hne : ∀ i j : Fin 48, i ≠ j → G i ≠ G j := fun i j h => G.injective.ne h
  have v1 : ∀ i : Fin 48, 24 ≤ i.val → σ1.val (G i) = σ.val (G i) := by
    intro i hi
    simp only [σ1, p1Out, WState.setv_val]
    rw [upd_ne _ _ (hne i 23 (by intro h; subst h; simp at hi)), upd_ne _ _ (hne i 21 (by intro h; subst h; simp at hi)),
      upd_ne _ _ (hne i 22 (by intro h; subst h; simp at hi)), upd_ne _ _ (hne i 21 (by intro h; subst h; simp at hi))]
    exact starOut_off G σ _ 0 (G i) (fun j => G_ne_SB G i (by omega) j)
  have q1 : σ1.val (G 0) = q := by
    simp only [σ1, p1Out, WState.setv_val]
    rw [upd_ne _ _ (hne 0 23 (by decide)), upd_ne _ _ (hne 0 21 (by decide)), upd_ne _ _ (hne 0 22 (by decide)),
      upd_ne _ _ (hne 0 21 (by decide))]
    have hS : ∀ f : Fin nr → ℕ, ∀ j : Fin 20, ∀ v : ℕ, j ≠ 0 → Function.update f (G (SB j)) v (G 0) = f (G 0) := by
      intro f j v hj
      refine upd_ne _ _ (fun h => hj ?_)
      have := congrArg Fin.val (G.injective h)
      rw [SB_val] at this
      exact Fin.ext (by simpa using this.symm)
    simp only [StarNums.starOut, WState.setv_val, Function.Embedding.trans_apply]
    rw [hS _ 10 _ (by decide), hS _ 9 _ (by decide), hS _ 8 _ (by decide), hS _ 7 _ (by decide), hS _ 6 _ (by decide),
      hS _ 5 _ (by decide), hS _ 4 _ (by decide), hS _ 3 _ (by decide), hS _ 1 _ (by decide)]
    exact hq
  have k1 : σ1.val (G 23) = k / 4 := by simp only [σ1, p1Out, WState.setv_val, Function.update_self, hkdef]
  have e2 := P2_spec cap G σ1 q (k / 4) q1 k1
    (by rw [v1 30 (by decide)]; exact hz 30 (by decide)) (by rw [v1 31 (by decide)]; exact hz 31 (by decide))
    (by rw [v1 32 (by decide)]; exact hz 32 (by decide)) (by rw [v1 43 (by decide)]; exact hz 43 (by decide))
    (by omega) (by omega)
  set σ2 := (σ1.setv (G 30) q).setv (G 30) (q - k / 4) with hσ2
  have v2 : ∀ i : Fin 48, 24 ≤ i.val → i ≠ 30 → σ2.val (G i) = 0 := by
    intro i hi hi30
    simp only [σ2, WState.setv_val]
    rw [upd_ne _ _ (hne i 30 hi30), upd_ne _ _ (hne i 30 hi30), v1 i hi]
    exact hz i (by intro h; subst h; simp at hi)
  have q2 : σ2.val (G 0) = q := by
    simp only [σ2, WState.setv_val]
    rw [upd_ne _ _ (hne 0 30 (by decide)), upd_ne _ _ (hne 0 30 (by decide))]; exact q1
  have e3 := P3_spec cap K A G σ2 q q2 (fun i h1 h2 => v2 i (by omega) (by intro h; subst h; simp at h1))
    (v2 43 (by decide) (by decide)) hK (by omega)
  set σ3 := ((((σ2.setv (G 33) q).setv (G 33) (q + 1)).setv (G 34) ((q + 1) ^ A)).setv (G 38) K).setv
    (G 39) (0 + (q + 1) ^ A * K) with hσ3
  have p3 : ∀ i : Fin 48, i ≠ 33 → i ≠ 34 → i ≠ 38 → i ≠ 39 → σ3.val (G i) = σ2.val (G i) := by
    intro i a1 a2 a3 a4
    simp only [σ3, WState.setv_val]
    rw [upd_ne _ _ (hne i 39 a4), upd_ne _ _ (hne i 38 a3), upd_ne _ _ (hne i 34 a2), upd_ne _ _ (hne i 33 a1),
      upd_ne _ _ (hne i 33 a1)]
  have e4 := P4_spec cap G σ3 q (by rw [p3 0 (by decide) (by decide) (by decide) (by decide)]; exact q2)
    (fun i h1 _ => by
      rw [p3 i (by intro h; subst h; simp at h1) (by intro h; subst h; simp at h1) (by intro h; subst h; simp at h1)
        (by intro h; subst h; simp at h1)]
      exact v2 i (by omega) (by intro h; subst h; simp at h1))
    (by rw [p3 35 (by decide) (by decide) (by decide) (by decide)]; exact v2 35 (by decide) (by decide))
    (by rw [p3 36 (by decide) (by decide) (by decide) (by decide)]; exact v2 36 (by decide) (by decide)) (by omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (4 * A + 40) * UnaryPow.sq cap = 10 * UnaryPow.sq cap + 3 * UnaryPow.sq cap +
        (4 * A + 12) * UnaryPow.sq cap + 8 * UnaryPow.sq cap + 7 * UnaryPow.sq cap := by ring
    omega
  · simp only [WState.setv_val]
    rw [upd_ne _ _ (hne 30 42 (by decide)), upd_ne _ _ (hne 30 41 (by decide)), upd_ne _ _ (hne 30 40 (by decide)),
      upd_ne _ _ (hne 30 40 (by decide)), p3 30 (by decide) (by decide) (by decide) (by decide)]
    simp only [σ2, WState.setv_val, Function.update_self]
  · simp only [WState.setv_val]
    rw [upd_ne _ _ (hne 39 42 (by decide)), upd_ne _ _ (hne 39 41 (by decide)), upd_ne _ _ (hne 39 40 (by decide)),
      upd_ne _ _ (hne 39 40 (by decide))]
    simp only [σ3, WState.setv_val, Function.update_self, Nat.zero_add]
  · simp only [WState.setv_val, Function.update_self, Nat.zero_add]
  · simp only [σ3, σ2, σ1, p1Out, StarNums.starOut, WState.setv_st]
  · simp only [σ3, σ2, σ1, p1Out, StarNums.starOut, WState.setv_sh]
  · simp only [σ3, σ2, σ1, p1Out, StarNums.starOut, WState.setv_cell]
  · intro r hr
    have hr' : ∀ i, r ≠ G i := fun i h => hr i h.symm
    have hupd : ∀ (f : Fin nr → ℕ) (i : Fin 48) (v : ℕ), Function.update f (G i) v r = f r :=
      fun f i v => upd_ne f v (hr' i)
    have hupd2 : ∀ (f : Fin nr → ℕ) (j : Fin 20) (v : ℕ), Function.update f ((SB.trans G) j) v r = f r :=
      fun f j v => upd_ne f v (hr' _)
    simp only [WState.setv_val, σ3, σ2, σ1, p1Out, StarNums.starOut, hupd, hupd2]

end Regs

/-! ## The capacity writer -/

section Writer
open NearCubicWires.WireExponent3_5.PrimAsm
variable {ns nr : ℕ} (cap : ℕ)

/-- A fresh unary stream `U 0` (the sentinel), head after it. -/
def initU (a : Fin (ns + 1)) : WM ns nr := .seq (.wr a false) (.fwd a)

theorem initU_spec (a : Fin (ns + 1)) (σ : WState ns nr) (h0 : σ.st a = []) (hh : σ.sh a = 0) :
    WExec cap (initU a) σ ((σ.sets a (U 0)).seth a 1) 3 := by
  have e1 := WExec.wr (cap := cap) a false σ
  have e2 := WExec.fwd (cap := cap) a (σ.sets a (writeTapeBit (σ.st a) (σ.sh a) false))
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply wst_eq
  · intro i; by_cases hi : i = a
    · subst hi; simp [hh]
    · simp [Function.update_apply, hi]
  · intro i; by_cases hi : i = a
    · subst hi; simp [h0, hh, writeTapeBit, U]
    · simp [Function.update_apply, hi]
  · rfl
  · rfl

/-- The seed `U 1`: sentinel, one `1`, head on it. -/
def initU1 (a : Fin (ns + 1)) : WM ns nr := .seq (initU a) (.wr a true)

theorem initU1_spec (a : Fin (ns + 1)) (σ : WState ns nr) (h0 : σ.st a = []) (hh : σ.sh a = 0) :
    WExec cap (initU1 a) σ ((σ.sets a (U 1)).seth a 1) 5 := by
  have e1 := initU_spec cap a σ h0 hh
  have e2 := WExec.wr (cap := cap) a true ((σ.sets a (U 0)).seth a 1)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply wst_eq
  · intro i; by_cases hi : i = a
    · subst hi; simp
    · simp [Function.update_apply, hi]
  · intro i; by_cases hi : i = a
    · subst hi; simp [writeTapeBit, U]
    · simp [Function.update_apply, hi]
  · rfl
  · rfl

/-- **The capacity writer**: the register phase, the four streams, `2^m` by doubling, `c` copies, `f` copies. -/
def capW (cr K A : ℕ) (G : Fin 48 ↪ Fin nr) (sA sB sC sD : Fin (ns + 1)) : WM ns nr :=
  .seq (capRegs cr K A G) (.seq (initU1 sA) (.seq (initU sB) (.seq (initU sC) (.seq (initU sD)
  (.seq (powS (G 30) sA sB) (.seq (repS (G 39) sA sC) (.seq (rewU sC) (.seq (repS (G 42) sC sD) (rewU sD)))))))))

/-- The writer's cost. -/
def capWCost (A m c f : ℕ) (sqc : ℕ) : ℕ :=
  (4 * A + 40) * sqc + 1 + (5 + 1 + (3 + 1 + (3 + 1 + (3 + 1 + ((32 * (1 * 2 ^ m) + 33 * m + 1 - 32 * 1) + 1 +
    ((c * (10 * (1 * 2 ^ m) + 11) + 1) + 1 + ((3 * (0 + c * (1 * 2 ^ m) + 1) + 2) + 1 +
    ((f * (10 * (0 + c * (1 * 2 ^ m)) + 11) + 1) + 1 + (3 * (0 + f * (0 + c * (1 * 2 ^ m)) + 1) + 2)))))))))

theorem capW_spec (cr K A : ℕ) (G : Fin 48 ↪ Fin nr) (sA sB sC sD : Fin (ns + 1))
    (hAB : sA ≠ sB) (hAC : sA ≠ sC) (hAD : sA ≠ sD) (hBC : sB ≠ sC) (hBD : sB ≠ sD) (hCD : sC ≠ sD)
    (σ : WState ns nr) (q : ℕ) (hq : σ.val (G 0) = q) (hz : ∀ i : Fin 48, i ≠ 0 → σ.val (G i) = 0)
    (hsA : σ.st sA = [] ∧ σ.sh sA = 0) (hsB : σ.st sB = [] ∧ σ.sh sB = 0) (hsC : σ.st sC = [] ∧ σ.sh sC = 0)
    (hsD : σ.st sD = [] ∧ σ.sh sD = 0) (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) (hK : 1 ≤ K)
    (hcap : K * (q + 1) ^ A + 1000 * (q + 7) + 2 * cr + 100 ≤ cap) :
    ∃ τ : WState ns nr, WExec cap (capW cr K A G sA sB sC sD) σ τ
        (capWCost A (q - Cost.starWidth (Ledger.rowBr cr q) q / 4) ((q + 1) ^ A * K) ((q + 6) * 1000)
          (UnaryPow.sq cap)) ∧
      τ.st sC = U ((q + 1) ^ A * K * 2 ^ (q - Cost.starWidth (Ledger.rowBr cr q) q / 4)) ∧ τ.sh sC = 1 ∧
      τ.st sD = U ((q + 6) * 1000 * ((q + 1) ^ A * K * 2 ^ (q - Cost.starWidth (Ledger.rowBr cr q) q / 4))) ∧
      τ.sh sD = 1 ∧
      (∀ s, s ≠ sA → s ≠ sB → s ≠ sC → s ≠ sD → τ.st s = σ.st s ∧ τ.sh s = σ.sh s) ∧
      (∀ r, (∀ i, G i ≠ r) → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, e1, v30, v39, v42, st1, sh1, c1, off1⟩ := capRegs_spec cap cr K A G σ q hq hz hcr h4 hK hcap
  set m := q - Cost.starWidth (Ledger.rowBr cr q) q / 4 with hm
  set c := (q + 1) ^ A * K with hc
  set f := (q + 6) * 1000 with hf
  have hmq : m ≤ q := by omega
  have hcle : c ≤ cap := by
    have : (q + 1) ^ A * K = K * (q + 1) ^ A := Nat.mul_comm _ _
    omega
  have hfle : f ≤ cap := by omega
  have e2 := initU1_spec cap sA τ1 (by rw [st1]; exact hsA.1) (by rw [sh1]; exact hsA.2)
  set τ2 := (τ1.sets sA (U 1)).seth sA 1 with hτ2
  have e3 := initU_spec cap sB τ2 (by simp [τ2, Function.update_of_ne hAB.symm, st1, hsB.1])
    (by simp [τ2, Function.update_of_ne hAB.symm, sh1, hsB.2])
  set τ3 := (τ2.sets sB (U 0)).seth sB 1 with hτ3
  have e4 := initU_spec cap sC τ3 (by simp [τ3, τ2, Function.update_of_ne hAC.symm, Function.update_of_ne hBC.symm,
    st1, hsC.1]) (by simp [τ3, τ2, Function.update_of_ne hAC.symm, Function.update_of_ne hBC.symm, sh1, hsC.2])
  set τ4 := (τ3.sets sC (U 0)).seth sC 1 with hτ4
  have e5 := initU_spec cap sD τ4 (by simp [τ4, τ3, τ2, Function.update_of_ne hAD.symm, Function.update_of_ne hBD.symm,
    Function.update_of_ne hCD.symm, st1, hsD.1]) (by simp [τ4, τ3, τ2, Function.update_of_ne hAD.symm,
    Function.update_of_ne hBD.symm, Function.update_of_ne hCD.symm, sh1, hsD.2])
  set τ5 := (τ4.sets sD (U 0)).seth sD 1 with hτ5
  obtain ⟨e', e6⟩ := powS_spec cap (G 30) sA sB hAB m τ5 1 0 (by simp [τ5, τ4, τ3, τ2, v30])
    (by omega) (by simp [τ5, τ4, τ3, τ2, Function.update_of_ne hAD, Function.update_of_ne hAC, Function.update_of_ne hAB])
    (by simp [τ5, τ4, τ3, τ2, Function.update_of_ne hAD, Function.update_of_ne hAC, Function.update_of_ne hAB])
    (by simp [τ5, τ4, τ3, Function.update_of_ne hBD, Function.update_of_ne hBC])
    (by simp [τ5, τ4, τ3, Function.update_of_ne hBD, Function.update_of_ne hBC]) (by omega)
  set τ6 := ((((τ5.sets sA (U (1 * 2 ^ m))).sets sB (U e')).seth sA 1).seth sB 1).setv (G 30) 0 with hτ6
  have e7 := repS_spec cap (G 39) sA sC hAC (1 * 2 ^ m) c τ6 0
    (by simp [τ6, τ5, τ4, τ3, τ2, Function.update_of_ne (G.injective.ne (show (39 : Fin 48) ≠ 30 by decide)), v39])
    hcle (by simp [τ6, Function.update_of_ne hAB]) (by simp [τ6, Function.update_of_ne hAB])
    (by simp [τ6, τ5, τ4, Function.update_of_ne hCD, Function.update_of_ne hAC.symm, Function.update_of_ne hBC.symm])
    (by simp [τ6, τ5, τ4, Function.update_of_ne hCD, Function.update_of_ne hAC.symm, Function.update_of_ne hBC.symm])
  set τ7 := ((τ6.sets sC (U (0 + c * (1 * 2 ^ m)))).seth sC (0 + c * (1 * 2 ^ m) + 1)).setv (G 39) 0 with hτ7
  have e8 := rewU_spec cap sC τ7 (0 + c * (1 * 2 ^ m)) (0 + c * (1 * 2 ^ m) + 1) (by simp [τ7]) (by simp [τ7])
    (by omega) le_rfl
  set τ8 := τ7.seth sC 1 with hτ8
  have e9 := repS_spec cap (G 42) sC sD hCD (0 + c * (1 * 2 ^ m)) f τ8 0
    (by simp [τ8, τ7, τ6, τ5, τ4, τ3, τ2, Function.update_of_ne (G.injective.ne (show (42 : Fin 48) ≠ 39 by decide)),
      Function.update_of_ne (G.injective.ne (show (42 : Fin 48) ≠ 30 by decide)), v42])
    hfle (by simp [τ8, τ7]) (by simp [τ8])
    (by simp [τ8, τ7, τ6, τ5, Function.update_of_ne hCD.symm, Function.update_of_ne hAD.symm,
      Function.update_of_ne hBD.symm])
    (by simp [τ8, τ7, τ6, τ5, Function.update_of_ne hCD.symm, Function.update_of_ne hAD.symm,
      Function.update_of_ne hBD.symm])
  set τ9 := ((τ8.sets sD (U (0 + f * (0 + c * (1 * 2 ^ m))))).seth sD (0 + f * (0 + c * (1 * 2 ^ m)) + 1)).setv
    (G 42) 0 with hτ9
  have e10 := rewU_spec cap sD τ9 (0 + f * (0 + c * (1 * 2 ^ m))) (0 + f * (0 + c * (1 * 2 ^ m)) + 1) (by simp [τ9])
    (by simp [τ9]) (by omega) le_rfl
  refine ⟨τ9.seth sD 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold capW capWCost
    exact WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
      (WExec.seq e8 (WExec.seq e9 e10))))))))
  · simp [τ9, τ8, τ7, Function.update_of_ne hCD]
  · simp [τ9, τ8, Function.update_of_ne hCD]
  · simp [τ9]
  · simp
  · intro s h1 h2 h3 h4'
    simp [τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ2, Function.update_apply, h1, h2, h3, h4', st1, sh1]
  · intro r hr
    have hr' : ∀ i, r ≠ G i := fun i h => hr i h.symm
    simp [τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ2, Function.update_apply, hr', off1 r hr]
  · simp [τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ2, c1]

end Writer

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCapW
