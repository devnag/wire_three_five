import Proof.Wire_3_5.FinalPass.TabEmit

/-! # S4 (f1), the tables writer, part 3: reading the unit's request (P3:2036-2101)

A unit of the tables writer reads its numbers from the request word `w` (framed on the request stream): the THR
request word of the empty tuple, `natWord n ++ [true, false, false] ++ unaryList [len, cap, err, L₀, L₁, |seeds|]`.
Word programs with parametric streams and registers, every head move counted in `ps` (so the request is rewound
exactly):

* `readUF`, **`readUF_spec`**: a framed unary field `1^v 0` into a register;
* `skipBF`, **`skipBF_spec`**: `m` framed payload bits skipped;
* `cntK`, **`cntK_spec`**: the unit counter `1^j` counted twice;
* `div2`, **`div2_spec`**: `j ↦ (j / 2, j % 2)`;
* `cmpD`, **`cmpD_spec`**: `(a, b) ↦ (b − a, a)` (the seed's test `a < b` is `b − a ≠ 0`).

Paper quantity of the main types: the unit's seed index `j / 2` and mask choice `j % 2`, and the request's numbers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem getD_drop' (W : List Bool) (p q : ℕ) : W.getD (p + q) false = (W.drop p).getD q false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

section Gen
variable {ns nr : ℕ} (cap : ℕ) (Q : Fin (ns + 1)) (ps r : Fin nr)

/-! ## A framed unary field -/

def loopUF : WM ns nr := .whs Q (.seq (.inc r) (.seq (WM.fwdC Q ps) (WM.fwdC Q ps)))

theorem loopUF_spec (hpr : ps ≠ r) (W R : List Bool) (p v : ℕ)
    (hd : W.drop p = List.replicate v true ++ false :: R) :
    ∀ (k q : ℕ) (σ : WState ns nr), q + k = v → σ.st Q = frameP W ++ [false] → σ.sh Q = 2 * (p + q) + 1 →
      σ.val r + k ≤ cap → σ.val ps + 2 * k ≤ cap →
      WExec cap (loopUF Q ps r) σ (((σ.seth Q (2 * (p + v) + 1)).setv ps (σ.val ps + 2 * k)).setv r (σ.val r + k))
        (k * 17 + 1)
  | 0, q, σ, hq, hst, hsh, _, _ => by
    have hqv : q = v := by omega
    have hlen : p + q < W.length := by
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_append, List.length_replicate, List.length_cons] at this
      omega
    have hb : wbit σ Q = false := by
      unfold wbit
      rw [hst, hsh, readTapeBit_frameP W [false] (p + q) hlen, getD_drop', hd, hqv]
      simp
    have e : (((σ.seth Q (2 * (p + v) + 1)).setv ps (σ.val ps + 2 * 0)).setv r (σ.val r + 0)) = σ := by
      apply WState.eq
      · funext i
        by_cases hi : i = Q
        · subst hi; simp [hsh, hqv]
        · simp [Function.update_of_ne hi]
      · rfl
      · funext x
        by_cases hx : x = r
        · subst hx; simp
        · by_cases hy : x = ps
          · subst hy; simp [Function.update_of_ne hx]
          · simp [Function.update_of_ne hx, Function.update_of_ne hy]
      · rfl
    rw [e]
    exact WExec.cast cap (WExec.whsF hb) rfl (by omega)
  | k + 1, q, σ, hq, hst, hsh, hr, hps => by
    have hlen : p + q < W.length := by
      have := congrArg List.length hd
      simp only [List.length_drop, List.length_append, List.length_replicate, List.length_cons] at this
      omega
    have hb : wbit σ Q = true := by
      unfold wbit
      rw [hst, hsh, readTapeBit_frameP W [false] (p + q) hlen, getD_drop', hd,
        List.getD_append _ _ _ _ (by simp; omega)]
      simp [List.getElem?_replicate, show q < v by omega]
    have e1 := WExec.inc (cap := cap) r σ (by omega)
    have e2 := wfwdC_spec cap Q ps (σ.setv r (σ.val r + 1)) (by rw [wsetv_val_ne _ _ hpr]; omega)
    have e3 := wfwdC_spec cap Q ps (((σ.setv r (σ.val r + 1)).seth Q ((σ.setv r (σ.val r + 1)).sh Q + 1)).setv ps
      ((σ.setv r (σ.val r + 1)).val ps + 1)) (by simp [Function.update_of_ne hpr]; omega)
    have ih := loopUF_spec hpr W R p v hd k (q + 1)
      ((((((σ.setv r (σ.val r + 1)).seth Q ((σ.setv r (σ.val r + 1)).sh Q + 1)).setv ps
        ((σ.setv r (σ.val r + 1)).val ps + 1)).seth Q ((((σ.setv r (σ.val r + 1)).seth Q
          ((σ.setv r (σ.val r + 1)).sh Q + 1)).setv ps ((σ.setv r (σ.val r + 1)).val ps + 1)).sh Q + 1)).setv ps
          ((((σ.setv r (σ.val r + 1)).seth Q ((σ.setv r (σ.val r + 1)).sh Q + 1)).setv ps
            ((σ.setv r (σ.val r + 1)).val ps + 1)).val ps + 1)))
      (by omega) (by simpa using hst) (by simp [hsh]; ring)
      (by simp [Function.update_of_ne hpr.symm]; omega) (by simp [Function.update_of_ne hpr]; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by ring_nf; omega)
    apply WState.eq
    · funext i
      by_cases hi : i = Q
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    · rfl
    · funext x
      by_cases hx : x = r
      · subst hx; simp [Function.update_of_ne hpr.symm]; omega
      · by_cases hy : x = ps
        · subst hy; simp [Function.update_of_ne hx, Function.update_of_ne hpr]; omega
        · simp [Function.update_of_ne hx, Function.update_of_ne hy]
    · rfl

/-- **Read a framed unary field** `1^v 0` into `r`, from its first marker to the next field's. -/
def readUF : WM ns nr := .seq (WM.fwdC Q ps) (.seq (loopUF Q ps r) (WM.fwdC Q ps))

theorem readUF_spec (hpr : ps ≠ r) (W R : List Bool) (p v : ℕ)
    (hd : W.drop p = List.replicate v true ++ false :: R) (σ : WState ns nr) (hst : σ.st Q = frameP W ++ [false])
    (hsh : σ.sh Q = 2 * p) (hr : σ.val r + v ≤ cap) (hps : σ.val ps + 2 * v + 2 ≤ cap) :
    WExec cap (readUF Q ps r) σ (((σ.seth Q (2 * (p + v + 1))).setv ps (σ.val ps + 2 * v + 2)).setv r (σ.val r + v))
      (17 * v + 13) := by
  have e1 := wfwdC_spec cap Q ps σ (by omega)
  have e2 := loopUF_spec cap Q ps r hpr W R p v hd v 0 ((σ.seth Q (σ.sh Q + 1)).setv ps (σ.val ps + 1)) (by omega)
    (by simpa using hst) (by simp [hsh]) (by simp [Function.update_of_ne hpr.symm]; omega) (by simp; omega)
  have e3 := wfwdC_spec cap Q ps ((((((σ.seth Q (σ.sh Q + 1)).setv ps (σ.val ps + 1))).seth Q (2 * (p + v) + 1)).setv ps
    (((σ.seth Q (σ.sh Q + 1)).setv ps (σ.val ps + 1)).val ps + 2 * v)).setv r
    (((σ.seth Q (σ.sh Q + 1)).setv ps (σ.val ps + 1)).val r + v)) (by simp [Function.update_of_ne hpr]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i = Q
    · subst hi; simp; ring
    · simp [Function.update_of_ne hi]
  · rfl
  · funext x
    by_cases hx : x = r
    · subst hx; simp [Function.update_of_ne hpr.symm]
    · by_cases hy : x = ps
      · subst hy; simp [Function.update_of_ne hx, Function.update_of_ne hpr]; omega
      · simp [Function.update_of_ne hx, Function.update_of_ne hy]
  · rfl

/-! ## Skipping framed payload bits -/

def skipBF : WM ns nr := .whr r (.seq (.dec r) (.seq (WM.fwdC Q ps) (WM.fwdC Q ps)))

theorem skipBF_spec (hpr : ps ≠ r) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val r = m → m ≤ cap → σ.val ps + 2 * m ≤ cap →
      WExec cap (skipBF Q ps r) σ (((σ.seth Q (σ.sh Q + 2 * m)).setv ps (σ.val ps + 2 * m)).setv r 0) (m * 15 + 1)
  | 0, σ, h0, _, _ => by
    have e : (((σ.seth Q (σ.sh Q + 2 * 0)).setv ps (σ.val ps + 2 * 0)).setv r 0) = σ := by
      apply WState.eq
      · funext i
        by_cases hi : i = Q
        · subst hi; simp
        · simp [Function.update_of_ne hi]
      · rfl
      · funext x
        by_cases hx : x = r
        · subst hx; simp [h0]
        · by_cases hy : x = ps
          · subst hy; simp [Function.update_of_ne hx]
          · simp [Function.update_of_ne hx, Function.update_of_ne hy]
      · rfl
    rw [e]
    exact WExec.whrF h0
  | m + 1, σ, hm, hc, hps => by
    have e1 := WExec.dec (cap := cap) r σ (by omega)
    have e2 := wfwdC_spec cap Q ps (σ.setv r (σ.val r - 1)) (by rw [wsetv_val_ne _ _ hpr]; omega)
    have e3 := wfwdC_spec cap Q ps (((σ.setv r (σ.val r - 1)).seth Q ((σ.setv r (σ.val r - 1)).sh Q + 1)).setv ps
      ((σ.setv r (σ.val r - 1)).val ps + 1)) (by simp [Function.update_of_ne hpr]; omega)
    have ih := skipBF_spec hpr m
      ((((((σ.setv r (σ.val r - 1)).seth Q ((σ.setv r (σ.val r - 1)).sh Q + 1)).setv ps
        ((σ.setv r (σ.val r - 1)).val ps + 1)).seth Q ((((σ.setv r (σ.val r - 1)).seth Q
          ((σ.setv r (σ.val r - 1)).sh Q + 1)).setv ps ((σ.setv r (σ.val r - 1)).val ps + 1)).sh Q + 1)).setv ps
          ((((σ.setv r (σ.val r - 1)).seth Q ((σ.setv r (σ.val r - 1)).sh Q + 1)).setv ps
            ((σ.setv r (σ.val r - 1)).val ps + 1)).val ps + 1)))
      (by simp [Function.update_of_ne hpr.symm]; omega) (by omega) (by simp [Function.update_of_ne hpr]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by ring_nf; omega)
    apply WState.eq
    · funext i
      by_cases hi : i = Q
      · subst hi; simp; ring
      · simp [Function.update_of_ne hi]
    · rfl
    · funext x
      by_cases hx : x = r
      · subst hx; simp
      · by_cases hy : x = ps
        · subst hy; simp [Function.update_of_ne hx, Function.update_of_ne hpr]; omega
        · simp [Function.update_of_ne hx, Function.update_of_ne hy]
    · rfl

end Gen

section Cnt
variable {ns nr : ℕ} (cap : ℕ) (K : Fin (ns + 1)) (a b : Fin nr)

/-! ## The unit counter, counted twice -/

def cntK : WM ns nr := .whs K (.seq (.fwd K) (.seq (.inc a) (.inc b)))

theorem cntK_spec (hab : a ≠ b) (j : ℕ) (hj : j ≤ cap) :
    ∀ (m i : ℕ) (σ : WState ns nr), i + m = j → σ.st K = List.replicate j true → σ.sh K = i →
      σ.val a + m ≤ cap → σ.val b + m ≤ cap →
      WExec cap (cntK K a b) σ (((σ.seth K j).setv a (σ.val a + m)).setv b (σ.val b + m)) (m * 11 + 1)
  | 0, i, σ, hl, hK, hKh, _, _ => by
    have hi : i = j := by omega
    have hr : wbit σ K = false := by
      unfold wbit
      rw [hK, hKh, hi]
      unfold readTapeBit
      simp
    have e : (((σ.seth K j).setv a (σ.val a + 0)).setv b (σ.val b + 0)) = σ := by
      apply WState.eq
      · funext x
        by_cases hx : x = K
        · subst hx; simp [hKh, hi]
        · simp [Function.update_of_ne hx]
      · rfl
      · funext x
        by_cases hx : x = b
        · subst hx; simp
        · by_cases hy : x = a
          · subst hy; simp [Function.update_of_ne hx]
          · simp [Function.update_of_ne hx, Function.update_of_ne hy]
      · rfl
    rw [e]
    exact WExec.cast cap (WExec.whsF hr) rfl (by omega)
  | m + 1, i, σ, hl, hK, hKh, ha, hb => by
    have hr : wbit σ K = true := by
      unfold wbit
      rw [hK, hKh]
      unfold readTapeBit
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    have e1 := WExec.fwd (cap := cap) K σ
    have e2 := WExec.inc (cap := cap) a (σ.seth K (σ.sh K + 1)) (by simp only [WState.seth_val]; omega)
    have e3 := WExec.inc (cap := cap) b ((σ.seth K (σ.sh K + 1)).setv a ((σ.seth K (σ.sh K + 1)).val a + 1))
      (by simp [Function.update_of_ne hab.symm]; omega)
    have ih := cntK_spec hab j hj m (i + 1)
      (((σ.seth K (σ.sh K + 1)).setv a ((σ.seth K (σ.sh K + 1)).val a + 1)).setv b
        (((σ.seth K (σ.sh K + 1)).setv a ((σ.seth K (σ.sh K + 1)).val a + 1)).val b + 1))
      (by omega) (by simpa using hK) (by simp [hKh]) (by simp [Function.update_of_ne hab]; omega)
      (by simp [Function.update_of_ne hab.symm]; omega)
    refine WExec.cast cap (WExec.whsT hr (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by ring_nf; omega)
    apply WState.eq
    · funext x
      by_cases hx : x = K
      · subst hx; simp
      · simp [Function.update_of_ne hx]
    · rfl
    · funext x
      by_cases hx : x = b
      · subst hx; simp [Function.update_of_ne hab.symm]; omega
      · by_cases hy : x = a
        · subst hy; simp [Function.update_of_ne hx, Function.update_of_ne hab]; omega
        · simp [Function.update_of_ne hx, Function.update_of_ne hy]
    · rfl

end Cnt

section Arith
variable {ns nr : ℕ} (cap : ℕ) (a b g : Fin nr)

/-! ## Halving -/

/-- `a` counted down into the parity `b` and the half `g`. -/
def div2 : WM ns nr := .whr a (.seq (.dec a) (.ifr b (.seq (.dec b) (.inc g)) (.inc b)))

theorem div2_spec (hab : a ≠ b) (hag : a ≠ g) (hbg : b ≠ g) (hc : 2 ≤ cap) :
    ∀ (m t : ℕ) (σ : WState ns nr), σ.val a = m → m ≤ cap → σ.val b = t % 2 → σ.val g = t / 2 →
      (t + m) / 2 ≤ cap →
      WExec cap (div2 a b g) σ (((σ.setv a 0).setv b ((t + m) % 2)).setv g ((t + m) / 2)) (m * 10 + 1)
  | 0, t, σ, h0, _, hb, hg, _ => by
    have e : (((σ.setv a 0).setv b ((t + 0) % 2)).setv g ((t + 0) / 2)) = σ := by
      apply WState.eq
      · rfl
      · rfl
      · funext x
        by_cases hx : x = g
        · subst hx; simp [hg]
        · by_cases hy : x = b
          · subst hy; simp [Function.update_of_ne hx, hb]
          · by_cases hz : x = a
            · subst hz; simp [Function.update_of_ne hx, Function.update_of_ne hy, h0]
            · simp [Function.update_of_ne hx, Function.update_of_ne hy, Function.update_of_ne hz]
      · rfl
    rw [e]
    exact WExec.whrF h0
  | m + 1, t, σ, hm, hmc, hb, hg, hcap => by
    have e1 := WExec.dec (cap := cap) a σ (by omega)
    rw [hm, Nat.add_sub_cancel] at e1
    have hb1 : (σ.setv a m).val b = t % 2 := by rw [wsetv_val_ne _ _ hab.symm, hb]
    have hg1 : (σ.setv a m).val g = t / 2 := by rw [wsetv_val_ne _ _ hag.symm, hg]
    have hstep : ∃ (σ2 : WState ns nr) (c2 : ℕ),
        WExec cap (.ifr b (.seq (.dec b) (.inc g)) (.inc b)) (σ.setv a m) σ2 c2 ∧ c2 ≤ 6 ∧
        σ2 = ((σ.setv a m).setv b ((t + 1) % 2)).setv g ((t + 1) / 2) := by
      by_cases ht : t % 2 = 0
      · have i1 := WExec.inc (cap := cap) b (σ.setv a m) (by rw [hb1, ht]; omega)
        refine ⟨_, _, WExec.ifrF (by rw [hb1, ht]) i1, by omega, ?_⟩
        apply WState.eq
        · rfl
        · rfl
        · funext x
          by_cases hx : x = g
          · rw [hx]
            simp only [WState.setv_val, Function.update_self, Function.update_of_ne hbg.symm,
              Function.update_of_ne hag.symm, hg]
            omega
          · by_cases hy : x = b
            · rw [hy]
              simp only [WState.setv_val, Function.update_self, Function.update_of_ne hbg,
                Function.update_of_ne hab.symm, hb]
              omega
            · simp only [WState.setv_val, Function.update_of_ne hx, Function.update_of_ne hy]
        · rfl
      · have d1 := WExec.dec (cap := cap) b (σ.setv a m) (by rw [hb1]; omega)
        have i1 := WExec.inc (cap := cap) g ((σ.setv a m).setv b ((σ.setv a m).val b - 1))
          (by rw [wsetv_val_ne _ _ hbg.symm, hg1]; omega)
        refine ⟨_, _, WExec.ifrT (by rw [hb1]; omega) (WExec.seq d1 i1), by omega, ?_⟩
        apply WState.eq
        · rfl
        · rfl
        · funext x
          by_cases hx : x = g
          · rw [hx]
            simp only [WState.setv_val, Function.update_self, Function.update_of_ne hbg.symm,
              Function.update_of_ne hag.symm, hg]
            omega
          · by_cases hy : x = b
            · rw [hy]
              simp only [WState.setv_val, Function.update_self, Function.update_of_ne hbg,
                Function.update_of_ne hab.symm, hb]
              omega
            · simp only [WState.setv_val, Function.update_of_ne hx, Function.update_of_ne hy]
        · rfl
    obtain ⟨σ2, c2, e2, hc2, rfl⟩ := hstep
    have ih := div2_spec hab hag hbg hc m (t + 1) (((σ.setv a m).setv b ((t + 1) % 2)).setv g ((t + 1) / 2))
      (by rw [wsetv_val_ne _ _ hag, wsetv_val_ne _ _ hab]; simp) (by omega)
      (by rw [wsetv_val_ne _ _ hbg]; simp) (by simp) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) ih) ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext x
      by_cases hx : x = g
      · rw [hx]
        simp only [WState.setv_val, Function.update_self]
        omega
      · by_cases hy : x = b
        · rw [hy]
          simp only [WState.setv_val, Function.update_self, Function.update_of_ne hbg]
          omega
        · by_cases hz : x = a
          · rw [hz]
            simp only [WState.setv_val, Function.update_self, Function.update_of_ne hag, Function.update_of_ne hab]
          · simp only [WState.setv_val, Function.update_of_ne hx, Function.update_of_ne hy, Function.update_of_ne hz]
    · rfl

/-! ## The seed's test -/

/-- `a` counted down, `b` with it, into `g`: `(a, b, g) ↦ (0, b − a, g + a)`. -/
def cmpD : WM ns nr := .whr a (.seq (.dec a) (.seq (.dec b) (.inc g)))

theorem cmpD_spec (hab : a ≠ b) (hag : a ≠ g) (hbg : b ≠ g) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val a = m → m ≤ cap → σ.val b ≤ cap → σ.val g + m ≤ cap →
      WExec cap (cmpD a b g) σ (((σ.setv a 0).setv b (σ.val b - m)).setv g (σ.val g + m)) (m * 9 + 1)
  | 0, σ, h0, _, _, _ => by
    have e : (((σ.setv a 0).setv b (σ.val b - 0)).setv g (σ.val g + 0)) = σ := by
      apply WState.eq
      · rfl
      · rfl
      · funext x
        by_cases hx : x = g
        · subst hx; simp
        · by_cases hy : x = b
          · subst hy; simp [Function.update_of_ne hx]
          · by_cases hz : x = a
            · subst hz; simp [Function.update_of_ne hx, Function.update_of_ne hy, h0]
            · simp [Function.update_of_ne hx, Function.update_of_ne hy, Function.update_of_ne hz]
      · rfl
    rw [e]
    exact WExec.whrF h0
  | m + 1, σ, hm, hmc, hbc, hgc => by
    have e1 := WExec.dec (cap := cap) a σ (by omega)
    have e2 := WExec.dec (cap := cap) b (σ.setv a (σ.val a - 1)) (by rw [wsetv_val_ne _ _ hab.symm]; omega)
    have e3 := WExec.inc (cap := cap) g ((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b - 1))
      (by simp [Function.update_of_ne hbg.symm, Function.update_of_ne hag.symm]; omega)
    have ih := cmpD_spec hab hag hbg m
      (((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b - 1)).setv g
        (((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b - 1)).val g + 1))
      (by simp [Function.update_of_ne hag, Function.update_of_ne hab]; omega) (by omega)
      (by simp [Function.update_of_ne hbg, Function.update_of_ne hab.symm]; omega)
      (by simp [Function.update_of_ne hbg.symm, Function.update_of_ne hag.symm]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by ring_nf; omega)
    apply WState.eq
    · rfl
    · rfl
    · funext x
      by_cases hx : x = g
      · subst hx; simp [Function.update_of_ne hbg.symm, Function.update_of_ne hag.symm]; omega
      · by_cases hy : x = b
        · subst hy; simp [Function.update_of_ne hx, Function.update_of_ne hab.symm]; omega
        · by_cases hz : x = a
          · subst hz; simp [Function.update_of_ne hx, Function.update_of_ne hy]
          · simp [Function.update_of_ne hx, Function.update_of_ne hy, Function.update_of_ne hz]
    · rfl

end Arith

end NearCubicWires.WireExponent3_5.FinalPass.TabW
