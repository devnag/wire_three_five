import Proof.Wire_3_5.Primitive.SeedFix.C4KW
import Proof.Wire_3_5.Primitive.SeedFix.C4HkC

/-! # C4KW, part 1: marker rulers and the framed emitter

The kept words writer's stages are word programs over streams only (no registers). A number `a` is held on a scratch
stream as the MARKER RULER `mk a = false :: 1^a` (head at `0`, the marker), so a loop over its ones can return to the
marker (`rewM`). The words are emitted framed: `prs u` (the pairs `true, b` of `u`), then the terminator.

* `mk`, `prs`, `repW`, `frame_prs`, `rd_mk`, `seth_same`, `seth_seth'`, `seth_comm`;
* **`rew_spec`** (`rewM`: back to the marker from any head `p ≤ a + 1`, or `p ≤ 2`);
* **`apd_loop`** (a loop over a stream's ones, each pass appending a fixed word to an output);
* **`emitU_spec`**: from a ruler `mk a`, append `frame (repW (a − [sk]) u ++ v)` to the output, the ruler kept.

Paper quantity of the main type: the unary and constant words of the Hb printer's static bank (P3:2253-2290). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

/-! ## Words -/

/-- **A marker ruler**: `false`, then `1^a`. -/
def mk (a : ℕ) : List Bool := false :: List.replicate a true

/-- The framed pairs of a word (without the terminator). -/
def prs (u : List Bool) : List Bool := u.flatMap fun b => [true, b]

/-- `k` copies of `u`. -/
def repW (k : ℕ) (u : List Bool) : List Bool := (List.replicate k u).flatten

theorem prs_append (u v : List Bool) : prs (u ++ v) = prs u ++ prs v := by simp [prs]

theorem prs_length (u : List Bool) : (prs u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have e : prs (b :: u) = [true, b] ++ prs u := rfl
    rw [e, List.length_append, ih]; simp only [List.length_cons, List.length_nil]; ring

theorem frame_prs (w : List Bool) : frame w = prs w ++ [false] := by
  have h := C4Hf.frame_append_pairs w []
  rw [List.append_nil] at h
  rw [h]; rfl

theorem repW_zero (u : List Bool) : repW 0 u = [] := rfl

theorem repW_succ (k : ℕ) (u : List Bool) : repW (k + 1) u = u ++ repW k u := by
  simp [repW, List.replicate_succ]

theorem prs_repW (k : ℕ) (u : List Bool) : prs (repW k u) = repW k (prs u) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [repW_succ, prs_append, ih, repW_succ]

theorem repW_single (k : ℕ) (b : Bool) : repW k [b] = List.replicate k b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [repW_succ, ih]; rfl

theorem repW_rep (k m : ℕ) (b : Bool) : repW k (List.replicate m b) = List.replicate (k * m) b := by
  induction k with
  | zero => simp [repW]
  | succ k ih => rw [repW_succ, ih, ← List.replicate_add]; congr 1; ring

theorem mk_length (a : ℕ) : (mk a).length = a + 1 := by simp [mk]

theorem rd_mk (a p : ℕ) : readTapeBit (mk a) p = decide (1 ≤ p ∧ p ≤ a) := by
  cases p with
  | zero => rfl
  | succ q =>
    simp only [mk, readTapeBit, List.getD_cons_succ]
    by_cases h : q < a
    · rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_replicate]
      symm; simp only [decide_eq_true_eq]; omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      symm; simp only [decide_eq_false_iff_not]; omega

variable {ns nr : ℕ} (cap : ℕ)

theorem seth_same (σ : WState ns nr) (i : Fin (ns + 1)) (v : ℕ) (h : σ.sh i = v) : σ.seth i v = σ := by
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp [WState.seth, h]
    · simp [WState.seth, Function.update_of_ne hj]
  · rfl
  · rfl
  · rfl

theorem seth_seth' (σ : WState ns nr) (i : Fin (ns + 1)) (x y : ℕ) : (σ.seth i x).seth i y = σ.seth i y := by
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp [WState.seth]
    · simp [WState.seth, Function.update_of_ne hj]
  · rfl
  · rfl
  · rfl

theorem seth_comm (σ : WState ns nr) (i j : Fin (ns + 1)) (hij : i ≠ j) (x y : ℕ) :
    (σ.seth i x).seth j y = (σ.seth j y).seth i x := by
  apply WState.eq
  · funext k
    by_cases hki : k = i
    · subst hki; simp [WState.seth, hij]
    · by_cases hkj : k = j
      · subst hkj; simp [WState.seth, hki]
      · simp [WState.seth, hki, hkj]
  · rfl
  · rfl
  · rfl

/-! ## Back to the marker -/

/-- Back to the marker of a ruler. -/
def rewM (R : Fin (ns + 1)) : WM ns nr := .seq (.bwd R) (.seq (.whs R (.bwd R)) (.bwd R))

theorem rew_loop (R : Fin (ns + 1)) (a : ℕ) : ∀ (q : ℕ) (σ : WState ns nr), σ.st R = mk a → σ.sh R = q → q ≤ a →
    WExec cap (.whs R (.bwd R)) σ (σ.seth R 0) (3 * q + 1)
  | 0, σ, hs, hq, _ => by
    rw [seth_same σ R 0 hq]
    exact WExec.whsF (by show readTapeBit _ _ = false; rw [hs, hq]; rfl)
  | q + 1, σ, hs, hq, hqa => by
    have hb : wbit σ R = true := by
      show readTapeBit _ _ = true
      rw [hs, hq, rd_mk]; simp only [decide_eq_true_eq]; omega
    have t1 := WExec.bwd (cap := cap) R σ
    have ih := rew_loop R a q (σ.seth R (σ.sh R - 1)) (by simp [hs]) (by simp [hq]) (by omega)
    rw [seth_seth'] at ih
    exact WExec.cast cap (WExec.whsT hb t1 ih) rfl (by omega)

/-- **Back to the marker** from a head `p ≥ 1` inside the ruler or just past it (or at `2` on `mk 0`). -/
theorem rew_spec (R : Fin (ns + 1)) (a p : ℕ) (σ : WState ns nr) (hs : σ.st R = mk a) (hp : σ.sh R = p)
    (h1 : 1 ≤ p) (h2 : p ≤ a + 1 ∨ p ≤ 2) : WExec cap (rewM R) σ (σ.seth R 0) (3 * p + 4) := by
  have t1 := WExec.bwd (cap := cap) R σ
  rw [hp] at t1
  by_cases hq : p - 1 ≤ a
  · have t2 := rew_loop cap R a (p - 1) (σ.seth R (p - 1)) (by simp [hs]) (by simp) hq
    rw [seth_seth'] at t2
    have t3 := WExec.bwd (cap := cap) R (σ.seth R 0)
    have e3 : (σ.seth R 0).seth R ((σ.seth R 0).sh R - 1) = σ.seth R 0 := by
      rw [seth_seth']; simp
    rw [e3] at t3
    exact WExec.cast cap (WExec.seq t1 (WExec.seq t2 t3)) rfl (by omega)
  · have hp2 : p = 2 := by omega
    have ha : a = 0 := by omega
    subst hp2 ha
    have t2 : WExec cap (.whs R (.bwd R)) (σ.seth R (2 - 1)) (σ.seth R (2 - 1)) 1 :=
      WExec.whsF (by show readTapeBit _ _ = false; simp [hs, mk, readTapeBit])
    have t3 := WExec.bwd (cap := cap) R (σ.seth R (2 - 1))
    have e3 : (σ.seth R (2 - 1)).seth R ((σ.seth R (2 - 1)).sh R - 1) = σ.seth R 0 := by
      rw [seth_seth']; simp
    rw [e3] at t3
    exact WExec.cast cap (WExec.seq t1 (WExec.seq t2 t3)) rfl (by omega)

/-! ## A loop over a stream's ones -/

/-- **A loop over the ones of `R`** (positions `lo … hi − 1`, `false` at `hi`, the head from `lo` on), each pass running
`Q`, which appends `w` to `O` (under an invariant `I` kept by the appends and by `R`'s moves). -/
theorem apd_loop (R O : Fin (ns + 1)) (hRO : R ≠ O) (Q : WM ns nr) (w : List Bool) (cQ : ℕ) (I : WState ns nr → Prop)
    (hQ : ∀ τ : WState ns nr, I τ → τ.sh O = (τ.st O).length → WExec cap Q τ (apd τ O w) cQ)
    (hIa : ∀ τ : WState ns nr, I τ → I (apd τ O w)) (hIs : ∀ (τ : WState ns nr) (v : ℕ), I τ → I (τ.seth R v))
    (c : List Bool) (lo hi : ℕ) (hT : ∀ q, lo ≤ q → q < hi → readTapeBit c q = true) (hF : readTapeBit c hi = false) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.st R = c → σ.sh R + k = hi → lo ≤ σ.sh R → I σ → σ.sh O = (σ.st O).length →
      WExec cap (.whs R (.seq Q (.fwd R))) σ ((apd σ O (repW k w)).seth R hi) (k * (cQ + 4) + 1)
  | 0, σ, hc, hk, _, _, hO => by
    rw [repW_zero, apd_nil σ O hO, seth_same σ R hi (by omega)]
    exact WExec.cast cap (WExec.whsF (by show readTapeBit _ _ = false; rw [hc, show σ.sh R = hi by omega]; exact hF))
      rfl (by omega)
  | k + 1, σ, hc, hk, hlo, hI, hO => by
    have hb : wbit σ R = true := by
      show readTapeBit _ _ = true
      rw [hc]; exact hT _ hlo (by omega)
    have t1 := hQ σ hI hO
    have t2 := WExec.fwd (cap := cap) R (apd σ O w)
    have e2 : (apd σ O w).sh R = σ.sh R := apd_sh_ne σ O R hRO w
    rw [e2] at t2
    have c1 : ((apd σ O w).seth R (σ.sh R + 1)).st R = c := by
      simp only [WState.seth_st]; rw [apd_st_ne σ O R hRO, hc]
    have c2 : ((apd σ O w).seth R (σ.sh R + 1)).sh R = σ.sh R + 1 := by
      simp only [WState.seth_sh, Function.update_self]
    have c3 : ((apd σ O w).seth R (σ.sh R + 1)).sh O = (((apd σ O w).seth R (σ.sh R + 1)).st O).length := by
      simp only [WState.seth_sh, WState.seth_st]
      rw [Function.update_of_ne (Ne.symm hRO), apd_sh_d, apd_st_d, List.length_append]
    have ih := apd_loop R O hRO Q w cQ I hQ hIa hIs c lo hi hT hF k ((apd σ O w).seth R (σ.sh R + 1))
      c1 (by rw [c2]; omega) (by rw [c2]; omega) (hIs _ _ (hIa σ hI)) c3
    have e3 : (apd ((apd σ O w).seth R (σ.sh R + 1)) O (repW k w)).seth R hi = (apd σ O (repW (k + 1) w)).seth R hi := by
      rw [apd_seth _ R O hRO, seth_seth', apd_apd, repW_succ]
    rw [e3] at ih
    refine WExec.cast cap (WExec.whsT hb (WExec.seq t1 t2) ih) rfl ?_
    have : (k + 1) * (cQ + 4) = k * (cQ + 4) + (cQ + 4) := by ring
    omega

/-! ## The framed emitter -/

/-- **The framed emitter**: skip the marker (and one more one if `sk`), then per remaining one of `R` append the pairs
of `u`; then the pairs of `v` and the terminator; back to the marker. -/
def emitU (R O : Fin (ns + 1)) (sk : Bool) (u v : List Bool) : WM ns nr :=
  .seq (.fwd R) (.seq (if sk then .fwd R else .skip) (.seq (.whs R (.seq (wlist O (prs u)) (.fwd R)))
    (.seq (wlist O (prs v ++ [false])) (rewM R))))

/-- The emitter's steps. -/
def emitCost (a : ℕ) (u v : List Bool) : ℕ := a * (8 * u.length + 4) + 8 * v.length + 3 * a + 30

/-- The emitter's loop, from its start `s` (`1`, or `2` past a skipped one). -/
theorem emit_loop (R O : Fin (ns + 1)) (hRO : R ≠ O) (u : List Bool) (a s : ℕ) (σ : WState ns nr)
    (hR : σ.st R = mk a) (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (hO : σ.sh O = (σ.st O).length) :
    ∃ p : ℕ, WExec cap (.whs R (.seq (wlist O (prs u)) (.fwd R))) (σ.seth R s)
      ((apd σ O (repW (a + 1 - s) (prs u))).seth R p) ((a + 1 - s) * (8 * u.length + 4) + 1) ∧ 1 ≤ p ∧
      (p ≤ a + 1 ∨ p ≤ 2) := by
  have hσs : (σ.seth R s).st R = mk a := by simp [hR]
  have hOs : (σ.seth R s).sh O = ((σ.seth R s).st O).length := by
    simp only [WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne (Ne.symm hRO)]; exact hO
  by_cases hsa : s ≤ a + 1
  · have t := apd_loop cap R O hRO (wlist O (prs u)) (prs u) (4 * (prs u).length) (fun _ => True)
      (fun τ _ h => wlist_spec cap O (prs u) τ h) (fun _ _ => trivial) (fun _ _ _ => trivial) (mk a) 1 (a + 1)
      (fun q h1 h2 => by rw [rd_mk]; simp only [decide_eq_true_eq]; omega)
      (by rw [rd_mk]; simp only [decide_eq_false_iff_not]; omega) (a + 1 - s) (σ.seth R s) hσs (by simp; omega)
      (by simp; omega) trivial hOs
    rw [apd_seth _ R O hRO, seth_seth', prs_length] at t
    refine ⟨a + 1, WExec.cast cap t rfl ?_, by omega, Or.inl le_rfl⟩
    have : 4 * (2 * u.length) + 4 = 8 * u.length + 4 := by ring
    rw [this]
  · have hs2' : s = 2 := by omega
    have ha0 : a = 0 := by omega
    refine ⟨2, ?_, by omega, Or.inr le_rfl⟩
    have hk0 : a + 1 - s = 0 := by omega
    rw [hk0, repW_zero, apd_nil σ O hO, ← hs2']
    exact WExec.mono (WExec.whsF (by show readTapeBit _ _ = false; rw [hσs, ha0]; simp [mk, readTapeBit, hs2']))
      (by omega)

theorem emitU_spec (R O : Fin (ns + 1)) (hRO : R ≠ O) (sk : Bool) (u v : List Bool) (a : ℕ) (σ : WState ns nr)
    (hR : σ.st R = mk a) (hR0 : σ.sh R = 0) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (emitU R O sk u v) σ (apd σ O (frame (repW (a - (if sk then 1 else 0)) u ++ v))) (emitCost a u v) := by
  set s : ℕ := 1 + (if sk then 1 else 0) with hs
  have t0 := WExec.fwd (cap := cap) R σ
  rw [hR0] at t0
  have t1 : WExec cap (if sk then .fwd R else .skip : WM ns nr) (σ.seth R (0 + 1)) (σ.seth R s) 1 := by
    cases sk
    · simp only [hs, if_false, Bool.false_eq_true]; exact WExec.mono (WExec.skip _) (by omega)
    · have t := WExec.fwd (cap := cap) R (σ.seth R (0 + 1))
      simp only [seth_seth', WState.seth_sh, Function.update_self] at t
      simp only [hs, if_true]
      exact t
  obtain ⟨p, t2, hp1, hp2⟩ := emit_loop cap R O hRO u a s σ hR (by rw [hs]; split_ifs <;> omega)
    (by rw [hs]; split_ifs <;> omega) hO
  set X := repW (a + 1 - s) (prs u) with hX
  set S2 := (apd σ O X).seth R p with hS2
  have hO2 : S2.sh O = (S2.st O).length := by
    rw [hS2]; simp only [WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (Ne.symm hRO), apd_sh_d, apd_st_d, List.length_append]
  have t3 := wlist_spec cap O (prs v ++ [false]) S2 hO2
  rw [hS2, apd_seth _ R O hRO, apd_apd] at t3
  have t4 := rew_spec cap R a p ((apd σ O (X ++ (prs v ++ [false]))).seth R p) (by simp [apd_st_ne σ O R hRO, hR])
    (by simp) hp1 hp2
  rw [seth_seth', seth_same _ R 0 (by rw [apd_sh_ne σ O R hRO, hR0])] at t4
  have hw : X ++ (prs v ++ [false]) = frame (repW (a - (if sk then 1 else 0)) u ++ v) := by
    rw [frame_prs, prs_append, prs_repW, hX]
    have : a + 1 - s = a - (if sk then 1 else 0) := by rw [hs]; split_ifs <;> omega
    rw [this, List.append_assoc]
  rw [hw] at t4 t3
  refine WExec.cast cap (WExec.seq t0 (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4)))) rfl ?_
  have hk : (a + 1 - s) * (8 * u.length + 4) ≤ a * (8 * u.length + 4) := Nat.mul_le_mul_right _ (by omega)
  have hl : (prs v ++ [false]).length = 2 * v.length + 1 := by rw [List.length_append, prs_length]; rfl
  rw [hl]
  unfold emitCost
  rcases hp2 with hp | hp <;> omega

end NearCubicWires.WireExponent3_5.PrimT.C4KW
