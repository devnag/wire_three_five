import Proof.Wire_3_5.FinalPass.HashBuild

/-! # The THR row's residues modulo `p`, part 1 (P3:2585-2623)

Row `(g, p)` of `row:radix` reduces the equation `L_g`'s coefficients modulo `p` (`redCoeff`: `a_i = w_i mod p`) and
its target (`r₀ = (−target) mod p`). The equation arrives as a word of signed integers (`intWord z = [z < 0] ++
natWord |z|`, the target first); the values can be far beyond any unary register, so a residue is computed from the
binary digits (least significant first) with unary registers below `p`: `modW` reads one integer and leaves
`((±z) mod p).toNat` in a register. Main declarations: `bval`, `bval_natBits`, `emod_toNat` (the residue from `|z|`
and the sign), `incModW`, `addLoopW`, `modW`, **`modW_spec`**. Paper quantity: the reduced coefficients `a_i` and the
residue `r₀` of row `(g, p)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Values -/

/-- The value of a bit list, least significant first. -/
def bval : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bval bs

theorem bval_fixed : ∀ (L v : ℕ), bval (WilliamsPublishedForm.fixedWidthNatBits L v) = v % 2 ^ L
  | 0, v => by simp [WilliamsPublishedForm.fixedWidthNatBits, bval, Nat.mod_one]
  | L + 1, v => by
    have ih := bval_fixed L (v / 2)
    have e : WilliamsPublishedForm.fixedWidthNatBits (L + 1) v =
        v.testBit 0 :: WilliamsPublishedForm.fixedWidthNatBits L (v / 2) := by
      simp only [WilliamsPublishedForm.fixedWidthNatBits, List.ofFn_succ, Fin.val_zero, Fin.val_succ]
      congr 1
      rw [List.ofFn_inj]
      funext b
      rw [Nat.testBit_succ]
    rw [e, bval, ih, pow_succ, Nat.mul_comm (2 ^ L) 2, Nat.mod_mul]
    have : (v.testBit 0).toNat = v % 2 := by
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]
    rw [this]

theorem natWord_split (v : ℕ) : RepairRepresentation.natWord v =
    List.replicate (natBitLength v) true ++ false :: WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v := rfl

theorem bval_natWord (v : ℕ) : bval (WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v) = v := by
  rw [bval_fixed]
  show v % 2 ^ (Nat.log 2 v + 1) = v
  exact Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) v)

theorem fixed_length (L v : ℕ) : (WilliamsPublishedForm.fixedWidthNatBits L v).length = L := by
  simp [WilliamsPublishedForm.fixedWidthNatBits]

/-- **The residue of `z` from `|z| mod p` and the sign.** -/
theorem emod_toNat (z : ℤ) (p : ℕ) (hp : 0 < p) :
    (z % (p : ℤ)).toNat = if z < 0 ∧ z.natAbs % p ≠ 0 then p - z.natAbs % p else z.natAbs % p := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hm : z.natAbs % p < p := Nat.mod_lt _ hp
  obtain ⟨n, hn⟩ : ∃ n, n = z.natAbs := ⟨_, rfl⟩
  rw [← hn] at hm ⊢
  obtain ⟨r, hr⟩ : ∃ r, r = n % p := ⟨_, rfl⟩
  rw [← hr] at hm ⊢
  have hdm : (n : ℤ) = (p : ℤ) * ((n / p : ℕ) : ℤ) + (r : ℤ) := by rw [hr]; exact_mod_cast (Nat.div_add_mod n p).symm
  by_cases hz : z < 0
  · have hzn : z = -(n : ℤ) := by rw [hn, Int.ofNat_natAbs_of_nonpos hz.le]; ring
    by_cases hr0 : r = 0
    · have hd : (p : ℤ) ∣ z := by
        rw [Int.natCast_dvd, ← hn]; exact Nat.dvd_of_mod_eq_zero (by rw [← hr, hr0])
      rw [Int.emod_eq_zero_of_dvd hd, if_neg (fun h => h.2 hr0), hr0]; rfl
    · rw [if_pos ⟨hz, hr0⟩]
      have h1 : z + (p : ℤ) * (((n / p : ℕ) : ℤ) + 1) = ((p - r : ℕ) : ℤ) := by
        rw [hzn, hdm, Nat.cast_sub hm.le]; ring
      have key : z % (p : ℤ) = ((p - r : ℕ) : ℤ) := by
        rw [← Int.add_mul_emod_self_left z (p : ℤ) (((n / p : ℕ) : ℤ) + 1), h1]
        exact Int.emod_eq_of_lt (by positivity) (by omega)
      rw [key, Int.toNat_natCast]
  · rw [if_neg (fun h => hz h.1)]
    have e : z = (n : ℤ) := by rw [hn, Int.natAbs_of_nonneg (by omega)]
    rw [e, hr, ← Int.natCast_mod, Int.toNat_natCast]

/-! ## Unary residues -/

section Prog
variable {ns nr : ℕ} (cap : ℕ)

/-- `X := (X + 1) mod p`, keeping `XD = p − X`. -/
def incModW (X XD : Fin nr) : WM ns nr := .seq (.dec XD) (.seq (.inc X) (.ifr XD .skip (WM.move X XD)))

theorem incMod_spec (X XD : Fin nr) (hX : X ≠ XD) (p x : ℕ) (σ : WState ns nr) (hx : σ.val X = x)
    (hd : σ.val XD = p - x) (hxp : x < p) (hpc : p ≤ cap) :
    WExec cap (incModW X XD) σ ((σ.setv X ((x + 1) % p)).setv XD (p - (x + 1) % p)) (7 * p + 8) := by
  have d1 := WExec.dec (cap := cap) XD σ (by omega)
  have d2 := WExec.inc (cap := cap) X (σ.setv XD (σ.val XD - 1)) (by simp [Function.update_apply, hX, hx]; omega)
  by_cases hlt : x + 1 < p
  · have d3 : WExec cap (WM.ifr XD .skip (WM.move X XD)) ((σ.setv XD (σ.val XD - 1)).setv X
        ((σ.setv XD (σ.val XD - 1)).val X + 1)) ((σ.setv XD (σ.val XD - 1)).setv X
        ((σ.setv XD (σ.val XD - 1)).val X + 1)) 1 :=
      WExec.ifrT (r := XD) (Q := WM.move X XD) (by simp [Function.update_apply, Ne.symm hX, hd]; omega) (WExec.skip _)
    refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext r; by_cases h1 : r = X
    · subst h1; simp [Function.update_apply, hX, hx, Nat.mod_eq_of_lt hlt]
    · by_cases h2 : r = XD
      · subst h2; simp [Function.update_apply, Ne.symm hX, hd, Nat.mod_eq_of_lt hlt]; omega
      · simp [Function.update_apply, h1, h2]
  · have hxe : x + 1 = p := by omega
    have d3 := wmove_spec cap X XD hX (x + 1) ((σ.setv XD (σ.val XD - 1)).setv X ((σ.setv XD (σ.val XD - 1)).val X + 1))
      (by simp [Function.update_apply, hX, hx]) (by simp [Function.update_apply, hX, hx]; omega)
      (by simp [Function.update_apply, hX, Ne.symm hX, hx, hd]; omega)
    have d3' := WExec.ifrF (r := XD) (P := WM.skip) (by simp [Function.update_apply, Ne.symm hX, hd]; omega) d3
    refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3')) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext r; by_cases h1 : r = X
    · subst h1; simp [Function.update_apply, hX, hxe]
    · by_cases h2 : r = XD
      · subst h2; simp [Function.update_apply, hX, Ne.symm hX, hd, hx, hxe]; omega
      · simp [Function.update_apply, h1, h2]

/-- `X := (X + T) mod p`, `T` counted down to `0`. -/
def addLoopW (X XD T : Fin nr) : WM ns nr := .whr T (.seq (.dec T) (incModW X XD))

theorem addLoop_spec (X XD T : Fin nr) (hX : X ≠ XD) (hXT : X ≠ T) (hDT : XD ≠ T) (p : ℕ) (hpc : p ≤ cap) :
    ∀ (k : ℕ) (σ : WState ns nr) (x : ℕ), σ.val T = k → k ≤ cap → σ.val X = x → σ.val XD = p - x → x < p →
      WExec cap (addLoopW X XD T) σ (((σ.setv X ((x + k) % p)).setv XD (p - (x + k) % p)).setv T 0)
        (k * (7 * p + 12) + 1)
  | 0, σ, x, hk, _, hx, hd, hxp => by
    refine WExec.cast cap (WExec.whrF hk) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext r; by_cases h1 : r = T
    · subst h1; simp [Function.update_apply, Ne.symm hXT, Ne.symm hDT, hk]
    · by_cases h2 : r = XD
      · subst h2; simp [Function.update_apply, h1, Ne.symm hX, hd, Nat.mod_eq_of_lt hxp]
      · by_cases h3 : r = X
        · subst h3; simp [Function.update_apply, h1, h2, hx, Nat.mod_eq_of_lt hxp]
        · simp [Function.update_apply, h1, h2, h3]
  | k + 1, σ, x, hk, hc, hx, hd, hxp => by
    have d1 := WExec.dec (cap := cap) T σ (by omega)
    have d2 := incMod_spec cap X XD hX p x (σ.setv T (σ.val T - 1)) (by simp [Function.update_apply, hXT, hx])
      (by simp [Function.update_apply, hDT, hd]) hxp hpc
    have ih := addLoop_spec X XD T hX hXT hDT p hpc k (((σ.setv T (σ.val T - 1)).setv X ((x + 1) % p)).setv XD
      (p - (x + 1) % p)) ((x + 1) % p) (by simp [Function.update_apply, Ne.symm hXT, Ne.symm hDT, hk])
      (by omega) (by simp [Function.update_apply, hX]) (by simp) (Nat.mod_lt _ (by omega))
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d2) ih) ?_ (by ring_nf; omega)
    have hm : ((x + 1) % p + k) % p = (x + (k + 1)) % p := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; congr 1; ring
    refine WState.eq rfl rfl ?_ rfl
    funext r; by_cases h1 : r = T
    · subst h1; simp [Function.update_apply, Ne.symm hXT, Ne.symm hDT]
    · by_cases h2 : r = XD
      · subst h2; simp [Function.update_apply, h1, Ne.symm hX, hm]
      · by_cases h3 : r = X
        · subst h3; simp [Function.update_apply, h1, h2, hm]
        · simp [Function.update_apply, h1, h2, h3]

/-- `X := (X + Src) mod p` (`Src` copied into `T`, `U` scratch). -/
def addModW (X XD Src T U : Fin nr) : WM ns nr := .seq (Hash4.wcopyR Src T U) (addLoopW X XD T)

theorem addMod_spec (X XD Src T U : Fin nr) (hX : X ≠ XD) (hXT : X ≠ T) (hDT : XD ≠ T) (hST : Src ≠ T)
    (hSU : Src ≠ U) (hTU : T ≠ U) (p : ℕ) (hpc : p ≤ cap) (σ : WState ns nr) (x w : ℕ) (hT : σ.val T = 0)
    (hU : σ.val U = 0) (hw : σ.val Src = w) (hwc : w ≤ cap) (hx : σ.val X = x) (hd : σ.val XD = p - x) (hxp : x < p) :
    WExec cap (addModW X XD Src T U) σ (((σ.setv X ((x + w) % p)).setv XD (p - (x + w) % p)).setv T 0)
      (18 * w + 3 + 1 + (w * (7 * p + 12) + 1)) := by
  have d1 := Hash4.wcopyR_spec cap Src T U hST hSU hTU σ hT hU (by omega)
  rw [hw] at d1
  have d2 := addLoop_spec cap X XD T hX hXT hDT p hpc w (σ.setv T w) x (by simp) hwc
    (by simp [Function.update_apply, hXT, hx]) (by simp [Function.update_apply, hDT, hd]) hxp
  refine WExec.cast cap (WExec.seq d1 d2) ?_ le_rfl
  refine WState.eq rfl rfl ?_ rfl
  funext r; by_cases h1 : r = T
  · subst h1; simp [Function.update_apply, Ne.symm hXT, Ne.symm hDT]
  · simp [Function.update_apply, h1]

/-! ## One residue from binary digits -/

variable (E : Fin (ns + 1)) (Rg : Fin 10 ↪ Fin nr)

theorem rne {i j : Fin 10} (h : i ≠ j) : Rg i ≠ Rg j := Rg.injective.ne h

/-- One digit's step bound. -/
def bitCost (p : ℕ) : ℕ := 2 * (18 * p + 5 + p * (7 * p + 12)) + 8

theorem mod_step (p a w b v : ℕ) :
    ((a + b * w) % p + (w + w) % p * v) % p = (a + w * (b + 2 * v)) % p := by
  have h : ((a + b * w) % p + (w + w) % p * v) ≡ (a + b * w) + (w + w) * v [MOD p] :=
    Nat.ModEq.add (Nat.mod_modEq _ _) (Nat.ModEq.mul_right _ (Nat.mod_modEq _ _))
  rw [show (a + b * w) + (w + w) * v = a + w * (b + 2 * v) by ring] at h
  exact h

theorem pow_step (p w k : ℕ) : (w + w) % p * 2 ^ k % p = w * 2 ^ (k + 1) % p := by
  have h : (w + w) % p * 2 ^ k ≡ (w + w) * 2 ^ k [MOD p] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
  rw [show (w + w) * 2 ^ k = w * 2 ^ (k + 1) by ring] at h
  exact h

/-! ## One signed integer -/

/-- The result: `V := A`, or `V := p − A` when the value's sign is negative and `A ≠ 0`; `A`, `D` cleared. -/
def finW (neg : Bool) : WM ns nr :=
  if neg then
    .ifr (Rg 2) (.seq (WM.move (Rg 4) (Rg 1)) (WM.clear (Rg 5)))
      (.ifr (Rg 4) (.seq (WM.move (Rg 5) (Rg 1)) (WM.clear (Rg 4))) (WM.clear (Rg 5)))
  else
    .ifr (Rg 2) (.ifr (Rg 4) (.seq (WM.move (Rg 5) (Rg 1)) (WM.clear (Rg 4))) (WM.clear (Rg 5)))
      (.seq (WM.move (Rg 4) (Rg 1)) (WM.clear (Rg 5)))

/-- Steps 5–7: `D := p`, `W := 1 mod p`. -/
def initW : WM ns nr :=
  .seq (Hash4.wcopyR (Rg 0) (Rg 5) (Rg 9)) (.seq (Hash4.wcopyR (Rg 0) (Rg 7) (Rg 9)) (incModW (Rg 6) (Rg 7)))

/-- Steps 9–12: the result, `W`, `WD`, `S` cleared. -/
def tailW (neg : Bool) : WM ns nr :=
  .seq (finW Rg neg) (.seq (WM.clear (Rg 6)) (.seq (WM.clear (Rg 7)) (WM.clear (Rg 2))))

/-- Steps 5–7: `D := p`, `W := 1 mod p` (with `WD = p − W`). -/
theorem init_spec (p : ℕ) (hp : 1 ≤ p) (hpc : p ≤ cap) (τ : WState ns nr) (hP : τ.val (Rg 0) = p)
    (h5 : τ.val (Rg 5) = 0) (h6 : τ.val (Rg 6) = 0) (h7 : τ.val (Rg 7) = 0) (h9 : τ.val (Rg 9) = 0) :
    WExec cap (initW Rg) τ ((((τ.setv (Rg 5) p).setv (Rg 7) p).setv (Rg 6) (1 % p)).setv (Rg 7) (p - 1 % p))
      (43 * p + 16) := by
  have d1 := Hash4.wcopyR_spec cap (Rg 0) (Rg 5) (Rg 9) (rne Rg (by decide)) (rne Rg (by decide)) (rne Rg (by decide))
    τ h5 h9 (by omega)
  rw [hP] at d1
  have d2 := Hash4.wcopyR_spec cap (Rg 0) (Rg 7) (Rg 9) (rne Rg (by decide)) (rne Rg (by decide)) (rne Rg (by decide))
    (τ.setv (Rg 5) p) (by simp [Function.update_apply, rne Rg (show (7 : Fin 10) ≠ 5 by decide), h7])
    (by simp [Function.update_apply, rne Rg (show (9 : Fin 10) ≠ 5 by decide), h9])
    (by simp [Function.update_apply, rne Rg (show (0 : Fin 10) ≠ 5 by decide), hP]; omega)
  rw [show (τ.setv (Rg 5) p).val (Rg 0) = p by simp [Function.update_apply, rne Rg (show (0 : Fin 10) ≠ 5 by decide), hP]]
    at d2
  have d3 := incMod_spec cap (Rg 6) (Rg 7) (rne Rg (by decide)) p 0 ((τ.setv (Rg 5) p).setv (Rg 7) p)
    (by simp [Function.update_apply, rne Rg (show (6 : Fin 10) ≠ 7 by decide),
      rne Rg (show (6 : Fin 10) ≠ 5 by decide), h6]) (by simp) (by omega) hpc
  exact WExec.mono (WExec.seq d1 (WExec.seq d2 d3)) (by omega)

/-- The result register's value. -/
def resOf (p s a : ℕ) (neg : Bool) : ℕ := if (decide (s = 1) != neg) = true ∧ a ≠ 0 then p - a else a

/-- The result, by the three program paths. -/
theorem finW_spec (neg : Bool) (p : ℕ) (hpc : p ≤ cap) (ρ : WState ns nr) (s a : ℕ) (hs : s ≤ 1)
    (hS : ρ.val (Rg 2) = s) (hA : ρ.val (Rg 4) = a) (hD : ρ.val (Rg 5) = p - a) (ha : a < p)
    (hV : ρ.val (Rg 1) = 0) :
    WExec cap (finW Rg neg) ρ (((ρ.setv (Rg 1) (resOf p s a neg)).setv (Rg 4) 0).setv (Rg 5) 0) (10 * p + 6) := by
  have h14 := rne Rg (show (1 : Fin 10) ≠ 4 by decide)
  have h15 := rne Rg (show (1 : Fin 10) ≠ 5 by decide)
  have h45 := rne Rg (show (4 : Fin 10) ≠ 5 by decide)
  have pA : WExec cap (.seq (WM.move (Rg 4) (Rg 1)) (WM.clear (Rg 5))) ρ
      (((ρ.setv (Rg 1) a).setv (Rg 4) 0).setv (Rg 5) 0) (7 * p + 5) := by
    have m := wmove_spec cap (Rg 4) (Rg 1) (Ne.symm h14) a ρ hA (by omega) (by omega)
    rw [hV, hA, Nat.zero_add] at m
    have c := wclear_spec cap (Rg 5) (p - a) ((ρ.setv (Rg 4) 0).setv (Rg 1) a)
      (by simp [Function.update_apply, Ne.symm h15, Ne.symm h45, hD])
      (by simp [Function.update_apply, Ne.symm h15, Ne.symm h45, hD]; omega)
    refine WExec.mono (WExec.cast cap (WExec.seq m c) ?_ le_rfl) (by omega)
    rw [wsetv_comm ρ (0 : ℕ) a (Ne.symm h14)]
  have pD : WExec cap (.seq (WM.move (Rg 5) (Rg 1)) (WM.clear (Rg 4))) ρ
      (((ρ.setv (Rg 1) (p - a)).setv (Rg 4) 0).setv (Rg 5) 0) (7 * p + 5) := by
    have m := wmove_spec cap (Rg 5) (Rg 1) (Ne.symm h15) (p - a) ρ hD (by omega) (by omega)
    rw [hV, hD, Nat.zero_add] at m
    have c := wclear_spec cap (Rg 4) a ((ρ.setv (Rg 5) 0).setv (Rg 1) (p - a))
      (by simp [Function.update_apply, Ne.symm h14, h45, hA])
      (by simp [Function.update_apply, Ne.symm h14, h45, hA]; omega)
    refine WExec.mono (WExec.cast cap (WExec.seq m c) ?_ le_rfl) (by omega)
    rw [wsetv_comm ρ (0 : ℕ) (p - a) (Ne.symm h15), wsetv_comm _ (0 : ℕ) (0 : ℕ) (Ne.symm h45)]
  have p0 : WExec cap (WM.clear (Rg 5)) ρ (ρ.setv (Rg 5) 0) (3 * p + 1) :=
    WExec.mono (wclear_spec cap (Rg 5) (p - a) ρ hD (by omega)) (by omega)
  have eq0 : a = 0 → ((ρ.setv (Rg 1) 0).setv (Rg 4) 0).setv (Rg 5) 0 = ρ.setv (Rg 5) 0 := fun ha0 => by
    refine WState.eq rfl rfl ?_ rfl
    funext q
    by_cases q5 : q = Rg 5
    · subst q5; simp
    · by_cases q4 : q = Rg 4
      · subst q4; simp [Function.update_apply, q5, Ne.symm h14, hA, ha0]
      · by_cases q1 : q = Rg 1
        · subst q1; simp [Function.update_apply, q5, q4, hV]
        · simp [Function.update_apply, q5, q4, q1]
  cases neg
  · have e : (finW Rg false : WM ns nr) = .ifr (Rg 2) (.ifr (Rg 4) (.seq (WM.move (Rg 5) (Rg 1)) (WM.clear (Rg 4)))
        (WM.clear (Rg 5))) (.seq (WM.move (Rg 4) (Rg 1)) (WM.clear (Rg 5))) := rfl
    rw [e]
    by_cases hs0 : s = 0
    · have hr : resOf p s a false = a := by simp [resOf, hs0]
      rw [hr]
      exact WExec.mono (WExec.ifrF (by rw [hS, hs0]) pA) (by omega)
    · have hs1 : s = 1 := by omega
      by_cases ha0 : a = 0
      · have hr : resOf p s a false = 0 := by simp [resOf, ha0]
        rw [hr, eq0 ha0]
        exact WExec.mono (WExec.ifrT (by rw [hS, hs1]; decide) (WExec.ifrF (by rw [hA, ha0]) p0)) (by omega)
      · have hr : resOf p s a false = p - a := by simp [resOf, hs1, ha0]
        rw [hr]
        exact WExec.mono (WExec.ifrT (by rw [hS, hs1]; decide) (WExec.ifrT (by rw [hA]; exact ha0) pD)) (by omega)
  · have e : (finW Rg true : WM ns nr) = .ifr (Rg 2) (.seq (WM.move (Rg 4) (Rg 1)) (WM.clear (Rg 5)))
        (.ifr (Rg 4) (.seq (WM.move (Rg 5) (Rg 1)) (WM.clear (Rg 4))) (WM.clear (Rg 5))) := rfl
    rw [e]
    by_cases hs0 : s = 0
    · by_cases ha0 : a = 0
      · have hr : resOf p s a true = 0 := by simp [resOf, ha0]
        rw [hr, eq0 ha0]
        exact WExec.mono (WExec.ifrF (by rw [hS, hs0]) (WExec.ifrF (by rw [hA, ha0]) p0)) (by omega)
      · have hr : resOf p s a true = p - a := by simp [resOf, hs0, ha0]
        rw [hr]
        exact WExec.mono (WExec.ifrF (by rw [hS, hs0]) (WExec.ifrT (by rw [hA]; exact ha0) pD)) (by omega)
    · have hs1 : s = 1 := by omega
      have hr : resOf p s a true = a := by simp [resOf, hs1]
      rw [hr]
      exact WExec.mono (WExec.ifrT (by rw [hS, hs1]; decide) pA) (by omega)

/-- Steps 9–12: the result, then `W`, `WD`, `S` cleared. -/
theorem tail_spec (neg : Bool) (p : ℕ) (hpc : p ≤ cap) (ρ : WState ns nr) (s a w : ℕ) (hs : s ≤ 1)
    (hS : ρ.val (Rg 2) = s) (hA : ρ.val (Rg 4) = a) (hD : ρ.val (Rg 5) = p - a) (ha : a < p)
    (hV : ρ.val (Rg 1) = 0) (hW : ρ.val (Rg 6) = w) (hWD : ρ.val (Rg 7) = p - w) (hw : w < p) :
    WExec cap (tailW Rg neg) ρ
      ((((((ρ.setv (Rg 1) (resOf p s a neg)).setv (Rg 4) 0).setv (Rg 5) 0).setv (Rg 6) 0).setv (Rg 7) 0).setv
        (Rg 2) 0) (20 * p + 20) := by
  have d1 := finW_spec cap Rg neg p hpc ρ s a hs hS hA hD ha hV
  have n61 := rne Rg (show (6 : Fin 10) ≠ 1 by decide)
  have n64 := rne Rg (show (6 : Fin 10) ≠ 4 by decide)
  have n65 := rne Rg (show (6 : Fin 10) ≠ 5 by decide)
  have n71 := rne Rg (show (7 : Fin 10) ≠ 1 by decide)
  have n74 := rne Rg (show (7 : Fin 10) ≠ 4 by decide)
  have n75 := rne Rg (show (7 : Fin 10) ≠ 5 by decide)
  have n76 := rne Rg (show (7 : Fin 10) ≠ 6 by decide)
  have n21 := rne Rg (show (2 : Fin 10) ≠ 1 by decide)
  have n24 := rne Rg (show (2 : Fin 10) ≠ 4 by decide)
  have n25 := rne Rg (show (2 : Fin 10) ≠ 5 by decide)
  have n26 := rne Rg (show (2 : Fin 10) ≠ 6 by decide)
  have n27 := rne Rg (show (2 : Fin 10) ≠ 7 by decide)
  have c6 := wclear_spec cap (Rg 6) w (((ρ.setv (Rg 1) (resOf p s a neg)).setv (Rg 4) 0).setv (Rg 5) 0)
    (by simp [Function.update_apply, n61, n64, n65, hW]) (by simp [Function.update_apply, n61, n64, n65, hW]; omega)
  have c7 := wclear_spec cap (Rg 7) (p - w)
    ((((ρ.setv (Rg 1) (resOf p s a neg)).setv (Rg 4) 0).setv (Rg 5) 0).setv (Rg 6) 0)
    (by simp [Function.update_apply, n71, n74, n75, n76, hWD])
    (by simp [Function.update_apply, n71, n74, n75, n76, hWD]; omega)
  have c2 := wclear_spec cap (Rg 2) s
    (((((ρ.setv (Rg 1) (resOf p s a neg)).setv (Rg 4) 0).setv (Rg 5) 0).setv (Rg 6) 0).setv (Rg 7) 0)
    (by simp [Function.update_apply, n21, n24, n25, n26, n27, hS])
    (by simp [Function.update_apply, n21, n24, n25, n26, n27, hS]; omega)
  exact WExec.mono (WExec.seq d1 (WExec.seq c6 (WExec.seq c7 c2))) (by omega)

theorem drop_intWord (z : ℤ) (rest : List Bool) :
    (RepairRepresentation.intWord z ++ rest).drop (2 + natBitLength z.natAbs) =
      WilliamsPublishedForm.fixedWidthNatBits (natBitLength z.natAbs) z.natAbs ++ rest := by
  rw [show 2 + natBitLength z.natAbs = (natBitLength z.natAbs + 1) + 1 by ring]
  simp [RepairRepresentation.intWord, natWord_split, List.drop_append]

theorem intWord_length' (z : ℤ) : (RepairRepresentation.intWord z).length = 2 * natBitLength z.natAbs + 2 := by
  simp [RepairRepresentation.intWord, natWord_split, fixed_length]; ring

theorem res_eq (z : ℤ) (p : ℕ) (hp : 0 < p) (neg : Bool) :
    resOf p (decide (z < 0)).toNat (z.natAbs % p) neg = ((if neg then -z else z) % (p : ℤ)).toNat := by
  rw [emod_toNat _ p hp]
  have hn : (if neg then -z else z).natAbs = z.natAbs := by cases neg <;> simp
  rw [hn]
  unfold resOf
  by_cases h0 : z.natAbs % p = 0
  · simp [h0]
  · have hz : z ≠ 0 := by rintro rfl; simp at h0
    cases neg <;> by_cases hlt : z < 0 <;> simp [hlt, h0] <;> omega

end Prog

end NearCubicWires.WireExponent3_5.FinalPass.ThrCore
