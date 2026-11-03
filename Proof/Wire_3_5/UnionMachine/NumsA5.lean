import Proof.Wire_3_5.UnionMachine.NumsA2
import Proof.Wire_3_5.Primitive.Writers.UnaryPow

/-! # NW phase (a), part 5: the unary kit, continued

Phase (a) writes the data stage's unary inputs (`1^n`, `1^W`) and stashes the role registers as `1^v` on blank
streams; it loads constants; and it rewinds a stream whose head the SYM numbers program left unspecified, by a bound
on the head: a word program moves a head by at most its step count.

* `wtb_len`, `onesU`, **`onesU_spec`** (`R = v` ↦ `1^v` on the blank `O`, `R := 0`, the head back at `0`);
* `incK`, **`incK_spec`** (`R += k`);
* **`WExec.sh_le`** (every head ends within the steps of where it started).

Paper quantity: none (plumbing). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- Writing past the end appends. -/
theorem wtb_len (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.length_cons, writeTapeBit, ih, List.cons_append]

/-- `1^v` on the blank `O` from `R` (consumed), the moves counted in `P`, the head back at `0`. -/
def onesU (O : Fin (ns + 1)) (R P : Fin nr) : WM ns nr :=
  .seq (.whr R (.seq (.dec R) (.seq (.wr O true) (.seq (.fwd O) (.inc P))))) (WM.rewind O P)

theorem onesU_spec (O : Fin (ns + 1)) (R P : Fin nr) (hRP : R ≠ P) (v : ℕ) (σ : WState ns nr)
    (hO : σ.st O = []) (hh : σ.sh O = 0) (hR : σ.val R = v) (hP : σ.val P = 0) (hv : v ≤ cap) :
    WExec cap (onesU O R P) σ ((σ.sets O (List.replicate v true)).setv R 0) (v * (9 + 2) + 1 + 1 + (5 * v + 1)) := by
  have hPR := Ne.symm hRP
  let S : ℕ → WState ns nr := fun k =>
    (((σ.sets O (List.replicate k true)).seth O k).setv R (v - k)).setv P k
  have hS0 : S 0 = σ := by
    apply WState.eq
    · funext i
      by_cases hi : i = O
      · subst hi; simp [S, hh]
      · simp [S, Function.update_of_ne hi]
    · funext i
      by_cases hi : i = O
      · subst hi; simp [S, hO]
      · simp [S, Function.update_of_ne hi]
    · funext q
      by_cases h1 : q = P
      · subst h1; simp [S, hP]
      · by_cases h2 : q = R
        · subst h2; simp [S, hR, h1]
        · simp [S, Function.update_of_ne h1, Function.update_of_ne h2]
    · rfl
  have l1 := UnaryPow.flagLoop cap R (.seq (.dec R) (.seq (.wr O true) (.seq (.fwd O) (.inc P)))) 9 v S
    (fun k hk => by simp [S, hRP]; omega) (by simp [S, hRP])
    (fun k hk => by
      have h1 := WExec.dec (cap := cap) R (S k) (by simp [S, hRP]; omega)
      have h2 := WExec.wr (cap := cap) O true ((S k).setv R ((S k).val R - 1))
      have h3 := WExec.fwd (cap := cap) O (((S k).setv R ((S k).val R - 1)).sets O
        (writeTapeBit (((S k).setv R ((S k).val R - 1)).st O) (((S k).setv R ((S k).val R - 1)).sh O) true))
      have h4 := WExec.inc (cap := cap) P ((((S k).setv R ((S k).val R - 1)).sets O
        (writeTapeBit (((S k).setv R ((S k).val R - 1)).st O) (((S k).setv R ((S k).val R - 1)).sh O) true)).seth O
        ((((S k).setv R ((S k).val R - 1)).sets O
        (writeTapeBit (((S k).setv R ((S k).val R - 1)).st O) (((S k).setv R ((S k).val R - 1)).sh O) true)).sh O + 1))
        (by simp [S, hRP, hPR]; omega)
      refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
      have ew : writeTapeBit (List.replicate k true) k true = List.replicate (k + 1) true := by
        have := wtb_len (List.replicate k true) true
        rw [List.length_replicate] at this
        rw [this, List.replicate_succ']
      apply WState.eq
      · funext i
        by_cases hi : i = O
        · subst hi; simp [S]
        · simp [S, Function.update_of_ne hi]
      · funext i
        by_cases hi : i = O
        · subst hi; simp [S, ew]
        · simp [S, Function.update_of_ne hi]
      · funext q
        by_cases h1 : q = P
        · subst h1; simp [S, hPR]
        · by_cases h2 : q = R
          · subst h2; simp [S, hRP]; omega
          · simp [S, Function.update_of_ne h1, Function.update_of_ne h2]
      · rfl)
  rw [hS0] at l1
  have h2 := FinalPass.Tm.wrewind_spec cap O P v (S v) (by simp [S]) (by simp [S]; omega)
  refine WExec.cast cap (WExec.seq l1 h2) ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i = O
    · subst hi; simp [S, hh]
    · simp [S, Function.update_of_ne hi]
  · funext i
    by_cases hi : i = O
    · subst hi; simp [S]
    · simp [S, Function.update_of_ne hi]
  · funext q
    by_cases h1 : q = P
    · subst h1; simp [S, hPR, hP]
    · by_cases h2 : q = R
      · subst h2; simp [S, h1]
      · simp [S, Function.update_of_ne h1, Function.update_of_ne h2]
  · rfl

/-- `R += k`. -/
def incK (R : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (.inc R) (incK R k)

theorem incK_spec (R : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val R + k ≤ cap → WExec cap (incK R k) σ (σ.setv R (σ.val R + k)) (4 * k)
  | 0, σ, _ => by
    rw [Nat.add_zero, wsetv_same]
    exact WExec.skip σ
  | k + 1, σ, h => by
    have h1 := WExec.inc (cap := cap) R σ (by omega)
    have h2 := incK_spec R k (σ.setv R (σ.val R + 1)) (by simp; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    rw [wsetv_setv]
    simp only [WState.setv_val, Function.update_self]
    congr 1
    omega

/-- **A word program moves each head by at most its step count.** -/
theorem WExec.sh_le {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    ∀ i, τ.sh i ≤ σ.sh i + n := by
  induction h with
  | skip => intro i; omega
  | inc r σ hv => intro i; simp
  | dec r σ hv => intro i; simp
  | fwd j σ =>
    intro i
    simp only [WState.seth_sh, Function.update_apply]
    split_ifs with hij
    · subst hij; omega
    · omega
  | bwd j σ =>
    intro i
    simp only [WState.seth_sh, Function.update_apply]
    split_ifs with hij
    · subst hij; omega
    · omega
  | wr j b σ => intro i; simp
  | setc v σ => intro i; simp
  | seq _ _ ih1 ih2 => intro i; have := ih1 i; have := ih2 i; omega
  | ifrT _ _ ih => intro i; have := ih i; omega
  | ifrF _ _ ih => intro i; have := ih i; omega
  | ifsT _ _ ih => intro i; have := ih i; omega
  | ifsF _ _ ih => intro i; have := ih i; omega
  | whrF _ => intro i; omega
  | whrT _ _ _ ih1 ih2 => intro i; have := ih1 i; have := ih2 i; omega
  | whsF _ => intro i; omega
  | whsT _ _ _ ih1 ih2 => intro i; have := ih1 i; have := ih2 i; omega
  | mono _ hnm ih => intro i; have := ih i; omega

end Kit

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
