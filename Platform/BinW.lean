import Platform.WMX
import Proof.Wire_3_5.UnionMachine.RegRatMul
import Proof.Wire_3_5.Foundations.OutMachineHalf
import Proof.Wire_3_5.UnionMachine.RoundDiv

/-! # K2 `BinW`: binary arithmetic on framed words

The near-cubic-gates paper machine model: "Arithmetic on polynomial-bit integers uses elementary multiword
algorithms." Numbers are proof 3's fixed-width framed words: `NumOn σ X W v` (`σ.st X = frame (binary W v)`, low bit
first, head `0`). Every operation is a `WMX` program with one spec `WXExec cap op σ τ cost`: the output value is
a function of the input values, every other stream/register is unchanged, every head and scratch register returns to
`0`, and the cost is linear (or quadratic for `mul`, `divmod`) in the width `W`. The scratch registers `F ≠ R` must be
`0` and `2W + 1 ≤ cap`.

Donors (proof 3, used verbatim through `wm`): `addB`, `incB`, `zeroB`, `oneB`, `subB`, `ltB`, `copyB`, `shlB`
(`UnionMachine.RegRat`), `mulB` (`RegRatMul`), `halfW` (`Out.Half`), and the generic bit pass `mapPass`.
New here: `shlc` (shift with carry in and out), `eq` (equality flag), `width` (the width `W` into a register).
`divmod` is in `Platform.BinWDiv`. -/

set_option autoImplicit false

namespace NearCubicGates.Close.Platform.BinW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.Platform
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Round (mapS_shl mapS_shl_carry mapS_keepA binary_mod)

variable {ns nr : ℕ}

/-! ## The number format -/

theorem setv_same {σ : WState ns nr} {r : Fin nr} {x : ℕ} (h : σ.val r = x) : σ.setv r x = σ := by
  rw [← h]; exact wsetv_same σ r

/-! ## Proof 3's operations as `WMX` instructions -/

section Facade
variable (cap W : ℕ) {A B : Fin (ns + 1)} {F R : Fin nr} (hAB : A ≠ B) (hFR : F ≠ R)

/-- `A := 0` (`B`: any width-`W` word). -/
def zero (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (zeroB A B F R)
/-- `A := 1`. -/
def one (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (oneB A B F R)
/-- `A := a + 1`. -/
def inc (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (incB A B F R)
/-- `A := a + b`. -/
def add (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (addB A B F R)
/-- `A := a − b` (`b ≤ a`). -/
def sub (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (subB A B F R)
/-- `F := [a < b]`. -/
def lt (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (ltB A B F R)
/-- `A := b`. -/
def copy (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (copyB A B F R)
/-- `A := 2a mod 2^W`. -/
def shl (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (shlB A B F R)
/-- `A := ⌊a / 2⌋`. -/
def half (A : Fin (ns + 1)) (R : Fin nr) : WMX ns nr := .wm (NearCubicWires.WireExponent3_5.FinalPass.Out.Half.halfW A R)
/-- `C := a·b` (scratch word `S` ends at `0`, scratch registers `F R G`). -/
def mul (A B C S : Fin (ns + 1)) (F R G : Fin nr) : WMX ns nr := .wm (mulB A B C S F R G)

end Facade

/-! ## Shift with carry in and carry out -/

/-- `A := 2a + c mod 2^W` with carry-in `c = F`, and `F :=` the bit shifted out. -/
def shlcW (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := mapPass shOut shNxt A B F R

/-- `A := 2a + c mod 2^W`, `F :=` the bit shifted out (`F` holds the carry-in `c` before). -/
def shlc (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (shlcW A B F R)

/-! ## Equality -/

/-- The equality pass's state: still equal so far. -/
def eqN (a b c : Bool) : Bool := c && (a == b)

theorem mapS_eq : ∀ (as bs : List Bool) (c : Bool), as.length = bs.length →
    (mapS keepA eqN as bs c).2 = (c && decide (as = bs))
  | [], [], c, _ => by simp [mapS]
  | a :: as, b :: bs, c, h => by
    simp only [mapS]
    rw [mapS_eq as bs _ (by simpa using h)]
    cases a <;> cases b <;> cases c <;> simp [eqN]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- `F := [a = b]` (both words kept). -/
def eqW (A B : Fin (ns + 1)) (F R : Fin nr) : WM ns nr := .seq (.inc F) (mapPass keepA eqN A B F R)

/-- `F := [a = b]`. -/
def eq (A B : Fin (ns + 1)) (F R : Fin nr) : WMX ns nr := .wm (eqW A B F R)

/-! ## The width of a word into a register -/

/-- Walk the frame of `A`, counting its bits into `K` and `T`. -/
def widthLoop (A : Fin (ns + 1)) (K T : Fin nr) : WM ns nr :=
  .whs A (.seq (.fwd A) (.seq (.fwd A) (.seq (.inc K) (.inc T))))

/-- Walk back by `T`. -/
def backLoop (A : Fin (ns + 1)) (T : Fin nr) : WM ns nr := .whr T (.seq (.dec T) (.seq (.bwd A) (.bwd A)))

/-- `K := W`, the width of the word on `A` (scratch `T`). -/
def widthW (A : Fin (ns + 1)) (K T : Fin nr) : WM ns nr := .seq (widthLoop A K T) (backLoop A T)

section Width
variable (cap : ℕ) {A : Fin (ns + 1)} {K T : Fin nr} (hKT : K ≠ T)
include hKT

theorem widthLoop_spec (W a : ℕ) (hW : W ≤ cap) : ∀ (m k : ℕ) (σ : WState ns nr), k + m = W →
    σ.st A = frame (binary W a) → σ.sh A = 2 * k → σ.val K = k → σ.val T = k →
    WExec cap (widthLoop A K T) σ (((σ.seth A (2 * W)).setv K W).setv T W) (13 * m + 1)
  | 0, k, σ, hk, hA, hAh, hK, hT => by
    have hb : wbit σ A = false := by
      unfold wbit; rw [hA, hAh, show k = W by omega]; exact frame_end W a
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl
  | m + 1, k, σ, hk, hA, hAh, hK, hT => by
    have hb : wbit σ A = true := by
      unfold wbit; rw [hA, hAh]; exact frame_marker W a k (by omega)
    have h1 := WExec.fwd (cap := cap) A σ
    have h2 := WExec.fwd (cap := cap) A (σ.seth A (σ.sh A + 1))
    have h3 := WExec.inc (cap := cap) K ((σ.seth A (σ.sh A + 1)).seth A ((σ.seth A (σ.sh A + 1)).sh A + 1))
      (by simp; omega)
    set σ3 := ((σ.seth A (σ.sh A + 1)).seth A ((σ.seth A (σ.sh A + 1)).sh A + 1)) with hσ3
    have h4 := WExec.inc (cap := cap) T (σ3.setv K (σ3.val K + 1)) (by simp [hσ3, Ne.symm hKT]; omega)
    set τ := (σ3.setv K (σ3.val K + 1)).setv T ((σ3.setv K (σ3.val K + 1)).val T + 1) with hτ
    have ih := widthLoop_spec W a hW m (k + 1) τ (by omega) (by simp [hτ, hσ3, hA]) (by simp [hτ, hσ3, hAh]; omega)
      (by simp [hτ, hσ3, hKT, hK]) (by simp [hτ, hσ3, Ne.symm hKT, hT])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ih) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [hτ, hσ3, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext j; simp only [hτ, hσ3, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
    · rfl

omit hKT in
theorem backLoop_spec : ∀ (j : ℕ) (σ : WState ns nr), σ.val T = j → σ.sh A = 2 * j → j ≤ cap →
    WExec cap (backLoop A T) σ ((σ.setv T 0).seth A 0) (7 * j + 1)
  | 0, σ, hT, hAh, _ => by
    refine WExec.cast cap (WExec.whrF hT) ?_ (by omega)
    apply WState.eq
    · funext i; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext i; simp only [WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
  | j + 1, σ, hT, hAh, hj => by
    have h1 := WExec.dec (cap := cap) T σ (by omega)
    have h2 := WExec.bwd (cap := cap) A (σ.setv T (σ.val T - 1))
    have h3 := WExec.bwd (cap := cap) A ((σ.setv T (σ.val T - 1)).seth A ((σ.setv T (σ.val T - 1)).sh A - 1))
    set τ := ((σ.setv T (σ.val T - 1)).seth A ((σ.setv T (σ.val T - 1)).sh A - 1)).seth A
      (((σ.setv T (σ.val T - 1)).seth A ((σ.setv T (σ.val T - 1)).sh A - 1)).sh A - 1) with hτ
    have ih := backLoop_spec j τ (by simp [hτ, hT]) (by simp [hτ, hAh]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    apply WState.eq
    · funext i; simp only [hτ, WState.seth_sh, WState.setv_sh, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl
    · funext i; simp only [hτ, WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs with h <;> subst_vars <;> simp_all
    · rfl

/-- **`K := W`**, the width of the number on `A`; `T` scratch (`0` before and after). -/
theorem widthW_spec (W a : ℕ) (σ : WState ns nr) (hA : NumOn σ A W a) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (hW : W ≤ cap) : WExec cap (widthW A K T) σ (σ.setv K W) (20 * W + 3) := by
  have h1 := widthLoop_spec cap hKT W a hW W 0 σ (by omega) hA.1 (by simp [hA.2]) hK hT
  set τ := ((σ.seth A (2 * W)).setv K W).setv T W with hτ
  have h2 := backLoop_spec cap (A := A) (T := T) W τ (by simp [hτ]) (by simp [hτ]) hW
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext i; simp only [hτ, WState.seth_sh, WState.setv_sh, Function.update_apply]
    split_ifs with h <;> subst_vars <;> simp_all [hA.2]
  · rfl
  · funext i; simp only [hτ, WState.seth_val, WState.setv_val, Function.update_apply]
    split_ifs with h1 h2 <;> subst_vars <;> simp_all
  · rfl

end Width

/-- `K := W` (as a `WMX` instruction). -/
def width (A : Fin (ns + 1)) (K T : Fin nr) : WMX ns nr := .wm (widthW A K T)

theorem width_spec (cap : ℕ) {A : Fin (ns + 1)} {K T : Fin nr} (hKT : K ≠ T) (W a : ℕ) (σ : WState ns nr)
    (hA : NumOn σ A W a) (hK : σ.val K = 0) (hT : σ.val T = 0) (hW : W ≤ cap) :
    WXExec cap (width A K T) σ (σ.setv K W) (20 * W + 3) :=
  WXExec.wm (widthW_spec cap hKT W a σ hA hK hT hW)

/-! Programs are opaque to consumers: use the spec theorems. -/
attribute [irreducible] zero one inc add sub lt copy shl half mul shlcW shlc eqW eq widthW width

end NearCubicGates.Close.Platform.BinW
