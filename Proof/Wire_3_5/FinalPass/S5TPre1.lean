import Proof.Wire_3_5.FinalPass.HashSeed

/-! # S5-THR, part 1: sentinel words and the unary product (the front's junk-free count, P3:3170-3181)

The final pass's front phase starts from the framed input alone (`fpEntry`) and must leave every scratch tape all
`false`; its register programs need register tapes of a capacity polynomial in `|fpIn|`. This module builds, with
register-free word programs (`WM ns nr` using no register), unary words in the sentinel form `sent c = 0 1^c`, whose
leading `0` lets a head return to cell `0` without a counter:

* `sent`, `read_sent`; `rewLoop_spec`, **`rewSent_spec`** (a head back from the end of `sent c` to `0`);
* `fillOnes_spec`, **`innerW_spec`** (the ones of `sent b` appended to a stream, the head back at `0`);
* `outerW_spec`, **`mulW_spec`**: `sent a`, `sent b` ↦ `sent (a·b)` on a blank stream, every head back at `0`.

Paper quantity of the main types: the front's register capacity `W = (|fpIn|+2)^D` (its unary count). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Sentinel words -/

/-- A unary word with a leading sentinel: `0 1^c`. -/
def sent (c : ℕ) : List Bool := false :: List.replicate c true

theorem sent_length (c : ℕ) : (sent c).length = c + 1 := by simp [sent]

theorem read_sent (c i : ℕ) : readTapeBit (sent c) i = decide (1 ≤ i ∧ i ≤ c) := by
  unfold readTapeBit sent
  cases i with
  | zero => simp
  | succ i =>
    rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs with h <;> simp <;> omega

theorem appW_seth (σ : WState ns nr) {Y T : Fin (ns + 1)} (h : Y ≠ T) (x : ℕ) (u : List Bool) :
    appW (σ.seth T x) Y u = (appW σ Y u).seth T x := by
  apply WState.eq
  · funext j
    by_cases hjY : j = Y
    · subst hjY; simp [Function.update_apply, h]
    · by_cases hjT : j = T
      · subst hjT; simp [Function.update_apply, hjY]
      · simp [Function.update_apply, hjY, hjT]
  · rfl
  · rfl
  · rfl

theorem appW_sh_ne (σ : WState ns nr) {Y T : Fin (ns + 1)} (h : T ≠ Y) (u : List Bool) :
    (appW σ Y u).sh T = σ.sh T := by simp [Function.update_apply, h]

/-! ## Back to the sentinel -/

theorem rewLoop_spec (S : Fin (ns + 1)) (c : ℕ) : ∀ (p : ℕ) (σ : WState ns nr), σ.st S = sent c → σ.sh S = p →
    p ≤ c → WExec cap (.whs S (.bwd S)) σ (σ.seth S 0) (3 * p + 1)
  | 0, σ, hs, hp, _ => by
    have hb : wbit σ S = false := by unfold wbit; rw [hs, hp, read_sent]; simp
    have e : σ.seth S 0 = σ := by rw [← hp, HashSeed.seth_same]
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | p + 1, σ, hs, hp, hc => by
    have hb : wbit σ S = true := by unfold wbit; rw [hs, hp, read_sent]; simp; omega
    have h1 := WExec.bwd (cap := cap) S σ
    have ih := rewLoop_spec S c p (σ.seth S (σ.sh S - 1)) (by simpa using hs) (by simp; omega) (by omega)
    refine WExec.cast cap (WExec.whsT hb h1 ih) (by rw [wseth_seth]) (by omega)

/-- From the end of `sent c` back to cell `0`. -/
def rewSent (S : Fin (ns + 1)) : WM ns nr := .seq (.bwd S) (.whs S (.bwd S))

theorem rewSent_spec (S : Fin (ns + 1)) (c : ℕ) (σ : WState ns nr) (hs : σ.st S = sent c) (hp : σ.sh S = c + 1) :
    WExec cap (rewSent S) σ (σ.seth S 0) (3 * c + 3) := by
  have h1 := WExec.bwd (cap := cap) S σ
  rw [hp, Nat.add_sub_cancel] at h1
  have h2 := rewLoop_spec cap S c c (σ.seth S c) (by simpa using hs) (by simp) le_rfl
  refine WExec.cast cap (WExec.seq h1 h2) (by rw [wseth_seth]) (by omega)

/-! ## One factor's ones -/

/-- The ones of `sent b` (from cell `1`) appended to `Y`. -/
def fillOnes (T Y : Fin (ns + 1)) : WM ns nr := .whs T (.seq (emit1 Y true) (.fwd T))

theorem fillOnes_spec (T Y : Fin (ns + 1)) (hTY : T ≠ Y) (b : ℕ) : ∀ (k : ℕ) (σ : WState ns nr),
    σ.st T = sent b → σ.sh T + k = b + 1 → 1 ≤ σ.sh T → σ.sh Y = (σ.st Y).length →
    WExec cap (fillOnes T Y) σ ((appW σ Y (List.replicate k true)).seth T (b + 1)) (7 * k + 1)
  | 0, σ, hs, hp, _, hY => by
    have hb : wbit σ T = false := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e : (appW σ Y (List.replicate 0 true)).seth T (b + 1) = σ := by
      rw [List.replicate_zero, appW_nil σ Y hY, show b + 1 = σ.sh T by omega, HashSeed.seth_same]
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | k + 1, σ, hs, hp, h1, hY => by
    have hb : wbit σ T = true := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e1 := emit1_spec cap Y true σ hY
    have e2 := WExec.fwd (cap := cap) T (appW σ Y [true])
    rw [appW_sh_ne σ hTY] at e2
    have ih := fillOnes_spec T Y hTY b k ((appW σ Y [true]).seth T (σ.sh T + 1))
      (by simp [Function.update_apply, hTY, hs]) (by simp; omega) (by simp)
      (by simp [Function.update_apply, Ne.symm hTY])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) ih) ?_ (by omega)
    rw [appW_seth _ (Ne.symm hTY), appW_appW, wseth_seth, List.replicate_succ]
    rfl

/-- **One factor**: from `sent b` at cell `0`, its ones appended to `Y`, the head back at `0`. -/
def innerW (T Y : Fin (ns + 1)) : WM ns nr := .seq (.fwd T) (.seq (fillOnes T Y) (rewSent T))

theorem innerW_spec (T Y : Fin (ns + 1)) (hTY : T ≠ Y) (b : ℕ) (σ : WState ns nr) (hs : σ.st T = sent b)
    (hp : σ.sh T = 0) (hY : σ.sh Y = (σ.st Y).length) :
    WExec cap (innerW T Y) σ (appW σ Y (List.replicate b true)) (10 * b + 7) := by
  have e1 := WExec.fwd (cap := cap) T σ
  rw [hp] at e1
  have e2 := fillOnes_spec cap T Y hTY b b (σ.seth T (0 + 1)) (by simpa using hs) (by simp; omega) (by simp)
    (by simp [Function.update_apply, Ne.symm hTY, hY])
  have e3 := rewSent_spec cap T b ((appW (σ.seth T (0 + 1)) Y (List.replicate b true)).seth T (b + 1))
    (by simp [Function.update_apply, hTY, hs]) (by simp)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  rw [wseth_seth, appW_seth _ (Ne.symm hTY), wseth_seth]
  have h := HashSeed.seth_same (appW σ Y (List.replicate b true)) T
  rw [appW_sh_ne σ hTY, hp] at h
  exact h

/-! ## The product -/

/-- The loop over the first factor's ones. -/
def outerW (X T Y : Fin (ns + 1)) : WM ns nr := .whs X (.seq (innerW T Y) (.fwd X))

theorem outerW_spec (X T Y : Fin (ns + 1)) (hXT : X ≠ T) (hXY : X ≠ Y) (hTY : T ≠ Y) (a b : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.st X = sent a → σ.sh X + k = a + 1 → 1 ≤ σ.sh X → σ.st T = sent b →
      σ.sh T = 0 → σ.sh Y = (σ.st Y).length →
      WExec cap (outerW X T Y) σ ((appW σ Y (List.replicate (k * b) true)).seth X (a + 1)) (k * (10 * b + 11) + 1)
  | 0, σ, hs, hp, _, _, _, hY => by
    have hb : wbit σ X = false := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e : (appW σ Y (List.replicate (0 * b) true)).seth X (a + 1) = σ := by
      rw [Nat.zero_mul, List.replicate_zero, appW_nil σ Y hY, show a + 1 = σ.sh X by omega, HashSeed.seth_same]
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | k + 1, σ, hs, hp, h1, hT, hTp, hY => by
    have hb : wbit σ X = true := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e1 := innerW_spec cap T Y hTY b σ hT hTp hY
    have e2 := WExec.fwd (cap := cap) X (appW σ Y (List.replicate b true))
    rw [appW_sh_ne σ hXY] at e2
    have ih := outerW_spec X T Y hXT hXY hTY a b k ((appW σ Y (List.replicate b true)).seth X (σ.sh X + 1))
      (by simp [Function.update_apply, hXY, hs]) (by simp; omega) (by simp)
      (by simp [Function.update_apply, hXT, hTY, hT]) (by simp [Function.update_apply, Ne.symm hXT, hTY, hTp])
      (by simp [Function.update_apply, Ne.symm hXY])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) ih) ?_ ?_
    · rw [appW_seth _ (Ne.symm hXY), appW_appW, wseth_seth, ← List.replicate_add]
      congr 3; ring
    · have : (k + 1) * (10 * b + 11) = k * (10 * b + 11) + (10 * b + 11) := by ring
      omega

/-- **The unary product**: `Y := sent (a·b)` from `X = sent a`, `T = sent b`, every head back at `0`. -/
def mulW (X T Y : Fin (ns + 1)) : WM ns nr :=
  .seq (emit1 Y false) (.seq (.fwd X) (.seq (outerW X T Y) (.seq (rewSent X) (rewSent Y))))

/-- The product's cost. -/
def mulCost (a b : ℕ) : ℕ := 3 + 1 + (1 + 1 + ((a * (10 * b + 11) + 1) + 1 + ((3 * a + 3) + 1 + (3 * (a * b) + 3))))

theorem mulW_spec (X T Y : Fin (ns + 1)) (hXT : X ≠ T) (hXY : X ≠ Y) (hTY : T ≠ Y) (a b : ℕ) (σ : WState ns nr)
    (hX : σ.st X = sent a) (hXh : σ.sh X = 0) (hT : σ.st T = sent b) (hTh : σ.sh T = 0) (hY : σ.st Y = [])
    (hYh : σ.sh Y = 0) :
    WExec cap (mulW X T Y) σ (σ.sets Y (sent (a * b))) (mulCost a b) := by
  have e1 := emit1_spec cap Y false σ (by rw [hY, hYh]; rfl)
  have e2 := WExec.fwd (cap := cap) X (appW σ Y [false])
  rw [appW_sh_ne σ hXY, hXh] at e2
  have e3 := outerW_spec cap X T Y hXT hXY hTY a b a ((appW σ Y [false]).seth X (0 + 1))
    (by simp [Function.update_apply, hXY, hX]) (by simp; omega) (by simp)
    (by simp [Function.update_apply, hXT, hTY, hT]) (by simp [Function.update_apply, Ne.symm hXT, hTY, hTh])
    (by simp [Function.update_apply, Ne.symm hXY])
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = (appW ((appW σ Y [false]).seth X (0 + 1)) Y (List.replicate (a * b) true)).seth X
      (a + 1) := ⟨_, rfl⟩
  rw [← hτ] at e3
  have e4 := rewSent_spec cap X a τ (by rw [hτ]; simp [Function.update_apply, hXY, hX]) (by rw [hτ]; simp)
  have e5 := rewSent_spec cap Y (a * b) (τ.seth X 0)
    (by rw [hτ]; simp [Function.update_apply, hY, sent])
    (by rw [hτ]; simp [Function.update_apply, Ne.symm hXY, hY, hYh]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by unfold mulCost; omega)
  rw [hτ]
  apply WState.eq
  · funext j
    by_cases hjY : j = Y
    · subst hjY; simp [Function.update_apply, Ne.symm hXY, hYh]
    · by_cases hjX : j = X
      · subst hjX; simp [Function.update_apply, hjY, hXh]
      · simp [Function.update_apply, hjY, hjX]
  · funext j
    by_cases hjY : j = Y
    · subst hjY; simp [Function.update_apply, hY, sent]
    · simp [Function.update_apply, hjY]
  · rfl
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.S5T
