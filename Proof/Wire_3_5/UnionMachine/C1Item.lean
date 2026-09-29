import Proof.Wire_3_5.UnionMachine.FrontTWKit
import Proof.Wire_3_5.Primitive.Writers.SymDecStreams

/-! # C6 front, the C1 dock: a variable's carrier code onto the carrier table's erased input (P3:3409-3410)

The writers' fold leaves the carriers' codes as a framed item list (`FrontTW.TWRel.crs`: the `X`-th item is
`natWord (Carrier.code (carrier X))`); the carrier table reads its input as `frame (natWord code)` on tape `0`.
Between rounds that tape is erased to `false`s, so the copy OVERWRITES a zero-padded stream:
* **`cpFrP_spec`**: a framed item's raw bits copied over `false`-padding (every write lands on a `false`);
* **`itemW_spec`**: `X := |XS|` (PA's `readUW`), `X` items skipped (`FrontTWKit.skipFrK`), the `X`-th item copied, `X`
  cleared: the output stream holds `frame w ++ 0^{k−|frame w|}`.

Paper quantity of the main type: the code of the carrier of one PCPP variable, as the carrier table reads it. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Item
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.RepairOrdinary.Streaming (marks)

theorem write_mid (u r : List Bool) (b : Bool) : writeTapeBit (u ++ false :: r) u.length b = u ++ b :: r := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [writeTapeBit, ih]

theorem frame_cons (b : Bool) (w : List Bool) : frame (b :: w) = true :: b :: frame w := rfl

theorem marks_cons (b : Bool) (w : List Bool) : marks (b :: w) = true :: b :: marks w := rfl

theorem marks_len (u : List Bool) : (marks u).length = 2 * u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => rw [marks_cons]; simp [ih]; ring

theorem frame_mk (w : List Bool) : frame w = marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [frame_cons, marks_cons, ih]; rfl

section Prog
variable {ns nr : ℕ} (cap : ℕ) (s o : Fin (ns + 1))

/-- One framed bit: `true` then the bit, over the padding. -/
def cpBody : WM ns nr :=
  .seq (.wr o true) (.seq (.fwd o) (.seq (.fwd s) (.seq (.ifs s (.wr o true) (.wr o false)) (.seq (.fwd o) (.fwd s)))))

/-- **Copy a framed item over `false`-padding.** -/
def cpFrP : WM ns nr := .seq (.whs s (cpBody s o)) (.seq (.wr o false) (.fwd o))

theorem cpLoop (hso : s ≠ o) : ∀ (w : List Bool) (σ : WState ns nr) (pre rest u : List Bool) (k : ℕ),
    σ.st s = pre ++ frame w ++ rest → σ.sh s = pre.length → σ.st o = u ++ List.replicate (2 * w.length + k) false →
    σ.sh o = u.length →
    WExec cap (.whs s (cpBody s o)) σ
      (((σ.sets o (u ++ marks w ++ List.replicate k false)).seth o (u.length + 2 * w.length)).seth s
        (pre.length + 2 * w.length)) (14 * w.length + 1)
  | [], σ, pre, rest, u, k, hs, hsh, ho, hoh => by
    have hb : wbit σ s = false := by
      unfold wbit; rw [hs, hsh]; simp [frame, marks, readTapeBit]
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at ho ⊢
    have e : ((σ.sets o (u ++ marks [] ++ List.replicate k false)).seth o u.length).seth s pre.length = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = s
        · subst hj; simp [hsh, Function.update_apply, hso]
        · by_cases hjo : j = o
          · subst hjo; simp [hoh, hj]
          · simp [hj, hjo]
      · funext j; by_cases hjo : j = o
        · subst hjo; simp [ho, marks]
        · simp [hjo]
      · rfl
      · rfl
    rw [e]; exact WExec.whsF hb
  | b :: w, σ, pre, rest, u, k, hs, hsh, ho, hoh => by
    have hb : wbit σ s = true := by
      unfold wbit; rw [hs, hsh, frame_cons]; simp [readTapeBit]
    have hso' : o ≠ s := fun h => hso h.symm
    -- write the mark
    have h1 := WExec.wr (cap := cap) o true σ
    set σ1 := σ.sets o (writeTapeBit (σ.st o) (σ.sh o) true) with hσ1
    have h2 := WExec.fwd (cap := cap) o σ1
    set σ2 := σ1.seth o (σ1.sh o + 1) with hσ2
    have h3 := WExec.fwd (cap := cap) s σ2
    set σ3 := σ2.seth s (σ2.sh s + 1) with hσ3
    have hb3 : wbit σ3 s = b := by
      simp only [wbit, hσ3, hσ2, hσ1, WState.seth_sh, WState.seth_st, WState.sets_st, WState.sets_sh,
        Function.update_apply, if_neg hso, if_true]
      rw [hs, hsh, frame_cons]; simp [readTapeBit]
    have ho1 : σ1.st o = u ++ true :: List.replicate (2 * w.length + 1 + k) false := by
      simp only [hσ1, WState.sets_st, Function.update_self]
      rw [ho, hoh, show 2 * (b :: w).length + k = (2 * w.length + 1 + k) + 1 by simp; ring,
        List.replicate_succ, write_mid]
    have h4 : WExec cap (.ifs s (.wr o true) (.wr o false)) σ3 (σ3.sets o (writeTapeBit (σ3.st o) (σ3.sh o) b)) 2 := by
      cases b
      · exact WExec.ifsF hb3 (WExec.wr o false σ3)
      · exact WExec.ifsT hb3 (WExec.wr o true σ3)
    set σ4 := σ3.sets o (writeTapeBit (σ3.st o) (σ3.sh o) b) with hσ4
    have h5 := WExec.fwd (cap := cap) o σ4
    set σ5 := σ4.seth o (σ4.sh o + 1) with hσ5
    have h6 := WExec.fwd (cap := cap) s σ5
    set σ6 := σ5.seth s (σ5.sh s + 1) with hσ6
    have ho4 : σ4.st o = (u ++ [true]) ++ b :: List.replicate (2 * w.length + k) false := by
      simp only [hσ4, hσ3, hσ2, WState.sets_st, WState.seth_st, WState.seth_sh, WState.sets_sh, Function.update_self]
      rw [ho1]
      have hl : σ1.sh o + 1 = (u ++ [true]).length := by
        simp only [hσ1, WState.sets_sh, hoh, List.length_append, List.length_singleton]
      simp only [Function.update_apply, if_neg hso', if_true]
      rw [hl, show u ++ true :: List.replicate (2 * w.length + 1 + k) false =
        (u ++ [true]) ++ false :: List.replicate (2 * w.length + k) false by
          simp [show 2 * w.length + 1 + k = (2 * w.length + k) + 1 by ring, List.replicate_succ]]
      rw [write_mid]
    have ih := cpLoop hso w σ6 (pre ++ [true, b]) rest (u ++ [true, b]) k
      (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso, hso']; rw [hs, frame_cons]; simp)
      (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso, hso', hsh])
      (by simp only [hσ6, hσ5, WState.seth_st, WState.sets_st]; rw [ho4]; simp)
      (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso, hso', hoh])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4
      (WExec.seq h5 h6))))) ih) ?_ (by simp; omega)
    apply WState.eq
    · funext j; by_cases hj : j = s
      · subst hj; simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hso, hsh]; omega
      · by_cases hjo : j = o
        · subst hjo; simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj, hoh]; omega
        · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hj, hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [marks_cons]
      · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hjo]
    · rfl
    · rfl

theorem cpFrP_spec (hso : s ≠ o) (w : List Bool) (σ : WState ns nr) (pre rest u : List Bool) (k : ℕ)
    (hs : σ.st s = pre ++ frame w ++ rest) (hsh : σ.sh s = pre.length)
    (ho : σ.st o = u ++ List.replicate (2 * w.length + 1 + k) false) (hoh : σ.sh o = u.length) :
    WExec cap (cpFrP s o) σ (((σ.sets o (u ++ frame w ++ List.replicate k false)).seth o
      (u.length + (frame w).length)).seth s (pre.length + 2 * w.length)) (14 * w.length + 6) := by
  have hso' : o ≠ s := fun h => hso h.symm
  have h1 := cpLoop cap s o hso w σ pre rest u (k + 1) hs hsh (by rw [ho]; congr 2; ring) hoh
  set σ1 := ((σ.sets o (u ++ marks w ++ List.replicate (k + 1) false)).seth o (u.length + 2 * w.length)).seth s
    (pre.length + 2 * w.length) with hσ1
  have h2 := WExec.wr (cap := cap) o false σ1
  have hw : writeTapeBit (σ1.st o) (σ1.sh o) false = u ++ marks w ++ List.replicate (k + 1) false := by
    simp only [hσ1, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh, Function.update_apply, if_neg hso',
      if_true]
    rw [show u.length + 2 * w.length = (u ++ marks w).length by simp [marks_len],
      List.replicate_succ, write_mid]
  have h3 := WExec.fwd (cap := cap) o (σ1.sets o (writeTapeBit (σ1.st o) (σ1.sh o) false))
  refine WExec.mono (WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ le_rfl) (by omega)
  rw [hw]
  apply WState.eq
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ1, Function.update_apply, hso]
    · by_cases hjo : j = o
      · subst hjo; simp [hσ1, Function.update_apply, hj, FrontTWKit.frame_length]; omega
      · simp [hσ1, Function.update_apply, hj, hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ1, frame_mk, List.replicate_succ]
    · simp [hσ1, Function.update_apply, hjo]
  · rfl
  · rfl

end Prog

/-! ## The item stage (layout `WState 2 2`: `SRC = 0`, `OUT = 1`, `XS = 2`; `K = 0`, `T = 1`) -/

/-- **The `X`-th item onto the erased input**, `X = |XS|`. -/
def itemW : WM 2 2 :=
  .seq (PrimAsm.SymDec.readUW 2 0) (.seq (skipFrK 0 0 1) (.seq (cpFrP 0 1) (WM.clear 0)))

/-- The item stage's cost. -/
def itemC (x L : ℕ) : ℕ := 7 * x + 1 + (x * (5 * L + 3 + 8) + 1 + 1 + (7 * x + 1)) + 14 * L + 6 + 3 * x + 10

theorem itemW_spec (cap : ℕ) (σ : WState 2 2) (ws : List (List Bool)) (rest : List Bool) (x k : ℕ)
    (hsrc : σ.st 0 = frItems ws ++ rest) (hout : σ.st 1 = List.replicate k false) (hxs : σ.st 2 = List.replicate x true)
    (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hx : x < ws.length)
    (hk : 2 * (ws.getD x []).length + 1 ≤ k) (hcap : x ≤ cap) :
    ∃ τ : WState 2 2, WExec cap itemW σ τ (itemC x (frItems ws).length) ∧
      τ.st 0 = σ.st 0 ∧ τ.st 1 = frame (ws.getD x []) ++ List.replicate (k - (2 * (ws.getD x []).length + 1)) false ∧
      τ.st 2 = σ.st 2 ∧ (∀ r, τ.val r = 0) ∧ τ.cell = σ.cell := by
  set w := ws.getD x [] with hw
  have hsplit := frItems_split ws x hx
  have hwl : w.length ≤ (frItems ws).length := by
    have := congrArg List.length hsplit
    simp only [List.length_append, FrontTWKit.frame_length] at this
    rw [hw]; omega
  -- 1. K := x
  have e1 := PrimAsm.SymDec.readU_spec cap 2 0 x 0 σ hxs (hsh 2) (hv 0) (by omega)
  set σ1 := (σ.seth 2 x).setv 0 (0 + x) with hσ1
  -- 2. skip x items
  have e2 := skipFrK_spec cap 0 0 1 (by decide) ws rest σ1 (by simp [hσ1, hsrc]) (by simp [hσ1, hsh 0])
    (by simp [hσ1, hv 1]) (by simp [hσ1]; omega) (by simp [hσ1]; omega)
  have v10 : σ1.val 0 = x := by simp [hσ1]
  rw [v10] at e2
  set σ2 := σ1.seth 0 (frItems (ws.take x)).length with hσ2
  -- 3. copy item x
  have e3 := cpFrP_spec cap 0 1 (by decide) w σ2 (frItems (ws.take x)) (frItems (ws.drop (x + 1)) ++ rest) [] (k - (2 * w.length + 1))
    (by simp [hσ2, hσ1, hsrc, hsplit, hw, List.append_assoc])
    (by simp [hσ2])
    (by simp [hσ2, hσ1, hout]; omega)
    (by simp [hσ2, hσ1, hsh 1])
  set σ3 := ((σ2.sets 1 ([] ++ frame w ++ List.replicate (k - (2 * w.length + 1)) false)).seth 1
    ([].length + (frame w).length)).seth 0 ((frItems (ws.take x)).length + 2 * w.length) with hσ3
  -- 4. K := 0
  have e4 := wclear_spec cap 0 x σ3 (by simp [hσ3, hσ2, hσ1]) (by simp [hσ3, hσ2, hσ1]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold itemC; omega
  · simp [hσ3, hσ2, hσ1]
  · simp [hσ3, hσ2, hσ1]
  · simp [hσ3, hσ2, hσ1]
  · intro r; fin_cases r
    · simp
    · simp [hσ3, hσ2, hσ1, hv 1]
  · simp [hσ3, hσ2, hσ1]

end NearCubicWires.WireExponent3_5.UnionMachine.C1Item
