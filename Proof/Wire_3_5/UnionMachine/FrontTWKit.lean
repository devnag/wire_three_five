import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.UnionMachine.RoundParse

/-! # C6 front, U5: the table writer's stream kit (register language)

The union machine writes each call's table entry by copying fields it already holds on streams (P3:3685-3691;
: the request writer copies framed fields): the setup's and the carriers' codes (framed items, one per
atom or variable), the guessed atoms' codes (the witness's raw fields), and the fixed head and tail of every request
word. This module gives the stream moves those copies need, in C5's register language (`WM`, `WExec`):

* `cloop K T body` (**`cloop_spec`**): run `body` `K` times, restoring `K`;
* `rewB s B T` (**`rewB_spec`**): return a stream to its start, for any head `≤ B`;
* `fwdK s K T` (**`fwdK_spec`**): move a head `K` cells forward;
* `skipFr`/`copyFr` (**`skipFr_spec`**, **`copyFr_spec`**): skip or copy one framed item `frame w` (the copy appends
  `marks w` to the output);
* `skipFrK` (**`skipFrK_spec`**): skip `K` framed items;
* `emitOnes` (**`emitOnes_spec`**): append `1^M` raw.

Paper quantity of the main statements: the fields of a call's word, as the machine moves over them. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## A counted loop that restores its counter -/

/-- `K` rounds of `body`, counted up in `T` and moved back into `K`. -/
def cloop (K T : Fin nr) (body : WM ns nr) : WM ns nr :=
  .seq (.whr K (.seq (.dec K) (.seq (.inc T) body))) (WM.move T K)

/-- **The counted loop**: from `K = n`, `T = 0` and the family `F j` of the states after `j` rounds (the body does
not read or write `K`, `T`), `K` and `T` end as they began. -/
theorem cloop_spec (K T : Fin nr) (hKT : K ≠ T) (body : WM ns nr) (n c : ℕ) (F : ℕ → WState ns nr) (hcap : n ≤ cap)
    (hbody : ∀ j < n, WExec cap body (((F j).setv K (n - j - 1)).setv T (j + 1))
      (((F (j + 1)).setv K (n - j - 1)).setv T (j + 1)) c) :
    WExec cap (cloop K T body) (((F 0).setv K n).setv T 0) (((F n).setv K n).setv T 0)
      (n * (c + 8) + 1 + 1 + (7 * n + 1)) := by
  set G : ℕ → WState ns nr := fun j => ((F j).setv K (n - j)).setv T j with hG
  have hGK : ∀ j ≤ n, (G j).val K = n - j := fun j _ => by simp [G, Function.update_of_ne hKT]
  have hstep : ∀ j < n, WExec cap (.seq (.inc T) body) ((G j).setv K (n - j - 1)) (G (j + 1)) (c + 4) := by
    intro j hj
    have e1 : (G j).setv K (n - j - 1) = ((F j).setv K (n - j - 1)).setv T j := by
      simp only [G]
      rw [wsetv_comm _ _ _ (Ne.symm hKT), wsetv_setv]
    have hT : (((F j).setv K (n - j - 1)).setv T j).val T < cap := by simp; omega
    have h1 := WExec.inc (cap := cap) T _ hT
    rw [show (((F j).setv K (n - j - 1)).setv T j).val T + 1 = j + 1 by simp, wsetv_setv] at h1
    have h2 := hbody j hj
    have e2 : G (j + 1) = ((F (j + 1)).setv K (n - j - 1)).setv T (j + 1) := by
      simp only [G]; rw [show n - (j + 1) = n - j - 1 by omega]
    rw [e1, e2]
    exact WExec.mono (WExec.seq h1 h2) (by omega)
  have hl := Round.wloop cap K (.seq (.inc T) body) (c + 4) n G hGK hcap hstep
  have hG0 : G 0 = ((F 0).setv K n).setv T 0 := by simp [G]
  rw [hG0] at hl
  have hmv := wmove_spec cap T K (Ne.symm hKT) n (G n) (by simp [G]) (by simp [G]; omega)
    (by simp [G, Function.update_of_ne hKT]; omega)
  have e3 : ((G n).setv T 0).setv K ((G n).val K + (G n).val T) = ((F n).setv K n).setv T 0 := by
    simp only [G]
    apply WState.eq <;> try rfl
    funext j
    by_cases hjT : j = T
    · subst hjT; simp [Function.update_of_ne (Ne.symm hKT)]
    · by_cases hjK : j = K
      · subst hjK; simp [Function.update_of_ne hKT]
      · simp [Function.update_of_ne hjT, Function.update_of_ne hjK]
  rw [e3] at hmv
  exact WExec.mono (WExec.seq hl hmv) (le_of_eq (by ring))

/-! ## Rewinding and moving by a count -/

/-- Step a stream back `B` cells (stopping at its start), restoring `B`. -/
def rewB (s : Fin (ns + 1)) (B T : Fin nr) : WM ns nr := cloop B T (.bwd s)

/-- **Rewinding**: a head at most `B` returns to `0`; `B` and `T` end as they began (`T = 0`). -/
theorem rewB_spec (s : Fin (ns + 1)) (B T : Fin nr) (hBT : B ≠ T) (σ : WState ns nr) (hT : σ.val T = 0)
    (hs : σ.sh s ≤ σ.val B) (hcap : σ.val B ≤ cap) :
    WExec cap (rewB s B T) σ (σ.seth s 0) (9 * σ.val B + 3 + 7 * σ.val B) := by
  set n := σ.val B with hn
  have h := cloop_spec cap B T hBT (.bwd s) n 1 (fun j => σ.seth s (σ.sh s - j)) hcap (by
    intro j _
    have hb := WExec.bwd (cap := cap) s (((σ.seth s (σ.sh s - j)).setv B (n - j - 1)).setv T (j + 1))
    refine WExec.cast cap hb ?_ le_rfl
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = s
    · subst hi; simp; omega
    · simp [Function.update_of_ne hi])
  have e0 : ((σ.seth s (σ.sh s - 0)).setv B n).setv T 0 = σ := by
    apply WState.eq <;> try rfl
    · funext i; by_cases hi : i = s
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = T
      · subst hi; simp [hT]
      · by_cases hi' : i = B
        · subst hi'; simp [Function.update_of_ne hi, hn]
        · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  have e1 : ((σ.seth s (σ.sh s - n)).setv B n).setv T 0 = σ.seth s 0 := by
    apply WState.eq <;> try rfl
    · funext i; by_cases hi : i = s
      · subst hi; simp; omega
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = T
      · subst hi; simp [hT]
      · by_cases hi' : i = B
        · subst hi'; simp [Function.update_of_ne hi, hn]
        · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  rw [e0, e1] at h
  exact WExec.mono h (by omega)

/-- Move a head `K` cells forward, restoring `K`. -/
def fwdK (s : Fin (ns + 1)) (K T : Fin nr) : WM ns nr := cloop K T (.fwd s)

theorem fwdK_spec (s : Fin (ns + 1)) (K T : Fin nr) (hKT : K ≠ T) (σ : WState ns nr) (hT : σ.val T = 0)
    (hcap : σ.val K ≤ cap) :
    WExec cap (fwdK s K T) σ (σ.seth s (σ.sh s + σ.val K)) (9 * σ.val K + 3 + 7 * σ.val K) := by
  set n := σ.val K with hn
  have h := cloop_spec cap K T hKT (.fwd s) n 1 (fun j => σ.seth s (σ.sh s + j)) hcap (by
    intro j _
    have hb := WExec.fwd (cap := cap) s (((σ.seth s (σ.sh s + j)).setv K (n - j - 1)).setv T (j + 1))
    refine WExec.cast cap hb ?_ le_rfl
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = s
    · subst hi; simp; omega
    · simp [Function.update_of_ne hi])
  have e0 : ((σ.seth s (σ.sh s + 0)).setv K n).setv T 0 = σ := by
    apply WState.eq <;> try rfl
    · funext i; by_cases hi : i = s
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = T
      · subst hi; simp [hT]
      · by_cases hi' : i = K
        · subst hi'; simp [Function.update_of_ne hi, hn]
        · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  have e1 : ((σ.seth s (σ.sh s + n)).setv K n).setv T 0 = σ.seth s (σ.sh s + n) := by
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = T
    · subst hi; simp [hT]
    · by_cases hi' : i = K
      · subst hi'; simp [Function.update_of_ne hi, hn]
      · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  rw [e0, e1] at h
  exact WExec.mono h (by omega)

/-! ## Framed items -/

theorem frame_length (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih]; ring

theorem read_frame_mark (pre w rest : List Bool) (k : ℕ) (hk : k < w.length) :
    readTapeBit (pre ++ frame w ++ rest) (pre.length + 2 * k) = true := by
  induction w generalizing pre k with
  | nil => simp at hk
  | cons b w ih =>
    cases k with
    | zero => simp [frame, readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_right]
    | succ k =>
      have e1 : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by simp [frame]
      have e2 : pre.length + 2 * (k + 1) = (pre ++ [true, b]).length + 2 * k := by simp; ring
      rw [e1, e2]
      exact ih _ k (by simp at hk; omega)

theorem read_frame_bit (pre w rest : List Bool) (k : ℕ) (hk : k < w.length) :
    readTapeBit (pre ++ frame w ++ rest) (pre.length + 2 * k + 1) = w.getD k false := by
  induction w generalizing pre k with
  | nil => simp at hk
  | cons b w ih =>
    cases k with
    | zero => simp [frame, readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_right]
    | succ k =>
      have e1 : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by simp [frame]
      have e2 : pre.length + 2 * (k + 1) + 1 = (pre ++ [true, b]).length + 2 * k + 1 := by simp; ring
      rw [e1, e2, List.getD_cons_succ]
      exact ih _ k (by simp at hk; omega)

theorem read_frame_end (pre w rest : List Bool) :
    readTapeBit (pre ++ frame w ++ rest) (pre.length + 2 * w.length) = false := by
  induction w generalizing pre with
  | nil => simp [frame, readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_append_right]
  | cons b w ih =>
    have e1 : pre ++ frame (b :: w) ++ rest = (pre ++ [true, b]) ++ frame w ++ rest := by simp [frame]
    have e2 : pre.length + 2 * (b :: w).length = (pre ++ [true, b]).length + 2 * w.length := by simp; ring
    rw [e1, e2]
    exact ih _

/-- Skip one framed item: over its pairs, then its end mark. -/
def skipFr (s : Fin (ns + 1)) : WM ns nr := .seq (.whs s (.seq (.fwd s) (.fwd s))) (.fwd s)

theorem skipFr_loop (s : Fin (ns + 1)) (pre w rest : List Bool) :
    ∀ j, j ≤ w.length → ∀ σ : WState ns nr, σ.st s = pre ++ frame w ++ rest → σ.sh s = pre.length + 2 * j →
      WExec cap (.whs s (.seq (.fwd s) (.fwd s))) σ (σ.seth s (pre.length + 2 * w.length)) (5 * (w.length - j) + 1) := by
  intro j
  induction h : w.length - j generalizing j with
  | zero =>
    intro hj σ hst hsh
    have hjw : j = w.length := by omega
    subst hjw
    have e : σ.seth s (pre.length + 2 * w.length) = σ := by
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = s
      · subst hi; simp [hsh]
      · simp [Function.update_of_ne hi]
    rw [e]
    exact WExec.whsF (by simp only [wbit, hst, hsh]; exact read_frame_end pre w rest)
  | succ m ih =>
    intro hj σ hst hsh
    have hlt : j < w.length := by omega
    have h1 := WExec.fwd (cap := cap) s σ
    have h2 := WExec.fwd (cap := cap) s (σ.seth s (σ.sh s + 1))
    have h3 := ih (j + 1) (by omega) (by omega) ((σ.seth s (σ.sh s + 1)).seth s ((σ.seth s (σ.sh s + 1)).sh s + 1))
      (by simp [hst]) (by simp [hsh]; ring)
    have e : ((σ.seth s (σ.sh s + 1)).seth s ((σ.seth s (σ.sh s + 1)).sh s + 1)).seth s (pre.length + 2 * w.length) =
        σ.seth s (pre.length + 2 * w.length) := by
      rw [wseth_seth, wseth_seth]
    rw [e] at h3
    exact WExec.mono (WExec.whsT (by simp only [wbit, hst, hsh]; exact read_frame_mark pre w rest j hlt)
      (WExec.seq h1 h2) h3) (by omega)

/-- **Skipping a framed item**: the head moves from its start to just past it. -/
theorem skipFr_spec (s : Fin (ns + 1)) (pre w rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ frame w ++ rest) (hsh : σ.sh s = pre.length) :
    WExec cap (skipFr s) σ (σ.seth s (pre.length + (frame w).length)) (5 * w.length + 3) := by
  have h1 := skipFr_loop cap s pre w rest 0 (Nat.zero_le _) σ hst (by simp [hsh])
  have h2 := WExec.fwd (cap := cap) s (σ.seth s (pre.length + 2 * w.length))
  rw [wseth_seth] at h2
  refine WExec.mono (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl) (by omega)
  congr 1
  simp [frame_length]; ring

/-- Copy one framed item's pairs to the output (as `marks w`), then step past its end mark. -/
def copyFr (s o : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.whs s (.seq (.fwd s) (.seq (.ifs s (emitPair o OP true) (emitPair o OP false)) (.fwd s)))) (.fwd s)

theorem copyFr_loop (s o : Fin (ns + 1)) (hso : s ≠ o) (OP : Fin nr) (pre w rest : List Bool) :
    ∀ j, j ≤ w.length → ∀ σ : WState ns nr, σ.st s = pre ++ frame w ++ rest → σ.sh s = pre.length + 2 * j →
      σ.sh o = (σ.st o).length → σ.val OP + 2 * (w.length - j) ≤ cap →
      WExec cap (.whs s (.seq (.fwd s) (.seq (.ifs s (emitPair o OP true) (emitPair o OP false)) (.fwd s)))) σ
        ((appendO σ o OP (marks (w.drop j))).seth s (pre.length + 2 * w.length)) (22 * (w.length - j) + 1) := by
  intro j
  induction h : w.length - j generalizing j with
  | zero =>
    intro hj σ hst hsh ho hc
    have hjw : j = w.length := by omega
    subst hjw
    have e : (appendO σ o OP (marks (w.drop w.length))).seth s (pre.length + 2 * w.length) = σ := by
      rw [List.drop_length, show marks ([] : List Bool) = [] from rfl, appendO_nil]
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = s
      · subst hi; simp [hsh]
      · simp [Function.update_of_ne hi]
    rw [e]
    exact WExec.whsF (by simp only [wbit, hst, hsh]; exact read_frame_end pre w rest)
  | succ m ih =>
    intro hj σ hst hsh ho hc
    have hlt : j < w.length := by omega
    set b := w.getD j false with hb
    have h1 := WExec.fwd (cap := cap) s σ
    set σ1 := σ.seth s (σ.sh s + 1) with hσ1
    have hbit : wbit σ1 s = b := by
      simp only [wbit, σ1, WState.seth_st, WState.seth_sh, Function.update_self, hst, hsh]
      exact read_frame_bit pre w rest j hlt
    have ho1 : σ1.sh o = (σ1.st o).length := by simp [σ1, Function.update_of_ne (Ne.symm hso), ho]
    have h2 : WExec cap (.ifs s (emitPair o OP true) (emitPair o OP false)) σ1 (appendO σ1 o OP [true, b]) 16 := by
      cases hbv : b
      · exact WExec.ifsF (by rw [hbit, hbv]) (emitPair_spec cap o OP false σ1 ho1 (by simp [σ1]; omega))
      · exact WExec.ifsT (by rw [hbit, hbv]) (emitPair_spec cap o OP true σ1 ho1 (by simp [σ1]; omega))
    set σ2 := appendO σ1 o OP [true, b] with hσ2
    have h3 := WExec.fwd (cap := cap) s σ2
    set σ3 := σ2.seth s (σ2.sh s + 1) with hσ3
    have hst3 : σ3.st s = pre ++ frame w ++ rest := by
      simp [σ3, σ2, σ1, Function.update_of_ne hso, hst]
    have hsh3 : σ3.sh s = pre.length + 2 * (j + 1) := by
      simp [σ3, σ2, σ1, Function.update_of_ne hso, hsh]; ring
    have ho3 : σ3.sh o = (σ3.st o).length := by
      simp [σ3, σ2, σ1, Function.update_of_ne (Ne.symm hso), ho]
    have hc3 : σ3.val OP + 2 * m ≤ cap := by
      simp [σ3, σ2, σ1]; omega
    have h4 := ih (j + 1) (by omega) (by omega) σ3 hst3 hsh3 ho3 hc3
    have hdrop : w.drop j = b :: w.drop (j + 1) := by
      rw [hb, List.getD_eq_getElem _ _ hlt]
      exact List.drop_eq_getElem_cons hlt
    have e : (appendO σ3 o OP (marks (w.drop (j + 1)))).seth s (pre.length + 2 * w.length) =
        (appendO σ o OP (marks (w.drop j))).seth s (pre.length + 2 * w.length) := by
      rw [hdrop]
      apply WState.eq
      · funext i
        by_cases hi : i = s
        · subst hi; simp
        · by_cases hio : i = o
          · subst hio; simp [σ3, σ2, σ1, Function.update_of_ne hi, Function.update_of_ne (Ne.symm hso), marks]
            ring
          · simp [σ3, σ2, σ1, Function.update_of_ne hi, Function.update_of_ne hio]
      · funext i
        by_cases hio : i = o
        · subst hio; simp [σ3, σ2, σ1, Function.update_of_ne (Ne.symm hso), marks]
        · simp [σ3, σ2, σ1, Function.update_of_ne hio]
      · funext i
        by_cases hi : i = OP
        · subst hi; simp [σ3, σ2, σ1, marks]; ring
        · simp [σ3, σ2, σ1, Function.update_of_ne hi]
      · simp [σ3, σ2, σ1]
    rw [e] at h4
    exact WExec.mono (WExec.whsT (by simp only [wbit, hst, hsh]; exact read_frame_mark pre w rest j hlt)
      (WExec.seq h1 (WExec.seq h2 h3)) h4) (by omega)

/-- **Copying a framed item**: `marks w` is appended to the output; the source head moves past the item. -/
theorem copyFr_spec (s o : Fin (ns + 1)) (hso : s ≠ o) (OP : Fin nr) (pre w rest : List Bool) (σ : WState ns nr)
    (hst : σ.st s = pre ++ frame w ++ rest) (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP + 2 * w.length ≤ cap) :
    WExec cap (copyFr s o OP) σ ((appendO σ o OP (marks w)).seth s (pre.length + (frame w).length))
      (22 * w.length + 3) := by
  have h1 := copyFr_loop cap s o hso OP pre w rest 0 (Nat.zero_le _) σ hst (by simp [hsh]) ho (by simpa using hc)
  rw [List.drop_zero] at h1
  have h2 := WExec.fwd (cap := cap) s ((appendO σ o OP (marks w)).seth s (pre.length + 2 * w.length))
  rw [wseth_seth] at h2
  refine WExec.mono (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl) (by omega)
  congr 1
  simp [frame_length]; ring

/-- The framed items' word. -/
def frItems (ws : List (List Bool)) : List Bool := (ws.map frame).flatten

theorem frItems_split (ws : List (List Bool)) (k : ℕ) (hk : k < ws.length) :
    frItems ws = frItems (ws.take k) ++ frame (ws.getD k []) ++ frItems (ws.drop (k + 1)) := by
  unfold frItems
  conv_lhs => rw [← List.take_append_drop k ws, List.drop_eq_getElem_cons hk]
  rw [List.getD_eq_getElem _ _ hk]
  simp only [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons, List.append_assoc]

/-- Skip `K` framed items, restoring `K`. -/
def skipFrK (s : Fin (ns + 1)) (K T : Fin nr) : WM ns nr := cloop K T (skipFr s)

/-- **Skipping `K` items** of a framed item list from its start. -/
theorem skipFrK_spec (s : Fin (ns + 1)) (K T : Fin nr) (hKT : K ≠ T) (ws : List (List Bool)) (rest : List Bool)
    (σ : WState ns nr) (hst : σ.st s = frItems ws ++ rest) (hsh : σ.sh s = 0) (hT : σ.val T = 0)
    (hK : σ.val K ≤ ws.length) (hcap : σ.val K ≤ cap) :
    WExec cap (skipFrK s K T) σ (σ.seth s (frItems (ws.take (σ.val K))).length)
      (σ.val K * (5 * (frItems ws).length + 3 + 8) + 1 + 1 + (7 * σ.val K + 1)) := by
  set n := σ.val K with hn
  have h := cloop_spec cap K T hKT (skipFr s) n (5 * (frItems ws).length + 3)
    (fun j => σ.seth s (frItems (ws.take j)).length) hcap (by
      intro j hj
      have hsplit := frItems_split ws j (by omega)
      have hsk := skipFr_spec cap s (frItems (ws.take j)) (ws.getD j []) (frItems (ws.drop (j + 1)) ++ rest)
        (((σ.seth s (frItems (ws.take j)).length).setv K (n - j - 1)).setv T (j + 1))
        (by simp [hst, hsplit, List.append_assoc]) (by simp)
      have hlen : (ws.getD j []).length ≤ (frItems ws).length := by
        rw [hsplit]; simp [frame_length]; omega
      refine WExec.mono (WExec.cast cap hsk ?_ le_rfl) (by omega)
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = s
      · subst hi
        simp only [WState.seth_sh, WState.setv_sh, Function.update_self]
        have e : ws.take (j + 1) = ws.take j ++ [ws.getD j []] := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.take_succ_eq_append_getElem (by omega)
        rw [e]; simp [frItems]
      · simp [Function.update_of_ne hi])
  have e0 : ((σ.seth s (frItems (ws.take 0)).length).setv K n).setv T 0 = σ := by
    apply WState.eq <;> try rfl
    · funext i; by_cases hi : i = s
      · subst hi; simp [hsh, frItems]
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = T
      · subst hi; simp [hT]
      · by_cases hi' : i = K
        · subst hi'; simp [Function.update_of_ne hi, hn]
        · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  have e1 : ((σ.seth s (frItems (ws.take n)).length).setv K n).setv T 0 = σ.seth s (frItems (ws.take n)).length := by
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = T
    · subst hi; simp [hT]
    · by_cases hi' : i = K
      · subst hi'; simp [Function.update_of_ne hi, hn]
      · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  rw [e0, e1] at h
  exact h

/-! ## Raw ones -/

/-- Append `1^M` raw, restoring `M`. -/
def emitOnes (o : Fin (ns + 1)) (OP M T : Fin nr) : WM ns nr := cloop M T (emitC o OP true)

theorem emitOnes_spec (o : Fin (ns + 1)) (OP M T : Fin nr) (hMT : M ≠ T) (hOM : OP ≠ M) (hOT : OP ≠ T)
    (σ : WState ns nr) (hT : σ.val T = 0) (ho : σ.sh o = (σ.st o).length) (hcap : σ.val OP + σ.val M ≤ cap)
    (hM : σ.val M ≤ cap) :
    WExec cap (emitOnes o OP M T) σ (appendO σ o OP (List.replicate (σ.val M) true)) (σ.val M * 15 + 3 + 7 * σ.val M) := by
  set n := σ.val M with hn
  have h := cloop_spec cap M T hMT (emitC o OP true) n 7 (fun j => appendO σ o OP (List.replicate j true)) hM (by
    intro j hj
    set τ := ((appendO σ o OP (List.replicate j true)).setv M (n - j - 1)).setv T (j + 1) with hτ
    have hτo : τ.sh o = (τ.st o).length := by simp [τ, ho]
    have hτc : τ.val OP < cap := by
      simp [τ, Function.update_of_ne hOT, Function.update_of_ne hOM]; omega
    have he := emitC_spec cap o OP true τ hτo hτc
    refine WExec.cast cap he ?_ le_rfl
    apply WState.eq
    · funext i; by_cases hi : i = o
      · subst hi; simp [τ, List.replicate_succ']; ring
      · simp [τ, Function.update_of_ne hi]
    · funext i; by_cases hi : i = o
      · subst hi; simp [τ, List.replicate_succ']
      · simp [τ, Function.update_of_ne hi]
    · funext i; by_cases hi : i = OP
      · subst hi; simp [τ, Function.update_of_ne hOT, Function.update_of_ne hOM]; ring
      · simp [τ, Function.update_apply, hi]
    · simp [τ])
  have e0 : ((appendO σ o OP (List.replicate 0 true)).setv M n).setv T 0 = σ := by
    rw [List.replicate_zero, appendO_nil]
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = T
    · subst hi; simp [hT]
    · by_cases hi' : i = M
      · subst hi'; simp [Function.update_of_ne hi, hn]
      · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  have e1 : ((appendO σ o OP (List.replicate n true)).setv M n).setv T 0 = appendO σ o OP (List.replicate n true) := by
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = T
    · subst hi; simp [hT, Function.update_of_ne (Ne.symm hOT)]
    · by_cases hi' : i = M
      · subst hi'; simp [Function.update_of_ne hi, Function.update_of_ne (Ne.symm hOM), hn]
      · simp [Function.update_of_ne hi, Function.update_of_ne hi']
  rw [e0, e1] at h
  exact WExec.mono h (by omega)


end NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
