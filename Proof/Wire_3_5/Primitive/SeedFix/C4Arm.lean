import Proof.Wire_3_5.Primitive.SeedFix.C4Loop

/-! # SEEDFIX C4.L, the enumeration's entry bank: word writers (samp:printable P3:2977-3055)

The enumeration (`SeedFix.JLink.sampEnum_run`, "For every seed prefix [...] print the conditional objective",
P3:2910-2923) starts from its bank at counter value `0` (`JCtx.jt 0 S0 [] 0`): framed zero words of the counter's
fields, unary rulers, blank capacities, the child prefix. Each child builds that bank on blank scratch. This module has
the word programs that APPEND one such word to a blank stream and restore every register (`emitSt`): constant words
(`emitWord`), `x` copies of a word (`repWord`, PA's `Emit.repW`), the framed zero word `frame (0^x)` (`frameZ`), and
eight of them then `false` (`frames8`, the counter's alpha/digit/cell fields at `0`); `ucount` loads a unary ruler.

Paper quantity of the main types: the words of the enumeration's entry bank (`frame (0^x)`, `0^x`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Arm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec (reps)

section Writers
variable {ns nr : ℕ} (cap : ℕ)

/-- The state after appending `w` to stream `d` (head at its end), every register unchanged. -/
def emitSt (σ : WState ns nr) (d : Fin (ns + 1)) (w : List Bool) : WState ns nr :=
  (σ.sets d (σ.st d ++ w)).seth d (σ.sh d + w.length)

@[simp] theorem emitSt_st (σ : WState ns nr) (d : Fin (ns + 1)) (w : List Bool) :
    (emitSt σ d w).st = Function.update σ.st d (σ.st d ++ w) := by simp [emitSt]
@[simp] theorem emitSt_sh (σ : WState ns nr) (d : Fin (ns + 1)) (w : List Bool) :
    (emitSt σ d w).sh = Function.update σ.sh d (σ.sh d + w.length) := by simp [emitSt]
@[simp] theorem emitSt_val (σ : WState ns nr) (d : Fin (ns + 1)) (w : List Bool) :
    (emitSt σ d w).val = σ.val := by simp [emitSt]
@[simp] theorem emitSt_cell (σ : WState ns nr) (d : Fin (ns + 1)) (w : List Bool) :
    (emitSt σ d w).cell = σ.cell := by simp [emitSt]

theorem appendO_clear (σ : WState ns nr) (d : Fin (ns + 1)) (OP : Fin nr) (w : List Bool) (h : σ.val OP = 0) :
    (appendO σ d OP w).setv OP 0 = emitSt σ d w := by
  apply WState.eq
  · simp [emitSt, PrimAsm.WriteNat.appendO]
  · simp [emitSt, PrimAsm.WriteNat.appendO]
  · funext r; simp only [WState.setv_val, appendO_val, emitSt_val, Function.update_apply]
    split_ifs with h1 <;> subst_vars <;> simp_all
  · simp [emitSt, PrimAsm.WriteNat.appendO]

/-- A constant word, then the length register cleared. -/
def emitWord (d : Fin (ns + 1)) (OP : Fin nr) (w : List Bool) : WM ns nr :=
  .seq (PrimAsm.Emit.emitW d OP w) (WM.clear OP)

theorem emitWord_spec (d : Fin (ns + 1)) (OP : Fin nr) (w : List Bool) (σ : WState ns nr) (hOP : σ.val OP = 0)
    (hd : σ.sh d = (σ.st d).length) (hc : w.length ≤ cap) :
    WExec cap (emitWord d OP w) σ (emitSt σ d w) (8 * w.length + 1 + (3 * w.length + 1)) := by
  have h1 := PrimAsm.Emit.emitW_spec cap d OP w σ hd (by omega)
  have h2 := wclear_spec cap OP w.length (appendO σ d OP w) (by simp [hOP]) (by simp [hOP]; omega)
  rw [appendO_clear σ d OP w hOP] at h2
  exact WExec.seq h1 h2

/-- `x` copies of `u` (`x` from register `rX`, kept), through the counter `K` and the temporary `T`. -/
def repWord (d : Fin (ns + 1)) (OP K T rX : Fin nr) (u : List Bool) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR rX K T) (.seq (PrimAsm.Emit.repW d OP K u) (WM.clear OP))

theorem repWord_spec (d : Fin (ns + 1)) (OP K T rX : Fin nr) (hKO : K ≠ OP) (hXK : rX ≠ K) (hXT : rX ≠ T)
    (hKT : K ≠ T) (hXO : rX ≠ OP) (hTO : T ≠ OP) (u : List Bool) (x : ℕ) (σ : WState ns nr)
    (hX : σ.val rX = x) (hK : σ.val K = 0) (hT : σ.val T = 0) (hOP : σ.val OP = 0)
    (hd : σ.sh d = (σ.st d).length) (hc : x * u.length + x + 1 ≤ cap) :
    WExec cap (repWord d OP K T rX u) σ (emitSt σ d (reps x u))
      (18 * x + 3 + 1 + (x * (8 * u.length + 4) + 1 + 1 + (3 * (x * u.length) + 1))) := by
  have h1 := FinalPass.Hash4.wcopyR_spec cap rX K T hXK hXT hKT σ hK hT (by omega)
  rw [hX] at h1
  set σ1 := σ.setv K x with hσ1
  have h2 := PrimAsm.Emit.repW_spec cap d OP K hKO u x σ1 (by simp [σ1]) (by simp [σ1, hd])
    (by simp [σ1, Function.update_apply, Ne.symm hKO, hOP]; omega) (by omega)
  have hlen : (reps x u).length = x * u.length := by unfold reps; simp
  have h3 := wclear_spec cap OP (x * u.length) ((appendO σ1 d OP (reps x u)).setv K 0)
    (by simp [σ1, Function.update_apply, Ne.symm hKO, hOP, hlen]) (by simp [σ1, Function.update_apply, Ne.symm hKO, hOP, hlen]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ le_rfl
  apply WState.eq
  · simp [σ1, emitSt, PrimAsm.WriteNat.appendO]
  · simp [σ1, emitSt, PrimAsm.WriteNat.appendO]
  · funext r; simp only [WState.setv_val, appendO_val, emitSt_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp [σ1, emitSt, PrimAsm.WriteNat.appendO]

/-- Load a unary ruler `1^x` (stream `s`, head `0`, then a `false` or its end) into the zero register `r`. -/
def ucount (s : Fin (ns + 1)) (r : Fin nr) : WM ns nr := .whs s (.seq (.inc r) (.fwd s))

theorem ucount_spec (s : Fin (ns + 1)) (r : Fin nr) (x : ℕ) (tl : List Bool) (htl : tl.headD false = false) :
    ∀ (m k : ℕ) (σ : WState ns nr), k + m = x → σ.st s = List.replicate x true ++ tl → σ.sh s = k →
      σ.val r = k → x ≤ cap →
      WExec cap (ucount s r) σ ((σ.setv r x).seth s x) (m * 7 + 1) := by
  intro m
  induction m with
  | zero =>
    intro k σ hk hs hh hr hx
    have hb : wbit σ s = false := by
      simp only [wbit, hs, hh, readTapeBit]
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_replicate, show k - x = 0 by omega]
      cases tl <;> simp_all
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply]; split_ifs <;> subst_vars <;> simp_all
      all_goals omega
    · rfl
    · funext j; simp only [WState.seth_val, WState.setv_val, Function.update_apply]; split_ifs <;> subst_vars <;> simp_all
      all_goals omega
    · rfl
  | succ m ih =>
    intro k σ hk hs hh hr hx
    have hb : wbit σ s = true := by
      simp only [wbit, hs, hh, readTapeBit]
      rw [List.getD_append _ _ _ _ (by simp; omega)]
      simp [List.getElem?_replicate, show k < x by omega]
    have h1 := WExec.inc (cap := cap) r σ (by rw [hr]; omega)
    have h2 := WExec.fwd (cap := cap) s (σ.setv r (σ.val r + 1))
    have hrec := ih (k + 1) ((σ.setv r (σ.val r + 1)).seth s ((σ.setv r (σ.val r + 1)).sh s + 1)) (by omega)
      (by simp [hs]) (by simp [hh]) (by simp [hr]) hx
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) hrec) ?_ (by omega)
    apply WState.eq
    · funext j; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply]; split_ifs <;> simp_all
    · rfl
    · funext j; simp only [WState.seth_val, WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
    · rfl

end Writers

section Frames
variable {ns nr : ℕ} (cap : ℕ)

theorem reps_one_frame (x : ℕ) : reps x [true, false] ++ [false] = frame (List.replicate x false) :=
  (C4Rec.frame_rep_false x).symm

/-- The framed zero word `frame (0^x)`. -/
def frameZ (d : Fin (ns + 1)) (OP K T rX : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR rX K T) (.seq (PrimAsm.Emit.repW d OP K [true, false])
    (.seq (PrimAsm.Emit.emitW d OP [false]) (WM.clear OP)))

def frameZCost (x : ℕ) : ℕ := 18 * x + 3 + 1 + (x * (8 * 2 + 4) + 1 + 1 + (8 * 1 + 1 + (3 * (x * 2 + 1) + 1)))

theorem frameZ_spec (d : Fin (ns + 1)) (OP K T rX : Fin nr) (hKO : K ≠ OP) (hXK : rX ≠ K) (hXT : rX ≠ T)
    (hKT : K ≠ T) (hXO : rX ≠ OP) (hTO : T ≠ OP) (x : ℕ) (σ : WState ns nr)
    (hX : σ.val rX = x) (hK : σ.val K = 0) (hT : σ.val T = 0) (hOP : σ.val OP = 0)
    (hd : σ.sh d = (σ.st d).length) (hc : 3 * x + 3 ≤ cap) :
    WExec cap (frameZ d OP K T rX) σ (emitSt σ d (frame (List.replicate x false))) (frameZCost x) := by
  have h1 := FinalPass.Hash4.wcopyR_spec cap rX K T hXK hXT hKT σ hK hT (by omega)
  rw [hX] at h1
  set σ1 := σ.setv K x with hσ1
  have h2 := PrimAsm.Emit.repW_spec cap d OP K hKO [true, false] x σ1 (by simp [σ1]) (by simp [σ1, hd])
    (by simp [σ1, Function.update_apply, Ne.symm hKO, hOP]; omega) (by omega)
  have hlen : (reps x [true, false]).length = x * 2 := by unfold reps; simp
  set σ2 := (appendO σ1 d OP (reps x [true, false])).setv K 0 with hσ2
  have h3 := PrimAsm.Emit.emitW_spec cap d OP [false] σ2 (by simp [σ2, σ1, hd, hlen])
    (by simp [σ2, σ1, Function.update_apply, Ne.symm hKO, hOP, hlen]; omega)
  have h4 := wclear_spec cap OP (x * 2 + 1) (appendO σ2 d OP [false])
    (by simp [σ2, σ1, Function.update_apply, Ne.symm hKO, hOP, hlen])
    (by simp [σ2, σ1, Function.update_apply, Ne.symm hKO, hOP, hlen]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by unfold frameZCost; simp)
  rw [← reps_one_frame]
  apply WState.eq
  · simp [σ2, σ1, emitSt, PrimAsm.WriteNat.appendO, hlen]; ring
  · simp [σ2, σ1, emitSt, PrimAsm.WriteNat.appendO]
  · funext r
    by_cases h1 : r = OP
    · subst h1; simp [σ2, σ1, Function.update_apply, Ne.symm hKO, hOP]
    · by_cases h2 : r = K
      · subst h2; simp [σ2, σ1, Function.update_apply, hKO, hK]
      · simp [σ2, σ1, Function.update_apply, h1, h2]
  · simp [σ2, σ1, emitSt, PrimAsm.WriteNat.appendO]

theorem emitSt_append (σ : WState ns nr) (d : Fin (ns + 1)) (u v : List Bool) :
    emitSt (emitSt σ d u) d v = emitSt σ d (u ++ v) := by
  apply WState.eq
  · funext j; simp only [emitSt_sh, Function.update_apply, emitSt_st]; split_ifs <;> simp; ring
  · funext j; simp only [emitSt_st, Function.update_apply]; split_ifs <;> simp
  · simp
  · simp

/-- Eight framed zero words, then `false`: the counter's fields at `0`. -/
def frames8 (d : Fin (ns + 1)) (OP K T rX : Fin nr) : WM ns nr :=
  .seq (frameZ d OP K T rX) (.seq (frameZ d OP K T rX) (.seq (frameZ d OP K T rX) (.seq (frameZ d OP K T rX)
    (.seq (frameZ d OP K T rX) (.seq (frameZ d OP K T rX) (.seq (frameZ d OP K T rX) (.seq (frameZ d OP K T rX)
      (emitWord d OP [false]))))))))

def frames8Cost (x : ℕ) : ℕ := 8 * (frameZCost x + 1) + (8 * 1 + 1 + (3 * 1 + 1))

theorem frames8_spec (d : Fin (ns + 1)) (OP K T rX : Fin nr) (hKO : K ≠ OP) (hXK : rX ≠ K) (hXT : rX ≠ T)
    (hKT : K ≠ T) (hXO : rX ≠ OP) (hTO : T ≠ OP) (x : ℕ) (σ : WState ns nr)
    (hX : σ.val rX = x) (hK : σ.val K = 0) (hT : σ.val T = 0) (hOP : σ.val OP = 0)
    (hd : σ.sh d = (σ.st d).length) (hc : 3 * x + 3 ≤ cap) :
    WExec cap (frames8 d OP K T rX) σ
      (emitSt σ d (reps 8 (frame (List.replicate x false)) ++ [false])) (frames8Cost x) := by
  have step : ∀ (τ : WState ns nr), τ.val = σ.val → τ.sh d = (τ.st d).length →
      WExec cap (frameZ d OP K T rX) τ (emitSt τ d (frame (List.replicate x false))) (frameZCost x) := by
    intro τ hv hτ
    exact frameZ_spec cap d OP K T rX hKO hXK hXT hKT hXO hTO x τ (by rw [hv, hX]) (by rw [hv, hK])
      (by rw [hv, hT]) (by rw [hv, hOP]) hτ hc
  have hsh : ∀ (τ : WState ns nr) (w : List Bool), τ.sh d = (τ.st d).length →
      (emitSt τ d w).sh d = ((emitSt τ d w).st d).length := by
    intro τ w h; simp [h]
  set F := frame (List.replicate x false) with hF
  have s1 := step σ rfl hd
  have s2 := step (emitSt σ d F) (by simp) (hsh _ _ hd)
  rw [emitSt_append] at s2
  have s3 := step (emitSt σ d (F ++ F)) (by simp) (hsh _ _ hd)
  rw [emitSt_append] at s3
  have s4 := step (emitSt σ d (F ++ F ++ F)) (by simp) (hsh _ _ hd)
  rw [emitSt_append] at s4
  have s5 := step (emitSt σ d (F ++ F ++ F ++ F)) (by simp) (hsh _ _ hd)
  rw [emitSt_append] at s5
  have s6 := step (emitSt σ d (F ++ F ++ F ++ F ++ F)) (by simp) (hsh _ _ hd)
  rw [emitSt_append] at s6
  have s7 := step (emitSt σ d (F ++ F ++ F ++ F ++ F ++ F)) (by simp) (hsh _ _ hd)
  rw [emitSt_append] at s7
  have s8 := step (emitSt σ d (F ++ F ++ F ++ F ++ F ++ F ++ F)) (by simp) (hsh _ _ hd)
  rw [emitSt_append] at s8
  have s9 := emitWord_spec cap d OP [false] (emitSt σ d (F ++ F ++ F ++ F ++ F ++ F ++ F ++ F)) (by simp [hOP])
    (hsh _ _ hd) (by simp; omega)
  rw [emitSt_append] at s9
  have e : F ++ F ++ F ++ F ++ F ++ F ++ F ++ F ++ [false] = reps 8 F ++ [false] := by
    simp [reps, List.replicate_succ, List.append_assoc]
  rw [e] at s9
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 s9)))))))) rfl (by unfold frames8Cost; simp; omega)

end Frames

section Chain
variable {ns nr : ℕ} (cap : ℕ)

/-- A writer: a word program appending `w` to stream `d` at any state with the register valuation `V0`. -/
structure Wr (ns nr : ℕ) where
  d : Fin (ns + 1)
  P : WM ns nr
  w : List Bool
  c : ℕ

/-- The writer's contract under the invariant `Inv` (the register valuation, the sources). -/
def Wr.Ok (Inv : WState ns nr → Prop) (x : Wr ns nr) : Prop :=
  ∀ τ : WState ns nr, Inv τ → τ.sh x.d = (τ.st x.d).length → WExec cap x.P τ (emitSt τ x.d x.w) x.c

/-- The writers in sequence. -/
def seqWr : List (Wr ns nr) → WM ns nr
  | [] => .skip
  | x :: L => .seq x.P (seqWr L)

def costWr : List (Wr ns nr) → ℕ
  | [] => 1
  | x :: L => x.c + 1 + costWr L

/-- The state after the writers. -/
def runWr (σ : WState ns nr) (L : List (Wr ns nr)) : WState ns nr := L.foldl (fun τ x => emitSt τ x.d x.w) σ

theorem runWr_val (L : List (Wr ns nr)) : ∀ σ : WState ns nr, (runWr σ L).val = σ.val := by
  induction L with
  | nil => intro σ; rfl
  | cons x L ih => intro σ; simp only [runWr, List.foldl_cons]; rw [← runWr, ih]; simp

theorem runWr_other (L : List (Wr ns nr)) (i : Fin (ns + 1)) (hi : ∀ x ∈ L, x.d ≠ i) :
    ∀ σ : WState ns nr, (runWr σ L).st i = σ.st i ∧ (runWr σ L).sh i = σ.sh i := by
  induction L with
  | nil => intro σ; exact ⟨rfl, rfl⟩
  | cons x L ih =>
    intro σ
    simp only [runWr, List.foldl_cons]
    rw [← runWr]
    obtain ⟨h1, h2⟩ := ih (fun y hy => hi y (List.mem_cons_of_mem _ hy)) (emitSt σ x.d x.w)
    have hx : x.d ≠ i := hi x List.mem_cons_self
    refine ⟨h1.trans ?_, h2.trans ?_⟩ <;> simp [Function.update_apply, Ne.symm hx]

theorem seqWr_spec (Inv : WState ns nr → Prop) (L : List (Wr ns nr)) (hok : ∀ x ∈ L, x.Ok cap Inv)
    (hinv : ∀ x ∈ L, ∀ τ, Inv τ → Inv (emitSt τ x.d x.w)) (hnd : (L.map Wr.d).Nodup) :
    ∀ σ : WState ns nr, Inv σ → (∀ x ∈ L, σ.sh x.d = (σ.st x.d).length) →
      WExec cap (seqWr L) σ (runWr σ L) (costWr L) := by
  induction L with
  | nil => intro σ _ _; exact WExec.mono (WExec.skip (cap := cap) σ) (by simp [costWr])
  | cons x L ih =>
    intro σ hv hsh
    rw [List.map_cons, List.nodup_cons] at hnd
    have h1 := hok x List.mem_cons_self σ hv (hsh x List.mem_cons_self)
    have h2 := ih (fun y hy => hok y (List.mem_cons_of_mem _ hy)) (fun y hy => hinv y (List.mem_cons_of_mem _ hy))
      hnd.2 (emitSt σ x.d x.w) (hinv x List.mem_cons_self σ hv)
      (fun y hy => by
        have hne : x.d ≠ y.d := fun h => hnd.1 (h ▸ List.mem_map_of_mem hy)
        simp [Function.update_apply, Ne.symm hne, hsh y (List.mem_cons_of_mem _ hy)])
    exact WExec.seq h1 h2

theorem runWr_mem (L : List (Wr ns nr)) (hnd : (L.map Wr.d).Nodup) (x : Wr ns nr) (hx : x ∈ L) :
    ∀ σ : WState ns nr, (runWr σ L).st x.d = σ.st x.d ++ x.w := by
  induction L with
  | nil => exact absurd hx (by simp)
  | cons y L ih =>
    intro σ
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [runWr, List.foldl_cons]
    rw [← runWr]
    rcases List.mem_cons.mp hx with h | h
    · subst h
      have hno : ∀ z ∈ L, z.d ≠ x.d := fun z hz e => hnd.1 (e ▸ List.mem_map_of_mem hz)
      rw [(runWr_other L x.d hno (emitSt σ x.d x.w)).1]
      simp
    · rw [ih hnd.2 h (emitSt σ y.d y.w)]
      have hne : y.d ≠ x.d := fun e => hnd.1 (e ▸ List.mem_map_of_mem h)
      simp [Function.update_apply, Ne.symm hne]

end Chain

section Prefix
variable {ns nr : ℕ} (cap : ℕ)

/-- Walk a framed prefix on `S`, copying its bits to `D` as marked pairs and counting them in `rP`. -/
def pcopyL (S D : Fin (ns + 1)) (OP rP : Fin nr) : WM ns nr :=
  .whs S (.seq (.fwd S) (.seq (.ifs S (PrimAsm.WriteNat.emitPair D OP true) (PrimAsm.WriteNat.emitPair D OP false))
    (.seq (.fwd S) (.inc rP))))

theorem pcopyL_spec (S D : Fin (ns + 1)) (hSD : S ≠ D) (OP rP : Fin nr) (hOP : OP ≠ rP) (p : List Bool) :
    ∀ (m k : ℕ) (σ : WState ns nr), k + m = p.length → σ.st S = frame p → σ.sh S = 2 * k →
      σ.val rP = k → σ.sh D = (σ.st D).length → σ.val OP + 2 * m ≤ cap → p.length ≤ cap →
      WExec cap (pcopyL S D OP rP) σ
        (((appendO σ D OP (Streaming.marks (p.drop k))).seth S (2 * p.length)).setv rP p.length) (m * 26 + 1) := by
  intro m
  induction m with
  | zero =>
    intro k σ hk hs hh hr hd hc hp
    have hb : wbit σ S = false := by simp only [wbit, hs, hh, C4Loop.frame_even]; simp; omega
    have hdrop : p.drop k = [] := List.drop_eq_nil_of_le (by omega)
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    rw [hdrop]
    simp only [Streaming.marks, List.flatMap_nil, PrimAsm.WriteNat.appendO_nil]
    apply WState.eq
    · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> subst_vars <;> simp_all
      all_goals omega
    · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs <;> subst_vars <;> simp_all
      all_goals omega
    · rfl
  | succ m ih =>
    intro k σ hk hs hh hr hd hc hp
    have hkp : k < p.length := by omega
    have hb : wbit σ S = true := by simp only [wbit, hs, hh, C4Loop.frame_even]; simp; omega
    have h1 := WExec.fwd (cap := cap) S σ
    set σ1 := σ.seth S (σ.sh S + 1) with hσ1
    have hbit : wbit σ1 S = p.getD k false := by
      simp only [σ1, wbit, WState.seth_st, WState.seth_sh, Function.update_self, hs, hh]
      exact C4Rec.frame_odd' p k
    have hd1 : σ1.sh D = (σ1.st D).length := by simp [σ1, Function.update_apply, Ne.symm hSD, hd]
    have hc1 : σ1.val OP + 2 ≤ cap := by simp [σ1]; omega
    have h2 : WExec cap (.ifs S (PrimAsm.WriteNat.emitPair D OP true) (PrimAsm.WriteNat.emitPair D OP false)) σ1
        (appendO σ1 D OP [true, p.getD k false]) 16 := by
      cases hpk : p.getD k false
      · exact WExec.ifsF (by rw [hbit, hpk]) (PrimAsm.WriteNat.emitPair_spec cap D OP false σ1 hd1 hc1)
      · exact WExec.ifsT (by rw [hbit, hpk]) (PrimAsm.WriteNat.emitPair_spec cap D OP true σ1 hd1 hc1)
    set σ2 := appendO σ1 D OP [true, p.getD k false] with hσ2
    have h3 := WExec.fwd (cap := cap) S σ2
    set σ3 := σ2.seth S (σ2.sh S + 1) with hσ3
    have h4 := WExec.inc (cap := cap) rP σ3 (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hOP, hr]; omega)
    set σ4 := σ3.setv rP (σ3.val rP + 1) with hσ4
    have hrec := ih (k + 1) σ4 (by omega) (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hSD, hs])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hSD, hh]; ring)
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hOP, hr])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hSD, hd])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hOP]; omega) hp
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) hrec) ?_ (by omega)
    have hmk : Streaming.marks (p.drop k) = [true, p.getD k false] ++ Streaming.marks (p.drop (k + 1)) := by
      rw [List.getD_eq_getElem _ _ hkp, List.drop_eq_getElem_cons hkp]
      simp only [Streaming.marks, List.flatMap_cons, List.cons_append, List.nil_append]
    rw [hmk]
    apply WState.eq
    · funext j
      by_cases hjS : j = S
      · subst hjS; simp [σ4, σ3, σ2, σ1, Function.update_apply, hSD]
      · by_cases hjD : j = D
        · subst hjD; simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hSD, hjS, Streaming.marks]; ring
        · simp [σ4, σ3, σ2, σ1, Function.update_apply, hjS, hjD]
    · funext j
      by_cases hjD : j = D
      · subst hjD; simp [σ4, σ3, σ2, σ1, Function.update_apply, Ne.symm hSD]
      · simp [σ4, σ3, σ2, σ1, Function.update_apply, hjD]
    · funext r
      by_cases hrP : r = rP
      · subst hrP; simp [σ4, σ3, σ2, σ1, Function.update_apply]
      · by_cases hrO : r = OP
        · subst hrO; simp [σ4, σ3, σ2, σ1, Function.update_apply, hOP, Streaming.marks]; ring
        · simp [σ4, σ3, σ2, σ1, Function.update_apply, hrP, hrO]
    · simp [σ4, σ3, σ2, σ1]

end Prefix

section PfxCC2
variable {ns nr : ℕ} (cap : ℕ)

/-- `A := A − n` through the counter `B` (consumed). -/
def subLoop (A B : Fin nr) : WM ns nr := .whr B (.seq (.dec B) (.dec A))

theorem subLoop_spec (A B : Fin nr) (hAB : A ≠ B) (n a : ℕ) (σ : WState ns nr) (hB : σ.val B = n) (hA : σ.val A = a)
    (hna : n ≤ a) (hc : n ≤ cap) (hac : a ≤ cap) :
    WExec cap (subLoop A B) σ ((σ.setv B 0).setv A (a - n)) (n * (1 + 4) + 1) := by
  let S : ℕ → WState ns nr := fun k => (σ.setv B (n - k)).setv A (a - k)
  have hS0 : S 0 = σ := by
    apply WState.eq <;> try rfl
    funext r; simp only [S, WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have hloop := UnionMachine.Round.wloop cap B (.dec A) 1 n S
    (fun k _ => by simp [S, Function.update_apply, Ne.symm hAB]) hc
    (fun k hk => by
      have h := WExec.dec (cap := cap) A ((S k).setv B (n - k - 1)) (by simp [S, Function.update_apply, hAB]; omega)
      refine WExec.cast cap h ?_ le_rfl
      apply WState.eq <;> try rfl
      funext r; simp only [S, WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  apply WState.eq <;> try rfl
  funext r; simp only [S, WState.setv_val, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

end PfxCC2

/-! ## The arm's layout -/

/-- The arm's word state: `0…9` the unary rulers (`ℓ, kh, TWd, Cap, 2kh, Wt, |RT|, w+1, wT+1, 8ℓ`), `10` the framed
prefix, `11…47` the bank's words; registers `0…9` the rulers' values, `10` K, `11` T, `12` OP, `13` the prefix
length, `14`, `15` counters, `16` spare. -/
abbrev AS := WState 47 17
abbrev AW := WM 47 17

section Pfx
variable (cap : ℕ)

theorem reps_single (n : ℕ) (x : Bool) : reps n [x] = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PrimAsm.FiltRec.reps_succ, ih, List.replicate_succ']

/-- The child prefix `frame (p ++ [b])` on stream `30`, then `1^{8ℓ−|p|−1} 0^{|p|+1}` on stream `34`. -/
def pfxW (b : Bool) : AW :=
  .seq (pcopyL 10 30 12 13) (.seq (PrimAsm.Emit.emitW 30 12 [true, b, false]) (.seq (WM.clear 12)
    (.seq (FinalPass.Hash4.wcopyR 9 14 11) (.seq (FinalPass.Hash4.wcopyR 13 15 11) (.seq (subLoop 14 15)
      (.seq (.dec 14) (.seq (PrimAsm.Emit.repW 34 12 14 [true]) (.seq (WM.clear 12)
        (.seq (FinalPass.Hash4.wcopyR 13 15 11) (.seq (.inc 15) (PrimAsm.Emit.repW 34 12 15 [false])))))))))))

theorem pfxW_spec (b : Bool) (p : List Bool) (L8 : ℕ) (σ : AS) (hs : σ.st 10 = frame p) (hsh : σ.sh 10 = 0)
    (h9 : σ.val 9 = L8) (h11 : σ.val 11 = 0) (h12 : σ.val 12 = 0) (h13 : σ.val 13 = 0) (h14 : σ.val 14 = 0)
    (h15 : σ.val 15 = 0) (hd1 : σ.sh 30 = (σ.st 30).length) (hd2 : σ.sh 34 = (σ.st 34).length)
    (hp : p.length + 1 ≤ L8) (hc : 4 * L8 + 16 ≤ cap) :
    ∃ (τ : AS) (c : ℕ), WExec cap (pfxW b) σ τ c ∧ c ≤ 200 * L8 + 200 ∧
      τ.st 30 = σ.st 30 ++ frame (p ++ [b]) ∧
      τ.st 34 = σ.st 34 ++ (List.replicate (L8 - (p.length + 1)) true ++ List.replicate (p.length + 1) false) ∧
      ∀ j : Fin 48, j ≠ 30 → j ≠ 34 → τ.st j = σ.st j := by
  have hml : (Streaming.marks p).length = 2 * p.length := C4Frame.marks_length p
  have s1 := pcopyL_spec cap 10 30 (by decide) 12 13 (by decide) p p.length 0 σ (by omega) hs (by simp [hsh]) h13
    hd1 (by rw [h12]; omega) (by omega)
  simp only [List.drop_zero] at s1
  set σ1 := ((appendO σ 30 12 (Streaming.marks p)).seth 10 (2 * p.length)).setv 13 p.length with hσ1
  have s2 := PrimAsm.Emit.emitW_spec cap 30 12 [true, b, false] σ1 (by simp [σ1, hd1])
    (by simp [σ1, h12, hml] <;> omega)
  set σ2 := appendO σ1 30 12 [true, b, false] with hσ2
  have v2 : σ2.val 12 = 2 * p.length + 3 := by simp [σ2, σ1, h12, hml] <;> ring
  have s3 := wclear_spec cap 12 (2 * p.length + 3) σ2 v2 (by rw [v2]; omega)
  set σ3 := σ2.setv 12 0 with hσ3
  have s4 := FinalPass.Hash4.wcopyR_spec cap 9 14 11 (by decide) (by decide) (by decide) σ3
    (by simp [σ3, σ2, σ1, h14]) (by simp [σ3, σ2, σ1, h11]) (by simp [σ3, σ2, σ1, h9]; omega)
  have v4 : σ3.val 9 = L8 := by simp [σ3, σ2, σ1, h9]
  rw [v4] at s4
  set σ4 := σ3.setv 14 L8 with hσ4
  have s5 := FinalPass.Hash4.wcopyR_spec cap 13 15 11 (by decide) (by decide) (by decide) σ4
    (by simp [σ4, σ3, σ2, σ1, h15]) (by simp [σ4, σ3, σ2, σ1, h11]) (by simp [σ4, σ3, σ2, σ1]; omega)
  have v5 : σ4.val 13 = p.length := by simp [σ4, σ3, σ2, σ1]
  rw [v5] at s5
  set σ5 := σ4.setv 15 p.length with hσ5
  have s6 := subLoop_spec cap 14 15 (by decide) p.length L8 σ5 (by simp [σ5]) (by simp [σ5, σ4]) (by omega)
    (by omega) (by omega)
  set σ6 := (σ5.setv 15 0).setv 14 (L8 - p.length) with hσ6
  have s7 := WExec.dec (cap := cap) 14 σ6 (by simp [σ6]; omega)
  set σ7 := σ6.setv 14 (σ6.val 14 - 1) with hσ7
  have v7 : σ7.val 14 = L8 - (p.length + 1) := by simp [σ7, σ6]; omega
  have s8 := PrimAsm.Emit.repW_spec cap 34 12 14 (by decide) [true] (L8 - (p.length + 1)) σ7 v7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hd2])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega) (by omega)
  set σ8 := (appendO σ7 34 12 (reps (L8 - (p.length + 1)) [true])).setv 14 0 with hσ8
  have hl8 : (reps (L8 - (p.length + 1)) [true]).length = L8 - (p.length + 1) := by rw [reps_single]; simp
  have v8 : σ8.val 12 = L8 - (p.length + 1) := by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hl8]
  have s9 := wclear_spec cap 12 (L8 - (p.length + 1)) σ8 v8 (by rw [v8]; omega)
  set σ9 := σ8.setv 12 0 with hσ9
  have s10 := FinalPass.Hash4.wcopyR_spec cap 13 15 11 (by decide) (by decide) (by decide) σ9
    (by simp [σ9, σ8, σ7, σ6]) (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, h11])
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega)
  have v10 : σ9.val 13 = p.length := by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  rw [v10] at s10
  set σ10 := σ9.setv 15 p.length with hσ10
  have s11 := WExec.inc (cap := cap) 15 σ10 (by simp [σ10]; omega)
  set σ11 := σ10.setv 15 (σ10.val 15 + 1) with hσ11
  have v11 : σ11.val 15 = p.length + 1 := by simp [σ11, σ10]
  have s12 := PrimAsm.Emit.repW_spec cap 34 12 15 (by decide) [false] (p.length + 1) σ11 v11
    (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hd2, hl8])
    (by simp [σ11, σ10, σ9]; omega) (by omega)
  refine ⟨_, _, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 (WExec.seq s7
    (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 s12)))))))))), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil]
    omega
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply]
    rw [C4Frame.frame_marks, PrimAsm.WriteNat.marks_append]
    simp [Streaming.marks]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, reps_single]
  · intro j h30 h34
    simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, h30, h34]

end Pfx

/-! ## The arm's writers and their contracts -/

section ArmWriters
variable (cap : ℕ)

/-- The rulers' values: `ℓ, kh, TWd, Cap, 2kh, Wt, |RT|, w+1, wT+1, 8ℓ`. -/
structure Nums where
  l : ℕ
  kh : ℕ
  twd : ℕ
  cap : ℕ
  kh2 : ℕ
  wt : ℕ
  rt : ℕ
  w1 : ℕ
  wt1 : ℕ
  l8 : ℕ

/-- The register valuation after the rulers are loaded. -/
def V0 (N : Nums) : Fin 17 → ℕ :=
  ![N.l, N.kh, N.twd, N.cap, N.kh2, N.wt, N.rt, N.w1, N.wt1, N.l8, 0, 0, 0, 0, 0, 0, 0]

/-- The largest ruler. -/
def Nums.mx (N : Nums) : ℕ := N.l + N.kh + N.twd + N.cap + N.kh2 + N.wt + N.rt + N.w1 + N.wt1 + N.l8

def wrConst (d : Fin 48) (w : List Bool) : Wr 47 17 := ⟨d, emitWord d 12 w, w, 8 * w.length + 1 + (3 * w.length + 1)⟩
def wrFrame (d : Fin 48) (r : Fin 17) (x : ℕ) : Wr 47 17 :=
  ⟨d, frameZ d 12 10 11 r, frame (List.replicate x false), frameZCost x⟩
def wrFrames8 (d : Fin 48) (r : Fin 17) (x : ℕ) : Wr 47 17 :=
  ⟨d, frames8 d 12 10 11 r, reps 8 (frame (List.replicate x false)) ++ [false], frames8Cost x⟩
def wrZeros (d : Fin 48) (r : Fin 17) (x : ℕ) : Wr 47 17 :=
  ⟨d, repWord d 12 10 11 r [false], reps x [false],
    18 * x + 3 + 1 + (x * (8 * [false].length + 4) + 1 + 1 + (3 * (x * [false].length) + 1))⟩

theorem wrConst_ok (N : Nums) (d : Fin 48) (w : List Bool) (hc : w.length ≤ cap) :
    (wrConst d w).Ok cap (fun τ => τ.val = V0 N) := by
  intro τ hv hd
  exact emitWord_spec cap d 12 w τ (by rw [hv]; rfl) hd hc

theorem wrFrame_ok (N : Nums) (d : Fin 48) (r : Fin 17) (hr : r.val < 10) (x : ℕ) (hx : V0 N r = x)
    (hc : 3 * x + 3 ≤ cap) : (wrFrame d r x).Ok cap (fun τ => τ.val = V0 N) := by
  intro τ hv hd
  have hr10 : r ≠ 10 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  have hr11 : r ≠ 11 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  have hr12 : r ≠ 12 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  exact frameZ_spec cap d 12 10 11 r (by decide) hr10 hr11 (by decide) hr12 (by decide) x τ (by rw [hv, hx])
    (by rw [hv]; rfl) (by rw [hv]; rfl) (by rw [hv]; rfl) hd hc

theorem wrFrames8_ok (N : Nums) (d : Fin 48) (r : Fin 17) (hr : r.val < 10) (x : ℕ) (hx : V0 N r = x)
    (hc : 3 * x + 3 ≤ cap) : (wrFrames8 d r x).Ok cap (fun τ => τ.val = V0 N) := by
  intro τ hv hd
  have hr10 : r ≠ 10 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  have hr11 : r ≠ 11 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  have hr12 : r ≠ 12 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  exact frames8_spec cap d 12 10 11 r (by decide) hr10 hr11 (by decide) hr12 (by decide) x τ (by rw [hv, hx])
    (by rw [hv]; rfl) (by rw [hv]; rfl) (by rw [hv]; rfl) hd hc

theorem wrZeros_ok (N : Nums) (d : Fin 48) (r : Fin 17) (hr : r.val < 10) (x : ℕ) (hx : V0 N r = x)
    (hc : 2 * x + 1 ≤ cap) : (wrZeros d r x).Ok cap (fun τ => τ.val = V0 N) := by
  intro τ hv hd
  have hr10 : r ≠ 10 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  have hr11 : r ≠ 11 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  have hr12 : r ≠ 12 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  exact repWord_spec cap d 12 10 11 r (by decide) hr10 hr11 (by decide) hr12 (by decide) [false] x τ
    (by rw [hv, hx]) (by rw [hv]; rfl) (by rw [hv]; rfl) (by rw [hv]; rfl) hd (by simp; omega)

/-- **The bank's words** (every word but the child prefix and `CC2`), in the bank's order. -/
def armWrs (N : Nums) : List (Wr 47 17) :=
  [wrConst 11 (frame (List.replicate 8 false)), wrFrames8 12 0 N.l, wrFrames8 13 1 N.kh, wrFrames8 14 1 N.kh,
   wrFrames8 15 4 N.kh2, wrFrame 16 0 N.l, wrConst 17 [true], wrConst 18 [true], wrConst 19 [false],
   wrFrame 20 5 N.wt, wrFrame 21 5 N.wt, wrConst 22 [false], wrFrame 23 2 N.twd, wrConst 24 [false],
   wrFrame 25 0 N.l, wrFrame 26 0 N.l, wrZeros 27 6 N.rt, wrFrame 28 0 N.l, wrFrame 29 0 N.l,
   wrFrame 31 0 N.l, wrConst 32 [false], wrZeros 33 9 N.l8, wrConst 35 [false],
   wrZeros 36 3 N.cap, wrZeros 37 3 N.cap, wrZeros 38 3 N.cap, wrZeros 39 3 N.cap,
   wrZeros 40 3 N.cap, wrZeros 41 3 N.cap, wrZeros 42 3 N.cap, wrZeros 43 3 N.cap,
   wrZeros 44 7 N.w1, wrZeros 45 7 N.w1, wrZeros 46 8 N.wt1, wrZeros 47 8 N.wt1]

theorem armWrs_d (N : Nums) : (armWrs N).map Wr.d =
    [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41,
     42, 43, 44, 45, 46, 47] := rfl

theorem armWrs_nodup (N : Nums) : ((armWrs N).map Wr.d).Nodup := by rw [armWrs_d]; decide

theorem armWrs_ok (N : Nums) (hc : 3 * N.mx + 20 ≤ cap) : ∀ x ∈ armWrs N, x.Ok cap (fun τ => τ.val = V0 N) := by
  unfold Nums.mx at hc
  intro x hx
  simp only [armWrs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact wrConst_ok cap N _ _ (by simp [frame_length]; omega)
    | exact wrFrames8_ok cap N _ _ (by decide) _ rfl (by omega)
    | exact wrFrame_ok cap N _ _ (by decide) _ rfl (by omega)
    | exact wrZeros_ok cap N _ _ (by decide) _ rfl (by omega)

end ArmWriters

/-! ## The arm -/

section Arm
variable (cap : ℕ)

/-- Load the ten rulers. -/
def loadW : AW :=
  .seq (ucount 0 0) (.seq (ucount 1 1) (.seq (ucount 2 2) (.seq (ucount 3 3) (.seq (ucount 4 4)
    (.seq (ucount 5 5) (.seq (ucount 6 6) (.seq (ucount 7 7) (.seq (ucount 8 8) (ucount 9 9)))))))))

/-- The rulers as a vector. -/
def rul (N : Nums) : Fin 10 → ℕ := ![N.l, N.kh, N.twd, N.cap, N.kh2, N.wt, N.rt, N.w1, N.wt1, N.l8]

/-- The arm's entry state: the rulers, the framed prefix, every other stream blank. -/
def armSt (N : Nums) (p : List Bool) : AS :=
  ⟨fun _ => 0, fun i => if h : i.val < 10 then List.replicate (rul N ⟨i.val, h⟩) true else if i.val = 10 then frame p
    else [], fun _ => 0, false⟩

theorem load_one (s : Fin 48) (r : Fin 17) (x : ℕ) (σ : AS) (hs : σ.st s = List.replicate x true) (hh : σ.sh s = 0)
    (hr : σ.val r = 0) (hc : x ≤ cap) : WExec cap (ucount s r) σ ((σ.setv r x).seth s x) (x * 7 + 1) :=
  ucount_spec cap s r x [] rfl x 0 σ (by omega) (by simp [hs]) hh hr hc

def loadCost (N : Nums) : ℕ :=
  N.l * 7 + 1 + 1 + (N.kh * 7 + 1 + 1 + (N.twd * 7 + 1 + 1 + (N.cap * 7 + 1 + 1 + (N.kh2 * 7 + 1 + 1 +
    (N.wt * 7 + 1 + 1 + (N.rt * 7 + 1 + 1 + (N.w1 * 7 + 1 + 1 + (N.wt1 * 7 + 1 + 1 + (N.l8 * 7 + 1)))))))))

/-- The state after the rulers are loaded. -/
def loadSt (N : Nums) (p : List Bool) : AS :=
  ⟨fun i => if h : i.val < 10 then rul N ⟨i.val, h⟩ else 0, (armSt N p).st, V0 N, false⟩

theorem load_spec (N : Nums) (p : List Bool) (hc : N.mx ≤ cap) :
    WExec cap loadW (armSt N p) (loadSt N p) (loadCost N) := by
  unfold Nums.mx at hc
  have g : ∀ (s : Fin 48) (r : Fin 17) (x : ℕ) (τ : AS), τ.st s = List.replicate x true → τ.sh s = 0 →
      τ.val r = 0 → x ≤ cap → WExec cap (ucount s r) τ ((τ.setv r x).seth s x) (x * 7 + 1) :=
    fun s r x τ h1 h2 h3 h4 => load_one cap s r x τ h1 h2 h3 h4
  have s0 := g 0 0 N.l (armSt N p) rfl rfl rfl (by omega)
  set τ0 := (WState.setv (armSt N p) 0 N.l).seth 0 N.l with hτ0
  have s1 := g 1 1 N.kh τ0 (by simp [τ0, armSt, Function.update_apply]; rfl) (by simp [τ0, armSt, Function.update_apply]) (by simp [τ0, armSt, Function.update_apply]) (by omega)
  set τ1 := (WState.setv τ0 1 N.kh).seth 1 N.kh with hτ1
  have s2 := g 2 2 N.twd τ1 (by simp [τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ1, τ0, armSt, Function.update_apply]) (by simp [τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ2 := (WState.setv τ1 2 N.twd).seth 2 N.twd with hτ2
  have s3 := g 3 3 N.cap τ2 (by simp [τ2, τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ2, τ1, τ0, armSt, Function.update_apply]) (by simp [τ2, τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ3 := (WState.setv τ2 3 N.cap).seth 3 N.cap with hτ3
  have s4 := g 4 4 N.kh2 τ3 (by simp [τ3, τ2, τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by simp [τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ4 := (WState.setv τ3 4 N.kh2).seth 4 N.kh2 with hτ4
  have s5 := g 5 5 N.wt τ4 (by simp [τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by simp [τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ5 := (WState.setv τ4 5 N.wt).seth 5 N.wt with hτ5
  have s6 := g 6 6 N.rt τ5 (by simp [τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by simp [τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ6 := (WState.setv τ5 6 N.rt).seth 6 N.rt with hτ6
  have s7 := g 7 7 N.w1 τ6 (by simp [τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by simp [τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ7 := (WState.setv τ6 7 N.w1).seth 7 N.w1 with hτ7
  have s8 := g 8 8 N.wt1 τ7 (by simp [τ7, τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ7, τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by simp [τ7, τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ8 := (WState.setv τ7 8 N.wt1).seth 8 N.wt1 with hτ8
  have s9 := g 9 9 N.l8 τ8 (by simp [τ8, τ7, τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]; rfl) (by simp [τ8, τ7, τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by simp [τ8, τ7, τ6, τ5, τ4, τ3, τ2, τ1, τ0, armSt, Function.update_apply]) (by omega)
  set τ9 := (WState.setv τ8 9 N.l8).seth 9 N.l8 with hτ9
  refine WExec.cast cap (WExec.seq s0 (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 (WExec.seq s7 (WExec.seq s8 s9))))))))) ?_ le_rfl
  simp only [τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ2, τ1, τ0]
  apply WState.eq
  · funext i; simp only [WState.seth_sh, WState.setv_sh, Function.update_apply, loadSt, armSt]
    fin_cases i <;> rfl
  · rfl
  · funext r; simp only [WState.seth_val, WState.setv_val, Function.update_apply, loadSt, V0]
    fin_cases r <;> rfl
  · rfl

end Arm

section ArmMain
variable (cap : ℕ)

/-- The rulers at zero (the writers' programs do not depend on the rulers). -/
def N0 : Nums := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem seqWr_armWrs (N : Nums) : seqWr (armWrs N) = seqWr (armWrs N0) := rfl

/-- **The arm** of child bit `b`: load the rulers, write the bank's words, then the child prefix and `CC2`. -/
def armW (b : Bool) : AW := .seq loadW (.seq (seqWr (armWrs N0)) (pfxW b))

def armCost (N : Nums) : ℕ := loadCost N + 1 + (costWr (armWrs N) + 1 + (200 * N.l8 + 200))

/-- **The arm's run**: from the rulers and the framed prefix `p`, every bank word, the child prefix
`frame (p ++ [b])` and `1^{8ℓ−|p|−1} 0^{|p|+1}` on their streams; the rulers and the prefix unchanged. -/
theorem armW_spec (b : Bool) (N : Nums) (p : List Bool) (hp : p.length + 1 ≤ N.l8)
    (hc : 4 * N.mx + 20 ≤ cap) :
    ∃ (τ : AS) (c : ℕ), WExec cap (armW b) (armSt N p) τ c ∧ c ≤ armCost N ∧
      (∀ x ∈ armWrs N, τ.st x.d = x.w) ∧ τ.st 30 = frame (p ++ [b]) ∧
      τ.st 34 = List.replicate (N.l8 - (p.length + 1)) true ++ List.replicate (p.length + 1) false ∧
      ∀ i : Fin 48, i.val ≤ 10 → τ.st i = (armSt N p).st i := by
  have hmx := hc
  unfold Nums.mx at hmx
  have sL := load_spec cap N p (by unfold Nums.mx; omega)
  have hnd := armWrs_nodup N
  have hd := armWrs_d N
  have sW := seqWr_spec cap (fun τ => τ.val = V0 N) (armWrs N) (armWrs_ok cap N (by omega))
    (fun x _ τ hτ => by simpa using hτ) hnd (loadSt N p) rfl (fun x hx => by
      have hx' : x.d ∈ (armWrs N).map Wr.d := List.mem_map_of_mem hx
      rw [hd] at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl)
  rw [seqWr_armWrs N] at sW
  set τW := runWr (loadSt N p) (armWrs N) with hτW
  have hno : ∀ i : Fin 48, i ∉ (armWrs N).map Wr.d → τW.st i = (loadSt N p).st i ∧ τW.sh i = (loadSt N p).sh i :=
    fun i hi => runWr_other (armWrs N) i (fun x hx e => hi (e ▸ List.mem_map_of_mem hx)) (loadSt N p)
  have hv := runWr_val (armWrs N) (loadSt N p)
  have n10 := hno 10 (by rw [hd]; decide)
  have n30 := hno 30 (by rw [hd]; decide)
  have n34 := hno 34 (by rw [hd]; decide)
  obtain ⟨τ, c, sP, hcP, t30, t34, toth⟩ := pfxW_spec cap b p N.l8 τW
    (by rw [n10.1]; simp [loadSt, armSt]) (by rw [n10.2]; simp [loadSt])
    (by rw [hv]; rfl) (by rw [hv]; rfl) (by rw [hv]; rfl) (by rw [hv]; rfl) (by rw [hv]; rfl) (by rw [hv]; rfl)
    (by rw [n30.1, n30.2]; simp [loadSt, armSt]) (by rw [n34.1, n34.2]; simp [loadSt, armSt]) hp (by omega)
  refine ⟨τ, _, WExec.seq sL (WExec.seq sW sP), by unfold armCost; omega, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x.d ∈ (armWrs N).map Wr.d := List.mem_map_of_mem hx
    have h30 : x.d ≠ 30 := fun e => by rw [e, hd] at hx'; revert hx'; decide
    have h34 : x.d ≠ 34 := fun e => by rw [e, hd] at hx'; revert hx'; decide
    rw [toth x.d h30 h34, runWr_mem (armWrs N) hnd x hx]
    have hge : ¬ x.d.val < 10 ∧ x.d.val ≠ 10 := by
      rw [hd] at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    simp [loadSt, armSt, hge.1, hge.2]
  · rw [t30, n30.1]; simp [loadSt, armSt]
  · rw [t34, n34.1]; simp [loadSt, armSt]
  · intro i hi
    have h30 : i ≠ 30 := fun e => by rw [e] at hi; exact absurd hi (by decide)
    have h34 : i ≠ 34 := fun e => by rw [e] at hi; exact absurd hi (by decide)
    have hni : i ∉ (armWrs N).map Wr.d := by
      rw [hd]; intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h <;> (rw [h] at hi; exact absurd hi (by decide))
    rw [toth i h30 h34, (hno i hni).1]
    rfl

end ArmMain

end NearCubicWires.WireExponent3_5.PrimT.C4Arm
