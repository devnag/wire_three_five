import Proof.Wire_3_5.UnionMachine.RadNums

/-! # RADIX, stage 4 (1): the record's setup fields at marks level 2 (P3:2585-2623)

The Route-B record's frame begins with its setup fields, each `fieldE f = f.flatMap m2 ++ [true, false]`
(`FiltRec.frame_fieldsWord`): `1^R`, `0^{Lg}`, then `radEv`'s `frame (encT M 0^{2τ})`, `zW M (2τ(M+1))`,
`fieldsU (consFrom M p 2 0 τ)`, `patT p s (2τp+1)`, `[true]`, `[]`, `0^{cap}`. This part holds the word forms and
the writers of the unary fields (**`repFieldW`**) and of the digit tuple field (**`encFieldW`**). All writers append
on the output stream `O` with its position register `OP` (`WriteNat.appendO`).

Paper quantity of the main type: the RADIX row record's setup fields (C2's `radRowRec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadFields
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.ListMachine.Row

/-! ## Word forms -/

theorem fieldE_rep (n : ℕ) (b : Bool) : fieldE (List.replicate n b) = reps n (m2 b) ++ [true, false] := by
  unfold fieldE; rw [flatMap_replicate]

theorem reps_flatMap (n : ℕ) (u : List Bool) (f : Bool → List Bool) : (reps n u).flatMap f = reps n (u.flatMap f) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [reps_succ, reps_succ, List.flatMap_append, ih]

theorem frame_flat (w : List Bool) : frame w = w.flatMap (fun b => [true, b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [frame, ih]; rfl

theorem fieldE_frame (w : List Bool) :
    fieldE (frame w) = w.flatMap (fun b => m2 true ++ m2 b) ++ (m2 false ++ [true, false]) := by
  unfold fieldE
  rw [frame_flat, List.flatMap_append, List.flatMap_assoc]
  simp [m2, List.append_assoc]

theorem ohB_zero (M : ℕ) : ohB M 0 = true :: List.replicate M false := by
  unfold ohB
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [decide_true]
  congr 1
  have h : ∀ i ∈ List.range M, ((fun i => decide (i = 0)) ∘ Nat.succ) i = (fun _ => false) i := by
    intro i _; simp
  rw [List.map_congr_left h]
  simp

theorem reps_len (n : ℕ) (u : List Bool) : (reps n u).length = n * u.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [reps_succ, List.length_append, ih]; ring

theorem encT_zeros (M k : ℕ) : encT M (List.replicate k 0) = reps k (true :: List.replicate M false) := by
  unfold encT
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ', List.flatMap_append, ih, reps_succ, List.flatMap_singleton, ohB_zero]

/-- **The digit tuple field's word**: per digit, `m2 1 m2 1`, then `M` times `m2 1 m2 0`. -/
theorem fieldE_enc (M k : ℕ) :
    fieldE (frame (encT M (List.replicate k 0))) =
      reps k ((m2 true ++ m2 true) ++ reps M (m2 true ++ m2 false)) ++ (m2 false ++ [true, false]) := by
  rw [fieldE_frame, encT_zeros, reps_flatMap]
  congr 2
  rw [List.flatMap_cons, flatMap_replicate]

/-! ## The unary fields -/

section W
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1))

/-- `fieldE (b^{A})`: `A` copies of `m2 b`, then the field's end. -/
def repFieldW (OP A K T : Fin nr) (b : Bool) : WM ns nr := .seq (repRegW O OP A K T (m2 b)) (emitW O OP [true, false])

theorem repFieldW_spec (OP A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ OP) (b : Bool) (σ : WState ns nr) (hK : σ.val K = 0) (hT : σ.val T = 0) (ho : σ.sh O = (σ.st O).length)
    (hA : σ.val A ≤ cap) (hc : σ.val OP + 4 * σ.val A + 2 ≤ cap) :
    WExec cap (repFieldW O OP A K T b) σ (appendO σ O OP (fieldE (List.replicate (σ.val A) b)))
      (60 * σ.val A + 40) := by
  have h1 := repRegW_spec cap O OP A K T hAK hAT hKT hKO (m2 b) σ hK hT ho hA (by simp [m2]; omega)
  have h2 := emitW_spec cap O OP [true, false] (appendO σ O OP (reps (σ.val A) (m2 b)))
    (by simp [ho]) (by simp [Function.update_apply, reps_len, m2]; omega)
  rw [appendO_append, ← fieldE_rep] at h2
  refine WExec.mono (WExec.seq h1 h2) ?_
  simp [m2]; omega

/-- `fieldE (frame (encT M 0^{k}))` with `k` in `C` (consumed): the digit tuple field. -/
def encFieldW (OP C M K T : Fin nr) : WM ns nr :=
  .seq (.whr C (.seq (.dec C) (.seq (emitW O OP (m2 true ++ m2 true)) (repRegW O OP M K T (m2 true ++ m2 false)))))
    (emitW O OP (m2 false ++ [true, false]))

theorem encFieldW_spec (OP C M K T : Fin nr) (hCO : C ≠ OP) (hMO : M ≠ OP) (hKO : K ≠ OP) (hTO : T ≠ OP)
    (hCM : C ≠ M) (hCK : C ≠ K) (hCT : C ≠ T) (hMK : M ≠ K) (hMT : M ≠ T) (hKT : K ≠ T) (σ : WState ns nr)
    (k : ℕ) (hC : σ.val C = k) (hK : σ.val K = 0) (hT : σ.val T = 0) (ho : σ.sh O = (σ.st O).length)
    (hM : σ.val M ≤ cap) (hk : k ≤ cap) (hc : σ.val OP + k * (8 * σ.val M + 8) + 6 ≤ cap) :
    WExec cap (encFieldW O OP C M K T) σ
      ((appendO σ O OP (fieldE (frame (encT (σ.val M) (List.replicate k 0))))).setv C 0)
      (k * (100 * σ.val M + 200) + 100) := by
  set m := σ.val M with hm
  set blk := (m2 true ++ m2 true) ++ reps m (m2 true ++ m2 false) with hblk
  have hbl : blk.length = 8 * m + 8 := by simp [blk, reps_len, m2]; ring
  let S : ℕ → WState ns nr := fun j => (appendO σ O OP (reps j blk)).setv C (k - j)
  have hS0 : S 0 = σ := by
    simp only [S, reps_zero, appendO_nil, Nat.sub_zero, ← hC, wsetv_same]
  have hSk : S k = (appendO σ O OP (reps k blk)).setv C 0 := by simp [S]
  have hloop := UnionMachine.Round.wloop cap C (.seq (emitW O OP (m2 true ++ m2 true))
      (repRegW O OP M K T (m2 true ++ m2 false))) (100 * m + 150) k S
    (fun j _ => by simp [S]) hk (fun j hj => by
      have e0 : (S j).setv C (k - j - 1) = (appendO σ O OP (reps j blk)).setv C (k - j - 1) := by
        simp only [S, wsetv_setv]
      rw [e0]
      set σj := (appendO σ O OP (reps j blk)).setv C (k - j - 1) with hσj
      have hlj : (reps j blk).length = j * (8 * m + 8) := by rw [reps_len, hbl]
      have hopj : σj.val OP = σ.val OP + j * (8 * m + 8) := by
        simp [σj, Function.update_apply, hCO.symm, hlj]
      have hmj : σj.val M = m := by simp [σj, Function.update_apply, hCM.symm, hMO, hm]
      have hoj : σj.sh O = (σj.st O).length := by simp [σj, ho]
      have hjk : j * (8 * m + 8) + (8 * m + 8) ≤ k * (8 * m + 8) := by
        have := Nat.mul_le_mul_right (8 * m + 8) (show j + 1 ≤ k by omega); nlinarith
      have e1 := emitW_spec cap O OP (m2 true ++ m2 true) σj hoj (by simp [m2]; omega)
      have e2 := repRegW_spec cap O OP M K T hMK hMT hKT hKO (m2 true ++ m2 false)
        (appendO σj O OP (m2 true ++ m2 true))
        (by simp [σj, Function.update_apply, hCK.symm, hKO, hK]) (by simp [σj, Function.update_apply, hCT.symm, hTO, hT])
        (by simp [hoj]) (by simp [Function.update_apply, hMO]; omega)
        (by simp [Function.update_apply, hMO, hopj, m2]; nlinarith)
      have e2v : (appendO σj O OP (m2 true ++ m2 true)).val M = m := by simp [Function.update_apply, hMO, hmj]
      rw [e2v, appendO_append] at e2
      refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
      · simp only [S, σj]
        rw [appendO_setv _ _ _ _ hCO, appendO_append, reps_succ, Nat.sub_sub, hblk]
      · have hm8 : m * (8 * 4 + 4) = 36 * m := by ring
        simp only [List.length_append, m2, List.length_cons, List.length_nil]
        omega)
  rw [hS0, hSk] at hloop
  have e3 := emitW_spec cap O OP (m2 false ++ [true, false]) ((appendO σ O OP (reps k blk)).setv C 0)
    (by simp [ho]) (by simp [Function.update_apply, hCO.symm, reps_len, hbl, m2]; omega)
  rw [appendO_setv _ _ _ _ hCO, appendO_append] at e3
  refine WExec.cast cap (WExec.seq hloop e3) ?_ ?_
  · rw [fieldE_enc]
  · simp [m2]; nlinarith

end W

/-! ## The mask and residue fields' words -/

/-- A pair word of `zW`. -/
def zPair (K j : ℕ) : List Bool := [decide (j = 0), decide (j % (K + 1) = 0)]

theorem zW_pairs (K : ℕ) : ∀ N : ℕ, zW K N = (List.range N).flatMap (zPair K)
  | 0 => by simp [zW]
  | N + 1 => by
    have ih := zW_pairs K N
    unfold zW at ih ⊢
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ, List.map_append, List.map_append,
      ih, List.range_succ, List.flatMap_append]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, zPair,
      List.append_assoc, List.singleton_append]
    have h1 : (2 * N) % 2 = 0 := by omega
    have h2 : (2 * N + 1) % 2 = 1 := by omega
    have h3 : (2 * N) / 2 = N := by omega
    have h4 : (2 * N + 1) / 2 = N := by omega
    simp [h1, h2, h3, h4]

theorem map_replicate_of (l : List ℕ) (f : ℕ → Bool) (b : Bool) (h : ∀ r ∈ l, f r = b) :
    l.map f = List.replicate l.length b := by
  apply List.eq_replicate_iff.mpr
  refine ⟨by simp, fun c hc => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  exact h r hr

theorem range_map_eq (s p : ℕ) (hs : s < p) :
    (List.range p).map (fun r => decide (r = s)) = List.replicate s false ++ true :: List.replicate (p - 1 - s) false := by
  have hp : p = s + (1 + (p - 1 - s)) := by omega
  conv_lhs => rw [hp]
  rw [List.range_add, List.range_add, List.map_append, List.map_append, List.map_append]
  have e1 := map_replicate_of (List.range s) (fun r => decide (r = s)) false (fun r hr => by
    have := List.mem_range.mp hr; simp; omega)
  rw [List.length_range] at e1
  rw [e1]
  congr 1
  have e2 : List.map (fun r => decide (r = s)) (List.map (fun x => s + x) (List.range 1)) = [true] := by simp
  rw [e2, List.singleton_append]
  congr 1
  have e3 := map_replicate_of (List.map (fun x => s + x) (List.map (fun x => 1 + x) (List.range (p - 1 - s))))
    (fun r => decide (r = s)) false (fun r hr => by
      simp only [List.mem_map, List.mem_range] at hr
      obtain ⟨a, ⟨b, _, rfl⟩, rfl⟩ := hr
      simp)
  simp only [List.length_map, List.length_range] at e3
  rw [List.map_map] at e3 ⊢
  exact e3

theorem patT_blocks (p s : ℕ) (hs : s < p) : ∀ k : ℕ, patT p s (k * p + 1) =
    reps k (List.replicate s false ++ true :: List.replicate (p - 1 - s) false) ++ [decide (0 = s)] := by
  have hrm : ∀ k : ℕ, (List.range (k * p)).map (fun i => decide (i % p = s)) =
      reps k (List.replicate s false ++ true :: List.replicate (p - 1 - s) false) := by
    intro k
    induction k with
    | zero => simp [reps]
    | succ k ih =>
      rw [show (k + 1) * p = k * p + p by ring, List.range_add, List.map_append, ih, reps_succ, List.map_map]
      congr 1
      rw [← range_map_eq s p hs]
      apply List.map_congr_left
      intro r hr
      have := List.mem_range.mp hr
      simp only [Function.comp]
      congr 1
      rw [propext_iff]
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt this]
  intro k
  unfold patT
  rw [List.range_succ, List.map_append, hrm k]
  simp [Nat.mul_mod_left, eq_comm]

theorem reps_succ' (n : ℕ) (u : List Bool) : reps (n + 1) u = u ++ reps n u := by
  unfold reps; rw [List.replicate_succ, List.flatten_cons]

theorem flatMap_const (l : List ℕ) (f : ℕ → List Bool) (u : List Bool) (h : ∀ i ∈ l, f i = u) :
    l.flatMap f = reps l.length u := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, h a (by simp), ih (fun i hi => h i (by simp [hi])), List.length_cons, reps_succ']

theorem flatMap_range_succ (M : ℕ) (f : ℕ → List Bool) :
    (List.range (M + 1)).flatMap f = f 0 ++ (List.range M).flatMap (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem zW_blocks (M : ℕ) : ∀ k : ℕ, 1 ≤ k → zW M (k * (M + 1)) =
    ([true, true] ++ reps M [false, false]) ++ reps (k - 1) ([false, true] ++ reps M [false, false]) := by
  have hb0 : (List.range (M + 1)).flatMap (zPair M) = [true, true] ++ reps M [false, false] := by
    rw [flatMap_range_succ]
    congr 1
    rw [flatMap_const (List.range M) _ [false, false] (fun i hi => by
      have := List.mem_range.mp hi
      have h1 : i + 1 ≠ 0 := by omega
      have h2 : (i + 1) % (M + 1) ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [zPair, h1, h2]), List.length_range]
  have hbq : ∀ q : ℕ, 1 ≤ q → ((List.range (M + 1)).map (q * (M + 1) + ·)).flatMap (zPair M) =
      [false, true] ++ reps M [false, false] := by
    intro q hq
    have hqM : M + 1 ≤ q * (M + 1) := by have := Nat.mul_le_mul_right (M + 1) hq; omega
    rw [List.flatMap_map, flatMap_range_succ]
    congr 1
    · have h1 : q * (M + 1) + 0 ≠ 0 := by omega
      have hq0 : q ≠ 0 := by omega
      simp [zPair, h1, hq0, Nat.mul_mod_left]
    · rw [flatMap_const (List.range M) _ [false, false] (fun i hi => by
        have := List.mem_range.mp hi
        have h1 : q * (M + 1) + (i + 1) ≠ 0 := by omega
        have h2' : (i + 1) % (M + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : (q * (M + 1) + (i + 1)) % (M + 1) ≠ 0 := by
          rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, h2']; omega
        have h3 : (i + 1) % (M + 1) ≠ 0 := by rw [h2']; omega
        simp [zPair, h1, h2, h3]), List.length_range]
  intro k hk
  rw [zW_pairs]
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp only [Nat.zero_add, Nat.one_mul, Nat.sub_self, reps_zero, List.append_nil]
      exact hb0
    · rw [show (k + 1) * (M + 1) = k * (M + 1) + (M + 1) by ring, List.range_add, List.flatMap_append, ih hk1,
        hbq k hk1, show k + 1 - 1 = (k - 1) + 1 by omega, reps_succ]
      simp only [List.append_assoc]

/-! ## Loop writers -/

section L
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (OP : Fin nr)

/-- **A counted loop appending one block per round.** -/
theorem repLoop_spec (C : Fin nr) (body : WM ns nr) (blk : List Bool) (cb k : ℕ) (σ : WState ns nr)
    (hC : σ.val C = k) (hk : k ≤ cap)
    (hbody : ∀ j < k, WExec cap body ((appendO σ O OP (reps j blk)).setv C (k - j - 1))
      ((appendO σ O OP (reps (j + 1) blk)).setv C (k - j - 1)) cb) :
    WExec cap (.whr C (.seq (.dec C) body)) σ ((appendO σ O OP (reps k blk)).setv C 0) (k * (cb + 4) + 1) := by
  let S : ℕ → WState ns nr := fun j => (appendO σ O OP (reps j blk)).setv C (k - j)
  have hS0 : S 0 = σ := by simp only [S, reps_zero, appendO_nil, Nat.sub_zero, ← hC, wsetv_same]
  have hSk : S k = (appendO σ O OP (reps k blk)).setv C 0 := by simp [S]
  have h := UnionMachine.Round.wloop cap C body cb k S (fun j _ => by simp [S]) hk (fun j hj => by
    have e0 : (S j).setv C (k - j - 1) = (appendO σ O OP (reps j blk)).setv C (k - j - 1) := by
      simp only [S, wsetv_setv]
    have e1 : S (j + 1) = (appendO σ O OP (reps (j + 1) blk)).setv C (k - j - 1) := by
      simp only [S, Nat.sub_sub]
    rw [e0, e1]; exact hbody j hj)
  rwa [hS0, hSk] at h

/-- Emit `u`, then `A` copies of `v`. -/
def emRep (A K T : Fin nr) (u v : List Bool) : WM ns nr := .seq (emitW O OP u) (repRegW O OP A K T v)

theorem emRep_spec (A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ OP) (hAO : A ≠ OP)
    (hTO : T ≠ OP) (u v : List Bool) (τ : WState ns nr) (hK : τ.val K = 0) (hT : τ.val T = 0) (ho : τ.sh O = (τ.st O).length)
    (hA : τ.val A ≤ cap) (hc : τ.val OP + u.length + τ.val A * v.length ≤ cap) :
    WExec cap (emRep O OP A K T u v) τ (appendO τ O OP (u ++ reps (τ.val A) v))
      (8 * u.length + 18 * τ.val A + 5 + τ.val A * (8 * v.length + 4) + 1) := by
  have e1 := emitW_spec cap O OP u τ ho (by omega)
  have e2 := repRegW_spec cap O OP A K T hAK hAT hKT hKO v (appendO τ O OP u)
    (by simp [Function.update_apply, hKO, hK]) (by simp [Function.update_apply, hTO, hT])
    (by simp [ho]) (by simp [Function.update_apply, hAO]; omega) (by simp [Function.update_apply, hAO]; omega)
  have eA : (appendO τ O OP u).val A = τ.val A := by simp [Function.update_apply, hAO]
  rw [eA, appendO_append] at e2
  exact WExec.mono (WExec.seq e1 e2) (by omega)

end L

/-! ## The mask field and the residue field -/

@[simp] theorem m2_len (b : Bool) : (m2 b).length = 4 := rfl

theorem fieldE_zW (M k : ℕ) (hk : 1 ≤ k) : fieldE (zW M (k * (M + 1))) =
    ((m2 true ++ m2 true) ++ reps M (m2 false ++ m2 false)) ++
      (reps (k - 1) ((m2 false ++ m2 true) ++ reps M (m2 false ++ m2 false)) ++ [true, false]) := by
  unfold fieldE
  rw [zW_blocks M k hk]
  simp [List.flatMap_append, reps_flatMap, List.append_assoc]

theorem fieldE_patT (p s k : ℕ) (hs : s < p) : fieldE (patT p s (k * p + 1)) =
    reps k (reps s (m2 false) ++ (m2 true ++ reps (p - 1 - s) (m2 false))) ++ (m2 (decide (0 = s)) ++ [true, false]) := by
  unfold fieldE
  rw [patT_blocks p s hs k]
  simp [List.flatMap_append, reps_flatMap, flatMap_replicate, List.append_assoc]

section Z
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (OP : Fin nr)

theorem ao_val_ne (σ : WState ns nr) (r : Fin nr) (h : r ≠ OP) (u : List Bool) :
    (appendO σ O OP u).val r = σ.val r := by simp [Function.update_apply, h]

theorem ao_val_op (σ : WState ns nr) (u : List Bool) : (appendO σ O OP u).val OP = σ.val OP + u.length := by simp

theorem ao_ho (σ : WState ns nr) (u : List Bool) (ho : σ.sh O = (σ.st O).length) :
    (appendO σ O OP u).sh O = ((appendO σ O OP u).st O).length := by simp [ho]

theorem cost_z (j m : ℕ) : j * (100 * m + 150 + 4) + (100 * m + 200) ≤ (j + 1) * (100 * m + 200) := by
  have h := Nat.mul_le_mul_left j (show 100 * m + 150 + 4 ≤ 100 * m + 200 by omega)
  have e : (j + 1) * (100 * m + 200) = j * (100 * m + 200) + (100 * m + 200) := by ring
  omega

/-- **The mask field** `fieldE (zW M (k(M+1)))` with `k − 1` in `C` (consumed). -/
def zFieldW (C M K T : Fin nr) : WM ns nr :=
  .seq (emRep O OP M K T (m2 true ++ m2 true) (m2 false ++ m2 false))
    (.seq (.whr C (.seq (.dec C) (emRep O OP M K T (m2 false ++ m2 true) (m2 false ++ m2 false))))
      (emitW O OP [true, false]))

theorem zFieldW_spec (C M K T : Fin nr) (hCO : C ≠ OP) (hMO : M ≠ OP) (hKO : K ≠ OP) (hTO : T ≠ OP)
    (hCM : C ≠ M) (hCK : C ≠ K) (hCT : C ≠ T) (hMK : M ≠ K) (hMT : M ≠ T) (hKT : K ≠ T) (σ : WState ns nr)
    (k : ℕ) (hk1 : 1 ≤ k) (hC : σ.val C = k - 1) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (ho : σ.sh O = (σ.st O).length) (hM : σ.val M ≤ cap) (hk : k ≤ cap)
    (hc : σ.val OP + k * (8 * σ.val M + 8) + 2 ≤ cap) :
    WExec cap (zFieldW O OP C M K T) σ ((appendO σ O OP (fieldE (zW (σ.val M) (k * (σ.val M + 1))))).setv C 0)
      (k * (100 * σ.val M + 200) + 100) := by
  obtain ⟨m, hm⟩ : ∃ m, σ.val M = m := ⟨_, rfl⟩
  rw [hm] at hM hc ⊢
  have hkm : (k - 1) * (8 * m + 8) + (8 * m + 8) = k * (8 * m + 8) := by
    have : k = (k - 1) + 1 := by omega
    conv_rhs => rw [this]
    ring
  have hk8 : 8 * m + 8 ≤ k * (8 * m + 8) := by nlinarith
  have e1 := emRep_spec cap O OP M K T hMK hMT hKT hKO hMO hTO (m2 true ++ m2 true) (m2 false ++ m2 false) σ hK hT ho
    (by rw [hm]; exact hM) (by rw [hm]; simp [reps_len]; nlinarith)
  rw [hm] at e1
  have hl1 : ((m2 true ++ m2 true) ++ reps m (m2 false ++ m2 false)).length = 8 * m + 8 := by
    simp [reps_len]; ring
  have hbl : ((m2 false ++ m2 true) ++ reps m (m2 false ++ m2 false)).length = 8 * m + 8 := by
    simp [reps_len]; ring
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, appendO σ O OP ((m2 true ++ m2 true) ++ reps m (m2 false ++ m2 false)) = σ1 := ⟨_, rfl⟩
  rw [hσ1] at e1
  have v1C : σ1.val C = k - 1 := by rw [← hσ1, ao_val_ne O OP _ _ hCO, hC]
  have v1K : σ1.val K = 0 := by rw [← hσ1, ao_val_ne O OP _ _ hKO, hK]
  have v1T : σ1.val T = 0 := by rw [← hσ1, ao_val_ne O OP _ _ hTO, hT]
  have v1M : σ1.val M = m := by rw [← hσ1, ao_val_ne O OP _ _ hMO, hm]
  have v1P : σ1.val OP = σ.val OP + (8 * m + 8) := by rw [← hσ1, ao_val_op, hl1]
  have v1o : σ1.sh O = (σ1.st O).length := by rw [← hσ1]; exact ao_ho O OP σ _ ho
  have e2 := repLoop_spec cap O OP C (emRep O OP M K T (m2 false ++ m2 true) (m2 false ++ m2 false))
    ((m2 false ++ m2 true) ++ reps m (m2 false ++ m2 false)) (100 * m + 150) (k - 1) σ1 v1C (by omega)
    (fun j hj => by
      have hjk : j * (8 * m + 8) + (8 * m + 8) ≤ (k - 1) * (8 * m + 8) := by
        have := Nat.mul_le_mul_right (8 * m + 8) (show j + 1 ≤ k - 1 by omega); nlinarith
      have hrl : (reps j ((m2 false ++ m2 true) ++ reps m (m2 false ++ m2 false))).length = j * (8 * m + 8) := by
        rw [reps_len, hbl]
      have e := emRep_spec cap O OP M K T hMK hMT hKT hKO hMO hTO (m2 false ++ m2 true) (m2 false ++ m2 false)
        ((appendO σ1 O OP (reps j ((m2 false ++ m2 true) ++ reps m (m2 false ++ m2 false)))).setv C (k - 1 - j - 1))
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCK.symm]; rw [ao_val_ne O OP _ _ hKO, v1K])
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCT.symm]; rw [ao_val_ne O OP _ _ hTO, v1T])
        (by simp only [WState.setv_sh, WState.setv_st]; exact ao_ho O OP σ1 _ v1o)
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCM.symm]; rw [ao_val_ne O OP _ _ hMO, v1M]
            exact hM)
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCO.symm, if_neg hCM.symm]
            rw [ao_val_op, ao_val_ne O OP _ _ hMO, v1M, v1P, hrl]; simp [reps_len]; nlinarith)
      have eM : ((appendO σ1 O OP (reps j ((m2 false ++ m2 true) ++ reps m (m2 false ++ m2 false)))).setv C
          (k - 1 - j - 1)).val M = m := by
        simp only [WState.setv_val, Function.update_apply, if_neg hCM.symm]; rw [ao_val_ne O OP _ _ hMO, v1M]
      rw [eM] at e
      refine WExec.cast cap e ?_ (by simp [reps_len]; nlinarith)
      rw [appendO_setv _ _ _ _ hCO, appendO_append, reps_succ])
  obtain ⟨σ2, hσ2⟩ : ∃ σ2, (appendO σ1 O OP (reps (k - 1) ((m2 false ++ m2 true) ++ reps m (m2 false ++ m2 false)))).setv
      C 0 = σ2 := ⟨_, rfl⟩
  rw [hσ2] at e2
  have v2o : σ2.sh O = (σ2.st O).length := by
    rw [← hσ2]; simp only [WState.setv_sh, WState.setv_st]; exact ao_ho O OP σ1 _ v1o
  have v2P : σ2.val OP = σ.val OP + (8 * m + 8) + (k - 1) * (8 * m + 8) := by
    rw [← hσ2]; simp only [WState.setv_val, Function.update_apply, if_neg hCO.symm]
    rw [ao_val_op, v1P, reps_len, hbl]
  have e3 := emitW_spec cap O OP [true, false] σ2 v2o (by rw [v2P]; simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · rw [fieldE_zW m k hk1, ← hσ2, ← hσ1, ← appendO_setv _ _ _ _ hCO, appendO_append, appendO_setv _ _ _ _ hCO,
      appendO_append]
  · have key := cost_z (k - 1) m
    rw [show k - 1 + 1 = k by omega] at key
    simp only [List.length_append, m2_len, List.length_cons, List.length_nil]
    omega

/-- One residue block: `s` copies of `m2 0`, `m2 1`, `q` copies of `m2 0`. -/
def pBody (S Q K T : Fin nr) : WM ns nr :=
  .seq (repRegW O OP S K T (m2 false)) (.seq (emitW O OP (m2 true)) (repRegW O OP Q K T (m2 false)))

theorem pBody_spec (S Q K T : Fin nr) (hSK : S ≠ K) (hST : S ≠ T) (hQK : Q ≠ K) (hQT : Q ≠ T) (hKT : K ≠ T)
    (hKO : K ≠ OP) (hTO : T ≠ OP) (hQO : Q ≠ OP) (τ : WState ns nr) (s q : ℕ) (hS : τ.val S = s)
    (hQ : τ.val Q = q) (hK : τ.val K = 0) (hT : τ.val T = 0) (ho : τ.sh O = (τ.st O).length) (hs : s ≤ cap)
    (hq : q ≤ cap) (hc : τ.val OP + 4 * s + 4 + 4 * q ≤ cap) :
    WExec cap (pBody O OP S Q K T) τ (appendO τ O OP (reps s (m2 false) ++ (m2 true ++ reps q (m2 false))))
      (60 * (s + q) + 60) := by
  have e1 := repRegW_spec cap O OP S K T hSK hST hKT hKO (m2 false) τ hK hT ho (by omega) (by rw [hS]; simp; omega)
  rw [hS] at e1
  have e2 := emitW_spec cap O OP (m2 true) (appendO τ O OP (reps s (m2 false))) (ao_ho O OP τ _ ho)
    (by rw [ao_val_op, reps_len]; simp; omega)
  rw [appendO_append] at e2
  have e3 := repRegW_spec cap O OP Q K T hQK hQT hKT hKO (m2 false) (appendO τ O OP (reps s (m2 false) ++ m2 true))
    (by rw [ao_val_ne O OP _ _ hKO, hK]) (by rw [ao_val_ne O OP _ _ hTO, hT]) (ao_ho O OP τ _ ho)
    (by rw [ao_val_ne O OP _ _ hQO, hQ]; exact hq)
    (by rw [ao_val_op, ao_val_ne O OP _ _ hQO, hQ, List.length_append, reps_len]; simp; omega)
  rw [ao_val_ne O OP _ _ hQO, hQ, appendO_append] at e3
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (by rw [List.append_assoc]) ?_
  simp only [m2_len]; omega

/-- **The residue field** `fieldE (patT p s (kp+1))` with `k` in `C` (consumed), `s` in `S`, `p − 1 − s` in `Q`. -/
def pFieldW (C S Q K T : Fin nr) : WM ns nr :=
  .seq (.whr C (.seq (.dec C) (pBody O OP S Q K T)))
    (.ifr S (emitW O OP (m2 false ++ [true, false])) (emitW O OP (m2 true ++ [true, false])))

theorem pFieldW_spec (C S Q K T : Fin nr) (hCO : C ≠ OP) (hSO : S ≠ OP) (hQO : Q ≠ OP) (hKO : K ≠ OP)
    (hTO : T ≠ OP) (hCS : C ≠ S) (hCQ : C ≠ Q) (hCK : C ≠ K) (hCT : C ≠ T) (hSK : S ≠ K) (hST : S ≠ T)
    (hQK : Q ≠ K) (hQT : Q ≠ T) (hKT : K ≠ T) (σ : WState ns nr) (p s k : ℕ) (hsp : s < p) (hC : σ.val C = k)
    (hS : σ.val S = s) (hQ : σ.val Q = p - 1 - s) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (ho : σ.sh O = (σ.st O).length) (hp : p ≤ cap) (hk : k ≤ cap) (hc : σ.val OP + k * (4 * p) + 6 ≤ cap) :
    WExec cap (pFieldW O OP C S Q K T) σ ((appendO σ O OP (fieldE (patT p s (k * p + 1)))).setv C 0)
      (k * (60 * p + 64) + 100) := by
  have hbl : (reps s (m2 false) ++ (m2 true ++ reps (p - 1 - s) (m2 false))).length = 4 * p := by
    simp [reps_len]; omega
  have e1 := repLoop_spec cap O OP C (pBody O OP S Q K T) (reps s (m2 false) ++ (m2 true ++ reps (p - 1 - s) (m2 false)))
    (60 * p + 60) k σ hC hk (fun j hj => by
      have hjk : j * (4 * p) + 4 * p ≤ k * (4 * p) := by
        have := Nat.mul_le_mul_right (4 * p) (show j + 1 ≤ k by omega); nlinarith
      have e := pBody_spec cap O OP S Q K T hSK hST hQK hQT hKT hKO hTO hQO
        ((appendO σ O OP (reps j (reps s (m2 false) ++ (m2 true ++ reps (p - 1 - s) (m2 false))))).setv C
          (k - j - 1)) s (p - 1 - s)
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCS.symm]; rw [ao_val_ne O OP _ _ hSO, hS])
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCQ.symm]; rw [ao_val_ne O OP _ _ hQO, hQ])
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCK.symm]; rw [ao_val_ne O OP _ _ hKO, hK])
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCT.symm]; rw [ao_val_ne O OP _ _ hTO, hT])
        (by simp only [WState.setv_sh, WState.setv_st]; exact ao_ho O OP σ _ ho) (by omega) (by omega)
        (by simp only [WState.setv_val, Function.update_apply, if_neg hCO.symm]
            rw [ao_val_op, reps_len, hbl]; omega)
      refine WExec.cast cap e ?_ (by omega)
      rw [appendO_setv _ _ _ _ hCO, appendO_append, reps_succ])
  obtain ⟨σ2, hσ2⟩ : ∃ σ2, (appendO σ O OP (reps k (reps s (m2 false) ++ (m2 true ++ reps (p - 1 - s) (m2 false))))).setv
      C 0 = σ2 := ⟨_, rfl⟩
  rw [hσ2] at e1
  have v2o : σ2.sh O = (σ2.st O).length := by
    rw [← hσ2]; simp only [WState.setv_sh, WState.setv_st]; exact ao_ho O OP σ _ ho
  have v2P : σ2.val OP = σ.val OP + k * (4 * p) := by
    rw [← hσ2]; simp only [WState.setv_val, Function.update_apply, if_neg hCO.symm]
    rw [ao_val_op, reps_len, hbl]
  have v2S : σ2.val S = s := by
    rw [← hσ2]; simp only [WState.setv_val, Function.update_apply, if_neg hCS.symm]; rw [ao_val_ne O OP _ _ hSO, hS]
  have hfin : fieldE (patT p s (k * p + 1)) =
      reps k (reps s (m2 false) ++ (m2 true ++ reps (p - 1 - s) (m2 false))) ++ (m2 (decide (0 = s)) ++ [true, false]) :=
    fieldE_patT p s k hsp
  by_cases hs0 : s = 0
  · subst hs0
    have e2 := emitW_spec cap O OP (m2 true ++ [true, false]) σ2 v2o (by rw [v2P]; simp <;> omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.ifrF (by rw [v2S]) e2)) ?_ (by simp <;> omega)
    rw [hfin, ← hσ2, ← appendO_setv _ _ _ _ hCO, appendO_append, appendO_setv _ _ _ _ hCO]
    simp
  · have e2 := emitW_spec cap O OP (m2 false ++ [true, false]) σ2 v2o (by rw [v2P]; simp <;> omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.ifrT (by rw [v2S]; exact hs0) e2)) ?_ (by simp <;> omega)
    rw [hfin, ← hσ2, ← appendO_setv _ _ _ _ hCO, appendO_append, appendO_setv _ _ _ _ hCO]
    have hd : decide (0 = s) = false := by simp; omega
    rw [hd]

end Z

end NearCubicWires.WireExponent3_5.UnionMachine.RadFields
