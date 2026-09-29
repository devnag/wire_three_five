import Proof.Wire_3_5.Selection.GatePhaseL

/-! # C1.4: the gate routine's constants (P3:1339-1358)

Paper: "Enumerate each half's score vectors" (P3:1344-1345). Before its joins, the gate routine fixes its constants
in unary registers: the word width `W` (counted from the offset word `OF = 2^V`), `W − 1`, `W − V − 2`, `2V + 3`,
`W − 2V − 3`, the offset `h` of the left segments, the counts `2^lw`, `2^rw`, `2^(s·h)` of the enumerations, and the
widths `lw + 1`, `s·h + 1` of the counters. Every program here moves registers only (and a head it returns).
Main declarations: `cntW_spec`, `cpy_spec`, `dbl_spec`, `pow2_spec`. Paper quantity: none (the machine's constants). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)

variable {ns nr : ℕ}

/-! ## Counting a word's width -/

/-- `N += (number of pairs of the framed word on A)`, `A` returned by its counter `C`. -/
def cntW (A : Fin (ns + 1)) (C N : Fin nr) : WM ns nr :=
  .seq (.whs A (.seq (WM.fwdC A C) (.seq (WM.fwdC A C) (.inc N)))) (WM.rewind A C)

theorem cntW_loop (cap : ℕ) (A : Fin (ns + 1)) (C N : Fin nr) (hCN : C ≠ N) (post : List Bool) :
    ∀ (bits pre : List Bool) (σ : WState ns nr), σ.st A = pre ++ frameP bits ++ false :: post →
      σ.sh A = pre.length → σ.val C = pre.length → pre.length + 2 * bits.length < cap →
      σ.val N + bits.length < cap →
      WExec cap (.whs A (.seq (WM.fwdC A C) (.seq (WM.fwdC A C) (.inc N)))) σ
        (((σ.seth A (pre.length + 2 * bits.length)).setv C (pre.length + 2 * bits.length)).setv N
          (σ.val N + bits.length)) (17 * bits.length + 1)
  | [], pre, σ, hA, hh, hc, _, _ => by
    have hb : wbit σ A = false := by
      simp only [wbit, hh, hA, frameP_nil, List.append_nil]; exact rd_app0 pre (false :: post) ▸ rd_cons0 false post
    have e : ((σ.seth A (pre.length + 2 * 0)).setv C (pre.length + 2 * 0)).setv N (σ.val N + 0) = σ := by
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs with h
        · subst h; simp [hh]
        · rfl
      · rfl
      · funext j; simp only [WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs with h1 h2 <;>
          subst_vars <;> simp_all
      · rfl
    simp only [List.length_nil] at e ⊢
    rw [e]; exact WExec.whsF hb
  | b :: bits, pre, σ, hA, hh, hc, hp, hn => by
    have hA2 : σ.st A = pre ++ (true :: b :: (frameP bits ++ false :: post)) := by rw [hA, frameP_cons]; simp
    have hb : wbit σ A = true := by simp only [wbit, hh, hA2]; rw [rd_app0, rd_cons0]
    simp only [List.length_cons] at hp hn ⊢
    have f1 := wfwdC_spec cap A C σ (by omega)
    set σ1 := (σ.seth A (σ.sh A + 1)).setv C (σ.val C + 1) with hσ1
    have f2 := wfwdC_spec cap A C σ1 (by simp [hσ1]; omega)
    set σ2 := (σ1.seth A (σ1.sh A + 1)).setv C (σ1.val C + 1) with hσ2
    have f3 := WExec.inc (cap := cap) N σ2 (by simp [hσ2, hσ1, Function.update_apply, Ne.symm hCN]; omega)
    set σ3 := σ2.setv N (σ2.val N + 1) with hσ3
    have ih := cntW_loop cap A C N hCN post bits (pre ++ [true, b]) σ3
      (by simp [hσ3, hσ2, hσ1, hA, frameP_cons]) (by simp [hσ3, hσ2, hσ1, hh])
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, hCN, hc]) (by simp <;> omega)
      (by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hCN]; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq f1 (WExec.seq f2 f3)) ih) ?_ (by simp; omega)
    apply WState.eq
    · funext j; simp only [hσ3, hσ2, hσ1, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all; omega
    · rfl
    · funext j; simp only [hσ3, hσ2, hσ1, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all <;> omega
    · rfl

/-- **The width of a framed word**: `N += w` for the word `frame bits`, `|bits| = w`. -/
theorem cntW_spec (cap : ℕ) (A : Fin (ns + 1)) (C N : Fin nr) (hCN : C ≠ N) (bits : List Bool) (σ : WState ns nr)
    (hA : σ.st A = frame bits) (hh : σ.sh A = 0) (hc : σ.val C = 0) (hcap : 2 * bits.length + 1 ≤ cap)
    (hn : σ.val N + bits.length < cap) :
    WExec cap (cntW A C N) σ (σ.setv N (σ.val N + bits.length)) (27 * bits.length + 3) := by
  have h1 := cntW_loop cap A C N hCN [] bits [] σ (by rw [hA, frame_eq_frameP]; simp) hh hc (by simp; omega) hn
  simp only [List.length_nil, Nat.zero_add] at h1
  have h2 := wrewind_spec cap A C (2 * bits.length)
    (((σ.seth A (2 * bits.length)).setv C (2 * bits.length)).setv N (σ.val N + bits.length))
    (by simp [Function.update_apply, hCN]) (by simp [Function.update_apply, hCN]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs with h
    · subst h; simp [hh]
    · rfl
  · rfl
  · funext j; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

/-! ## Register arithmetic -/

section Regs
variable (cap : ℕ)

/-- **Iterating a register update**: `K` rounds of `body`, each `P := f P`, the other registers kept. -/
theorem iterP (K T P : Fin nr) (hKT : K ≠ T) (hKP : K ≠ P) (hTP : T ≠ P) (body : WM ns nr) (f : ℕ → ℕ) (c n v0 : ℕ)
    (σ0 : WState ns nr) (hK : σ0.val K = n) (hT : σ0.val T = 0) (hcap : n ≤ cap)
    (hbody : ∀ j < n, ∀ σ : WState ns nr, (∀ r, r ≠ K → r ≠ T → r ≠ P → σ.val r = σ0.val r) → σ.sh = σ0.sh →
      σ.st = σ0.st → σ.cell = σ0.cell → σ.val P = f^[j] v0 → WExec cap body σ (σ.setv P (f^[j + 1] v0)) c) :
    WExec cap (cloop K T body) (σ0.setv P v0) (σ0.setv P (f^[n] v0)) (n * (c + 8) + 1 + 1 + (7 * n + 1)) := by
  have hl := Point.cloopM cap K T hKT body (fun σ j => σ.setv P (f^[j] v0))
    (fun σ j v w => by
      apply WState.eq
      · rfl
      · rfl
      · funext i; simp only [WState.setv_val, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all
      · rfl)
    σ0 n c hK hT hcap (by
      intro j hj v w
      have h := hbody j hj ((((σ0.setv K v).setv T w)).setv P (f^[j] v0))
        (fun r h1 h2 h3 => by simp [Function.update_apply, h1, h2, h3]) rfl rfl rfl (by simp)
      rw [wsetv_setv] at h
      exact h)
  exact hl

/-- `B += A` (`A` restored). -/
def cpy (A T B : Fin nr) : WM ns nr := cloop A T (.inc B)

theorem iter_add_one (b : ℕ) : ∀ j, (fun x : ℕ => x + 1)^[j] b = b + j
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', iter_add_one b j]; ring

theorem cpy_spec (A T B : Fin nr) (hAT : A ≠ T) (hAB : A ≠ B) (hTB : T ≠ B) (σ : WState ns nr) (a b : ℕ)
    (hA : σ.val A = a) (hT : σ.val T = 0) (hB : σ.val B = b) (hcap : a + b < cap) :
    WExec cap (cpy A T B) σ (σ.setv B (b + a)) (a * (3 + 8) + 1 + 1 + (7 * a + 1)) := by
  have h := iterP cap A T B hAT hAB hTB (.inc B) (fun x => x + 1) 3 a b σ hA hT (by omega) (by
    intro j hj σ' _ _ _ _ hv
    have := WExec.inc (cap := cap) B σ' (by rw [hv, iter_add_one]; omega)
    rw [hv, iter_add_one] at this
    rw [iter_add_one, ← Nat.add_assoc]; exact this)
  rw [iter_add_one] at h
  have e : σ.setv B b = σ := by rw [← hB]; exact wsetv_same σ B
  rw [e] at h
  exact h

/-- `B := B − A` (truncated; `A` restored). -/
def subN (A T B : Fin nr) : WM ns nr := cloop A T (.dec B)

theorem iter_sub_one (b : ℕ) : ∀ j, (fun x : ℕ => x - 1)^[j] b = b - j
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', iter_sub_one b j]; omega

theorem subN_spec (A T B : Fin nr) (hAT : A ≠ T) (hAB : A ≠ B) (hTB : T ≠ B) (σ : WState ns nr) (a b : ℕ)
    (hA : σ.val A = a) (hT : σ.val T = 0) (hB : σ.val B = b) (hcap : a + b ≤ cap) :
    WExec cap (subN A T B) σ (σ.setv B (b - a)) (a * (1 + 8) + 1 + 1 + (7 * a + 1)) := by
  have h := iterP cap A T B hAT hAB hTB (.dec B) (fun x => x - 1) 1 a b σ hA hT (by omega) (by
    intro j hj σ' _ _ _ _ hv
    have := WExec.dec (cap := cap) B σ' (by rw [hv, iter_sub_one]; omega)
    rw [hv, iter_sub_one] at this
    rw [iter_sub_one, ← Nat.sub_sub]; exact this)
  rw [iter_sub_one] at h
  have e : σ.setv B b = σ := by rw [← hB]; exact wsetv_same σ B
  rw [e] at h
  exact h

/-- `B := B + 2A` (`A` restored). -/
def add2 (A T B : Fin nr) : WM ns nr := cloop A T (.seq (.inc B) (.inc B))

theorem iter_add_two (b : ℕ) : ∀ j, (fun x : ℕ => x + 2)^[j] b = b + 2 * j
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', iter_add_two b j]; ring

theorem add2_spec (A T B : Fin nr) (hAT : A ≠ T) (hAB : A ≠ B) (hTB : T ≠ B) (σ : WState ns nr) (a b : ℕ)
    (hA : σ.val A = a) (hT : σ.val T = 0) (hB : σ.val B = b) (hcap : 2 * a + b < cap) :
    WExec cap (add2 A T B) σ (σ.setv B (b + 2 * a)) (a * (7 + 8) + 1 + 1 + (7 * a + 1)) := by
  have h := iterP cap A T B hAT hAB hTB (.seq (.inc B) (.inc B)) (fun x => x + 2) 7 a b σ hA hT (by omega) (by
    intro j hj σ' _ _ _ _ hv
    have h1 := WExec.inc (cap := cap) B σ' (by rw [hv, iter_add_two]; omega)
    have h2 := WExec.inc (cap := cap) B (σ'.setv B (σ'.val B + 1)) (by simp [hv, iter_add_two]; omega)
    have e : (σ'.setv B (σ'.val B + 1)).setv B ((σ'.setv B (σ'.val B + 1)).val B + 1) =
        σ'.setv B ((fun x : ℕ => x + 2)^[j + 1] b) := by
      rw [wsetv_setv]; congr 1; simp [hv, iter_add_two]; ring
    rw [e] at h2
    exact WExec.seq h1 h2)
  rw [iter_add_two] at h
  have e : σ.setv B b = σ := by rw [← hB]; exact wsetv_same σ B
  rw [e] at h
  exact h

/-- `P := 2P` through `Tm` (back to `0`). -/
def dbl (P T Tm : Fin nr) : WM ns nr := .seq (cloop P T (.seq (.inc Tm) (.inc Tm))) (.seq (WM.clear P) (WM.move Tm P))

theorem dbl_spec (P T Tm : Fin nr) (hPT : P ≠ T) (hPm : P ≠ Tm) (hTm : T ≠ Tm) (σ : WState ns nr) (p : ℕ)
    (hP : σ.val P = p) (hT : σ.val T = 0) (hm : σ.val Tm = 0) (hcap : 2 * p < cap) :
    WExec cap (dbl P T Tm) σ (σ.setv P (2 * p)) (p * (7 + 8) + 1 + 1 + (7 * p + 1) + 1 + (3 * p + 1 + 1 + (7 * (2 * p) + 1))) := by
  have h1 := add2_spec cap P T Tm hPT hPm hTm σ p 0 hP hT hm (by omega)
  simp only [Nat.zero_add] at h1
  have h2 := wclear_spec cap P p (σ.setv Tm (2 * p)) (by simp [Function.update_apply, hPm, hP])
    (by simp [Function.update_apply, hPm, hP]; omega)
  have h3 := wmove_spec cap Tm P (Ne.symm hPm) (2 * p) ((σ.setv Tm (2 * p)).setv P 0)
    (by simp [Function.update_apply, hPm, Ne.symm hPm])
    (by simp [Function.update_apply, hPm, Ne.symm hPm]; omega) (by simp [Function.update_apply, hPm, Ne.symm hPm]; omega)
  have e : (((σ.setv Tm (2 * p)).setv P 0).setv Tm 0).setv P (((σ.setv Tm (2 * p)).setv P 0).val P +
      ((σ.setv Tm (2 * p)).setv P 0).val Tm) = σ.setv P (2 * p) := by
    apply WState.eq
    · rfl
    · rfl
    · funext j; simp only [WState.setv_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · rfl
  rw [e] at h3
  unfold dbl
  exact WExec.seq h1 (WExec.seq h2 h3)

theorem iter_mul_two (p : ℕ) : ∀ j, (fun x : ℕ => 2 * x)^[j] p = p * 2 ^ j
  | 0 => by simp
  | j + 1 => by rw [Function.iterate_succ_apply', iter_mul_two p j, pow_succ]; ring

/-- `P := P·2^k` (`K` restored). -/
theorem powIn_spec (K T P T3 Tm : Fin nr) (hd : [K, T, P, T3, Tm].Nodup) (σ : WState ns nr) (k p : ℕ)
    (hK : σ.val K = k) (hT : σ.val T = 0) (hT3 : σ.val T3 = 0) (hm : σ.val Tm = 0) (hP : σ.val P = p)
    (hcap : 2 * (p * 2 ^ k) < cap) (hk : k ≤ cap) :
    WExec cap (cloop K T (dbl P T3 Tm)) σ (σ.setv P (p * 2 ^ k)) (k * (40 * (p * 2 ^ k) + 20 + 8) + 1 + 1 + (7 * k + 1)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hKT, hKP, hK3, hKm⟩, ⟨hTP, hT3', hTm⟩, ⟨hP3, hPm⟩, h3m, -⟩ := hd
  have h := iterP cap K T P hKT hKP hTP (dbl P T3 Tm) (fun x => 2 * x) (40 * (p * 2 ^ k) + 20) k p σ hK hT hk (by
    intro j hj σ' hv _ _ _ hvP
    rw [iter_mul_two] at hvP ⊢
    have hj2 : p * 2 ^ j * 2 ≤ p * 2 ^ k := by
      rw [mul_assoc, ← pow_succ]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
    have := dbl_spec cap P T3 Tm hP3 hPm h3m σ' (p * 2 ^ j) hvP
      (by rw [hv T3 (Ne.symm hK3) (Ne.symm hT3') (Ne.symm hP3)]; exact hT3)
      (by rw [hv Tm (Ne.symm hKm) (Ne.symm hTm) (Ne.symm hPm)]; exact hm) (by omega)
    rw [show 2 * (p * 2 ^ j) = p * 2 ^ (j + 1) by rw [pow_succ]; ring] at this
    have hjk : p * 2 ^ j ≤ p * 2 ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine WExec.mono this ?_
    have hc : p * 2 ^ j * (7 + 8) + 1 + 1 + (7 * (p * 2 ^ j) + 1) + 1 + (3 * (p * 2 ^ j) + 1 + 1 +
        (7 * (p * 2 ^ (j + 1)) + 1)) = 39 * (p * 2 ^ j) + 7 := by rw [pow_succ]; ring
    rw [hc]; omega)
  rw [iter_mul_two] at h
  have e : σ.setv P p = σ := by rw [← hP]; exact wsetv_same σ P
  rw [e] at h
  exact h

theorem iter_add_b (c b : ℕ) : ∀ j, (fun x : ℕ => x + b)^[j] c = c + j * b
  | 0 => by simp
  | j + 1 => by rw [Function.iterate_succ_apply', iter_add_b c b j]; ring

/-- `C := C + a·b` (`A`, `B` restored). -/
theorem mulAdd_spec (A T1 B T2 C : Fin nr) (hd : [A, T1, B, T2, C].Nodup) (σ : WState ns nr) (a b c : ℕ)
    (hA : σ.val A = a) (hT1 : σ.val T1 = 0) (hB : σ.val B = b) (hT2 : σ.val T2 = 0) (hC : σ.val C = c)
    (hcap : c + a * b + b < cap) (ha : a ≤ cap) :
    WExec cap (cloop A T1 (cpy B T2 C)) σ (σ.setv C (c + a * b))
      (a * (b * (3 + 8) + 1 + 1 + (7 * b + 1) + 8) + 1 + 1 + (7 * a + 1)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hA1, hAB, hA2, hAC⟩, ⟨h1B, h12, h1C⟩, ⟨hB2, hBC⟩, h2C, -⟩ := hd
  have h := iterP cap A T1 C hA1 hAC h1C (cpy B T2 C) (fun x => x + b) (b * (3 + 8) + 1 + 1 + (7 * b + 1)) a c σ hA hT1 ha
    (by
      intro j hj σ' hv _ _ _ hvC
      rw [iter_add_b] at hvC ⊢
      have hjb : j * b + b ≤ a * b := by
        have := Nat.mul_le_mul_right b (show j + 1 ≤ a by omega); rwa [add_one_mul] at this
      have := cpy_spec cap B T2 C hB2 hBC h2C σ' b (c + j * b) (by rw [hv B (Ne.symm hAB) (Ne.symm h1B) hBC]; exact hB)
        (by rw [hv T2 (Ne.symm hA2) (Ne.symm h12) h2C]; exact hT2) hvC (by omega)
      rw [show c + j * b + b = c + (j + 1) * b by ring] at this
      exact this)
  rw [iter_add_b] at h
  have e : σ.setv C c = σ := by rw [← hC]; exact wsetv_same σ C
  rw [e] at h
  exact h

end Regs

/-! ## The constants -/

/-- **The constants' program.** -/
def consts (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) : WM ns nr :=
  .seq (cntW (G 2) (R 40) (R 23)) (.seq (cpy (R 23) (R 37) (R 24)) (.seq (.dec (R 24))
  (.seq (cpy (R 23) (R 37) (R 21)) (.seq (subN (R 5) (R 37) (R 21)) (.seq (.dec (R 21))
  (.seq (add2 (R 5) (R 37) (R 25)) (.seq (.inc (R 25))
  (.seq (cpy (R 23) (R 37) (R 26)) (.seq (subN (R 25) (R 37) (R 26))
  (.seq (cpy (R 0) (R 37) (R 15))
  (.seq (cloop (R 0) (R 37) (cpy (R 1) (R 38) (R 41))) (.seq (cpy (R 3) (R 37) (R 41))
  (.seq (.inc (R 31)) (.seq (cloop (R 41) (R 37) (dbl (R 31) (R 39) (R 44))) (.seq (WM.clear (R 41))
  (.seq (cloop (R 0) (R 37) (cpy (R 1) (R 38) (R 41))) (.seq (cpy (R 4) (R 37) (R 41))
  (.seq (.inc (R 35)) (.seq (cloop (R 41) (R 37) (dbl (R 35) (R 39) (R 44))) (.seq (WM.clear (R 41))
  (.seq (cloop (R 0) (R 37) (cpy (R 2) (R 38) (R 41)))
  (.seq (.inc (R 32)) (.seq (cloop (R 41) (R 37) (dbl (R 32) (R 39) (R 44))) (.seq (WM.clear (R 41))
  (.seq (cloop (R 0) (R 37) (cpy (R 1) (R 38) (R 42))) (.seq (cpy (R 3) (R 37) (R 42)) (.seq (.inc (R 42))
  (.seq (cloop (R 0) (R 37) (cpy (R 2) (R 38) (R 43))) (.inc (R 43))))))))))))))))))))))))))))))

/-- The constants' values. -/
def constSt (R : Fin 48 → Fin nr) (σ : WState ns nr) (W V hh b s fL fR : ℕ) : WState ns nr :=
  ((((((((((σ.setv (R 23) W).setv (R 24) (W - 1)).setv (R 21) (W - (V + 1) - 1)).setv (R 25) (2 * (V + 1) + 1)).setv
    (R 26) (W - (2 * (V + 1) + 1))).setv (R 15) hh).setv (R 31) (1 * 2 ^ (hh * b + fL))).setv (R 35)
    (1 * 2 ^ (hh * b + fR))).setv (R 32) (1 * 2 ^ (hh * s))).setv (R 42) (hh * b + fL + 1)).setv (R 43) (hh * s + 1)

theorem setv_back (τ : WState ns nr) (a b : Fin nr) (hab : a ≠ b) (x y : ℕ) (ha : τ.val a = 0) :
    ((τ.setv a x).setv b y).setv a 0 = τ.setv b y := by
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [WState.setv_val, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · rfl

/-- The constants' cost. -/
def constsCost (W V hh b s fL fR : ℕ) : ℕ :=
  27 * W + 3 + 1 + (W * (3 + 8) + 1 + 1 + (7 * W + 1) + 1 + (1 + 1 + (W * (3 + 8) + 1 + 1 + (7 * W + 1) + 1 + ((V + 1) * (1 + 8) + 1 + 1 + (7 * (V + 1) + 1) + 1 + (1 + 1 + ((V + 1) * (7 + 8) + 1 + 1 + (7 * (V + 1) + 1) + 1 + (3 + 1 + (W * (3 + 8) + 1 + 1 + (7 * W + 1) + 1 + ((2 * (V + 1) + 1) * (1 + 8) + 1 + 1 + (7 * (2 * (V + 1) + 1) + 1) + 1 + (hh * (3 + 8) + 1 + 1 + (7 * hh + 1) + 1 + (hh * (b * (3 + 8) + 1 + 1 + (7 * b + 1) + 8) + 1 + 1 + (7 * hh + 1) + 1 + (fL * (3 + 8) + 1 + 1 + (7 * fL + 1) + 1 + (3 + 1 + ((hh * b + fL) * (40 * (1 * 2 ^ (hh * b + fL)) + 20 + 8) + 1 + 1 + (7 * (hh * b + fL) + 1) + 1 + (3 * (hh * b + fL) + 1 + 1 + (hh * (b * (3 + 8) + 1 + 1 + (7 * b + 1) + 8) + 1 + 1 + (7 * hh + 1) + 1 + (fR * (3 + 8) + 1 + 1 + (7 * fR + 1) + 1 + (3 + 1 + ((hh * b + fR) * (40 * (1 * 2 ^ (hh * b + fR)) + 20 + 8) + 1 + 1 + (7 * (hh * b + fR) + 1) + 1 + (3 * (hh * b + fR) + 1 + 1 + (hh * (s * (3 + 8) + 1 + 1 + (7 * s + 1) + 8) + 1 + 1 + (7 * hh + 1) + 1 + (3 + 1 + ((hh * s) * (40 * (1 * 2 ^ (hh * s)) + 20 + 8) + 1 + 1 + (7 * (hh * s) + 1) + 1 + (3 * (hh * s) + 1 + 1 + (hh * (b * (3 + 8) + 1 + 1 + (7 * b + 1) + 8) + 1 + 1 + (7 * hh + 1) + 1 + (fL * (3 + 8) + 1 + 1 + (7 * fL + 1) + 1 + (3 + 1 + (hh * (s * (3 + 8) + 1 + 1 + (7 * s + 1) + 8) + 1 + 1 + (7 * hh + 1) + 1 + (3)))))))))))))))))))))))))))))

section Consts
variable (cap : ℕ) (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
include hR

set_option maxHeartbeats 4000000 in
/-- **The constants.** -/
theorem consts_spec (σ : WState ns nr) (W V hh b s fL fR : ℕ) (hOF : σ.st (G 2) = frame (binary W (2 ^ V)))
    (hOFh : σ.sh (G 2) = 0) (h0 : σ.val (R 0) = hh) (h1 : σ.val (R 1) = b) (h2 : σ.val (R 2) = s)
    (h3 : σ.val (R 3) = fL) (h4 : σ.val (R 4) = fR) (h5 : σ.val (R 5) = V + 1)
    (z15 : σ.val (R 15) = 0) (z21 : σ.val (R 21) = 0) (z23 : σ.val (R 23) = 0) (z24 : σ.val (R 24) = 0)
    (z25 : σ.val (R 25) = 0) (z26 : σ.val (R 26) = 0) (z31 : σ.val (R 31) = 0) (z32 : σ.val (R 32) = 0)
    (z35 : σ.val (R 35) = 0) (z37 : σ.val (R 37) = 0) (z38 : σ.val (R 38) = 0) (z39 : σ.val (R 39) = 0)
    (z40 : σ.val (R 40) = 0) (z41 : σ.val (R 41) = 0) (z42 : σ.val (R 42) = 0) (z43 : σ.val (R 43) = 0)
    (z44 : σ.val (R 44) = 0)
    (hcap : 2 * W + 4 * V + 2 ^ (hh * b + fL + 1) + 2 ^ (hh * b + fR + 1) + 2 ^ (hh * s + 1) + hh * b + hh * s + hh +
      b + s + fL + fR + 10 ≤ cap) :
    WExec cap (consts G R) σ (constSt R σ W V hh b s fL fR) (constsCost W V hh b s fL fR) := by
  have rne : ∀ a b : Fin 48, a ≠ b → R a ≠ R b := fun a b h => hR.ne h
  have p1 : 1 ≤ 2 ^ (hh * b + fL + 1) := Nat.one_le_two_pow
  have p2 : 1 ≤ 2 ^ (hh * b + fR + 1) := Nat.one_le_two_pow
  have p3 : 1 ≤ 2 ^ (hh * s + 1) := Nat.one_le_two_pow
  have q1 : 2 * (1 * 2 ^ (hh * b + fL)) < cap := by rw [Nat.one_mul, ← pow_succ']; omega
  have q2 : 2 * (1 * 2 ^ (hh * b + fR)) < cap := by rw [Nat.one_mul, ← pow_succ']; omega
  have q3 : 2 * (1 * 2 ^ (hh * s)) < cap := by rw [Nat.one_mul, ← pow_succ']; omega
  have hb2 : hh * b ≤ 2 ^ (hh * b + fL + 1) := by
    have := Nat.lt_two_pow_self (n := hh * b + fL + 1); omega
  have hs2 : hh * s ≤ 2 ^ (hh * s + 1) := by
    have := Nat.lt_two_pow_self (n := hh * s + 1); omega
  -- R23 := W
  have x1 := cntW_spec cap (G 2) (R 40) (R 23) (rne _ _ (by decide)) (binary W (2 ^ V)) σ hOF hOFh z40
    (by simp; omega) (by rw [z23]; simp; omega)
  rw [z23, binary_length, Nat.zero_add] at x1
  -- R24 := W − 1
  have x2 := cpy_spec cap (R 23) (R 37) (R 24) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide))
    (σ.setv (R 23) W) W 0 (by simp) (by simp [Function.update_apply, hR.eq_iff, z37])
    (by simp [Function.update_apply, hR.eq_iff, z24]) (by omega)
  rw [Nat.zero_add] at x2
  have x3 := WExec.dec (cap := cap) (R 24) ((σ.setv (R 23) W).setv (R 24) W) (by simp; omega)
  rw [show ((σ.setv (R 23) W).setv (R 24) W).val (R 24) = W by simp, wsetv_setv] at x3
  set s2 := (σ.setv (R 23) W).setv (R 24) (W - 1) with hs2
  -- R21 := W − (V+1) − 1
  have x4 := cpy_spec cap (R 23) (R 37) (R 21) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) s2 W 0
    (by simp [hs2, Function.update_apply, hR.eq_iff]) (by simp [hs2, Function.update_apply, hR.eq_iff, z37])
    (by simp [hs2, Function.update_apply, hR.eq_iff, z21]) (by omega)
  rw [Nat.zero_add] at x4
  have x5 := subN_spec cap (R 5) (R 37) (R 21) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide))
    (s2.setv (R 21) W) (V + 1) W (by simp [hs2, Function.update_apply, hR.eq_iff, h5])
    (by simp [hs2, Function.update_apply, hR.eq_iff, z37]) (by simp) (by omega)
  rw [wsetv_setv] at x5
  have x6 := WExec.dec (cap := cap) (R 21) (s2.setv (R 21) (W - (V + 1))) (by simp; omega)
  rw [show (s2.setv (R 21) (W - (V + 1))).val (R 21) = W - (V + 1) by simp, wsetv_setv] at x6
  set s3 := s2.setv (R 21) (W - (V + 1) - 1) with hs3
  -- R25 := 2(V+1) + 1
  have x7 := add2_spec cap (R 5) (R 37) (R 25) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) s3 (V + 1) 0
    (by simp [hs3, hs2, Function.update_apply, hR.eq_iff, h5]) (by simp [hs3, hs2, Function.update_apply, hR.eq_iff, z37])
    (by simp [hs3, hs2, Function.update_apply, hR.eq_iff, z25]) (by omega)
  rw [Nat.zero_add] at x7
  have x8 := WExec.inc (cap := cap) (R 25) (s3.setv (R 25) (2 * (V + 1))) (by simp; omega)
  rw [show (s3.setv (R 25) (2 * (V + 1))).val (R 25) = 2 * (V + 1) by simp, wsetv_setv] at x8
  set s4 := s3.setv (R 25) (2 * (V + 1) + 1) with hs4
  -- R26 := W − (2(V+1) + 1)
  have x9 := cpy_spec cap (R 23) (R 37) (R 26) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) s4 W 0
    (by simp [hs4, hs3, hs2, Function.update_apply, hR.eq_iff])
    (by simp [hs4, hs3, hs2, Function.update_apply, hR.eq_iff, z37])
    (by simp [hs4, hs3, hs2, Function.update_apply, hR.eq_iff, z26]) (by omega)
  rw [Nat.zero_add] at x9
  have x10 := subN_spec cap (R 25) (R 37) (R 26) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide))
    (s4.setv (R 26) W) (2 * (V + 1) + 1) W (by simp [hs4, Function.update_apply, hR.eq_iff])
    (by simp [hs4, hs3, hs2, Function.update_apply, hR.eq_iff, z37]) (by simp) (by omega)
  rw [wsetv_setv] at x10
  set s5 := s4.setv (R 26) (W - (2 * (V + 1) + 1)) with hs5
  -- R15 := hh
  have x11 := cpy_spec cap (R 0) (R 37) (R 15) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide)) s5 hh 0
    (by simp [hs5, hs4, hs3, hs2, Function.update_apply, hR.eq_iff, h0])
    (by simp [hs5, hs4, hs3, hs2, Function.update_apply, hR.eq_iff, z37])
    (by simp [hs5, hs4, hs3, hs2, Function.update_apply, hR.eq_iff, z15]) (by omega)
  rw [Nat.zero_add] at x11
  set s6 := s5.setv (R 15) hh with hs6
  have lk : ∀ (i : Fin 48) (x : ℕ), σ.val (R i) = x → i ≠ 23 → i ≠ 24 → i ≠ 21 → i ≠ 25 → i ≠ 26 → i ≠ 15 →
      s6.val (R i) = x := by
    intro i x hx a1 a2 a3 a4 a5 a6
    simp only [hs6, hs5, hs4, hs3, hs2, WState.setv_val, Function.update_apply, hR.eq_iff]
    rw [if_neg a6, if_neg a5, if_neg a4, if_neg a3, if_neg a2, if_neg a1]; exact hx
  -- R31 := 2^(hh·b + fL)
  have x12 := mulAdd_spec cap (R 0) (R 37) (R 1) (R 38) (R 41) (by
      have := List.Nodup.map hR (show ([0, 37, 1, 38, 41] : List (Fin 48)).Nodup by decide); simpa using this) s6 hh b 0
    (lk 0 hh h0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk 1 b h1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk 38 0 z38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk 41 0 z41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by omega) (by omega)
  rw [Nat.zero_add] at x12
  have x13 := cpy_spec cap (R 3) (R 37) (R 41) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide))
    (s6.setv (R 41) (hh * b)) fL (hh * b)
    (by rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk 3 fL h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by simp) (by omega)
  rw [wsetv_setv] at x13
  have x14 := WExec.inc (cap := cap) (R 31) (s6.setv (R 41) (hh * b + fL)) (by
    rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide)),
      lk 31 0 z31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
  rw [show (s6.setv (R 41) (hh * b + fL)).val (R 31) = 0 by
    rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
    exact lk 31 0 z31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), Nat.zero_add] at x14
  have x15 := powIn_spec cap (R 41) (R 37) (R 31) (R 39) (R 44) (by
      have := List.Nodup.map hR (show ([41, 37, 31, 39, 44] : List (Fin 48)).Nodup by decide); simpa using this)
    ((s6.setv (R 41) (hh * b + fL)).setv (R 31) 1) (hh * b + fL) 1 (by simp [Function.update_apply, hR.eq_iff])
    (by simp [Function.update_apply, hR.eq_iff]; exact lk 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [Function.update_apply, hR.eq_iff]; exact lk 39 0 z39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [Function.update_apply, hR.eq_iff]; exact lk 44 0 z44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp) q1 (by omega)
  rw [wsetv_setv] at x15
  have x16 := wclear_spec cap (R 41) (hh * b + fL) ((s6.setv (R 41) (hh * b + fL)).setv (R 31) (1 * 2 ^ (hh * b + fL)))
    (by simp [Function.update_apply, hR.eq_iff]) (by simp [Function.update_apply, hR.eq_iff]; omega)
  rw [setv_back _ _ _ (rne _ _ (by decide)) _ _ (lk 41 0 z41 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide))] at x16
  set s7 := s6.setv (R 31) (1 * 2 ^ (hh * b + fL)) with hs7
  have lk7 : ∀ (i : Fin 48) (x : ℕ), s6.val (R i) = x → i ≠ 31 → s7.val (R i) = x := by
    intro i x hx a; simp only [hs7, WState.setv_val, Function.update_apply, hR.eq_iff]; rw [if_neg a]; exact hx
  -- R35 := 2^(hh·b + fR)
  have x17 := mulAdd_spec cap (R 0) (R 37) (R 1) (R 38) (R 41) (by
      have := List.Nodup.map hR (show ([0, 37, 1, 38, 41] : List (Fin 48)).Nodup by decide); simpa using this) s7 hh b 0
    (lk7 0 hh (lk 0 hh h0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (lk7 37 0 (lk 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (lk7 1 b (lk 1 b h1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (lk7 38 0 (lk 38 0 z38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (lk7 41 0 (lk 41 0 z41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (by omega) (by omega)
  rw [Nat.zero_add] at x17
  have x18 := cpy_spec cap (R 4) (R 37) (R 41) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide))
    (s7.setv (R 41) (hh * b)) fR (hh * b)
    (by rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk7 4 fR (lk 4 fR h4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (by rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk7 37 0 (lk 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (by simp) (by omega)
  rw [wsetv_setv] at x18
  have hs7_35 : s7.val (R 35) = 0 :=
    lk7 35 0 (lk 35 0 z35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)
  have x19 := WExec.inc (cap := cap) (R 35) (s7.setv (R 41) (hh * b + fR)) (by
    rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide)), hs7_35]; omega)
  rw [show (s7.setv (R 41) (hh * b + fR)).val (R 35) = 0 by
    rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide)), hs7_35], Nat.zero_add] at x19
  have x20 := powIn_spec cap (R 41) (R 37) (R 35) (R 39) (R 44) (by
      have := List.Nodup.map hR (show ([41, 37, 35, 39, 44] : List (Fin 48)).Nodup by decide); simpa using this)
    ((s7.setv (R 41) (hh * b + fR)).setv (R 35) 1) (hh * b + fR) 1 (by simp [Function.update_apply, hR.eq_iff])
    (by simp [Function.update_apply, hR.eq_iff];
        exact lk7 37 0 (lk 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (by simp [Function.update_apply, hR.eq_iff];
        exact lk7 39 0 (lk 39 0 z39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (by simp [Function.update_apply, hR.eq_iff];
        exact lk7 44 0 (lk 44 0 z44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))
    (by simp) q2 (by omega)
  rw [wsetv_setv] at x20
  have x21 := wclear_spec cap (R 41) (hh * b + fR) ((s7.setv (R 41) (hh * b + fR)).setv (R 35) (1 * 2 ^ (hh * b + fR)))
    (by simp [Function.update_apply, hR.eq_iff]) (by simp [Function.update_apply, hR.eq_iff]; omega)
  rw [setv_back _ _ _ (rne _ _ (by decide)) _ _
    (lk7 41 0 (lk 41 0 z41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide))] at x21
  set s8 := s7.setv (R 35) (1 * 2 ^ (hh * b + fR)) with hs8
  have lk8 : ∀ (i : Fin 48) (x : ℕ), σ.val (R i) = x → i ≠ 23 → i ≠ 24 → i ≠ 21 → i ≠ 25 → i ≠ 26 → i ≠ 15 →
      i ≠ 31 → i ≠ 35 → s8.val (R i) = x := by
    intro i x hx a1 a2 a3 a4 a5 a6 a7 a8
    simp only [hs8, WState.setv_val, Function.update_apply, hR.eq_iff]; rw [if_neg a8]
    exact lk7 i x (lk i x hx a1 a2 a3 a4 a5 a6) a7
  -- R32 := 2^(hh·s)
  have x22 := mulAdd_spec cap (R 0) (R 37) (R 2) (R 38) (R 41) (by
      have := List.Nodup.map hR (show ([0, 37, 2, 38, 41] : List (Fin 48)).Nodup by decide); simpa using this) s8 hh s 0
    (lk8 0 hh h0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk8 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk8 2 s h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk8 38 0 z38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk8 41 0 z41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by omega) (by omega)
  rw [Nat.zero_add] at x22
  have hs8_32 : s8.val (R 32) = 0 :=
    lk8 32 0 z32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have x23 := WExec.inc (cap := cap) (R 32) (s8.setv (R 41) (hh * s)) (by
    rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide)), hs8_32]; omega)
  rw [show (s8.setv (R 41) (hh * s)).val (R 32) = 0 by
    rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide)), hs8_32], Nat.zero_add] at x23
  have x24 := powIn_spec cap (R 41) (R 37) (R 32) (R 39) (R 44) (by
      have := List.Nodup.map hR (show ([41, 37, 32, 39, 44] : List (Fin 48)).Nodup by decide); simpa using this)
    ((s8.setv (R 41) (hh * s)).setv (R 32) 1) (hh * s) 1 (by simp [Function.update_apply, hR.eq_iff])
    (by simp [Function.update_apply, hR.eq_iff];
        exact lk8 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [Function.update_apply, hR.eq_iff];
        exact lk8 39 0 z39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp [Function.update_apply, hR.eq_iff];
        exact lk8 44 0 z44 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simp) q3 (by omega)
  rw [wsetv_setv] at x24
  have x25 := wclear_spec cap (R 41) (hh * s) ((s8.setv (R 41) (hh * s)).setv (R 32) (1 * 2 ^ (hh * s)))
    (by simp [Function.update_apply, hR.eq_iff]) (by simp [Function.update_apply, hR.eq_iff]; omega)
  rw [setv_back _ _ _ (rne _ _ (by decide)) _ _
    (lk8 41 0 z41 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))] at x25
  set s9 := s8.setv (R 32) (1 * 2 ^ (hh * s)) with hs9
  have lk9 : ∀ (i : Fin 48) (x : ℕ), σ.val (R i) = x → i ≠ 23 → i ≠ 24 → i ≠ 21 → i ≠ 25 → i ≠ 26 → i ≠ 15 →
      i ≠ 31 → i ≠ 35 → i ≠ 32 → s9.val (R i) = x := by
    intro i x hx a1 a2 a3 a4 a5 a6 a7 a8 a9
    simp only [hs9, WState.setv_val, Function.update_apply, hR.eq_iff]; rw [if_neg a9]
    exact lk8 i x hx a1 a2 a3 a4 a5 a6 a7 a8
  -- R42 := hh·b + fL + 1
  have x26 := mulAdd_spec cap (R 0) (R 37) (R 1) (R 38) (R 42) (by
      have := List.Nodup.map hR (show ([0, 37, 1, 38, 42] : List (Fin 48)).Nodup by decide); simpa using this) s9 hh b 0
    (lk9 0 hh h0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk9 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk9 1 b h1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk9 38 0 z38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (lk9 42 0 z42 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by omega) (by omega)
  rw [Nat.zero_add] at x26
  have x27 := cpy_spec cap (R 3) (R 37) (R 42) (rne _ _ (by decide)) (rne _ _ (by decide)) (rne _ _ (by decide))
    (s9.setv (R 42) (hh * b)) fL (hh * b)
    (by rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk9 3 fL h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide))
    (by rw [WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk9 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)) (by simp) (by omega)
  rw [wsetv_setv] at x27
  have x28 := WExec.inc (cap := cap) (R 42) (s9.setv (R 42) (hh * b + fL)) (by simp; omega)
  rw [show (s9.setv (R 42) (hh * b + fL)).val (R 42) = hh * b + fL by simp, wsetv_setv] at x28
  set s10 := s9.setv (R 42) (hh * b + fL + 1) with hs10
  -- R43 := hh·s + 1
  have x29 := mulAdd_spec cap (R 0) (R 37) (R 2) (R 38) (R 43) (by
      have := List.Nodup.map hR (show ([0, 37, 2, 38, 43] : List (Fin 48)).Nodup by decide); simpa using this) s10 hh s 0
    (by rw [hs10, WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk9 0 hh h0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide))
    (by rw [hs10, WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk9 37 0 z37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide))
    (by rw [hs10, WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk9 2 s h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide))
    (by rw [hs10, WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk9 38 0 z38 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide))
    (by rw [hs10, WState.setv_val, Function.update_of_ne (rne _ _ (by decide))];
        exact lk9 43 0 z43 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide))
    (by omega) (by omega)
  rw [Nat.zero_add] at x29
  have x30 := WExec.inc (cap := cap) (R 43) (s10.setv (R 43) (hh * s)) (by simp; omega)
  rw [show (s10.setv (R 43) (hh * s)).val (R 43) = hh * s by simp, wsetv_setv] at x30
  unfold consts constSt constsCost
  exact (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6 (WExec.seq x7 (WExec.seq x8
    (WExec.seq x9 (WExec.seq x10 (WExec.seq x11 (WExec.seq x12 (WExec.seq x13 (WExec.seq x14 (WExec.seq x15 (WExec.seq x16
    (WExec.seq x17 (WExec.seq x18 (WExec.seq x19 (WExec.seq x20 (WExec.seq x21 (WExec.seq x22 (WExec.seq x23 (WExec.seq x24
    (WExec.seq x25 (WExec.seq x26 (WExec.seq x27 (WExec.seq x28 (WExec.seq x29 x30)))))))))))))))))))))))))))))

end Consts

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
