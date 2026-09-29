import Proof.Wire_3_5.Primitive.SeedFix.C4KWn

/-! # C4KW, part 14: stage B2's emission and erasure

* **`emitB_spec`**: from a width-`W` word `frame (binary W p)` (`p < 2^W`, head `0`), append the letter code
  `cw e₀ e₁ (Nat.bits p)` and a terminator to the output `O`: per bit, a `1` flushes the held-back zeros (register
  `z`, each as `e₀`) and writes `e₁`, a `0` is held back; the word is kept and rewound (position count `q`), `z`, `q`
  back at `0`. `frame_cw` / `frame2_cw`: `frame` and `frame ∘ frame` are such codes.
* **`eraseF_spec`**: a framed word `frame w` overwritten by falses (`2|w| + 1` of them).

Paper quantity of the main type: `Nat.bits` of the cleared weights (the Hb printer's stream `WT`, P3:2280-2281). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Reading a framed word -/

theorem rd_prs : ∀ (w : List Bool) (i : ℕ) (t : List Bool), i < w.length →
    readTapeBit (prs w ++ t) (2 * i) = true ∧ readTapeBit (prs w ++ t) (2 * i + 1) = w.getD i false
  | [], _, _, h => absurd h (by simp)
  | b :: w, 0, t, _ => ⟨rfl, rfl⟩
  | b :: w, i + 1, t, h => by
    have ih := rd_prs w i t (by simp at h; omega)
    have e : prs (b :: w) ++ t = true :: b :: (prs w ++ t) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]; exact ih.1
    · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring]; exact ih.2

theorem rd_frame_end (w : List Bool) : readTapeBit (frame w) (2 * w.length) = false := by
  rw [frame_prs]
  simp only [readTapeBit]
  rw [List.getD_append_right _ _ _ _ (by rw [prs_length])]
  simp [prs_length]

theorem binary_getD : ∀ (W p i : ℕ), i < W → (binary W p).getD i false = (p / 2 ^ i % 2 == 1)
  | 0, _, _, h => absurd h (by omega)
  | W + 1, p, 0, _ => by simp [binary]
  | W + 1, p, i + 1, h => by
    have ih := binary_getD W (p / 2) i (by omega)
    show (binary W (p / 2)).getD i false = _
    rw [ih, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-! ## Flushing held-back zeros -/

/-- `z` times the word `u` onto `O`. -/
def flushZ (O : Fin (ns + 1)) (z : Fin nr) (u : List Bool) : WM ns nr := .whr z (.seq (.dec z) (wlist O u))

theorem flush_spec (O : Fin (ns + 1)) (z : Fin nr) (u : List Bool) : ∀ (n : ℕ) (σ : WState ns nr), σ.val z = n →
    σ.sh O = (σ.st O).length → n ≤ cap →
    WExec cap (flushZ O z u) σ ((apd σ O (repW n u)).setv z 0) (n * (4 * u.length + 4) + 1)
  | 0, σ, h0, hO, _ => by
    rw [repW_zero, apd_nil σ O hO, ← h0, wsetv_same]
    exact WExec.mono (WExec.whrF h0) (by omega)
  | n + 1, σ, h0, hO, hn => by
    have t1 := WExec.dec (cap := cap) z σ (by omega)
    rw [h0] at t1
    have t2 := wlist_spec cap O u (σ.setv z (n + 1 - 1)) hO
    have ih := flush_spec O z u n (apd (σ.setv z (n + 1 - 1)) O u) (by simp [apd])
      (by rw [apd_sh_d, apd_st_d, List.length_append]) (by omega)
    have e : (apd (apd (σ.setv z (n + 1 - 1)) O u) O (repW n u)).setv z 0 =
        (apd σ O (repW (n + 1) u)).setv z 0 := by
      rw [apd_apd, ← repW_succ]
      refine WState.eq rfl rfl ?_ rfl
      funext r; by_cases hr : r = z <;> simp [apd, hr]
    rw [e] at ih
    refine WExec.mono (WExec.whrT (by omega) (WExec.seq t1 t2) ih) ?_
    rw [Nat.add_mul, Nat.one_mul]; omega

/-! ## `Nat.bits` of a width-`W` word -/

/-- The bits of `l` coded letter by letter (`e₀` for a `0`, `e₁` for a `1`). -/
def cw (e0 e1 : List Bool) (l : List Bool) : List Bool := l.flatMap fun b => if b then e1 else e0

theorem cw_append (e0 e1 u v : List Bool) : cw e0 e1 (u ++ v) = cw e0 e1 u ++ cw e0 e1 v := by simp [cw]

theorem cw_rep_false (e0 e1 : List Bool) (k : ℕ) : cw e0 e1 (List.replicate k false) = repW k e0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, repW_succ, ← ih]; simp [cw]

theorem cw_true (e0 e1 : List Bool) : cw e0 e1 [true] = e1 := by simp [cw]

theorem cw_nil (e0 e1 : List Bool) : cw e0 e1 [] = [] := rfl

/-- `frame (frame w)` is the letter code `[true, true, true, b]` and `[true, false]`, then the terminator. -/
theorem frame2_cw (w : List Bool) : prs (frame w) = cw [true, true, true, false] [true, true, true, true] w ++ [true, false] := by
  rw [frame_prs, prs_append]
  congr 1
  induction w with
  | nil => rfl
  | cons b w ih =>
    have e1 : prs (prs (b :: w)) = [true, true, true, b] ++ prs (prs w) := by simp [prs]
    rw [e1, ih]; cases b <;> simp [cw]

/-- One bit: to the bit, flush and write `1`, or hold back a `0`; to the next marker; count two positions. -/
def ebBody (O P : Fin (ns + 1)) (z q : Fin nr) (e0 e1 : List Bool) : WM ns nr :=
  .seq (.fwd P) (.seq (.ifs P (.seq (flushZ O z e0) (wlist O e1)) (.inc z))
    (.seq (.fwd P) (.seq (.inc q) (.inc q))))

/-- **Append `frame (Nat.bits p)`** from the word `frame (binary W p)`. -/
def emitB (O P : Fin (ns + 1)) (z q : Fin nr) (e0 e1 tm : List Bool) : WM ns nr :=
  .seq (.whs P (ebBody O P z q e0 e1)) (.seq (wlist O tm) (.seq (WM.clear z) (WM.rewind P q)))

@[simp] theorem apd_val (τ : WState ns nr) (d : Fin (ns + 1)) (x : List Bool) : (apd τ d x).val = τ.val := rfl
@[simp] theorem apd_cell (τ : WState ns nr) (d : Fin (ns + 1)) (x : List Bool) : (apd τ d x).cell = τ.cell := rfl

/-- The emission's state after `i` bits (relative to its entry `σ`). -/
structure EB (σ : WState ns nr) (O P : Fin (ns + 1)) (z q : Fin nr) (e0 e1 : List Bool) (p i : ℕ) (τ : WState ns nr) :
    Prop where
  o : τ.st O = σ.st O ++ cw e0 e1 (Nat.bits (p % 2 ^ i))
  oh : τ.sh O = (τ.st O).length
  pw : τ.st P = σ.st P
  ph : τ.sh P = 2 * i
  zv : τ.val z = i - (Nat.bits (p % 2 ^ i)).length
  qv : τ.val q = 2 * i
  st : ∀ j, j ≠ O → j ≠ P → τ.st j = σ.st j
  sh : ∀ j, j ≠ O → j ≠ P → τ.sh j = σ.sh j
  vl : ∀ r, r ≠ z → r ≠ q → τ.val r = σ.val r
  cl : τ.cell = σ.cell

section Emit
variable {O P : Fin (ns + 1)} {z q : Fin nr} (hOP : O ≠ P) (hzq : z ≠ q)
include hOP hzq

theorem eb_step (e0 e1 : List Bool) (h0l : e0.length ≤ 4) (h1l : e1.length ≤ 4) (σ : WState ns nr) (W p i : ℕ)
    (hP : σ.st P = frame (binary W p)) (hi : i < W)
    (hc : 2 * W + 2 ≤ cap) (τ : WState ns nr) (h : EB σ O P z q e0 e1 p i τ) :
    ∃ τ' : WState ns nr, WExec cap (ebBody O P z q e0 e1) τ τ' (20 * W + 40) ∧ EB σ O P z q e0 e1 p (i + 1) τ' := by
  have hbl := bits_length_le (p % 2 ^ i) i (Nat.mod_lt _ (Nat.two_pow_pos i))
  have hPl : (binary W p).length = W := SignedSortKey.binary_length W p
  have rd := rd_prs (binary W p) i [false] (by rw [hPl]; exact hi)
  rw [← frame_prs] at rd
  have hms := bits_mod_succ p i
  have hPO : P ≠ O := Ne.symm hOP
  have hqz : q ≠ z := Ne.symm hzq
  have t1 := WExec.fwd (cap := cap) P τ
  rw [h.ph] at t1
  have hbit : wbit (τ.seth P (2 * i + 1)) P = (p / 2 ^ i % 2 == 1) := by
    show readTapeBit ((τ.seth P (2 * i + 1)).st P) ((τ.seth P (2 * i + 1)).sh P) = _
    simp only [WState.seth_st, WState.seth_sh, Function.update_self]
    rw [h.pw, hP, rd.2, binary_getD W p i hi]
  rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ i) with h0 | h1
  · have hbit0 : wbit (τ.seth P (2 * i + 1)) P = false := by rw [hbit, h0]; rfl
    have t2 := WExec.inc (cap := cap) z (τ.seth P (2 * i + 1)) (by simp [h.zv]; omega)
    have t3 := WExec.fwd (cap := cap) P ((τ.seth P (2 * i + 1)).setv z ((τ.seth P (2 * i + 1)).val z + 1))
    have t4 := WExec.inc (cap := cap) q (((τ.seth P (2 * i + 1)).setv z ((τ.seth P (2 * i + 1)).val z + 1)).seth P
      (((τ.seth P (2 * i + 1)).setv z ((τ.seth P (2 * i + 1)).val z + 1)).sh P + 1)) (by simp [hqz, h.qv]; omega)
    have t5 := WExec.inc (cap := cap) q ((((τ.seth P (2 * i + 1)).setv z ((τ.seth P (2 * i + 1)).val z + 1)).seth P
      (((τ.seth P (2 * i + 1)).setv z ((τ.seth P (2 * i + 1)).val z + 1)).sh P + 1)).setv q
      ((((τ.seth P (2 * i + 1)).setv z ((τ.seth P (2 * i + 1)).val z + 1)).seth P
      (((τ.seth P (2 * i + 1)).setv z ((τ.seth P (2 * i + 1)).val z + 1)).sh P + 1)).val q + 1))
      (by simp [hqz, h.qv]; omega)
    refine ⟨_, WExec.mono (WExec.seq t1 (WExec.seq (WExec.ifsF hbit0 t2) (WExec.seq t3 (WExec.seq t4 t5))))
      (by omega), ?_⟩
    rw [if_neg (by omega)] at hms
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun r h1 h2 => ?_, ?_⟩
    · simp only [WState.setv_st, WState.seth_st]; rw [h.o, hms]
    · simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh]
      rw [Function.update_of_ne hOP, Function.update_of_ne hOP, h.oh]
    · simp only [WState.setv_st, WState.seth_st]; exact h.pw
    · simp only [WState.setv_sh, WState.seth_sh, Function.update_self]; omega
    · simp only [WState.setv_val, WState.seth_val, Function.update_of_ne hzq, Function.update_self]
      rw [h.zv, hms]; omega
    · simp only [WState.setv_val, WState.seth_val, Function.update_self, Function.update_of_ne hqz]
      rw [h.qv]; omega
    · simp only [WState.setv_st, WState.seth_st]; exact h.st j h1 h2
    · simp only [WState.setv_sh, WState.seth_sh]
      rw [Function.update_of_ne h2, Function.update_of_ne h2]; exact h.sh j h1 h2
    · simp [h1, h2]; exact h.vl r h1 h2
    · simp; exact h.cl
  · have hbit1 : wbit (τ.seth P (2 * i + 1)) P = true := by rw [hbit, h1]; rfl
    have hO1 : (τ.seth P (2 * i + 1)).sh O = ((τ.seth P (2 * i + 1)).st O).length := by
      simp only [WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne hOP]; exact h.oh
    have t2 := flush_spec cap O z e0 (i - (Nat.bits (p % 2 ^ i)).length) (τ.seth P (2 * i + 1)) (by simp [h.zv])
      hO1 (by omega)
    set τ2 := (apd (τ.seth P (2 * i + 1)) O (repW (i - (Nat.bits (p % 2 ^ i)).length) e0)).setv z 0
      with hτ2
    have hO2 : τ2.sh O = (τ2.st O).length := by
      rw [hτ2]; simp only [WState.setv_sh, WState.setv_st]; rw [apd_sh_d, apd_st_d, List.length_append]
    have t3 := wlist_spec cap O e1 τ2 hO2
    have t4 := WExec.fwd (cap := cap) P (apd τ2 O e1)
    set τ4 := (apd τ2 O e1).seth P ((apd τ2 O e1).sh P + 1) with hτ4
    have t5 := WExec.inc (cap := cap) q τ4 (by rw [hτ4, hτ2]; simp [hqz, h.qv]; omega)
    have t6 := WExec.inc (cap := cap) q (τ4.setv q (τ4.val q + 1)) (by rw [hτ4, hτ2]; simp [hqz, h.qv]; omega)
    have hzl : (i - (Nat.bits (p % 2 ^ i)).length) * (4 * e0.length + 4) ≤ W * 20 :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨_, WExec.mono (WExec.seq t1 (WExec.seq (WExec.ifsT hbit1 (WExec.seq t2 t3))
      (WExec.seq t4 (WExec.seq t5 t6)))) (by omega), ?_⟩
    rw [if_pos h1] at hms
    have eO : cw e0 e1 (Nat.bits (p % 2 ^ i)) ++ repW (i - (Nat.bits (p % 2 ^ i)).length) e0 ++ e1 =
        cw e0 e1 (Nat.bits (p % 2 ^ i) ++ List.replicate (i - (Nat.bits (p % 2 ^ i)).length) false ++ [true]) := by
      rw [cw_append, cw_append, cw_rep_false, cw_true]
    have hbl2 : (Nat.bits (p % 2 ^ (i + 1))).length = i + 1 := by
      rw [hms]; simp only [List.length_append, List.length_replicate, List.length_singleton]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun j j1 j2 => ?_, fun j j1 j2 => ?_, fun r r1 r2 => ?_, ?_⟩
    · rw [hτ4, hτ2]; simp only [WState.setv_st, WState.seth_st, apd_st_d]
      rw [h.o, hms, ← eO]; simp only [List.append_assoc]
    · rw [hτ4, hτ2]
      simp only [WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, apd_st_d,
        Function.update_of_ne hOP, apd_sh_d, List.length_append]
    · rw [hτ4, hτ2]; simp only [WState.setv_st, WState.seth_st, apd_st_ne _ _ _ hPO]; exact h.pw
    · rw [hτ4, hτ2]
      simp only [WState.setv_sh, WState.seth_sh, Function.update_self, apd_sh_ne _ _ _ hPO]
      omega
    · rw [hτ4, hτ2]
      simp only [WState.setv_val, WState.seth_val, apd_val, Function.update_of_ne hzq, Function.update_self]
      omega
    · rw [hτ4, hτ2]
      simp only [WState.setv_val, WState.seth_val, apd_val, Function.update_self, Function.update_of_ne hqz]
      rw [h.qv]; omega
    · rw [hτ4, hτ2]; simp only [WState.setv_st, WState.seth_st]
      rw [apd_st_ne _ _ _ j1, WState.setv_st, apd_st_ne _ _ _ j1, WState.seth_st]; exact h.st j j1 j2
    · rw [hτ4, hτ2]; simp only [WState.setv_sh, WState.seth_sh]
      rw [Function.update_of_ne j2, apd_sh_ne _ _ _ j1, WState.setv_sh, apd_sh_ne _ _ _ j1, WState.seth_sh,
        Function.update_of_ne j2]
      exact h.sh j j1 j2
    · rw [hτ4, hτ2]; simp [r1, r2]; exact h.vl r r1 r2
    · rw [hτ4, hτ2]; simp; exact h.cl

theorem eb_loop (e0 e1 : List Bool) (h0l : e0.length ≤ 4) (h1l : e1.length ≤ 4) (σ : WState ns nr) (W p : ℕ)
    (hP : σ.st P = frame (binary W p)) (hc : 2 * W + 2 ≤ cap) :
    ∀ (k i : ℕ) (τ : WState ns nr), i + k = W → EB σ O P z q e0 e1 p i τ →
      ∃ τ' : WState ns nr, WExec cap (.whs P (ebBody O P z q e0 e1)) τ τ' (k * (20 * W + 42) + 1) ∧
        EB σ O P z q e0 e1 p W τ'
  | 0, i, τ, hk, h => by
    have hiW : i = W := by omega
    subst hiW
    refine ⟨τ, WExec.mono (WExec.whsF ?_) (by omega), h⟩
    show readTapeBit (τ.st P) (τ.sh P) = false
    rw [h.pw, hP, h.ph]
    have := rd_frame_end (binary i p); rwa [SignedSortKey.binary_length] at this
  | k + 1, i, τ, hk, h => by
    obtain ⟨τ1, t1, h1⟩ := eb_step cap hOP hzq e0 e1 h0l h1l σ W p i hP (by omega) hc τ h
    obtain ⟨τ2, t2, h2⟩ := eb_loop e0 e1 h0l h1l σ W p hP hc k (i + 1) τ1 (by omega) h1
    have hb : wbit τ P = true := by
      show readTapeBit (τ.st P) (τ.sh P) = true
      rw [h.pw, hP, h.ph]
      have hPl : (binary W p).length = W := SignedSortKey.binary_length W p
      have rd := rd_prs (binary W p) i [false] (by rw [hPl]; omega)
      rw [← frame_prs] at rd; exact rd.1
    exact ⟨τ2, WExec.mono (WExec.whsT hb t1 t2) (by rw [Nat.add_mul, Nat.one_mul]; omega), h2⟩

/-- The emission's cost. -/
def emitCostB (W : ℕ) : ℕ := W * (20 * W + 42) + 13 * W + 40

/-- **The coded `Nat.bits` of a width-`W` word, appended** (then the terminator `tm`). -/
theorem emitB_spec (e0 e1 tm : List Bool) (h0l : e0.length ≤ 4) (h1l : e1.length ≤ 4) (htl : tm.length ≤ 4)
    (σ : WState ns nr) (W p : ℕ) (hP : σ.st P = frame (binary W p)) (hP0 : σ.sh P = 0)
    (hO : σ.sh O = (σ.st O).length) (hz : σ.val z = 0) (hq : σ.val q = 0) (hp : p < 2 ^ W)
    (hc : 2 * W + 2 ≤ cap) :
    WExec cap (emitB O P z q e0 e1 tm) σ (apd σ O (cw e0 e1 (Nat.bits p) ++ tm)) (emitCostB W) := by
  have hPO : P ≠ O := Ne.symm hOP
  have hqz : q ≠ z := Ne.symm hzq
  have h0 : EB σ O P z q e0 e1 p 0 σ := ⟨by rw [pow_zero, Nat.mod_one, Nat.zero_bits, cw_nil, List.append_nil], hO, rfl,
    by rw [hP0],
    by rw [pow_zero, Nat.mod_one, Nat.zero_bits, hz]; rfl, by rw [hq],
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl⟩
  obtain ⟨τ, t1, hτ⟩ := eb_loop cap hOP hzq e0 e1 h0l h1l σ W p hP hc W 0 σ (by omega) h0
  have hpm : p % 2 ^ W = p := Nat.mod_eq_of_lt hp
  have hbl := bits_length_le p W hp
  have t2 := wlist_spec cap O tm τ hτ.oh
  have t3 := wclear_spec cap z (W - (Nat.bits (p % 2 ^ W)).length) (apd τ O tm) (by simp [hτ.zv])
    (by simp [hτ.zv]; omega)
  have t4 := wrewind_spec cap P q (2 * W) ((apd τ O tm).setv z 0) (by simp [hqz, hτ.qv])
    (by simp [hqz, hτ.qv]; omega)
  refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4))) ?_ ?_
  · refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases hjP : j = P
      · subst hjP; simp [apd_sh_ne _ _ _ hPO, hτ.ph, hP0, Function.update_of_ne hPO]
      · by_cases hjO : j = O
        · subst hjO
          simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne hOP, apd_sh_d, hτ.o, hpm,
            List.length_append]
          omega
        · simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne hjP, apd_sh_ne _ _ _ hjO]
          exact hτ.sh j hjO hjP
    · funext j
      by_cases hjO : j = O
      · subst hjO; simp only [WState.seth_st, WState.setv_st, apd_st_d, hτ.o, hpm, List.append_assoc]
      · simp only [WState.seth_st, WState.setv_st, apd_st_ne _ _ _ hjO]
        by_cases hjP : j = P
        · subst hjP; exact hτ.pw
        · exact hτ.st j hjO hjP
    · funext r
      by_cases hrq : r = q
      · subst hrq; simp [hq]
      · by_cases hrz : r = z
        · subst hrz; simp [hrq, hz]
        · simp [hrq, hrz]; exact hτ.vl r hrz hrq
    · simp; exact hτ.cl
  · unfold emitCostB
    have : W - (Nat.bits (p % 2 ^ W)).length ≤ W := Nat.sub_le _ _
    omega

end Emit

/-! ## Erasing a framed word -/

/-- Overwrite a framed word by falses (marker and bit cells), up to its terminator. -/
def eraseF (S : Fin (ns + 1)) : WM ns nr :=
  .whs S (.seq (.wr S false) (.seq (.fwd S) (.seq (.wr S false) (.fwd S))))

theorem wtb_app : ∀ (pre rest : List Bool) (x v : Bool), writeTapeBit (pre ++ x :: rest) pre.length v = pre ++ v :: rest
  | [], _, _, _ => rfl
  | a :: pre, rest, x, v => by
    show a :: writeTapeBit (pre ++ x :: rest) pre.length v = _
    rw [wtb_app pre rest x v]; rfl

theorem erase_loop (S : Fin (ns + 1)) : ∀ (w : List Bool) (i : ℕ) (σ : WState ns nr),
    σ.st S = List.replicate (2 * i) false ++ (prs w ++ [false]) → σ.sh S = 2 * i →
    WExec cap (eraseF S) σ ((σ.sets S (List.replicate (2 * (i + w.length) + 1) false)).seth S (2 * (i + w.length)))
      (w.length * 9 + 1)
  | [], i, σ, hs, hh => by
    have e : (σ.sets S (List.replicate (2 * (i + ([] : List Bool).length) + 1) false)).seth S
        (2 * (i + ([] : List Bool).length)) = σ := by
      refine WState.eq ?_ ?_ rfl rfl
      · funext j; by_cases hj : j = S
        · subst hj; simp [hh]
        · simp [Function.update_of_ne hj]
      · funext j; by_cases hj : j = S
        · subst hj
          simp only [WState.seth_st, WState.sets_st, Function.update_self]
          rw [hs, List.replicate_succ']; simp [prs]
        · simp [Function.update_of_ne hj]
    rw [e]
    refine WExec.mono (WExec.whsF ?_) (by simp)
    show readTapeBit (σ.st S) (σ.sh S) = false
    rw [hs, hh]; simp [readTapeBit, prs]
  | b :: w, i, σ, hs, hh => by
    have hb : wbit σ S = true := by
      show readTapeBit (σ.st S) (σ.sh S) = true
      rw [hs, hh]; simp [readTapeBit, prs, List.getD_append_right]
    have t1 := WExec.wr (cap := cap) S false σ
    have e1 : writeTapeBit (σ.st S) (σ.sh S) false = List.replicate (2 * i) false ++ false :: (b :: (prs w ++ [false])) := by
      rw [hs, hh]
      have := wtb_app (List.replicate (2 * i) false) (b :: (prs w ++ [false])) true false
      simp only [List.length_replicate] at this
      rw [← this]; rfl
    rw [e1] at t1
    set σ1 := σ.sets S (List.replicate (2 * i) false ++ false :: (b :: (prs w ++ [false]))) with hσ1
    have t2 := WExec.fwd (cap := cap) S σ1
    have h1 : σ1.sh S = 2 * i := by rw [hσ1]; simpa using hh
    rw [h1] at t2
    set σ2 := σ1.seth S (2 * i + 1) with hσ2
    have t3 := WExec.wr (cap := cap) S false σ2
    have e3 : writeTapeBit (σ2.st S) (σ2.sh S) false = List.replicate (2 * (i + 1)) false ++ (prs w ++ [false]) := by
      rw [hσ2, hσ1]; simp only [WState.seth_st, WState.seth_sh, WState.sets_st, Function.update_self]
      have := wtb_app (List.replicate (2 * i) false ++ [false]) (prs w ++ [false]) b false
      simp only [List.length_append, List.length_replicate, List.length_singleton, List.append_assoc,
        List.singleton_append] at this
      rw [this, show 2 * (i + 1) = 2 * i + 2 by ring, List.replicate_add]
      simp
    rw [e3] at t3
    set σ3 := σ2.sets S (List.replicate (2 * (i + 1)) false ++ (prs w ++ [false])) with hσ3
    have t4 := WExec.fwd (cap := cap) S σ3
    have h3 : σ3.sh S = 2 * i + 1 := by rw [hσ3, hσ2]; simp
    rw [h3] at t4
    have ih := erase_loop S w (i + 1) (σ3.seth S (2 * i + 1 + 1)) (by rw [hσ3]; simp)
      (by simp; ring)
    have e : ((σ3.seth S (2 * i + 1 + 1)).sets S (List.replicate (2 * (i + 1 + w.length) + 1) false)).seth S
        (2 * (i + 1 + w.length)) = (σ.sets S (List.replicate (2 * (i + (b :: w).length) + 1) false)).seth S
        (2 * (i + (b :: w).length)) := by
      rw [hσ3, hσ2, hσ1]
      simp only [List.length_cons, show i + (w.length + 1) = i + 1 + w.length by ring]
      refine WState.eq ?_ ?_ rfl rfl
      · funext j; by_cases hj : j = S
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      · funext j; by_cases hj : j = S
        · subst hj; simp
        · simp [Function.update_of_ne hj]
    rw [e] at ih
    refine WExec.mono (WExec.whsT hb (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4))) ih) ?_
    simp only [List.length_cons]; rw [Nat.add_mul, Nat.one_mul]; omega

/-- **A framed word erased**: `frame w` becomes `2|w| + 1` falses. -/
theorem eraseF_spec (S : Fin (ns + 1)) (w : List Bool) (σ : WState ns nr) (hs : σ.st S = frame w) (h0 : σ.sh S = 0) :
    WExec cap (eraseF S) σ ((σ.sets S (List.replicate (2 * w.length + 1) false)).seth S (2 * w.length))
      (w.length * 9 + 1) := by
  have := erase_loop cap S w 0 σ (by rw [hs, frame_prs]; rfl) (by rw [h0])
  simpa using this

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
