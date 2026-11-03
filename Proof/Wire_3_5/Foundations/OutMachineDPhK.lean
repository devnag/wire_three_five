import Proof.Wire_3_5.Foundations.OutMachineP5
import Proof.Wire_3_5.UnionMachine.BinW

/-! # NW phase (d), part 1: the register kit

NW's last phase prints the final pass's denominator `max (2^e·v) 1` in `T`-bit binary (P3:3044-3048, 3170-3181) from
the unary registers `T`, `e`, `v`. Generic in the layout:

* `binary_zero`, **`binary_shift`** (`binary (e + w) (2^e·v) = replicate e false ++ binary w v`);
* **`halfStep`**, **`halfStep_spec`** (`V := 0`, `H += ⌊u/2⌋`, `B := u mod 2`);
* **`zerosLoop`**, **`zerosLoop_spec`** (`E` counted down, `K` with it, one framed `0` per count on `O`);
* **`bitsLoop`**, **`bitsLoop_spec`** (`K` counted down; the framed `binary K u` on `O`, `V := u / 2^K`).

Paper quantity of the main type: the printed denominator's `T`-bit binary (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.DPh
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Out.P5 (emit emit_spec)
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR dupR_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)

theorem binary_zero : ∀ w : ℕ, binary w 0 = List.replicate w false
  | 0 => rfl
  | w + 1 => by
    show (0 % 2 == 1) :: binary w (0 / 2) = List.replicate (w + 1) false
    rw [binary_zero w]; rfl

theorem binary_shift (w v : ℕ) : ∀ e : ℕ, binary (e + w) (2 ^ e * v) = List.replicate e false ++ binary w v
  | 0 => by simp
  | e + 1 => by
    rw [show e + 1 + w = (e + w) + 1 by omega]
    show (2 ^ (e + 1) * v % 2 == 1) :: binary (e + w) (2 ^ (e + 1) * v / 2) = _
    have h1 : 2 ^ (e + 1) * v % 2 = 0 := by rw [pow_succ]; rw [show 2 ^ e * 2 * v = 2 * (2 ^ e * v) by ring]; simp
    have h2 : 2 ^ (e + 1) * v / 2 = 2 ^ e * v := by
      rw [pow_succ, show 2 ^ e * 2 * v = 2 * (2 ^ e * v) by ring]; simp
    rw [h1, h2, binary_shift w v e]
    rfl

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- `V := 0`, `H += ⌊V/2⌋`, `B := V mod 2`. -/
def halfStep (V H B : Fin nr) : WM ns nr := .whr V (.seq (.dec V) (.ifr V (.seq (.dec V) (.inc H)) (.inc B)))

theorem halfStep_spec (V H B : Fin nr) (hVH : V ≠ H) (hVB : V ≠ B) (hHB : H ≠ B) :
    ∀ (u : ℕ) (σ : WState ns nr), σ.val V = u → σ.val B = 0 → u ≤ cap → σ.val H + u ≤ cap → 1 ≤ cap →
      WExec cap (halfStep V H B) σ (((σ.setv V 0).setv H (σ.val H + u / 2)).setv B (u % 2)) (8 * u + 1) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro σ hV hB hu hH h1
    rcases u with _ | _ | k
    · refine WExec.cast cap (WExec.whrF hV) ?_ (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext q
      simp only [WState.setv_val]
      by_cases qB : q = B
      · subst qB; simp [hB]
      · by_cases qH : q = H
        · subst qH; simp [Function.update_apply, qB]
        · by_cases qV : q = V
          · subst qV; simp [Function.update_apply, qB, qH, hV]
          · simp [Function.update_apply, qB, qH, qV]
    · -- `u = 1`: the last odd unit
      have s1 := WExec.dec (cap := cap) V σ (by omega)
      have hz : (σ.setv V (σ.val V - 1)).val V = 0 := by simp [hV]
      have s2 := WExec.inc (cap := cap) B (σ.setv V (σ.val V - 1))
        (by simp [Function.update_apply, Ne.symm hVB, hB]; omega)
      have s3 := WExec.ifrF (P := .seq (.dec V) (.inc H)) hz s2
      have s4 : WExec cap (halfStep V H B) (((σ.setv V (σ.val V - 1)).setv B ((σ.setv V (σ.val V - 1)).val B + 1)))
          (((σ.setv V (σ.val V - 1)).setv B ((σ.setv V (σ.val V - 1)).val B + 1))) 1 :=
        WExec.whrF (by simp [Function.update_apply, hVB, hV])
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 s3) s4) ?_ (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext q
      simp only [WState.setv_val]
      by_cases qB : q = B
      · subst qB; simp [Function.update_apply, Ne.symm hVB, hB]
      · by_cases qH : q = H
        · subst qH; simp [Function.update_apply, qB, Ne.symm hVH]
        · by_cases qV : q = V
          · subst qV; simp [Function.update_apply, qB, qH, hV]
          · simp [Function.update_apply, qB, qH, qV]
    · -- `u = k + 2`
      have s1 := WExec.dec (cap := cap) V σ (by omega)
      set σ1 := σ.setv V (σ.val V - 1) with hσ1
      have hnz : σ1.val V ≠ 0 := by simp [hσ1, hV]
      have s2 := WExec.dec (cap := cap) V σ1 (by simp [hσ1, hV]; omega)
      set σ2 := σ1.setv V (σ1.val V - 1) with hσ2
      have s3 := WExec.inc (cap := cap) H σ2 (by simp [hσ2, hσ1, Function.update_apply, Ne.symm hVH]; omega)
      set σ3 := σ2.setv H (σ2.val H + 1) with hσ3
      have s4 := WExec.ifrT (Q := .inc B) hnz (WExec.seq s2 s3)
      have h3V : σ3.val V = k := by simp [hσ3, hσ2, hσ1, Function.update_apply, hVH, hV]
      have h3B : σ3.val B = 0 := by simp [hσ3, hσ2, hσ1, Function.update_apply, hHB.symm, hVB.symm, hB]
      have h3H : σ3.val H = σ.val H + 1 := by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hVH]
      have r := ih k (by omega) σ3 h3V h3B (by omega) (by rw [h3H]; omega) h1
      refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 s4) r) ?_ (by omega)
      refine WState.eq rfl rfl ?_ rfl
      funext q
      simp only [WState.setv_val]
      have hk2 : (k + 1 + 1) / 2 = k / 2 + 1 := by omega
      have hk3 : (k + 1 + 1) % 2 = k % 2 := by omega
      by_cases qB : q = B
      · subst qB; simp [Function.update_apply, hk3]
      · by_cases qH : q = H
        · subst qH; simp [Function.update_apply, qB, h3H, hk2]; omega
        · by_cases qV : q = V
          · subst qV; simp [Function.update_apply, qB, qH]
          · simp [Function.update_apply, qB, qH, qV, hσ3, hσ2, hσ1]

/-- One framed `0` per count of `E`, `K` counted down with it. -/
def zerosLoop (O : Fin (ns + 1)) (E K : Fin nr) : WM ns nr :=
  .whr E (.seq (.dec E) (.seq (.dec K) (.seq (emit O true) (emit O false))))

theorem zerosLoop_spec (O : Fin (ns + 1)) (E K : Fin nr) (hEK : E ≠ K) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val E = m → m ≤ σ.val K → σ.val K ≤ cap → m ≤ cap →
      σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (zerosLoop O E K) σ τ (13 * m + 1) ∧ τ.st O = σ.st O ++ marks (List.replicate m false) ∧
        τ.sh O = (τ.st O).length ∧ τ.val = Function.update (Function.update σ.val E 0) K (σ.val K - m) ∧
        (∀ i, i ≠ O → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.cell = σ.cell
  | 0, σ, hE, _, _, _, hO => by
    refine ⟨σ, WExec.mono (WExec.whrF hE) (by omega), by simp [marks], hO, ?_, fun _ _ => ⟨rfl, rfl⟩, rfl⟩
    funext q
    by_cases qK : q = K
    · subst qK; simp
    · by_cases qE : q = E
      · subst qE; simp [Function.update_apply, qK, hE]
      · simp [Function.update_apply, qK, qE]
  | m + 1, σ, hE, hm, hK, hc, hO => by
    have s1 := WExec.dec (cap := cap) E σ (by omega)
    set σ1 := σ.setv E (σ.val E - 1) with hσ1
    have s2 := WExec.dec (cap := cap) K σ1 (by simp [hσ1, Function.update_apply, Ne.symm hEK]; omega)
    set σ2 := σ1.setv K (σ1.val K - 1) with hσ2
    have s3 := emit_spec cap O true σ2 (by simp [hσ2, hσ1, hO])
    set σ3 := (σ2.sets O (σ2.st O ++ [true])).seth O ((σ2.st O).length + 1) with hσ3
    have s4 := emit_spec cap O false σ3 (by simp [hσ3])
    set σ4 := (σ3.sets O (σ3.st O ++ [false])).seth O ((σ3.st O).length + 1) with hσ4
    have h4E : σ4.val E = m := by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hEK, hE]
    have h4K : σ4.val K = σ.val K - 1 := by simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hEK]
    obtain ⟨τ, s5, e5, e5h, v5, o5, c5⟩ := zerosLoop_spec O E K hEK m σ4 h4E (by rw [h4K]; omega)
      (by rw [h4K]; omega) (by omega) (by simp [hσ4])
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) s5) (by omega),
      ?_, e5h, ?_, fun i hi => ?_, ?_⟩
    · rw [e5]; simp [hσ4, hσ3, hσ2, hσ1, marks, List.replicate_succ, List.append_assoc]
    · rw [v5]; funext q
      by_cases qK : q = K
      · subst qK; simp [h4K]; omega
      · by_cases qE : q = E
        · subst qE; simp [Function.update_apply, qK]
        · simp [Function.update_apply, qK, qE, hσ4, hσ3, hσ2, hσ1]
    · obtain ⟨a1, a2⟩ := o5 i hi
      refine ⟨a1.trans ?_, a2.trans ?_⟩
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hi]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hi]
    · rw [c5]; simp [hσ4, hσ3, hσ2, hσ1]

theorem zerosLoop_exact (O : Fin (ns + 1)) (E K : Fin nr) (hEK : E ≠ K) (m : ℕ) (σ : WState ns nr)
    (hE : σ.val E = m) (hm : m ≤ σ.val K) (hK : σ.val K ≤ cap) (hc : m ≤ cap) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (zerosLoop O E K) σ
      ((((σ.sets O (σ.st O ++ marks (List.replicate m false))).seth O ((σ.st O).length + 2 * m)).setv E 0).setv K
        (σ.val K - m)) (13 * m + 1) := by
  obtain ⟨τ, s, e1, e2, e3, e4, e5⟩ := zerosLoop_spec cap O E K hEK m σ hE hm hK hc hO
  refine WExec.cast cap s (WState.eq ?_ ?_ ?_ ?_) le_rfl
  · funext i
    by_cases hi : i = O
    · subst hi; rw [e2, e1]; simp
    · simp [Function.update_apply, hi, (e4 i hi).2]
  · funext i
    by_cases hi : i = O
    · subst hi; rw [e1]; simp
    · simp [Function.update_apply, hi, (e4 i hi).1]
  · rw [e3]; simp
  · rw [e5]; simp

theorem marks_cons (b : Bool) (l : List Bool) : marks (b :: l) = true :: b :: marks l := by
  simp [marks]

theorem frame_eq_marks (w : List Bool) : frame w = marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih, marks]

theorem binary_succ (k u : ℕ) : binary (k + 1) u = (u % 2 == 1) :: binary k (u / 2) := rfl

/-- Append the bit `u mod 2` held in the flag `B` (`B := 0`). -/
def bitOut (O : Fin (ns + 1)) (B : Fin nr) : WM ns nr := .ifr B (.seq (.dec B) (emit O true)) (emit O false)

theorem bitOut_spec (O : Fin (ns + 1)) (B : Fin nr) (u : ℕ) (σ : WState ns nr) (hB : σ.val B = u % 2)
    (hO : σ.sh O = (σ.st O).length) (h1 : 1 ≤ cap) :
    WExec cap (bitOut O B) σ (((σ.setv B 0).sets O (σ.st O ++ [u % 2 == 1])).seth O ((σ.st O).length + 1)) 6 := by
  rcases Nat.mod_two_eq_zero_or_one u with h | h
  · have e := emit_spec cap O false σ hO
    refine WExec.cast cap (WExec.ifrF (by rw [hB, h]) e) ?_ (by omega)
    refine WState.eq (by simp) (by simp [h]) ?_ rfl
    funext q
    by_cases hq : q = B
    · subst hq; simp [hB, h]
    · simp [Function.update_apply, hq]
  · have d := WExec.dec (cap := cap) B σ (by omega)
    have e := emit_spec cap O true (σ.setv B (σ.val B - 1)) (by simpa using hO)
    refine WExec.cast cap (WExec.ifrT (by omega) (WExec.seq d e)) ?_ (by omega)
    refine WState.eq (by simp) (by simp [h]) ?_ rfl
    funext q
    by_cases hq : q = B
    · subst hq; simp [hB, h]
    · simp [Function.update_apply, hq]

/-- `K` rounds: print the low bit of `V` framed, halve `V` (through `H`, `B`). -/
def bitsLoop (O : Fin (ns + 1)) (K V H B : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (halfStep V H B) (.seq (emit O true) (.seq (bitOut O B) (WM.move H V)))))

theorem bitsLoop_spec (O : Fin (ns + 1)) (K V H B : Fin nr) (hKV : K ≠ V) (hKH : K ≠ H) (hKB : K ≠ B)
    (hVH : V ≠ H) (hVB : V ≠ B) (hHB : H ≠ B) :
    ∀ (k u : ℕ) (σ : WState ns nr), σ.val K = k → σ.val V = u → σ.val H = 0 → σ.val B = 0 → k ≤ cap → u ≤ cap →
      1 ≤ cap → σ.sh O = (σ.st O).length →
      WExec cap (bitsLoop O K V H B) σ
        ((((σ.sets O (σ.st O ++ marks (binary k u))).seth O ((σ.st O).length + 2 * k)).setv K 0).setv V
          (u / 2 ^ k)) (k * (16 * u + 20) + 1)
  | 0, u, σ, hK, hV, _, _, _, _, _, hO => by
    refine WExec.cast cap (WExec.whrF hK) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i
      by_cases hi : i = O
      · subst hi; simp [hO]
      · simp [Function.update_apply, hi]
    · funext i
      by_cases hi : i = O
      · subst hi; simp [binary, marks]
      · simp [Function.update_apply, hi]
    · funext q
      by_cases hq : q = V
      · subst hq; simp [hV]
      · by_cases hq' : q = K
        · subst hq'; simp [Function.update_apply, hq, hK]
        · simp [Function.update_apply, hq, hq']
  | k + 1, u, σ, hK, hV, hH, hB, hk, hu, h1, hO => by
    have s1 := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have s2 := halfStep_spec cap V H B hVH hVB hHB u σ1 (by simp [hσ1, Function.update_apply, Ne.symm hKV, hV])
      (by simp [hσ1, Function.update_apply, Ne.symm hKB, hB]) hu
      (by simp [hσ1, Function.update_apply, Ne.symm hKH, hH]; omega) h1
    set σ2 := ((σ1.setv V 0).setv H (σ1.val H + u / 2)).setv B (u % 2) with hσ2
    have s3 := emit_spec cap O true σ2 (by simp [hσ2, hσ1, hO])
    set σ3 := (σ2.sets O (σ2.st O ++ [true])).seth O ((σ2.st O).length + 1) with hσ3
    have s4 := bitOut_spec cap O B u σ3 (by simp [hσ3, hσ2]) (by simp [hσ3]) h1
    set σ4 := ((σ3.setv B 0).sets O (σ3.st O ++ [u % 2 == 1])).seth O ((σ3.st O).length + 1) with hσ4
    have h4H : σ4.val H = u / 2 := by
      simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hHB, Ne.symm hKH, hH]
    have h4V : σ4.val V = 0 := by simp [hσ4, hσ3, hσ2, Function.update_apply, hVB, hVH]
    have s5 := wmove_spec cap H V (Ne.symm hVH) (u / 2) σ4 h4H (by rw [h4H]; omega) (by rw [h4H, h4V]; omega)
    set σ5 := (σ4.setv H 0).setv V (σ4.val V + σ4.val H) with hσ5
    have r := bitsLoop_spec O K V H B hKV hKH hKB hVH hVB hHB k (u / 2) σ5
      (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hKV, hKH, hKB, hK])
      (by simp [hσ5, h4V, h4H])
      (by simp [hσ5, Function.update_apply, Ne.symm hVH])
      (by simp [hσ5, hσ4, Function.update_apply, Ne.symm hHB, Ne.symm hVB])
      (by omega) (by omega) h1 (by simp [hσ5, hσ4, hσ3])
    have hm : k * (16 * (u / 2) + 20) ≤ k * (16 * u + 20) := Nat.mul_le_mul_left _ (by omega)
    have hs : (k + 1) * (16 * u + 20) = k * (16 * u + 20) + (16 * u + 20) := by ring
    have hdiv : u / 2 / 2 ^ k = u / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) r)
      ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ ?_
    · funext i
      by_cases hi : i = O
      · subst hi; simp [hσ5, hσ4, hσ3, hσ2, hσ1] <;> omega
      · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hi]
    · funext i
      by_cases hi : i = O
      · subst hi; simp [hσ5, hσ4, hσ3, hσ2, hσ1, binary_succ, marks_cons]
      · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hi]
    · funext q
      by_cases qV : q = V
      · subst qV; simp [hdiv]
      · by_cases qK : q = K
        · subst qK; simp [qV]
        · by_cases qH : q = H
          · subst qH; simp [hσ5, Function.update_apply, qV, qK, hH]
          · by_cases qB : q = B
            · subst qB; simp [hσ5, hσ4, Function.update_apply, qV, qK, qH, hB]
            · simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, qV, qK, qH, qB]
    · simp [hσ5, hσ4, hσ3, hσ2, hσ1]

/-- `rE := 0`, `rV := 1` when `rV = 0` (the denominator `max (2^e·v) 1` as `2^{e'}·v'` with `v' ≥ 1`). -/
def normE (rE rV : Fin nr) : WM ns nr := .ifr rV .skip (.seq (WM.clear rE) (.inc rV))

theorem normE_spec (rE rV : Fin nr) (hEV : rE ≠ rV) (e v e' v' : ℕ)
    (hn : (v = 0 ∧ e' = 0 ∧ v' = 1) ∨ (v ≠ 0 ∧ e' = e ∧ v' = v)) (σ : WState ns nr) (hE : σ.val rE = e)
    (hV : σ.val rV = v) (he : e ≤ cap) (h1 : 1 ≤ cap) :
    WExec cap (normE rE rV) σ ((σ.setv rE e').setv rV v') (3 * e + 6) := by
  rcases hn with ⟨hv, h1', h2'⟩ | ⟨hv, h1', h2'⟩
  · subst h1' h2'
    have c := wclear_spec cap rE e σ hE (by omega)
    have i := WExec.inc (cap := cap) rV (σ.setv rE 0) (by simp [Function.update_apply, Ne.symm hEV, hV, hv]; omega)
    refine WExec.cast cap (WExec.ifrF (by rw [hV, hv]) (WExec.seq c i)) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext q
    by_cases hq : q = rV
    · subst hq; simp [Function.update_apply, Ne.symm hEV, hV, hv]
    · simp [Function.update_apply, hq]
  · subst h1' h2'
    refine WExec.cast cap (WExec.ifrT (by rw [hV]; exact hv) (WExec.skip σ)) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext q
    by_cases hq : q = rV
    · subst hq; simp [hV]
    · by_cases hq' : q = rE
      · subst hq'; simp [Function.update_apply, hq, hE]
      · simp [Function.update_apply, hq, hq']

theorem norm_exists (T e v : ℕ) (hden : max (2 ^ e * v) 1 < 2 ^ T) :
    ∃ e' v' : ℕ, ((v = 0 ∧ e' = 0 ∧ v' = 1) ∨ (v ≠ 0 ∧ e' = e ∧ v' = v)) ∧ 2 ^ e' * v' = max (2 ^ e * v) 1 ∧
      e' < T ∧ v' < 2 ^ (T - e') ∧ e' ≤ e ∧ v' ≤ v + 1 := by
  by_cases hv : v = 0
  · subst hv
    have h1 : 1 < 2 ^ T := by simpa using hden
    have hT : 0 < T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · subst h; simp at h1
      · exact h
    exact ⟨0, 1, Or.inl ⟨rfl, rfl, rfl⟩, by simp, hT, by simpa using h1, by omega, by omega⟩
  · have hpos : 1 ≤ 2 ^ e * v := Nat.mul_pos (Nat.two_pow_pos e) (Nat.pos_of_ne_zero hv)
    have hm : max (2 ^ e * v) 1 = 2 ^ e * v := max_eq_left hpos
    rw [hm] at hden
    have hle : 2 ^ e ≤ 2 ^ e * v := by
      have := Nat.mul_le_mul_left (2 ^ e) (Nat.pos_of_ne_zero hv); simpa using this
    have heT : e < T := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show T ≤ e by omega)
      omega
    have h2 : 2 ^ T = 2 ^ e * 2 ^ (T - e) := by rw [← pow_add]; congr 1; omega
    rw [h2] at hden
    exact ⟨e, v, Or.inr ⟨hv, rfl, rfl⟩, hm.symm, heT, Nat.lt_of_mul_lt_mul_left hden, le_rfl, by omega⟩

/-- Return `O`'s head over a frame of `2T + 1` cells (`K`, `H` scratch, `rT = T` kept). -/
def rewTwice (O : Fin (ns + 1)) (rT K H : Fin nr) : WM ns nr :=
  .seq (dupR rT K H) (.seq (WM.rewind O K) (.seq (dupR rT K H) (.seq (WM.rewind O K) (.bwd O))))

theorem rewTwice_spec (O : Fin (ns + 1)) (rT K H : Fin nr) (hTK : rT ≠ K) (hTH : rT ≠ H) (hKH : K ≠ H) (T : ℕ)
    (σ : WState ns nr) (hT : σ.val rT = T) (hK : σ.val K = 0) (hH : σ.val H = 0) (hc : T ≤ cap)
    (hO : σ.sh O = 2 * T + 1) : WExec cap (rewTwice O rT K H) σ (σ.seth O 0) (46 * T + 13) := by
  have s1 := dupR_spec cap rT K H hTK hTH hKH σ T hT hK hH hc
  have s2 := wrewind_spec cap O K T (σ.setv K T) (by simp) (by simp; omega)
  set σ2 := ((σ.setv K T).setv K 0).seth O ((σ.setv K T).sh O - T) with hσ2
  have s3 := dupR_spec cap rT K H hTK hTH hKH σ2 T (by simp [hσ2, Function.update_apply, hTK, hT])
    (by simp [hσ2]) (by simp [hσ2, Function.update_apply, Ne.symm hKH, hH]) hc
  have s4 := wrewind_spec cap O K T (σ2.setv K T) (by simp) (by simp; omega)
  have s5 := WExec.bwd (cap := cap) O (((σ2.setv K T).setv K 0).seth O ((σ2.setv K T).sh O - T))
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext i
    by_cases hi : i = O
    · subst hi; simp [hσ2, hO] <;> omega
    · simp [hσ2, Function.update_apply, hi]
  · funext q
    by_cases hq : q = K
    · subst hq; simp [hσ2, hK]
    · simp [hσ2, Function.update_apply, hq]

/-- The six registers of (d): `rT`, `rE`, `rV` and the scratch `K`, `H`, `B`, pairwise distinct. -/
structure DRegs (rT rE rV K H B : Fin nr) : Prop where
  tE : rT ≠ rE
  tV : rT ≠ rV
  tK : rT ≠ K
  tH : rT ≠ H
  tB : rT ≠ B
  eV : rE ≠ rV
  eK : rE ≠ K
  eH : rE ≠ H
  eB : rE ≠ B
  vK : rV ≠ K
  vH : rV ≠ H
  vB : rV ≠ B
  kH : K ≠ H
  kB : K ≠ B
  hB : H ≠ B

/-- **Phase (d)'s program**: normalize, `sW1 := frame (binary T (2^e'·v'))`, `sW0 := frame (binary T 0)`, both
heads back to `0`, every register `0`. -/
def dProg (O0 O1 : Fin (ns + 1)) (rT rE rV K H B : Fin nr) : WM ns nr :=
  .seq (normE rE rV) (.seq (dupR rT K H) (.seq (zerosLoop O1 rE K) (.seq (bitsLoop O1 K rV H B)
    (.seq (emit O1 false) (.seq (dupR rT K H) (.seq (dupR rT B H) (.seq (zerosLoop O0 K B)
    (.seq (emit O0 false) (.seq (rewTwice O0 rT K H) (.seq (rewTwice O1 rT K H) (WM.clear rT)))))))))))

theorem dCost_le (T e v e' v' : ℕ) (he : e' ≤ e) (hv : v' ≤ v + 1) :
    3 * e + 6 + 1 + (18 * T + 3 + 1 + (13 * e' + 1 + 1 + ((T - e') * (16 * v' + 20) + 1 + 1 + (3 + 1 +
      (18 * T + 3 + 1 + (18 * T + 3 + 1 + (13 * T + 1 + 1 + (3 + 1 + (46 * T + 13 + 1 + (46 * T + 13 + 1 +
      (3 * T + 1))))))))))) ≤ 300 * (T + e + v + 1) ^ 2 := by
  have hP : (T - e') * (16 * v' + 20) ≤ (T + e + v + 1) * (36 * (T + e + v + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsq : (T + e + v + 1) * (36 * (T + e + v + 1)) = 36 * (T + e + v + 1) ^ 2 := by ring
  have hN : T + e + v + 1 ≤ (T + e + v + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-- **(d)'s generic run**: from `rT = T`, `rE = e`, `rV = v`, the scratch `0` and both output streams blank at
head `0`, `dProg` writes `frame (binary T 0)` and `frame (binary T (max (2^e·v) 1))` and zeroes `rT`, `rE`, `rV`,
within `300·(T+e+v+1)^2` steps. -/
theorem dProg_spec (O0 O1 : Fin (ns + 1)) (hO : O0 ≠ O1) (rT rE rV K H B : Fin nr) (L : DRegs rT rE rV K H B)
    (T e v : ℕ) (σ : WState ns nr) (hT : σ.val rT = T) (hE : σ.val rE = e) (hV : σ.val rV = v)
    (hK : σ.val K = 0) (hH : σ.val H = 0) (hB : σ.val B = 0) (h0 : σ.st O0 = []) (h0h : σ.sh O0 = 0)
    (h1 : σ.st O1 = []) (h1h : σ.sh O1 = 0) (hden : max (2 ^ e * v) 1 < 2 ^ T) (hc : T + e + v + 2 ≤ cap) :
    WExec cap (dProg O0 O1 rT rE rV K H B) σ
      (((((σ.sets O0 (frame (binary T 0))).sets O1 (frame (binary T (max (2 ^ e * v) 1)))).setv rT 0).setv rE
        0).setv rV 0) (300 * (T + e + v + 1) ^ 2) := by
  obtain ⟨tE, tV, tK, tH, tB, eV, eK, eH, eB, vK, vH, vB, kH, kB, hB'⟩ := L
  obtain ⟨e', v', hn, hD, heT, hvT, he'e, hv'v⟩ := norm_exists T e v hden
  have s1 := normE_spec cap rE rV eV e v e' v' hn σ hE hV (by omega) (by omega)
  set σ1 := (σ.setv rE e').setv rV v' with hσ1
  have s2 := dupR_spec cap rT K H tK tH kH σ1 T (by simp [hσ1, Function.update_apply, tV, tE, hT])
    (by simp [hσ1, Function.update_apply, Ne.symm vK, Ne.symm eK, hK])
    (by simp [hσ1, Function.update_apply, Ne.symm vH, Ne.symm eH, hH]) (by omega)
  set σ2 := σ1.setv K T with hσ2
  have s3 := zerosLoop_exact cap O1 rE K eK e' σ2 (by simp [hσ2, hσ1, Function.update_apply, eK, eV])
    (by simp [hσ2]; omega) (by simp [hσ2]; omega) (by omega) (by simp [hσ2, hσ1, h1, h1h])
  set σ3 := (((σ2.sets O1 (σ2.st O1 ++ marks (List.replicate e' false))).seth O1 ((σ2.st O1).length + 2 * e')).setv
    rE 0).setv K (σ2.val K - e') with hσ3
  have s4 := bitsLoop_spec cap O1 K rV H B (Ne.symm vK) kH kB vH vB hB' (T - e') v' σ3
    (by simp [hσ3, hσ2]) (by simp [hσ3, hσ2, hσ1, Function.update_apply, vK, eV.symm])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm kH, eH.symm, vH.symm, hH])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, Ne.symm kB, eB.symm, vB.symm, hB])
    (by omega) (by omega) (by omega) (by simp [hσ3, hσ2, hσ1, h1, h1h])
  set σ4 := (((σ3.sets O1 (σ3.st O1 ++ marks (binary (T - e') v'))).seth O1 ((σ3.st O1).length + 2 * (T - e'))).setv
    K 0).setv rV (v' / 2 ^ (T - e')) with hσ4
  have s5 := emit_spec cap O1 false σ4 (by simp [hσ4, hσ3, hσ2, hσ1, h1])
  set σ5 := (σ4.sets O1 (σ4.st O1 ++ [false])).seth O1 ((σ4.st O1).length + 1) with hσ5
  have s6 := dupR_spec cap rT K H tK tH kH σ5 T
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, tK, tV, tE, hT])
    (by simp [hσ5, hσ4, Function.update_apply, vK.symm])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, vH.symm, kH.symm, eH.symm, hH]) (by omega)
  set σ6 := σ5.setv K T with hσ6
  have s7 := dupR_spec cap rT B H tB tH (Ne.symm hB') σ6 T
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, tK, tV, tE, hT])
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, kB.symm, vB.symm, eB.symm, hB])
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, vH.symm, kH.symm, eH.symm, hH]) (by omega)
  set σ7 := σ6.setv B T with hσ7
  have s8 := zerosLoop_exact cap O0 K B kB T σ7 (by simp [hσ7, hσ6, Function.update_apply, kB])
    (by simp [hσ7]) (by simp [hσ7]; omega) (by omega)
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hO, h0, h0h])
  set σ8 := (((σ7.sets O0 (σ7.st O0 ++ marks (List.replicate T false))).seth O0 ((σ7.st O0).length + 2 * T)).setv
    K 0).setv B (σ7.val B - T) with hσ8
  have s9 := emit_spec cap O0 false σ8 (by simp [hσ8])
  set σ9 := (σ8.sets O0 (σ8.st O0 ++ [false])).seth O0 ((σ8.st O0).length + 1) with hσ9
  have s10 := rewTwice_spec cap O0 rT K H tK tH kH T σ9
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, tK, tB, tV, tE, hT])
    (by simp [hσ9, hσ8, Function.update_apply, kB])
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, kH.symm, hB', vH.symm, eH.symm,
      hH]) (by omega)
    (by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hO, h0])
  set σ10 := σ9.seth O0 0 with hσ10
  have s11 := rewTwice_spec cap O1 rT K H tK tH kH T σ10
    (by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, tK, tB, tV, tE, hT])
    (by simp [hσ10, hσ9, hσ8, Function.update_apply, kB])
    (by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, kH.symm, hB', vH.symm,
      eH.symm, hH]) (by omega)
    (by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hO, Ne.symm hO, h1]
        <;> omega)
  set σ11 := σ10.seth O1 0 with hσ11
  have s12 := wclear_spec cap rT T σ11
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, tK, tB, tV, tE, hT])
    (by simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, tK, tB, tV, tE, hT]
        <;> omega)
  have hz : v' / 2 ^ (T - e') = 0 := Nat.div_eq_of_lt hvT
  have hW1 : frame (binary T (max (2 ^ e * v) 1)) =
      marks (List.replicate e' false) ++ (marks (binary (T - e') v') ++ [false]) := by
    rw [← hD, frame_eq_marks, ← List.append_assoc, ← marks_append, ← binary_shift, Nat.add_sub_cancel' heT.le]
  have hW0 : frame (binary T 0) = marks (List.replicate T false) ++ [false] := by
    rw [frame_eq_marks, binary_zero]
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 s12))))))))))) ?_
    (dCost_le T e v e' v' he'e hv'v)
  refine WState.eq ?_ ?_ ?_ ?_
  · funext i
    by_cases i0 : i = O0
    · subst i0; simp [hσ11, hσ10, Function.update_apply, hO, h0h]
    · by_cases i1 : i = O1
      · subst i1; simp [hσ11, h1h]
      · simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, i0, i1]
  · funext i
    by_cases i0 : i = O0
    · subst i0
      simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, hO, h0, hW0]
    · by_cases i1 : i = O1
      · subst i1
        simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, Ne.symm hO, h1, hW1]
      · simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, i0, i1]
  · funext q
    by_cases qT : q = rT
    · subst qT; simp [tE, tV]
    · by_cases qE : q = rE
      · subst qE
        simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, Function.update_apply, eV, eK, eB, qT]
      · by_cases qV : q = rV
        · subst qV
          simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, Function.update_apply, qT, vK, vB, hz]
        · by_cases qK : q = K
          · subst qK
            simp [hσ11, hσ10, hσ9, hσ8, Function.update_apply, qT, qE, qV, kB, hK]
          · by_cases qB : q = B
            · subst qB
              simp [hσ11, hσ10, hσ9, hσ8, hσ7, Function.update_apply, qT, qE, qV, qK, hB]
            · simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_apply, qT, qE, qV, qK,
                qB]
  · simp [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]

end Kit

end NearCubicWires.WireExponent3_5.FinalPass.Out.DPh
