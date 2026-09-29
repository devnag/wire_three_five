import Proof.Wire_3_5.UnionMachine.RadFields

/-! # RADIX, stage 4 (2): the contribution field `fieldsU (consFrom M p 2 0 τ)` (P3:2608-2618)

The RADIX row's contribution fields are, per digit `d < τ`, the values `(2^d·t) mod p` and `((p − 2^d mod p)·t) mod p`
for `t = 0 … M`, each in unary (`fieldsU`), at marks level 2 (`fieldE`). **`consW`** computes them with the running
power `2^d mod p` and a running value `(a·t) mod p` (one addition and one reduction per step, PA's `divW`), and
appends the field (**`consW_spec`**).

Paper quantity of the main type: the row's residue contributions `b_0^d·t` modulo `p` (row:radix, P3:2608-2618). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadFields2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.UnionMachine.RadFields

/-- One value in unary at level 2. -/
def enc (c : ℕ) : List Bool := reps c (m2 true) ++ m2 false

theorem enc_len (c : ℕ) : (enc c).length = 4 * c + 4 := by simp [enc, reps_len]; ring

section W
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (OP : Fin nr) (Rf : Fin 24 ↪ Fin nr)

theorem rne {i j : Fin 24} (h : i ≠ j) : Rf i ≠ Rf j := Rf.injective.ne h

/-- The reduction's registers: `V` (`6`), `P` (`0`), the quotient (`7`), scratch `10 … 15`. -/
def d9 : Fin 9 ↪ Fin 24 := ⟨![6, 0, 7, 10, 11, 12, 13, 14, 15], by decide⟩

/-- `V := (V + A) mod P`. -/
def stepM (a : Fin 24) : WM ns nr :=
  .seq (addTo (Rf a) (Rf 6) (Rf 16)) (.seq (divW (d9.trans Rf)) (WM.clear (Rf 7)))

theorem stepM_spec (a : Fin 24) (ha6 : a ≠ 6) (ha16 : a ≠ 16) (σ : WState ns nr) (p v x : ℕ) (hP : σ.val (Rf 0) = p) (hp1 : 1 ≤ p)
    (hV : σ.val (Rf 6) = v) (hA : σ.val (Rf a) = x) (hz : ∀ i : Fin 24, (i = 7 ∨ (10 ≤ i.val ∧ i.val ≤ 16)) →
      σ.val (Rf i) = 0) (hc : v + x + p ≤ cap) (hcap1 : 1 ≤ cap) :
    WExec cap (stepM Rf a) σ (σ.setv (Rf 6) ((v + x) % p)) (100 * (cap + 2) * (cap + 2)) := by
  have z7 := hz 7 (Or.inl rfl)
  have z : ∀ i : Fin 24, 10 ≤ i.val → i.val ≤ 16 → σ.val (Rf i) = 0 := fun i h1 h2 => hz i (Or.inr ⟨h1, h2⟩)
  have s1 := addTo_spec cap (Rf a) (Rf 6) (Rf 16) (rne Rf ha6) (rne Rf ha16) (rne Rf (by decide)) σ
    (z 16 (by decide) (by decide)) (by omega) (by omega)
  rw [hV, hA] at s1
  set σ1 := σ.setv (Rf 6) (v + x) with hσ1
  have v1 : ∀ i : Fin 24, i ≠ 6 → σ1.val (Rf i) = σ.val (Rf i) := fun i h => by
    simp [σ1, Function.update_of_ne (rne Rf h)]
  have s2 := divW_spec cap (d9.trans Rf) σ1
    (by show 1 ≤ σ1.val (Rf 0); rw [v1 0 (by decide), hP]; exact hp1)
    (by show σ1.val (Rf 10) = 0; rw [v1 10 (by decide), z 10 (by decide) (by decide)])
    (by show σ1.val (Rf 11) = 0; rw [v1 11 (by decide), z 11 (by decide) (by decide)])
    (by show σ1.val (Rf 12) = 0; rw [v1 12 (by decide), z 12 (by decide) (by decide)])
    (by show σ1.val (Rf 13) = 0; rw [v1 13 (by decide), z 13 (by decide) (by decide)])
    (by show σ1.val (Rf 14) = 0; rw [v1 14 (by decide), z 14 (by decide) (by decide)])
    (by show σ1.val (Rf 6) ≤ cap; simp [σ1]; omega)
    (by show σ1.val (Rf 0) ≤ cap; rw [v1 0 (by decide), hP]; omega)
    (by show σ1.val (Rf 7) + σ1.val (Rf 6) ≤ cap; rw [v1 7 (by decide), z7]; simp [σ1]; omega) hcap1
  have q0 : (d9.trans Rf) 0 = Rf 6 := rfl
  have q1 : (d9.trans Rf) 1 = Rf 0 := rfl
  have q2 : (d9.trans Rf) 2 = Rf 7 := rfl
  rw [q0, q1, q2] at s2
  have e6 : σ1.val (Rf 6) = v + x := by simp [σ1]
  have e0 : σ1.val (Rf 0) = p := by rw [v1 0 (by decide), hP]
  have e7 : σ1.val (Rf 7) = 0 := by rw [v1 7 (by decide), z7]
  rw [e6, e0, e7, Nat.zero_add] at s2
  set σ2 := (σ1.setv (Rf 6) ((v + x) % p)).setv (Rf 7) ((v + x) / p) with hσ2
  have s3 := wclear_spec cap (Rf 7) (σ2.val (Rf 7)) σ2 rfl (by
    simp [σ2]; have := Nat.div_le_self (v + x) p; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ ?_
  · apply WState.eq
    · simp [σ2, σ1]
    · simp [σ2, σ1]
    · funext r
      simp only [σ2, σ1, WState.setv_val, Function.update_apply]
      by_cases a7 : r = Rf 7
      · subst a7; simp [z7]
      · by_cases a6 : r = Rf 6
        · subst a6; simp
        · simp [a7, a6]
    · simp [σ2, σ1]
  · have hd : (v + x) / p ≤ v + x := Nat.div_le_self _ _
    have h1 : (v + x + 2) * (90 * (v + x) + 90 * p + 60) ≤ (cap + 2) * (90 * (cap + 2) + 90 * (cap + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [σ2, WState.setv_val, Function.update_self]
    nlinarith

/-- One value `V` in unary at level 2. -/
def valW : WM ns nr := .seq (repRegW O OP (Rf 6) (Rf 8) (Rf 9) (m2 true)) (emitW O OP (m2 false))

theorem valW_spec (hOP : ∀ i, Rf i ≠ OP) (σ : WState ns nr) (v : ℕ) (hV : σ.val (Rf 6) = v)
    (h8 : σ.val (Rf 8) = 0) (h9 : σ.val (Rf 9) = 0) (ho : σ.sh O = (σ.st O).length) (hv : v ≤ cap)
    (hc : σ.val OP + 4 * v + 4 ≤ cap) :
    WExec cap (valW O OP Rf) σ (appendO σ O OP (enc v)) (60 * v + 40) := by
  have e1 := repRegW_spec cap O OP (Rf 6) (Rf 8) (Rf 9) (rne Rf (by decide)) (rne Rf (by decide)) (rne Rf (by decide))
    (hOP 8) (m2 true) σ h8 h9 ho (by rw [hV]; exact hv) (by rw [hV]; simp; omega)
  rw [hV] at e1
  have e2 := emitW_spec cap O OP (m2 false) (appendO σ O OP (reps v (m2 true))) (ao_ho O OP σ _ ho)
    (by rw [ao_val_op, reps_len]; simp; omega)
  rw [appendO_append] at e2
  exact WExec.mono (WExec.seq e1 e2) (by simp; omega)

/-- **Half a digit**: `n` values `(x·t) mod p`, `t = 0 … n−1`, with `n` in `CT = 3`, `x` in `A`. -/
def halfW (a : Fin 24) : WM ns nr := .whr (Rf 3) (.seq (.dec (Rf 3)) (.seq (valW O OP Rf) (stepM Rf a)))

theorem halfW_spec (a : Fin 24) (ha6 : a ≠ 6) (ha16 : a ≠ 16) (ha3 : a ≠ 3) (hOP : ∀ i, Rf i ≠ OP) (σ : WState ns nr) (p x n : ℕ)
    (hP : σ.val (Rf 0) = p) (hp1 : 1 ≤ p) (hA : σ.val (Rf a) = x) (hC : σ.val (Rf 3) = n) (hV : σ.val (Rf 6) = 0)
    (hz : ∀ i : Fin 24, (i = 7 ∨ i = 8 ∨ i = 9 ∨ (10 ≤ i.val ∧ i.val ≤ 16)) → σ.val (Rf i) = 0)
    (ho : σ.sh O = (σ.st O).length) (hx : x ≤ p) (hn : n ≤ cap) (hc : σ.val OP + n * (4 * p + 4) + 3 * p ≤ cap) :
    WExec cap (halfW O OP Rf a) σ
      (((appendO σ O OP ((List.range n).flatMap fun t => enc (x * t % p))).setv (Rf 3) 0).setv (Rf 6) (x * n % p))
      (n * (100 * (cap + 2) * (cap + 2) + 60 * cap + 60) + 1) := by
  have hcap1 : 1 ≤ cap := by omega
  let E : ℕ → List Bool := fun t => (List.range t).flatMap fun t => enc (x * t % p)
  have hEl : ∀ t, (E t).length ≤ t * (4 * p + 4) := by
    intro t
    induction t with
    | zero => simp [E]
    | succ t ih =>
      have e : E (t + 1) = E t ++ enc (x * t % p) := by simp [E, List.range_succ, List.flatMap_append]
      rw [e, List.length_append, enc_len]
      have : x * t % p < p := Nat.mod_lt _ (by omega)
      nlinarith
  let S : ℕ → WState ns nr := fun t => ((appendO σ O OP (E t)).setv (Rf 3) (n - t)).setv (Rf 6) (x * t % p)
  have hS0 : S 0 = σ := by
    apply WState.eq
    · simp [S, E]
    · simp [S, E]
    · funext r
      simp only [S, E, WState.setv_val, Function.update_apply, appendO_val]
      by_cases a6 : r = Rf 6
      · subst a6; simp [hV]
      · by_cases a3 : r = Rf 3
        · subst a3; simp [hC]
        · simp only [a6, a3, if_false]
          split_ifs with h
          · subst h; simp
          · rfl
    · simp [S]
  have hSn : S n = ((appendO σ O OP (E n)).setv (Rf 3) 0).setv (Rf 6) (x * n % p) := by simp [S]
  have h := UnionMachine.Round.wloop cap (Rf 3) (.seq (valW O OP Rf) (stepM Rf a))
    (100 * (cap + 2) * (cap + 2) + 60 * cap + 41) n S (fun t _ => by
      simp [S, Function.update_apply, rne Rf (show (3 : Fin 24) ≠ 6 by decide)]) hn (fun t ht => by
      have hvt : x * t % p < p := Nat.mod_lt _ (by omega)
      set τ := (S t).setv (Rf 3) (n - t - 1) with hτ
      have v6 : τ.val (Rf 6) = x * t % p := by simp [τ, S, Function.update_apply, rne Rf (show (6 : Fin 24) ≠ 3 by decide)]
      have vi : ∀ i : Fin 24, i ≠ 3 → i ≠ 6 → τ.val (Rf i) = σ.val (Rf i) := fun i h3 h6 => by
        simp [τ, S, Function.update_of_ne (rne Rf h3), Function.update_of_ne (rne Rf h6), hOP i]
      have vP : τ.val OP = σ.val OP + (E t).length := by
        simp [τ, S, Function.update_apply, (hOP 3).symm, (hOP 6).symm]
      have vo : τ.sh O = (τ.st O).length := by simp [τ, S, ho]
      have hEt := hEl t
      have htn : t * (4 * p + 4) + (4 * p + 4) ≤ n * (4 * p + 4) := by
        have := Nat.mul_le_mul_right (4 * p + 4) (show t + 1 ≤ n by omega); nlinarith
      have e1 := valW_spec cap O OP Rf hOP τ (x * t % p) v6 (by rw [vi 8 (by decide) (by decide)]; exact hz 8 (by simp))
        (by rw [vi 9 (by decide) (by decide)]; exact hz 9 (by simp)) vo (by omega) (by rw [vP]; omega)
      have e2 := stepM_spec cap Rf a ha6 ha16 (appendO τ O OP (enc (x * t % p))) p (x * t % p) x
        (by rw [ao_val_ne O OP _ _ (hOP 0), vi 0 (by decide) (by decide), hP]) hp1
        (by rw [ao_val_ne O OP _ _ (hOP 6), v6])
        (by rw [ao_val_ne O OP _ _ (hOP a), vi a ha3 ha6, hA])
        (fun i hi => by
          have hv : i.val = 7 ∨ (10 ≤ i.val ∧ i.val ≤ 16) := by
            rcases hi with h | h
            · left; rw [h]; rfl
            · right; exact h
          have h3 : i ≠ 3 := fun h => by subst h; simp at hv
          have h6 : i ≠ 6 := fun h => by subst h; simp at hv
          rw [ao_val_ne O OP _ _ (hOP i), vi i h3 h6]
          exact hz i (by rcases hi with h | h; exact Or.inl h; exact Or.inr (Or.inr (Or.inr h))))
        (by omega) hcap1
      refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
      have hmod : (x * t % p + x) % p = x * (t + 1) % p := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mul_succ]
      rw [hmod]
      apply WState.eq
      · simp [τ, S, E, List.range_succ, List.flatMap_append, Nat.add_assoc]
      · simp [τ, S, E, List.range_succ, List.flatMap_append]
      · funext r
        simp only [τ, S, WState.setv_val, appendO_val, Function.update_apply]
        by_cases a6 : r = Rf 6
        · subst a6; simp [(hOP 6)]
        · by_cases a3 : r = Rf 3
          · subst a3; simp [(hOP 3), rne Rf (show (3 : Fin 24) ≠ 6 by decide)]; omega
          · by_cases aO : r = OP
            · subst aO; simp [(hOP 6).symm, (hOP 3).symm, E, List.range_succ, List.flatMap_append]; omega
            · simp [a6, a3, aO]
      · simp [τ, S])
  rw [hS0, hSn] at h
  refine WExec.mono h ?_
  have : n * (100 * (cap + 2) * (cap + 2) + 60 * cap + 41 + 4) ≤ n * (100 * (cap + 2) * (cap + 2) + 60 * cap + 60) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- The positive half's values of power `w`. -/
def posE (p m w : ℕ) : List Bool := (List.range (m + 1)).flatMap fun t => enc (w * t % p)

/-- The negative half's values of power `w`. -/
def negE (p m w : ℕ) : List Bool := (List.range (m + 1)).flatMap fun t => enc ((p - w) * t % p)

theorem posE_len (p m w : ℕ) (hp : 1 ≤ p) : (posE p m w).length ≤ (m + 1) * (4 * p + 4) := by
  unfold posE
  rw [List.length_flatMap]
  have h : ∀ t ∈ List.range (m + 1), (enc (w * t % p)).length ≤ 4 * p + 4 := fun t _ => by
    rw [enc_len]; have := Nat.mod_lt (w * t) (show 0 < p by omega); omega
  calc ((List.range (m + 1)).map fun t => (enc (w * t % p)).length).sum
      ≤ ((List.range (m + 1)).map fun _ => 4 * p + 4).sum := List.sum_le_sum (fun t ht => h t ht)
    _ = (m + 1) * (4 * p + 4) := by simp

theorem negE_len (p m w : ℕ) (hp : 1 ≤ p) : (negE p m w).length ≤ (m + 1) * (4 * p + 4) := by
  unfold negE
  rw [List.length_flatMap]
  have h : ∀ t ∈ List.range (m + 1), (enc ((p - w) * t % p)).length ≤ 4 * p + 4 := fun t _ => by
    rw [enc_len]; have := Nat.mod_lt ((p - w) * t) (show 0 < p by omega); omega
  calc ((List.range (m + 1)).map fun t => (enc ((p - w) * t % p)).length).sum
      ≤ ((List.range (m + 1)).map fun _ => 4 * p + 4).sum := List.sum_le_sum (fun t ht => h t ht)
    _ = (m + 1) * (4 * p + 4) := by simp

/-- The power's reduction registers: `PW` (`4`), `P` (`0`), the quotient (`7`), scratch `10 … 15`. -/
def d9p : Fin 9 ↪ Fin 24 := ⟨![4, 0, 7, 10, 11, 12, 13, 14, 15], by decide⟩

/-- The negative power's subtraction registers: `NW` (`5`), `PW` (`4`), scratch `17`, `18`. -/
def sE4 : Fin 4 ↪ Fin 24 := ⟨![5, 4, 17, 18], by decide⟩

/-- The registers a half leaves as it found them: `CT = 3`, `NW = 5`, `V = 6`, scratch `7 … 18`. -/
def Clean (σ : WState ns nr) : Prop := ∀ i : Fin 24, (i = 3 ∨ i = 5 ∨ i = 6 ∨ (7 ≤ i.val ∧ i.val ≤ 18)) → σ.val (Rf i) = 0

/-- **A half** at the power in register `a`: `M + 1` values, `CT` and `V` back to `0`. -/
def hbW (a : Fin 24) : WM ns nr :=
  .seq (addTo (Rf 1) (Rf 3) (Rf 16)) (.seq (.inc (Rf 3)) (.seq (halfW O OP Rf a) (WM.clear (Rf 6))))

theorem hbW_spec (a : Fin 24) (ha3 : a ≠ 3) (ha6 : a ≠ 6) (ha16 : a ≠ 16) (hOP : ∀ i, Rf i ≠ OP) (σ : WState ns nr)
    (p m w : ℕ) (hP : σ.val (Rf 0) = p) (hp1 : 1 ≤ p)
    (hM : σ.val (Rf 1) = m) (hW : σ.val (Rf a) = w) (hwp : w ≤ p)
    (hz : ∀ i : Fin 24, (i = 3 ∨ i = 6 ∨ (7 ≤ i.val ∧ i.val ≤ 18)) → σ.val (Rf i) = 0)
    (ho : σ.sh O = (σ.st O).length) (hm : m + 1 ≤ cap) (hc : σ.val OP + (m + 1) * (4 * p + 4) + 3 * p + 2 ≤ cap) :
    WExec cap (hbW O OP Rf a) σ (appendO σ O OP (posE p m w)) ((m + 1) * (200 * (cap + 2) * (cap + 2)) + 60 * cap + 60) := by
  have hcap1 : 1 ≤ cap := by omega
  have z16 := hz 16 (Or.inr (Or.inr ⟨by decide, by decide⟩))
  have s1 := addTo_spec cap (Rf 1) (Rf 3) (Rf 16) (rne Rf (by decide)) (rne Rf (by decide)) (rne Rf (by decide)) σ z16
    (by omega) (by rw [hz 3 (by simp), hM]; omega)
  rw [hz 3 (by simp), hM, Nat.zero_add] at s1
  have s2 := WExec.inc (cap := cap) (Rf 3) (σ.setv (Rf 3) m) (by simp; omega)
  rw [show (σ.setv (Rf 3) m).setv (Rf 3) ((σ.setv (Rf 3) m).val (Rf 3) + 1) = σ.setv (Rf 3) (m + 1) by
    rw [wsetv_setv]; simp] at s2
  have v2 : ∀ i : Fin 24, i ≠ 3 → (σ.setv (Rf 3) (m + 1)).val (Rf i) = σ.val (Rf i) := fun i h => by
    simp [Function.update_of_ne (rne Rf h)]
  have s3 := halfW_spec cap O OP Rf a ha6 ha16 ha3 hOP (σ.setv (Rf 3) (m + 1)) p w (m + 1)
    (by rw [v2 0 (by decide), hP]) hp1 (by rw [v2 a ha3, hW]) (by simp) (by rw [v2 6 (by decide), hz 6 (by simp)])
    (fun i hi => by
      have h3 : i ≠ 3 := fun h => by subst h; rcases hi with h | h | h | h <;> simp_all
      rw [v2 i h3]
      exact hz i (by rcases hi with h | h | h | h <;> [(subst h; right; right; decide); (subst h; right; right; decide);
        (subst h; right; right; decide); (right; right; omega)]))
    (by simp [ho]) hwp hm (by simp [Function.update_apply, (hOP 3).symm]; omega)
  have s4 := wclear_spec cap (Rf 6) _ ((((appendO (σ.setv (Rf 3) (m + 1)) O OP (posE p m w)).setv (Rf 3) 0).setv (Rf 6)
    (w * (m + 1) % p))) rfl (by simp; have := Nat.mod_lt (w * (m + 1)) (show 0 < p by omega); omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · rw [wsetv_setv, appendO_setv _ _ _ _ (hOP 3), wsetv_setv]
    apply WState.eq
    · simp
    · simp
    · funext r
      simp only [WState.setv_val, appendO_val, Function.update_apply]
      by_cases a6 : r = Rf 6
      · subst a6; simp [hOP 6, hz 6 (by simp)]
      · by_cases a3 : r = Rf 3
        · subst a3; simp [hOP 3, hz 3 (by simp)]
        · simp [a6, a3]
    · simp
  · have hx : (w * (m + 1) % p) ≤ cap := by have := Nat.mod_lt (w * (m + 1)) (show 0 < p by omega); omega
    have e : (m + 1) * (100 * (cap + 2) * (cap + 2) + 60 * cap + 60) ≤ (m + 1) * (200 * (cap + 2) * (cap + 2)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    simp only [WState.setv_val, Function.update_self]
    omega

theorem posE_neg (p m w : ℕ) : posE p m (p - w) = negE p m w := rfl

/-- **The negative half**: `NW := P − PW`, then `M + 1` values at `NW`, `NW` back to `0`. -/
def negW : WM ns nr :=
  .seq (addTo (Rf 0) (Rf 5) (Rf 16)) (.seq (subW (sE4.trans Rf)) (.seq (hbW O OP Rf 5) (WM.clear (Rf 5))))

theorem negW_spec (hOP : ∀ i, Rf i ≠ OP) (σ : WState ns nr) (p m w : ℕ) (hP : σ.val (Rf 0) = p) (hp1 : 1 ≤ p)
    (hM : σ.val (Rf 1) = m) (hW : σ.val (Rf 4) = w) (hwp : w ≤ p) (hz : Clean Rf σ)
    (ho : σ.sh O = (σ.st O).length) (hm : m + 1 ≤ cap) (hc : σ.val OP + (m + 1) * (4 * p + 4) + 3 * p + 2 ≤ cap) :
    WExec cap (negW O OP Rf) σ (appendO σ O OP (negE p m w))
      ((m + 1) * (200 * (cap + 2) * (cap + 2)) + 200 * cap + 200) := by
  have z16 := hz 16 (Or.inr (Or.inr (Or.inr ⟨by decide, by decide⟩)))
  have s1 := addTo_spec cap (Rf 0) (Rf 5) (Rf 16) (rne Rf (by decide)) (rne Rf (by decide)) (rne Rf (by decide)) σ z16
    (by omega) (by rw [hz 5 (by simp), hP]; omega)
  rw [hz 5 (by simp), hP, Nat.zero_add] at s1
  have s2 := subW_spec cap (sE4.trans Rf) (σ.setv (Rf 5) p)
    (by show (σ.setv (Rf 5) p).val (Rf 17) = 0; simp [Function.update_apply]
        exact hz 17 (by right; right; right; decide))
    (by show (σ.setv (Rf 5) p).val (Rf 18) = 0; simp [Function.update_apply]
        exact hz 18 (by right; right; right; decide))
    (by show (σ.setv (Rf 5) p).val (Rf 5) ≤ cap; simp; omega)
    (by show (σ.setv (Rf 5) p).val (Rf 4) ≤ cap; simp [Function.update_apply, hW]; omega)
  have q0 : (sE4.trans Rf) 0 = Rf 5 := rfl
  have q1 : (sE4.trans Rf) 1 = Rf 4 := rfl
  rw [q0, q1] at s2
  have e5 : (σ.setv (Rf 5) p).val (Rf 5) = p := by simp
  have e4 : (σ.setv (Rf 5) p).val (Rf 4) = w := by simp [Function.update_apply, hW]
  rw [e5, e4, wsetv_setv] at s2
  have v2 : ∀ i : Fin 24, i ≠ 5 → (σ.setv (Rf 5) (p - w)).val (Rf i) = σ.val (Rf i) := fun i h => by
    simp [Function.update_of_ne (rne Rf h)]
  have s3 := hbW_spec cap O OP Rf 5 (by decide) (by decide) (by decide) hOP (σ.setv (Rf 5) (p - w)) p m (p - w)
    (by rw [v2 0 (by decide), hP]) hp1 (by rw [v2 1 (by decide), hM]) (by simp) (by omega)
    (fun i hi => by
      have h5 : i ≠ 5 := fun h => by subst h; simp at hi
      rw [v2 i h5]
      exact hz i (by rcases hi with h | h | h <;> [(left; exact h); (right; right; left; exact h); (right; right; right; exact h)]))
    (by simp [ho]) hm (by simp [Function.update_apply, (hOP 5).symm]; omega)
  rw [posE_neg] at s3
  have s4 := wclear_spec cap (Rf 5) _ (appendO (σ.setv (Rf 5) (p - w)) O OP (negE p m w)) rfl
    (by rw [ao_val_ne O OP _ _ (hOP 5)]; simp; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · rw [appendO_setv _ _ _ _ (hOP 5), wsetv_setv]
    apply WState.eq
    · simp
    · simp
    · funext r
      simp only [WState.setv_val, appendO_val, Function.update_apply]
      by_cases a5 : r = Rf 5
      · subst a5; simp [hOP 5, hz 5 (by simp)]
      · simp [a5]
    · simp
  · have hs := UnaryPow.sq_ge cap
    have hl := UnaryPow.lin_le_sq cap
    have hv5 : (appendO (σ.setv (Rf 5) (p - w)) O OP (negE p m w)).val (Rf 5) = p - w := by
      rw [ao_val_ne O OP _ _ (hOP 5)]; simp
    rw [hv5]
    omega

/-- **One digit**: both halves at the power `PW = 2^d mod p`, then `PW := 2·PW mod p`. -/
def digitW : WM ns nr :=
  .seq (hbW O OP Rf 4) (.seq (negW O OP Rf) (.seq (addTo (Rf 4) (Rf 5) (Rf 16)) (.seq (addTo (Rf 5) (Rf 4) (Rf 16))
    (.seq (WM.clear (Rf 5)) (.seq (divW (d9p.trans Rf)) (WM.clear (Rf 7)))))))

/-- A digit's cost. -/
def digitCost (c m : ℕ) : ℕ := (2 * m + 10) * (200 * (c + 2) * (c + 2))

theorem digitW_spec (hOP : ∀ i, Rf i ≠ OP) (σ : WState ns nr) (p m w : ℕ) (hP : σ.val (Rf 0) = p) (hp1 : 1 ≤ p)
    (hM : σ.val (Rf 1) = m) (hW : σ.val (Rf 4) = w) (hwp : w < p) (hz : Clean Rf σ)
    (ho : σ.sh O = (σ.st O).length) (hm : m + 1 ≤ cap)
    (hc : σ.val OP + 2 * ((m + 1) * (4 * p + 4)) + 3 * p + 2 * p + 2 ≤ cap) :
    WExec cap (digitW O OP Rf) σ ((appendO σ O OP (posE p m w ++ negE p m w)).setv (Rf 4) ((w + w) % p))
      (digitCost cap m) := by
  have hcap1 : 1 ≤ cap := by omega
  have hpl := posE_len p m w hp1
  have s1 := hbW_spec cap O OP Rf 4 (by decide) (by decide) (by decide) hOP σ p m w hP hp1 hM hW (by omega)
    (fun i hi => hz i (by rcases hi with h | h | h <;> [(left; exact h); (right; right; left; exact h);
      (right; right; right; exact h)])) ho hm (by omega)
  set σ1 := appendO σ O OP (posE p m w) with hσ1
  have e1 : ∀ i, σ1.val (Rf i) = σ.val (Rf i) := fun i => by rw [hσ1, ao_val_ne O OP _ _ (hOP i)]
  have s2 := negW_spec cap O OP Rf hOP σ1 p m w (by rw [e1, hP]) hp1 (by rw [e1, hM]) (by rw [e1, hW]) (by omega)
    (fun i hi => by rw [e1]; exact hz i hi) (ao_ho O OP σ _ ho) hm (by rw [hσ1, ao_val_op]; omega)
  set σ2 := appendO σ1 O OP (negE p m w) with hσ2
  have e2 : ∀ i, σ2.val (Rf i) = σ.val (Rf i) := fun i => by rw [hσ2, ao_val_ne O OP _ _ (hOP i), e1]
  have z16 := hz 16 (Or.inr (Or.inr (Or.inr ⟨by decide, by decide⟩)))
  have s3 := addTo_spec cap (Rf 4) (Rf 5) (Rf 16) (rne Rf (by decide)) (rne Rf (by decide)) (rne Rf (by decide)) σ2
    (by rw [e2, z16]) (by rw [e2, hW]; omega) (by rw [e2, e2, hW, hz 5 (by simp)]; omega)
  rw [e2, e2, hW, hz 5 (by simp), Nat.zero_add] at s3
  set σ3 := σ2.setv (Rf 5) w with hσ3
  have s4 := addTo_spec cap (Rf 5) (Rf 4) (Rf 16) (rne Rf (by decide)) (rne Rf (by decide)) (rne Rf (by decide)) σ3
    (by simp [σ3, Function.update_apply]; rw [e2, z16]) (by simp [σ3]; omega)
    (by simp [σ3, Function.update_apply]; rw [e2, hW]; omega)
  have f35 : σ3.val (Rf 5) = w := by simp [σ3]
  have f34 : σ3.val (Rf 4) = w := by simp [σ3, Function.update_apply]; rw [e2, hW]
  rw [f35, f34] at s4
  set σ4 := σ3.setv (Rf 4) (w + w) with hσ4
  have s5 := wclear_spec cap (Rf 5) (σ4.val (Rf 5)) σ4 rfl (by simp [σ4, σ3, Function.update_apply]; omega)
  set σ5 := σ4.setv (Rf 5) 0 with hσ5
  have e5 : ∀ i : Fin 24, i ≠ 4 → i ≠ 5 → σ5.val (Rf i) = σ.val (Rf i) := fun i h4 h5 => by
    simp [σ5, σ4, σ3, Function.update_of_ne (rne Rf h4), Function.update_of_ne (rne Rf h5)]; rw [e2]
  have s6 := divW_spec cap (d9p.trans Rf) σ5
    (by show 1 ≤ σ5.val (Rf 0); rw [e5 0 (by decide) (by decide), hP]; exact hp1)
    (by show σ5.val (Rf 10) = 0; rw [e5 10 (by decide) (by decide)]; exact hz 10 (by right; right; right; decide))
    (by show σ5.val (Rf 11) = 0; rw [e5 11 (by decide) (by decide)]; exact hz 11 (by right; right; right; decide))
    (by show σ5.val (Rf 12) = 0; rw [e5 12 (by decide) (by decide)]; exact hz 12 (by right; right; right; decide))
    (by show σ5.val (Rf 13) = 0; rw [e5 13 (by decide) (by decide)]; exact hz 13 (by right; right; right; decide))
    (by show σ5.val (Rf 14) = 0; rw [e5 14 (by decide) (by decide)]; exact hz 14 (by right; right; right; decide))
    (by show σ5.val (Rf 4) ≤ cap; simp [σ5, σ4, Function.update_apply]; omega)
    (by show σ5.val (Rf 0) ≤ cap; rw [e5 0 (by decide) (by decide), hP]; omega)
    (by show σ5.val (Rf 7) + σ5.val (Rf 4) ≤ cap
        rw [e5 7 (by decide) (by decide), hz 7 (by right; right; right; decide)]
        simp [σ5, σ4, Function.update_apply]; omega) hcap1
  have r0 : (d9p.trans Rf) 0 = Rf 4 := rfl
  have r1 : (d9p.trans Rf) 1 = Rf 0 := rfl
  have r2 : (d9p.trans Rf) 2 = Rf 7 := rfl
  have f54 : σ5.val (Rf 4) = w + w := by simp [σ5, σ4, Function.update_apply]
  have f50 : σ5.val (Rf 0) = p := by rw [e5 0 (by decide) (by decide), hP]
  have f57 : σ5.val (Rf 7) = 0 := by rw [e5 7 (by decide) (by decide), hz 7 (by right; right; right; decide)]
  rw [r0, r1, r2, f54, f50, f57, Nat.zero_add] at s6
  set σ6 := (σ5.setv (Rf 4) ((w + w) % p)).setv (Rf 7) ((w + w) / p) with hσ6
  have s7 := wclear_spec cap (Rf 7) (σ6.val (Rf 7)) σ6 rfl (by
    simp [σ6]; have := Nat.div_le_self (w + w) p; omega)
  have hs := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7)))))) ?_ ?_
  · apply WState.eq
    · simp [σ6, σ5, σ4, σ3, σ2, σ1, Nat.add_assoc]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
    · funext r
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, appendO_val, Function.update_apply]
      by_cases a7 : r = Rf 7
      · subst a7; simp [hOP 7, hz 7 (by right; right; right; decide)]
      · by_cases a4 : r = Rf 4
        · subst a4; simp [hOP 4]
        · by_cases a5 : r = Rf 5
          · subst a5; simp [hOP 5, hz 5 (by simp)]
          · by_cases aO : r = OP
            · subst aO; simp [(hOP 4).symm, (hOP 5).symm, (hOP 7).symm]; omega
            · simp [a7, a4, a5, aO]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
  · unfold digitCost
    have hq : (w + w + 2) * (90 * (w + w) + 90 * p + 60) ≤ (cap + 2) * (90 * (cap + 2) + 90 * (cap + 2)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hq2 : (cap + 2) * (90 * (cap + 2) + 90 * (cap + 2)) ≤ 200 * (cap + 2) * (cap + 2) := by nlinarith
    have hv5 : σ4.val (Rf 5) = w := by simp [σ4, σ3, Function.update_apply]
    have hv7 : σ6.val (Rf 7) = (w + w) / p := by simp [σ6]
    have hd : (w + w) / p ≤ w + w := Nat.div_le_self _ _
    rw [hv5, hv7]
    have e : (2 * m + 10) * (200 * (cap + 2) * (cap + 2)) = 2 * ((m + 1) * (200 * (cap + 2) * (cap + 2))) +
        8 * (200 * (cap + 2) * (cap + 2)) := by ring
    unfold UnaryPow.sq at hs hl
    omega

/-- The contribution field's values, digit by digit. -/
def consWord (p m n : ℕ) : List Bool :=
  (List.range n).flatMap fun o => posE p m (2 ^ o % p) ++ negE p m (2 ^ o % p)

theorem consWord_len (p m n : ℕ) (hp : 1 ≤ p) : (consWord p m n).length ≤ n * (2 * ((m + 1) * (4 * p + 4))) := by
  induction n with
  | zero => simp [consWord]
  | succ n ih =>
    have e : consWord p m (n + 1) = consWord p m n ++ (posE p m (2 ^ n % p) ++ negE p m (2 ^ n % p)) := by
      simp [consWord, List.range_succ, List.flatMap_append]
    rw [e, List.length_append, List.length_append]
    have := posE_len p m (2 ^ n % p) hp
    have := negE_len p m (2 ^ n % p) hp
    nlinarith

/-- **The contribution field's values**: `PW := 1`, then `τ` digits (`τ` in `CD = 2`, consumed), then `PW := 0`. -/
def consW : WM ns nr := .seq (.inc (Rf 4)) (.seq (.whr (Rf 2) (.seq (.dec (Rf 2)) (digitW O OP Rf))) (WM.clear (Rf 4)))

theorem consW_spec (hOP : ∀ i, Rf i ≠ OP) (σ : WState ns nr) (p m n : ℕ) (hP : σ.val (Rf 0) = p) (hp2 : 2 ≤ p)
    (hM : σ.val (Rf 1) = m) (hN : σ.val (Rf 2) = n) (hW : σ.val (Rf 4) = 0) (hz : Clean Rf σ)
    (ho : σ.sh O = (σ.st O).length) (hm : m + 1 ≤ cap) (hn : n ≤ cap) (hp : p ≤ cap)
    (hc : σ.val OP + n * (2 * ((m + 1) * (4 * p + 4)) + 5 * p + 2) ≤ cap) :
    WExec cap (consW O OP Rf) σ ((appendO σ O OP (consWord p m n)).setv (Rf 2) 0)
      (n * (digitCost cap m + 4) + 4 * cap + 20) := by
  have hcap1 : 1 ≤ cap := by omega
  have s1 := WExec.inc (cap := cap) (Rf 4) σ (by rw [hW]; omega)
  rw [hW, Nat.zero_add] at s1
  set σ1 := σ.setv (Rf 4) 1 with hσ1
  let S : ℕ → WState ns nr := fun o => ((appendO σ O OP (consWord p m o)).setv (Rf 4) (2 ^ o % p)).setv (Rf 2) (n - o)
  have hS0 : S 0 = σ1 := by
    apply WState.eq
    · simp [S, σ1, consWord]
    · simp [S, σ1, consWord]
    · funext r
      simp only [S, σ1, consWord, WState.setv_val, appendO_val, Function.update_apply]
      by_cases a2 : r = Rf 2
      · subst a2; simp [hN]
      · by_cases a4 : r = Rf 4
        · subst a4; simp; exact Nat.mod_eq_of_lt (by omega)
        · simp only [a2, a4, if_false]
          split_ifs with h
          · subst h; simp
          · rfl
    · simp [S, σ1]
  have hSn : S n = ((appendO σ O OP (consWord p m n)).setv (Rf 4) (2 ^ n % p)).setv (Rf 2) 0 := by simp [S]
  have h := UnionMachine.Round.wloop cap (Rf 2) (digitW O OP Rf) (digitCost cap m) n S
    (fun o _ => by simp [S]) hn (fun o ho' => by
      set τ := (S o).setv (Rf 2) (n - o - 1) with hτ
      have vτ : ∀ i : Fin 24, i ≠ 2 → i ≠ 4 → τ.val (Rf i) = σ.val (Rf i) := fun i h2 h4 => by
        simp [τ, S, Function.update_of_ne (rne Rf h2), Function.update_of_ne (rne Rf h4), hOP i]
      have hcl := consWord_len p m o (by omega)
      have hon : o * (2 * ((m + 1) * (4 * p + 4))) + 2 * ((m + 1) * (4 * p + 4)) ≤
          n * (2 * ((m + 1) * (4 * p + 4))) := by
        have := Nat.mul_le_mul_right (2 * ((m + 1) * (4 * p + 4))) (show o + 1 ≤ n by omega); nlinarith
      have hno : o * (5 * p + 2) + (5 * p + 2) ≤ n * (5 * p + 2) := by
        have := Nat.mul_le_mul_right (5 * p + 2) (show o + 1 ≤ n by omega); nlinarith
      have e := digitW_spec cap O OP Rf hOP τ p m (2 ^ o % p) (by rw [vτ 0 (by decide) (by decide), hP]) (by omega)
        (by rw [vτ 1 (by decide) (by decide), hM])
        (by simp [τ, S, Function.update_apply, rne Rf (show (4 : Fin 24) ≠ 2 by decide)])
        (Nat.mod_lt _ (by omega))
        (fun i hi => by
          have h2 : i ≠ 2 := fun h => by subst h; simp at hi
          have h4 : i ≠ 4 := fun h => by subst h; simp at hi
          rw [vτ i h2 h4]; exact hz i hi)
        (by simp [τ, S, ho]) hm (by
          have vP : τ.val OP = σ.val OP + (consWord p m o).length := by
            simp [τ, S, Function.update_apply, (hOP 2).symm, (hOP 4).symm]
          have hmul : n * (2 * ((m + 1) * (4 * p + 4)) + 5 * p + 2) =
              n * (2 * ((m + 1) * (4 * p + 4))) + n * (5 * p + 2) := by ring
          rw [vP]
          omega)
      refine WExec.cast cap e ?_ le_rfl
      have hpow : (2 ^ o % p + 2 ^ o % p) % p = 2 ^ (o + 1) % p := by
        rw [← Nat.add_mod, pow_succ]; congr 1; ring
      rw [hpow]
      apply WState.eq
      · simp [τ, S, consWord, List.range_succ, List.flatMap_append, Nat.add_assoc]
      · simp [τ, S, consWord, List.range_succ, List.flatMap_append]
      · funext r
        simp only [τ, S, WState.setv_val, appendO_val, Function.update_apply]
        by_cases a4 : r = Rf 4
        · subst a4; simp [hOP 4, rne Rf (show (4 : Fin 24) ≠ 2 by decide)]
        · by_cases a2 : r = Rf 2
          · subst a2; simp [hOP 2]; omega
          · by_cases aO : r = OP
            · subst aO; simp [(hOP 2).symm, (hOP 4).symm, consWord, List.range_succ, List.flatMap_append]; omega
            · simp [a4, a2, aO]
      · simp [τ, S])
  rw [hS0, hSn] at h
  have s3 := wclear_spec cap (Rf 4) _ (((appendO σ O OP (consWord p m n)).setv (Rf 4) (2 ^ n % p)).setv (Rf 2) 0) rfl
    (by simp [Function.update_apply, rne Rf (show (4 : Fin 24) ≠ 2 by decide)]
        have := Nat.mod_lt (2 ^ n) (show 0 < p by omega); omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq h s3)) ?_ ?_
  · apply WState.eq
    · simp
    · simp
    · funext r
      simp only [WState.setv_val, appendO_val, Function.update_apply]
      by_cases a4 : r = Rf 4
      · subst a4; simp [hOP 4, rne Rf (show (4 : Fin 24) ≠ 2 by decide), hW]
      · simp [a4]
    · simp
  · have h4 : (((appendO σ O OP (consWord p m n)).setv (Rf 4) (2 ^ n % p)).setv (Rf 2) 0).val (Rf 4) = 2 ^ n % p := by
      simp [Function.update_apply, rne Rf (show (4 : Fin 24) ≠ 2 by decide)]
    have := Nat.mod_lt (2 ^ n) (show 0 < p by omega)
    rw [h4]
    omega

/-- **The contribution field's word**: `fieldsU (consFrom M p 2 0 τ)` at level 2 is the values' word and the field's
end. -/
theorem fieldE_cons (p m n : ℕ) : fieldE (fieldsU (consFrom m p 2 0 n)) = consWord p m n ++ [true, false] := by
  have key : ∀ (n o : ℕ), (consFrom m p 2 o n).flatMap enc =
      (List.range n).flatMap fun i => posE p m (2 ^ (o + i) % p) ++ negE p m (2 ^ (o + i) % p) := by
    intro n
    induction n with
    | zero => intro o; simp [consFrom]
    | succ n ih =>
      intro o
      have hpos : ((List.range (m + 1)).map fun t => 2 ^ o * t % p).flatMap enc = posE p m (2 ^ o % p) := by
        unfold posE; rw [List.flatMap_map]
        apply List.flatMap_congr; intro t _; rw [Nat.mod_mul_mod]
      have hneg : ((List.range (m + 1)).map fun t => (p - 2 ^ o % p) * t % p).flatMap enc = negE p m (2 ^ o % p) := by
        unfold negE; rw [List.flatMap_map]
      have hrest : (List.range n).flatMap (fun i => posE p m (2 ^ (o + 1 + i) % p) ++ negE p m (2 ^ (o + 1 + i) % p)) =
          (List.range n).flatMap (fun i => posE p m (2 ^ (o + (i + 1)) % p) ++ negE p m (2 ^ (o + (i + 1)) % p)) := by
        apply List.flatMap_congr; intro i _; rw [show o + 1 + i = o + (i + 1) by ring]
      rw [consFrom, List.flatMap_append, List.flatMap_append, ih (o + 1), hpos, hneg, hrest,
        List.range_succ_eq_map (n := n), List.flatMap_cons, List.flatMap_map]
      simp [List.append_assoc]
  unfold fieldE fieldsU
  rw [List.flatMap_assoc]
  have e2 : (fun c => (List.replicate c true ++ [false]).flatMap m2) = enc := by
    funext c; simp [enc, List.flatMap_append, flatMap_replicate]
  rw [e2, key n 0]
  simp [consWord]

end W

end NearCubicWires.WireExponent3_5.UnionMachine.RadFields2
