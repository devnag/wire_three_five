import Proof.Packets.PacketsMetaSweep

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
noncomputable section

/-! ## Update-form docking -/

theorem foldr_upd_slot {m N : ℕ} (slots : Fin m → Fin N) (hi : Function.Injective slots) (σ : Fin N → TS)
    (τ' : Fin m → TS) (j : Fin m) : ∀ js : List (Fin m),
    (js.foldr (fun k ρ => Function.update ρ (slots k) (τ' k)) σ) (slots j) =
      if j ∈ js then τ' j else σ (slots j)
  | [] => by simp
  | k :: ks => by
    simp only [List.foldr_cons, List.mem_cons]
    by_cases h : j = k
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (hi e)), foldr_upd_slot slots hi σ τ' j ks]
      simp [h]

theorem foldr_upd_other {m N : ℕ} (slots : Fin m → Fin N) (σ : Fin N → TS) (τ' : Fin m → TS) (i : Fin N)
    (hn : ∀ j, slots j ≠ i) : ∀ js : List (Fin m),
    (js.foldr (fun k ρ => Function.update ρ (slots k) (τ' k)) σ) i = σ i
  | [] => rfl
  | k :: ks => by
    simp only [List.foldr_cons]
    rw [Function.update_of_ne (fun e => hn k e.symm), foldr_upd_other slots σ τ' i hn ks]

/-- **Docking in update form.** The ambient roles change exactly at the slots of the listed local tapes. -/
theorem LRuns.dockK {m N s W : ℕ} {P : Machine m s} {n : ℕ} {τ τ' : Fin m → TS} (h : LRuns W P n τ τ')
    (slots : Fin m → Fin N) (hi : Function.Injective slots) (σ : Fin N → TS) (hin : ∀ j, σ (slots j) = τ j)
    (js : List (Fin m)) (hsame : ∀ j, j ∉ js → τ' j = τ j) :
    LRuns W (RecoveryFocus.machine slots P) n σ (js.foldr (fun k ρ => Function.update ρ (slots k) (τ' k)) σ) := by
  refine h.focus slots hi σ _ hin (fun j => ?_) (fun i hn => foldr_upd_other slots σ τ' i hn js)
  rw [foldr_upd_slot slots hi]
  split_ifs with hj
  · rfl
  · rw [hin, hsame j hj]

/-- Rewriting the target roles of a run. -/
theorem LRuns.congr_out {t s W : ℕ} {P : Machine t s} {n : ℕ} {σ σ' σ'' : Fin t → TS}
    (h : LRuns W P n σ σ') (e : σ' = σ'') : LRuns W P n σ σ'' := e ▸ h

/-! ## Four distinct slots -/

def D4 {N : ℕ} (r x y fl : Fin N) : Prop := r ≠ x ∧ r ≠ y ∧ r ≠ fl ∧ x ≠ y ∧ x ≠ fl ∧ y ≠ fl

instance {N : ℕ} (r x y fl : Fin N) : Decidable (D4 r x y fl) := by unfold D4; infer_instance

theorem inj4 {N : ℕ} {r x y fl : Fin N} (h : D4 r x y fl) : Function.Injective ![r, x, y, fl] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-! ## The sweep on register roles -/

/-- The bit stream of a register value. -/
abbrev bits (x : ℕ) : ℕ → Bool := fun k => x.testBit k

/-- The sweep's output bits and final carry on two register values. -/
def swOut (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (W a b : ℕ) : List Bool × Bool :=
  sw f c0 (bits a) (bits b) W

theorem swOut_length (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (W a b : ℕ) :
    (swOut f c0 W a b).1.length = W := sw_length _ _ _ _ _

theorem sweep_lruns (f : Bool → Bool → Bool → Bool × Bool) (c0 wr : Bool) (W a b : ℕ) (c : Bool) :
    LRuns W (Sweep.machine f c0 wr) (2 * W + 3) ![.ruler, .reg a, .reg b, .flag c]
      ![.ruler, .reg (if wr then lval (swOut f c0 W a b).1 else a), .reg b, .flag (swOut f c0 W a b).2] := by
  intro H A hA
  have h0 : H 0 = 0 ∧ readTapeBit (A 0) 0 = false ∧ (∀ j, 1 ≤ j → j ≤ W → readTapeBit (A 0) j = true) ∧
      readTapeBit (A 0) (W + 1) = false := hA 0
  have h1 : H 1 = 0 ∧ ∀ j, 1 ≤ j → j ≤ W → readTapeBit (A 1) j = a.testBit (j - 1) := hA 1
  have h2 : H 2 = 0 ∧ ∀ j, 1 ≤ j → j ≤ W → readTapeBit (A 2) j = b.testBit (j - 1) := hA 2
  have h3 : H 3 = 0 ∧ readTapeBit (A 3) 0 = c := hA 3
  have hs := Sweep.run f c0 wr W 0 0 (A 0) (A 1) (A 2) (A 3) h0.2.1 h0.2.2.1 h0.2.2.2
  have hcg : sw f c0 (fun k => readTapeBit (A 1) (0 + 1 + k)) (fun k => readTapeBit (A 2) (0 + 1 + k)) W =
      swOut f c0 W a b := by
    apply sw_congr
    · intro k hk
      rw [h1.2 (0 + 1 + k) (by omega) (by omega)]
      simp
    · intro k hk
      rw [h2.2 (0 + 1 + k) (by omega) (by omega)]
      simp
  rw [hcg] at hs
  have eH : (![0, 0, 0, 0] : Fin 4 → ℕ) = H := by
    funext i; fin_cases i
    · exact h0.1.symm
    · exact h1.1.symm
    · exact h2.1.symm
    · exact h3.1.symm
  have eA : (![A 0, A 1, A 2, A 3] : Fin 4 → List Bool) = A := by
    funext i; fin_cases i <;> rfl
  refine ⟨_, _, hs.congr_in eH eA, ?_⟩
  intro i
  fin_cases i
  · exact ⟨rfl, h0.2⟩
  · cases wr
    · exact ⟨rfl, h1.2⟩
    · refine ⟨rfl, fun j hj1 hjW => ?_⟩
      change readTapeBit (writes (A 1) (0 + 1) (swOut f c0 W a b).1) j = _
      rw [read_writes, if_pos ⟨by omega, by rw [swOut_length]; omega⟩, if_pos rfl, lval_testBit]
  · exact ⟨rfl, h2.2⟩
  · exact ⟨rfl, by change readTapeBit (writeTapeBit (A 3) 0 _) 0 = _; rw [read_write, if_pos rfl]⟩

/-- The sweep docked at four ambient slots (ruler, `x`, `y`, flag). -/
def swAt {N : ℕ} (f : Bool → Bool → Bool → Bool × Bool) (c0 wr : Bool) (r x y fl : Fin N) :=
  RecoveryFocus.machine ![r, x, y, fl] (Sweep.machine f c0 wr)

theorem sweep_at {N W : ℕ} (f : Bool → Bool → Bool → Bool × Bool) (c0 wr : Bool) (σ : Fin N → TS)
    (r x y fl : Fin N) (hd : D4 r x y fl) (a b : ℕ) (c : Bool) (hr : σ r = .ruler) (hx : σ x = .reg a)
    (hy : σ y = .reg b) (hf : σ fl = .flag c) :
    LRuns W (swAt f c0 wr r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg (if wr then lval (swOut f c0 W a b).1 else a))) fl
        (.flag (swOut f c0 W a b).2)) := by
  have h := (sweep_lruns f c0 wr W a b c).dockK ![r, x, y, fl] (inj4 hd) σ
    (by intro j; fin_cases j
        · exact hr
        · exact hx
        · exact hy
        · exact hf) [3, 1]
    (by intro j hj; fin_cases j
        · rfl
        · simp at hj
        · rfl
        · simp at hj)
  exact h

/-! ## Value laws -/

theorem lval_swOut_lt (f : Bool → Bool → Bool → Bool × Bool) (c0 : Bool) (W a b : ℕ) :
    lval (swOut f c0 W a b).1 < 2 ^ W := by
  have := lval_lt (swOut f c0 W a b).1
  rwa [swOut_length] at this

theorem add_val (c0 : Bool) (W a b : ℕ) (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hab : a + b + c0.toNat < 2 ^ W) :
    lval (swOut addF c0 W a b).1 = a + b + c0.toNat ∧ (swOut addF c0 W a b).2 = false := by
  have h := sw_add c0 (bits a) (bits b) W
  rw [fv_testBit, fv_testBit, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  change lval (swOut addF c0 W a b).1 + 2 ^ W * (swOut addF c0 W a b).2.toNat = _ at h
  have hl := lval_swOut_lt addF c0 W a b
  cases hc : (swOut addF c0 W a b).2
  · rw [hc] at h; simp at h; exact ⟨h, rfl⟩
  · rw [hc] at h; simp at h; omega

theorem sub_val (c0 : Bool) (W a b : ℕ) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    (a ≥ b + c0.toNat → lval (swOut subF c0 W a b).1 = a - b - c0.toNat ∧ (swOut subF c0 W a b).2 = false) ∧
      (swOut subF c0 W a b).2 = decide (a < b + c0.toNat) := by
  have h := sw_sub c0 (bits a) (bits b) W
  rw [fv_testBit, fv_testBit, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  change a + 2 ^ W * (swOut subF c0 W a b).2.toNat = lval (swOut subF c0 W a b).1 + b + c0.toNat at h
  have hl := lval_swOut_lt subF c0 W a b
  cases hc : (swOut subF c0 W a b).2
  · rw [hc] at h; simp at h
    refine ⟨fun _ => ⟨by omega, rfl⟩, ?_⟩
    simp; omega
  · rw [hc] at h; simp at h
    refine ⟨fun hge => by omega, ?_⟩
    simp; omega

theorem copy_val (c0 : Bool) (W a b : ℕ) (hb : b < 2 ^ W) :
    lval (swOut copyF c0 W a b).1 = b ∧ (swOut copyF c0 W a b).2 = c0 := by
  obtain ⟨h1, h2⟩ := sw_copy c0 (bits a) (bits b) W
  rw [fv_testBit, Nat.mod_eq_of_lt hb] at h1
  exact ⟨h1, h2⟩

theorem zero_val (c0 : Bool) (W a b : ℕ) :
    lval (swOut zeroF c0 W a b).1 = 0 ∧ (swOut zeroF c0 W a b).2 = c0 :=
  sw_zero c0 (bits a) (bits b) W

theorem shl_val (W a b : ℕ) (ha : a < 2 ^ W) :
    lval (swOut shlF false W a b).1 = 2 * a % 2 ^ W ∧ (swOut shlF false W a b).2 = decide (2 ^ W ≤ 2 * a) := by
  have h := sw_shl false (bits a) (bits b) W
  rw [fv_testBit, Nat.mod_eq_of_lt ha] at h
  change lval (swOut shlF false W a b).1 + 2 ^ W * (swOut shlF false W a b).2.toNat = 2 * a + 0 at h
  have hl := lval_swOut_lt shlF false W a b
  cases hc : (swOut shlF false W a b).2
  · rw [hc] at h; simp at h
    refine ⟨?_, ?_⟩
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · simp; omega
  · rw [hc] at h; simp at h
    refine ⟨?_, ?_⟩
    · have e : 2 * a = lval (swOut shlF false W a b).1 + 2 ^ W * 1 := by omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
    · simp; omega

/-! ## The eight instructions at ambient slots -/

section Instr
variable {N W : ℕ} (σ : Fin N → TS) (r x y fl : Fin N) (hd : D4 r x y fl) (a b : ℕ) (c : Bool)
  (hr : σ r = .ruler) (hx : σ x = .reg a) (hy : σ y = .reg b) (hf : σ fl = .flag c)
include hd hr hx hy hf

/-- `x := x + y`. -/
theorem add_at (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hab : a + b < 2 ^ W) :
    LRuns W (swAt addF false true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg (a + b))) fl (.flag false)) := by
  have h := sweep_at (W := W) addF false true σ r x y fl hd a b c hr hx hy hf
  obtain ⟨e1, e2⟩ := add_val false W a b ha hb (by simpa using hab)
  simp only [if_true, e1, e2, Bool.toNat_false, Nat.add_zero] at h
  exact h

/-- `x := x + 1` (`y` holds `0`). -/
theorem inc_at (hb0 : b = 0) (ha : a + 1 < 2 ^ W) :
    LRuns W (swAt addF true true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg (a + 1))) fl (.flag false)) := by
  subst hb0
  have h := sweep_at (W := W) addF true true σ r x y fl hd a 0 c hr hx hy hf
  obtain ⟨e1, e2⟩ := add_val true W a 0 (by omega) (Nat.two_pow_pos W) (by simpa using ha)
  simp only [if_true, e1, e2, Bool.toNat_true, Nat.add_zero] at h
  exact h

/-- `x := x - y` (no borrow). -/
theorem sub_at (ha : a < 2 ^ W) (hb : b < 2 ^ W) (hba : b ≤ a) :
    LRuns W (swAt subF false true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg (a - b))) fl (.flag false)) := by
  have h := sweep_at (W := W) subF false true σ r x y fl hd a b c hr hx hy hf
  obtain ⟨e1, e2⟩ := (sub_val false W a b ha hb).1 (by simpa using hba)
  simp only [if_true, e1, e2, Bool.toNat_false, Nat.sub_zero] at h
  exact h

/-- `x := x - 1` (`y` holds `0`, `x ≥ 1`). -/
theorem dec_at (hb0 : b = 0) (ha : a < 2 ^ W) (h1 : 1 ≤ a) :
    LRuns W (swAt subF true true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg (a - 1))) fl (.flag false)) := by
  subst hb0
  have h := sweep_at (W := W) subF true true σ r x y fl hd a 0 c hr hx hy hf
  obtain ⟨e1, e2⟩ := (sub_val true W a 0 ha (Nat.two_pow_pos W)).1 (by simpa using h1)
  simp only [if_true, e1, e2, Bool.toNat_true, Nat.sub_zero] at h
  exact h

/-- `flag := decide (x < y)` (nothing written). -/
theorem lt_at (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    LRuns W (swAt subF false false r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg a)) fl (.flag (decide (a < b)))) := by
  have h := sweep_at (W := W) subF false false σ r x y fl hd a b c hr hx hy hf
  have e2 := (sub_val false W a b ha hb).2
  simp only [Bool.false_eq_true, if_false, e2, Bool.toNat_false, Nat.add_zero] at h
  exact h

/-- `x := y`. -/
theorem cpy_at (hb : b < 2 ^ W) :
    LRuns W (swAt copyF false true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg b)) fl (.flag false)) := by
  have h := sweep_at (W := W) copyF false true σ r x y fl hd a b c hr hx hy hf
  obtain ⟨e1, e2⟩ := copy_val false W a b hb
  simp only [if_true, e1, e2] at h
  exact h

/-- `x := 0`. -/
theorem zero_at :
    LRuns W (swAt zeroF false true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg 0)) fl (.flag false)) := by
  have h := sweep_at (W := W) zeroF false true σ r x y fl hd a b c hr hx hy hf
  obtain ⟨e1, e2⟩ := zero_val false W a b
  simp only [if_true, e1, e2] at h
  exact h

/-- `x := 2x mod 2^W`, `flag :=` the bit shifted out. -/
theorem shl_at (ha : a < 2 ^ W) :
    LRuns W (swAt shlF false true r x y fl) (2 * W + 3) σ
      (Function.update (Function.update σ x (.reg (2 * a % 2 ^ W))) fl (.flag (decide (2 ^ W ≤ 2 * a)))) := by
  have h := sweep_at (W := W) shlF false true σ r x y fl hd a b c hr hx hy hf
  obtain ⟨e1, e2⟩ := shl_val W a b ha
  simp only [if_true, e1, e2] at h
  exact h

end Instr

/-! ## The machine that does nothing -/

def nop (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

theorem nop_lruns {t W : ℕ} (σ : Fin t → TS) : LRuns W (nop t) 0 σ σ := by
  intro H A hA
  exact ⟨H, A, ⟨⟨⟨0, H, A⟩, 0, _⟩, rfl, rfl, rfl, le_refl 0⟩, hA⟩

end
end NearCubicWires.PacketsMeta

