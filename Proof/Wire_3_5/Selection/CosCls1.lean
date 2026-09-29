import Proof.Wire_3_5.Selection.CosBnd4

/-! # C1.5 class bound, part 1: cost bounds uniform in the request (P3:1335, 1358-1360)

Paper: "A product-code coset [...] is findable deterministically in `2^{n/2+O(k)}poly(n)` time" (P3:1328-1335); "There
are `2^k` candidate cosets, so the total is bounded as claimed" (P3:1358-1359). The machine's cost is a large
nonnegative combination of the request's small numbers (`n`, `r`, `s`, `b`, the halves, `L`, `W`) and of the
exponentials `2^lw`, `2^rw` (one half's points, at most `2^{(n+1)/2}`), `2^{s·r/2}` (one side's error rows) and
`2^k` (the cosets). `Bd ex f`: the cost function `f` is at most `K·W^a·ex` with `K`, `a` INDEPENDENT of the request.
The closure lemmas and the atoms build such bounds for the machine's cost formulas mechanically (the tactic
`cos_bd`). Main declarations: `eP`, `eH`, `e1`, `eG`, `eK`, `Bd`, its closure lemmas and atoms. Paper quantity: the
selection time's shape `2^{n/2+O(k)}·poly`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Point NearCubicWires.WireExponent3_5.SelectionMachine.Sort

/-! ## The exponential kinds -/

/-- Polynomial. -/
def eP (_R : SelectionReq) (_h : ParamsOk _R) : ℕ := 1
/-- One half's points: `2^{(n+1)/2}`. -/
def eH (R : SelectionReq) (_h : ParamsOk R) : ℕ := 2 ^ ((R.n + 1) / 2)
/-- One side's error rows: `2^{s·r/2}`. -/
def e1 (R : SelectionReq) (_h : ParamsOk R) : ℕ := 2 ^ (R.s * (R.r / 2))
/-- One gate at one coset. -/
def eG (R : SelectionReq) (h : ParamsOk R) : ℕ := e1 R h * eH R h
/-- All cosets. -/
def eK (R : SelectionReq) (h : ParamsOk R) : ℕ := 2 ^ (R.r * R.s) * eG R h

theorem eP_pos : ∀ (R : SelectionReq) (h : ParamsOk R), 1 ≤ eP R h := fun _ _ => le_rfl
theorem eH_pos : ∀ (R : SelectionReq) (h : ParamsOk R), 1 ≤ eH R h := fun _ _ => Nat.one_le_two_pow
theorem e1_pos : ∀ (R : SelectionReq) (h : ParamsOk R), 1 ≤ e1 R h := fun _ _ => Nat.one_le_two_pow
theorem eG_pos : ∀ (R : SelectionReq) (h : ParamsOk R), 1 ≤ eG R h := fun R h => by
  have := e1_pos R h; have := eH_pos R h; unfold eG; nlinarith
theorem eK_pos : ∀ (R : SelectionReq) (h : ParamsOk R), 1 ≤ eK R h := fun R h => by
  have := eG_pos R h; have : 1 ≤ 2 ^ (R.r * R.s) := Nat.one_le_two_pow; unfold eK; nlinarith

theorem eH_le_eG : ∀ (R : SelectionReq) (h : ParamsOk R), eH R h ≤ eG R h := fun R h => by
  have := e1_pos R h; unfold eG; nlinarith
theorem e1_le_eG : ∀ (R : SelectionReq) (h : ParamsOk R), e1 R h ≤ eG R h := fun R h => by
  have := eH_pos R h; unfold eG; nlinarith
theorem eG_le_eK : ∀ (R : SelectionReq) (h : ParamsOk R), eG R h ≤ eK R h := fun R h => by
  have : 1 ≤ 2 ^ (R.r * R.s) := Nat.one_le_two_pow; unfold eK; nlinarith
theorem eH_le_eK : ∀ (R : SelectionReq) (h : ParamsOk R), eH R h ≤ eK R h := fun R h =>
  (eH_le_eG R h).trans (eG_le_eK R h)
theorem e1_le_eK : ∀ (R : SelectionReq) (h : ParamsOk R), e1 R h ≤ eK R h := fun R h =>
  (e1_le_eG R h).trans (eG_le_eK R h)

/-! ## Uniform bounds -/

/-- **`f` is at most `K·W^a·ex`**, `K` and `a` independent of the request. -/
def Bd (ex : (R : SelectionReq) → ParamsOk R → ℕ) (f : (R : SelectionReq) → ParamsOk R → ℕ) : Prop :=
  ∃ K a : ℕ, ∀ (R : SelectionReq) (h : ParamsOk R), f R h ≤ K * Wof R ^ a * ex R h

theorem W_pos (R : SelectionReq) : 1 ≤ Wof R := by unfold Wof; omega

theorem pow_le_pow_W (R : SelectionReq) (a b : ℕ) (hab : a ≤ b) : Wof R ^ a ≤ Wof R ^ b :=
  Nat.pow_le_pow_right (W_pos R) hab

section Closure
variable {ex : (R : SelectionReq) → ParamsOk R → ℕ} {f g : (R : SelectionReq) → ParamsOk R → ℕ}

theorem bd_mono (hle : ∀ R h, f R h ≤ g R h) (hg : Bd ex g) : Bd ex f := by
  obtain ⟨K, a, hK⟩ := hg
  exact ⟨K, a, fun R h => le_trans (hle R h) (hK R h)⟩

theorem bd_lift {ex' : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, ex R h ≤ ex' R h) (hf : Bd ex f) :
    Bd ex' f := by
  obtain ⟨K, a, hK⟩ := hf
  exact ⟨K, a, fun R h => le_trans (hK R h) (Nat.mul_le_mul_left _ (hex R h))⟩

theorem bd_liftP (hex : ∀ R h, 1 ≤ ex R h) (hf : Bd eP f) : Bd ex f := bd_lift hex hf

theorem bd_of_le (hf : ∀ R h, f R h ≤ ex R h) : Bd ex f :=
  ⟨1, 0, fun R h => by rw [pow_zero, Nat.mul_one, Nat.one_mul]; exact hf R h⟩

theorem bd_add (hf : Bd ex f) (hg : Bd ex g) : Bd ex (fun R h => f R h + g R h) := by
  obtain ⟨K₁, a₁, h₁⟩ := hf
  obtain ⟨K₂, a₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, a₁ + a₂, fun R h => ?_⟩
  have e1 := pow_le_pow_W R a₁ (a₁ + a₂) (by omega)
  have e2 := pow_le_pow_W R a₂ (a₁ + a₂) (by omega)
  have m1 : K₁ * Wof R ^ a₁ * ex R h ≤ K₁ * Wof R ^ (a₁ + a₂) * ex R h :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ e1)
  have m2 : K₂ * Wof R ^ a₂ * ex R h ≤ K₂ * Wof R ^ (a₁ + a₂) * ex R h :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ e2)
  have := h₁ R h
  have := h₂ R h
  show f R h + g R h ≤ (K₁ + K₂) * Wof R ^ (a₁ + a₂) * ex R h
  rw [Nat.add_mul, Nat.add_mul]
  omega

theorem bd_mul_poly (hf : Bd eP f) (hg : Bd ex g) : Bd ex (fun R h => f R h * g R h) := by
  obtain ⟨K₁, a₁, h₁⟩ := hf
  obtain ⟨K₂, a₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, a₁ + a₂, fun R h => ?_⟩
  have u : f R h ≤ K₁ * Wof R ^ a₁ := by have := h₁ R h; simpa [eP] using this
  calc f R h * g R h ≤ (K₁ * Wof R ^ a₁) * (K₂ * Wof R ^ a₂ * ex R h) := Nat.mul_le_mul u (h₂ R h)
    _ = K₁ * K₂ * Wof R ^ (a₁ + a₂) * ex R h := by rw [pow_add]; ring

theorem bd_mul_poly' (hg : Bd ex g) (hf : Bd eP f) : Bd ex (fun R h => g R h * f R h) := by
  have := bd_mul_poly hf hg
  exact bd_mono (fun _ _ => le_of_eq (Nat.mul_comm _ _)) this

theorem bd_sub (hf : Bd ex f) : Bd ex (fun R h => f R h - g R h) := bd_mono (fun _ _ => Nat.sub_le _ _) hf

theorem bd_div {c : ℕ} (hf : Bd ex f) : Bd ex (fun R h => f R h / c) := bd_mono (fun _ _ => Nat.div_le_self _ _) hf

theorem bd_mod {c : ℕ} (hf : Bd ex f) : Bd ex (fun R h => f R h % c) := bd_mono (fun _ _ => Nat.mod_le _ _) hf

theorem bd_const (hex : ∀ R h, 1 ≤ ex R h) (c : ℕ) : Bd ex (fun _ _ => c) :=
  ⟨c, 0, fun R h => by rw [pow_zero, Nat.mul_one]; exact Nat.le_mul_of_pos_right _ (hex R h)⟩

theorem bd_leW (hex : ∀ R h, 1 ≤ ex R h) (c a : ℕ) (hf : ∀ R h, f R h ≤ c * Wof R ^ a) : Bd ex f :=
  ⟨c, a, fun R h => le_trans (hf R h) (Nat.le_mul_of_pos_right _ (hex R h))⟩

theorem bd_leW1 (hex : ∀ R h, 1 ≤ ex R h) (hf : ∀ R h, f R h ≤ Wof R) : Bd ex f :=
  bd_leW hex 1 1 fun R h => by rw [pow_one, Nat.one_mul]; exact hf R h

end Closure

/-! ## The small atoms (all at most `W`) -/

theorem n_le_W (R : SelectionReq) : R.n ≤ Wof R := by unfold Wof; omega
theorem L_le_W (R : SelectionReq) : Lof R ≤ Wof R := by unfold Wof; omega

theorem lw_le (R : SelectionReq) (h : ParamsOk R) : lw (starParamsOf R h) ≤ (R.n + 1) / 2 := by
  have hb : R.r * (starParamsOf R h).b ≤ R.n := (starParamsOf R h).r_mul_b_le
  have hr2 : R.r % 2 = 0 := h.1
  have key : R.r / 2 * (starParamsOf R h).b * 2 = R.r * (starParamsOf R h).b := by
    rw [Nat.mul_right_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hr2)]
  show R.r / 2 * (starParamsOf R h).b + (R.n - R.r * (starParamsOf R h).b + 1) / 2 ≤ (R.n + 1) / 2
  omega

theorem rw_le (R : SelectionReq) (h : ParamsOk R) : rw (starParamsOf R h) ≤ (R.n + 1) / 2 := by
  have := lw_le R h
  have e : lw (starParamsOf R h) = R.r / 2 * (starParamsOf R h).b + (R.n - R.r * (starParamsOf R h).b + 1) / 2 := rfl
  show R.r / 2 * (starParamsOf R h).b + (R.n - R.r * (starParamsOf R h).b) / 2 ≤ (R.n + 1) / 2
  omega

/-- The star numbers and the request's counts are at most `W`. -/
theorem atoms_le (R : SelectionReq) (h : ParamsOk R) :
    hh (starParamsOf R h) ≤ Wof R ∧ (starParamsOf R h).b ≤ Wof R ∧ R.s ≤ Wof R ∧
      fL (starParamsOf R h) ≤ Wof R ∧ fR (starParamsOf R h) ≤ Wof R ∧ R.r ≤ Wof R ∧
      lw (starParamsOf R h) ≤ Wof R ∧ rw (starParamsOf R h) ≤ Wof R ∧ R.gates.length ≤ Wof R ∧
      R.pops.length ≤ Wof R ∧ R.s + 1 ≤ Wof R := by
  obtain ⟨_, s1, b1, r1, _⟩ := star_le R h
  have hn := n_le_W R
  have hL := L_le_W R
  have g1 := gates_le_L R
  have p1 := pops_le_L R
  have l1 := lw_le R h
  have r2 := rw_le R h
  have hW : R.n + 8 ≤ Wof R := by unfold Wof; omega
  have e1 : hh (starParamsOf R h) = R.r / 2 := rfl
  have e2 : fL (starParamsOf R h) = (R.n - R.r * (starParamsOf R h).b + 1) / 2 := rfl
  have e3 : fR (starParamsOf R h) = (R.n - R.r * (starParamsOf R h).b) / 2 := rfl
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem pow_natBitLength_le (v : ℕ) : 2 ^ natBitLength v ≤ 2 * v + 2 := by
  show 2 ^ (Nat.log 2 v + 1) ≤ 2 * v + 2
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos v with h0 | hp
  · subst h0; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hp)
    omega

theorem natBitLength_two_pow (s : ℕ) : natBitLength (2 ^ s) = s + 1 := by
  show Nat.log 2 (2 ^ s) + 1 = s + 1
  rw [Nat.log_pow (by norm_num)]

section Atoms
variable {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h)
include hex

theorem bd_W : Bd ex (fun R _ => Wof R) := bd_leW1 hex fun _ _ => le_rfl
theorem bd_L : Bd ex (fun R _ => Lof R) := bd_leW1 hex fun R _ => L_le_W R
theorem bd_n : Bd ex (fun R _ => R.n) := bd_leW1 hex fun R _ => n_le_W R
theorem bd_r : Bd ex (fun R _ => R.r) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.2.2.1
theorem bd_s : Bd ex (fun R _ => R.s) := bd_leW1 hex fun R h => (atoms_le R h).2.2.1
theorem bd_ng : Bd ex (fun R _ => R.gates.length) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.2.2.2.2.2.1
theorem bd_np : Bd ex (fun R _ => R.pops.length) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.2.2.2.2.2.2.1
theorem bd_hh : Bd ex (fun R h => hh (starParamsOf R h)) := bd_leW1 hex fun R h => (atoms_le R h).1
theorem bd_b : Bd ex (fun R h => (starParamsOf R h).b) := bd_leW1 hex fun R h => (atoms_le R h).2.1
theorem bd_Ps : Bd ex (fun R h => (starParamsOf R h).s) := bd_leW1 hex fun R h => (atoms_le R h).2.2.1
theorem bd_Pn : Bd ex (fun R h => (starParamsOf R h).n) := bd_leW1 hex fun R _ => n_le_W R
theorem bd_Pr : Bd ex (fun R h => (starParamsOf R h).r) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.2.2.1
theorem bd_fL : Bd ex (fun R h => fL (starParamsOf R h)) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.1
theorem bd_fR : Bd ex (fun R h => fR (starParamsOf R h)) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.2.1
theorem bd_lw : Bd ex (fun R h => lw (starParamsOf R h)) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.2.2.2.1
theorem bd_rw : Bd ex (fun R h => rw (starParamsOf R h)) := bd_leW1 hex fun R h => (atoms_le R h).2.2.2.2.2.2.2.1
theorem bd_B : Bd ex (fun R _ => Bof R) := bd_leW hex 8 2 fun R _ => le_of_eq (by unfold Bof; ring)
theorem bd_tl : Bd ex (fun R _ => (popTable (Wof R) R).length) :=
  bd_leW hex 8 2 fun R _ => le_trans (popTable_le R) (le_of_eq (by unfold Bof; ring))

theorem bd_nbl {v : (R : SelectionReq) → ParamsOk R → ℕ} (hv : Bd eP v) :
    Bd ex (fun R h => natBitLength (v R h)) := by
  obtain ⟨K, a, hK⟩ := hv
  refine bd_leW hex (K + 1) a fun R h => ?_
  have h1 := natBitLength_le (v R h)
  have h2 : v R h ≤ K * Wof R ^ a := by have := hK R h; simpa [eP] using this
  have h3 : 1 ≤ Wof R ^ a := Nat.one_le_pow _ _ (W_pos R)
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem bd_pnbl {v : (R : SelectionReq) → ParamsOk R → ℕ} (hv : Bd eP v) :
    Bd ex (fun R h => 2 ^ natBitLength (v R h)) := by
  obtain ⟨K, a, hK⟩ := hv
  refine bd_leW hex (2 * K + 2) a fun R h => ?_
  have h1 := pow_natBitLength_le (v R h)
  have h2 : v R h ≤ K * Wof R ^ a := by have := hK R h; simpa [eP] using this
  have h3 : 1 ≤ Wof R ^ a := Nat.one_le_pow _ _ (W_pos R)
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

theorem bd_nbls : Bd ex (fun R _ => natBitLength (2 ^ R.s)) :=
  bd_leW1 hex fun R h => by rw [natBitLength_two_pow]; exact (atoms_le R h).2.2.2.2.2.2.2.2.2.2

end Atoms

/-! ## The exponential atoms -/

section ExpAtoms
variable {ex : (R : SelectionReq) → ParamsOk R → ℕ}

theorem bd_EL (hex : ∀ R h, eH R h ≤ ex R h) :
    Bd ex (fun R h => 2 ^ (hh (starParamsOf R h) * (starParamsOf R h).b + fL (starParamsOf R h))) :=
  bd_lift hex (bd_of_le fun R h => Nat.pow_le_pow_right (by norm_num) (lw_le R h))

theorem bd_ER (hex : ∀ R h, eH R h ≤ ex R h) :
    Bd ex (fun R h => 2 ^ (hh (starParamsOf R h) * (starParamsOf R h).b + fR (starParamsOf R h))) :=
  bd_lift hex (bd_of_le fun R h => Nat.pow_le_pow_right (by norm_num) (rw_le R h))

theorem bd_lwE (hex : ∀ R h, eH R h ≤ ex R h) : Bd ex (fun R h => 2 ^ lw (starParamsOf R h)) :=
  bd_lift hex (bd_of_le fun R h => Nat.pow_le_pow_right (by norm_num) (lw_le R h))

theorem bd_rwE (hex : ∀ R h, eH R h ≤ ex R h) : Bd ex (fun R h => 2 ^ rw (starParamsOf R h)) :=
  bd_lift hex (bd_of_le fun R h => Nat.pow_le_pow_right (by norm_num) (rw_le R h))

theorem bd_E1 (hex : ∀ R h, e1 R h ≤ ex R h) :
    Bd ex (fun R h => 2 ^ ((starParamsOf R h).s * hh (starParamsOf R h))) :=
  bd_lift hex (bd_of_le fun _ _ => le_rfl)

theorem bd_E1' (hex : ∀ R h, e1 R h ≤ ex R h) :
    Bd ex (fun R h => 2 ^ (hh (starParamsOf R h) * (starParamsOf R h).s)) :=
  bd_lift hex (bd_of_le fun R h => by
    show 2 ^ (R.r / 2 * R.s) ≤ 2 ^ (R.s * (R.r / 2))
    rw [Nat.mul_comm])

theorem pow_k_le (R : SelectionReq) (h : ParamsOk R) : 2 ^ (R.r * R.s) ≤ eK R h :=
  Nat.le_mul_of_pos_right _ (eG_pos R h)

theorem bd_Ek (hex : ∀ R h, eK R h ≤ ex R h) : Bd ex (fun R _ => 2 ^ (R.r * R.s)) :=
  bd_lift hex (bd_of_le fun R h => pow_k_le R h)

theorem pow_s_le (R : SelectionReq) (h : ParamsOk R) : 2 ^ R.s ≤ eK R h := by
  have hr : 1 ≤ R.r := by have := h.2.1; omega
  have : R.s ≤ R.r * R.s := Nat.le_mul_of_pos_left _ hr
  exact le_trans (Nat.pow_le_pow_right (by norm_num) this) (pow_k_le R h)

theorem bd_Es (hex : ∀ R h, eK R h ≤ ex R h) : Bd ex (fun R _ => 2 ^ R.s) :=
  bd_lift hex (bd_of_le fun R h => pow_s_le R h)

theorem bd_Es1 (hex : ∀ R h, eK R h ≤ ex R h) : Bd ex (fun R _ => 2 ^ (R.s + 1)) :=
  bd_lift hex ⟨2, 0, fun R h => by
    show 2 ^ (R.s + 1) ≤ 2 * Wof R ^ 0 * eK R h
    rw [pow_zero, Nat.mul_one, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (pow_s_le R h)⟩

/-- `2^{s·hh} · f` for a half-bounded `f`. -/
theorem bd_E1_mul {f : (R : SelectionReq) → ParamsOk R → ℕ} (hf : Bd eH f) :
    Bd eG (fun R h => 2 ^ ((starParamsOf R h).s * hh (starParamsOf R h)) * f R h) := by
  obtain ⟨K, a, hK⟩ := hf
  refine ⟨K, a, fun R h => ?_⟩
  show e1 R h * f R h ≤ K * Wof R ^ a * eG R h
  calc e1 R h * f R h ≤ e1 R h * (K * Wof R ^ a * eH R h) := Nat.mul_le_mul_left _ (hK R h)
    _ = K * Wof R ^ a * eG R h := by unfold eG; ring

/-- `2^k · f` for a gate-bounded `f`. -/
theorem bd_K_mul {f : (R : SelectionReq) → ParamsOk R → ℕ} (hf : Bd eG f) :
    Bd eK (fun R h => 2 ^ (R.r * R.s) * f R h) := by
  obtain ⟨K, a, hK⟩ := hf
  refine ⟨K, a, fun R h => ?_⟩
  show 2 ^ (R.r * R.s) * f R h ≤ K * Wof R ^ a * eK R h
  calc 2 ^ (R.r * R.s) * f R h ≤ 2 ^ (R.r * R.s) * (K * Wof R ^ a * eG R h) := Nat.mul_le_mul_left _ (hK R h)
    _ = K * Wof R ^ a * eK R h := by unfold eK; ring

end ExpAtoms

/-- The `2^{s·hh}` prefactor at any kind above `eG`. -/
theorem bd_E1_mulL {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h)
    {f : (R : SelectionReq) → ParamsOk R → ℕ} (hf : Bd eH f) :
    Bd ex (fun R h => 2 ^ ((starParamsOf R h).s * hh (starParamsOf R h)) * f R h) := bd_lift hex (bd_E1_mul hf)

/-- The `2^k` prefactor at any kind above `eK`. -/
theorem bd_K_mulL {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eK R h ≤ ex R h)
    {f : (R : SelectionReq) → ParamsOk R → ℕ} (hf : Bd eG f) : Bd ex (fun R h => 2 ^ (R.r * R.s) * f R h) :=
  bd_lift hex (bd_K_mul hf)

/-! ## The bounding tactic -/

/-- The kind is at least `1`. -/
syntax "cos_pos" : tactic
macro_rules
  | `(tactic| cos_pos) => `(tactic| first
    | exact eP_pos
    | exact eH_pos
    | exact e1_pos
    | exact eG_pos
    | exact eK_pos
    | assumption)

/-- One kind below another. -/
syntax "cos_le" : tactic
macro_rules
  | `(tactic| cos_le) => `(tactic| first
    | exact fun _ _ => le_rfl
    | exact eH_le_eG
    | exact e1_le_eG
    | exact eG_le_eK
    | exact eH_le_eK
    | exact e1_le_eK
    | assumption)

/-- A side condition of a bound lemma. -/
syntax "cos_side" : tactic
macro_rules
  | `(tactic| cos_side) => `(tactic| first | cos_pos | cos_le)

/-- **A uniform bound for a cost formula**, by its sums, products (one factor polynomial), the `2^{s·hh}` and `2^k`
prefactors, and the atoms. -/
syntax "cos_bd" : tactic

/-- A hypothesis, or a docked component bound (extended as components are bounded). -/
syntax "cos_atom" : tactic
macro_rules
  | `(tactic| cos_atom) => `(tactic| first
    | assumption
    | (refine bd_liftP (by cos_pos) ?_; assumption))

open Lean Meta Elab Tactic in
/-- Apply the bound lemma `lem` to the main goal by unification alone, then close its side conditions by `cos_side`
and its bound premises by `cos_bd`, in order. -/
def cosUse (lem : Name) : TacticM Unit := do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  let e ← mkConstWithFreshMVarLevels lem
  let (ms, _, ty) ← g.withContext (forallMetaTelescopeReducing (← inferType e))
  unless ← g.withContext (isDefEq ty (← g.getType)) do throwError "cos: no match"
  g.assign (mkAppN e ms)
  for m in ms do
    let mv := m.mvarId!
    unless ← mv.isAssigned do
      setGoals [mv]
      let t ← instantiateMVars (← mv.getType)
      if t.isAppOf ``Bd then evalTactic (← `(tactic| cos_bd)) else evalTactic (← `(tactic| cos_side))
      unless (← getGoals).isEmpty do throwError "cos: unsolved"
  setGoals rest

open Lean Meta Elab Tactic in
/-- Try the bound lemmas in order (restoring the state after each failure), then the hypotheses and components. -/
def cosTry (cands : List Name) : TacticM Unit := do
  for c in cands do
    let s ← saveState
    try
      cosUse c
      return
    catch _ =>
      s.restore
  evalTactic (← `(tactic| cos_atom))

open Lean in
/-- The bound lemmas for a body with head constant `hd`. -/
def cosCands (hd : Name) : List Name :=
  if hd == ``HAdd.hAdd then [``bd_add]
  else if hd == ``HMul.hMul then [``bd_E1_mulL, ``bd_K_mulL, ``bd_mul_poly, ``bd_mul_poly']
  else if hd == ``HSub.hSub then [``bd_sub]
  else if hd == ``HDiv.hDiv then [``bd_div]
  else if hd == ``HMod.hMod then [``bd_mod]
  else if hd == ``OfNat.ofNat then [``bd_const]
  else if hd == ``HPow.hPow then
    [``bd_pnbl, ``bd_EL, ``bd_ER, ``bd_lwE, ``bd_rwE, ``bd_E1, ``bd_E1', ``bd_Ek, ``bd_Es, ``bd_Es1]
  else if hd == ``natBitLength then [``bd_nbls, ``bd_nbl]
  else if hd == ``List.length then [``bd_ng, ``bd_np, ``bd_tl]
  else if hd == ``Wof then [``bd_W]
  else if hd == ``Lof then [``bd_L]
  else if hd == ``Bof then [``bd_B]
  else if hd == ``SelectionReq.n then [``bd_n]
  else if hd == ``SelectionReq.r then [``bd_r]
  else if hd == ``SelectionReq.s then [``bd_s]
  else if hd == ``StarParams.n then [``bd_Pn]
  else if hd == ``StarParams.r then [``bd_Pr]
  else if hd == ``StarParams.s then [``bd_Ps]
  else if hd == ``StarParams.b then [``bd_b]
  else if hd == ``hh then [``bd_hh]
  else if hd == ``fL then [``bd_fL]
  else if hd == ``fR then [``bd_fR]
  else if hd == ``lw then [``bd_lw]
  else if hd == ``rw then [``bd_rw]
  else []

open Lean Meta Elab Tactic in
/-- The head constant of a bound goal's body. -/
def cosHead (g : MVarId) : MetaM Name := do
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (``Bd, #[_, f]) => lambdaTelescope f fun _ body => pure (body.getAppFn.constName?.getD Name.anonymous)
  | _ => pure Name.anonymous

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| cos_bd) => do cosTry (cosCands (← cosHead (← getMainGoal)))

/-- Apply one docked component bound. -/
syntax "cos_app " ident : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| cos_app $id:ident) => do cosUse (← realizeGlobalConstNoOverloadWithInfo id)

/-! ## First components -/

theorem bd_zw {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, 1 ≤ ex R h)
    {x : (R : SelectionReq) → ParamsOk R → ℕ} (hx : Bd eP x) : Bd ex (fun R h => zwCost (x R h)) := by
  refine bd_liftP hex ?_
  unfold zwCost
  with_reducible cos_bd

macro_rules
  | `(tactic| cos_atom) => `(tactic| cos_app bd_zw)

theorem bd_kw {ex : (R : SelectionReq) → ParamsOk R → ℕ} (hex : ∀ R h, eG R h ≤ ex R h)
    {cR cL : (R : SelectionReq) → ParamsOk R → ℕ} (hR : Bd eP cR) (hL : Bd eP cL) :
    Bd ex (fun R h => kwCost (starParamsOf R h) (Wof R) (cR R h) (cL R h)) := by
  refine bd_lift hex ?_
  unfold kwCost enumCost pointCost
  with_reducible cos_bd

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
