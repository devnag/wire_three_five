import Proof.Wire_3_5.Selection.CosBnd3

/-! # C1.5: the register capacity and the whole run (P3:1324-1362, 3673)

Paper: star:selection's algorithm (P3:1337-1360), run by one register machine. The register capacity `capOf R` only
bounds the unary registers (the time does not depend on it): it is the gate routine's space need plus `2^(8W²+2W)`
plus the gate record count. With it, the parse's side conditions (`ParseOK`) and the loop's width and capacity facts
(`GlobalOK`) hold for every admissible request, and **`c1WM_Pw`**: the machine `Pw` runs from the framed request word
to the selected coset's word, every head and register back at `0` (Top's residual `C1WM`). Main declarations:
`capOf`, `parseOK_of`, `globalOK_of`, `parseCostF`, **`c1WM_Pw`**. Paper quantity: the selected coset's word. -/

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
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (selWord)

/-- **The register capacity.** -/
def capOf (R : SelectionReq) : ℕ :=
  (if h : ParamsOk R then gateNeed (starParamsOf R h) (Wof R) (Lof R) else 0) + 2 ^ (Bof R + 2 * Wof R) +
    R.gates.length * (R.n + 1) * (2 * Wof R + 2) + 3

theorem cap_ge (R : SelectionReq) : 2 ^ (Bof R + 2 * Wof R) ≤ capOf R := by unfold capOf; omega

/-- The capacity's small facts: every term below `T = 2^(B+W)`, `16·T ≤ 2^(B+2W)`. -/
theorem cap_facts (R : SelectionReq) :
    Wof R ≤ Bof R ∧ Bof R < 2 ^ (Bof R + Wof R) ∧ 16 * 2 ^ (Bof R + Wof R) ≤ 2 ^ (Bof R + 2 * Wof R) ∧
      (∀ a, a ≤ Bof R + Wof R → 2 ^ a ≤ 2 ^ (Bof R + Wof R)) ∧ 2 * Wof R + 1 ≤ Bof R := by
  have hW : 16 ≤ Wof R := by unfold Wof; omega
  have hWW : 16 * Wof R ≤ Wof R * Wof R := Nat.mul_le_mul_right _ hW
  have hB : Bof R = 8 * (Wof R * Wof R) := rfl
  have h1 : Bof R < 2 ^ (Bof R + Wof R) := by
    have := Nat.lt_two_pow_self (n := Bof R)
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show Bof R ≤ Bof R + Wof R by omega)
    omega
  have h2 : 16 * 2 ^ (Bof R + Wof R) ≤ 2 ^ (Bof R + 2 * Wof R) := by
    have e : 2 ^ (Bof R + 2 * Wof R) = 2 ^ (Bof R + Wof R) * 2 ^ Wof R := by
      rw [← pow_add]; congr 1; ring
    have h16 : 16 ≤ 2 ^ Wof R := le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ Wof R by omega))
    rw [e, Nat.mul_comm 16]
    exact Nat.mul_le_mul_left _ h16
  exact ⟨by omega, h1, h2, fun a ha => Nat.pow_le_pow_right (by norm_num) ha, by omega⟩

/-- Two terms below `T` are below the capacity. -/
theorem cap_two (R : SelectionReq) (a b : ℕ) (ha : a ≤ 2 ^ (Bof R + Wof R)) (hb : b ≤ 2 ^ (Bof R + Wof R)) :
    a + b ≤ capOf R := by
  obtain ⟨_, _, h16, _, _⟩ := cap_facts R
  have := cap_ge R
  omega

/-- The small numbers of the request. -/
theorem small_facts (R : SelectionReq) (h : ParamsOk R) :
    R.r * R.s ≤ R.n ∧ R.s ≤ R.n ∧ (starParamsOf R h).b ≤ R.n ∧ R.r ≤ R.n ∧ R.r * (starParamsOf R h).b ≤ R.n ∧
      R.s * (R.r / 2) ≤ R.n ∧ R.gates.length ≤ Lof R ∧ R.pops.length ≤ Lof R ∧
      R.gates.length * (R.n + 1) ≤ Lof R ∧ 3 ≤ Lof R ∧ Wof R = 8 * (Lof R + R.n + 2) := by
  obtain ⟨a, b, c, d, e⟩ := star_le R h
  have f : R.s * (R.r / 2) ≤ R.r * R.s := by rw [Nat.mul_comm R.r]; exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  have g := gInts_len_le R
  rw [gInts_length] at g
  refine ⟨a, b, c, d, e, by omega, gates_le_L R, pops_le_L R, by omega, Lof_ge R, rfl⟩

/-- **The parse's side conditions** hold at `capOf`. -/
theorem parseOK_of (R : SelectionReq) (h : ParamsOk R) (hnn : ∀ X ∈ R.pops, 0 ≤ X.2) : ParseOK R h (capOf R) := by
  obtain ⟨hWB, hBT, h16, hE, hB2⟩ := cap_facts R
  have hX := cap_ge R
  obtain ⟨k1, s1, b1, r1, rb1, sr1, g1, p1, gn1, L3, LW⟩ := small_facts R h
  obtain ⟨nb1, nb2, _, _⟩ := nr_bits R
  set T := 2 ^ (Bof R + Wof R)
  have e1 : ∀ a, a ≤ Bof R → a ≤ T := fun a ha => by omega
  have hpT := popTable_le R
  have hgT := gateTable_le R
  have p2 : ∀ a, a ≤ Lof R + 2 → 2 ^ a ≤ T := fun a ha => hE a (by omega)
  have p3 : ∀ a, a ≤ R.n + 2 → 2 ^ a ≤ T := fun a ha => hE a (by omega)
  refine ⟨by omega, by have := p3 _ (show natBitLength R.n + 1 ≤ R.n + 2 by have := natBitLength_le R.n; omega); omega,
    by have := p3 _ (show natBitLength R.r + 1 ≤ R.n + 2 by have := natBitLength_le R.r; omega); omega,
    by omega, by have := p3 _ (show R.s + 1 ≤ R.n + 2 by omega); omega, by omega, by omega, by omega, by omega,
    by unfold Bof at *; omega, by omega, by omega,
    by have := p2 _ (show R.gates.length + 2 ≤ Lof R + 2 by omega); omega,
    by have := p2 _ (show R.pops.length + 2 ≤ Lof R + 2 by omega); omega,
    by have := p3 _ (show R.r * R.s + 1 ≤ R.n + 2 by omega); omega,
    by unfold Bof at *; have : Wof R ≤ Wof R * Wof R := Nat.le_mul_self _; omega, by omega,
    fun z hz => le_trans (gInts_bits R z hz) (by omega), hgT, hpT,
    lt_of_lt_of_le (by have := Nat.lt_two_pow_self (n := Lof R); omega)
      (Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show Lof R ≤ Wof R by omega)), ?_⟩
  intro X hXm
  obtain ⟨hi, hn, hd, hl⟩ := pop_bits R X hXm
  refine ⟨hnn X hXm, fun i hi' => le_trans (hi i hi') (by omega), le_trans hn (by omega), le_trans hd (by omega), ?_⟩
  have a1 := p2 _ (show X.1.length + 2 ≤ Lof R + 2 by omega)
  have a2 : (X.1.length + 2) * (2 * Wof R + 2) ≤ Bof R := by
    unfold Bof; nlinarith
  omega

/-- A term below `8W²` is below the capacity. -/
theorem cap_lin (R : SelectionReq) (t : ℕ) (ht : t ≤ Bof R) : t ≤ capOf R := by
  obtain ⟨_, hBT, h16, _, _⟩ := cap_facts R
  have := cap_ge R
  omega

/-- A power of two below `2^(8W² + W)` is below the capacity. -/
theorem cap_pow (R : SelectionReq) (a : ℕ) (ha : a ≤ Bof R + Wof R) : 2 ^ a ≤ capOf R := by
  obtain ⟨_, _, h16, hE, _⟩ := cap_facts R
  have := cap_ge R
  have := hE a ha
  omega

theorem ite_le' {c : Prop} [Decidable c] {a b M : ℕ} (ha : a ≤ M) (hb : b ≤ M) : (if c then a else b) ≤ M := by
  split_ifs <;> assumption

theorem pvP_le_cap (R : SelectionReq) (h : ParamsOk R) (r : Fin 112) : pvP R h r ≤ capOf R := by
  obtain ⟨hWB, _, _, _, hB2⟩ := cap_facts R
  obtain ⟨k1, s1, b1, r1, rb1, sr1, g1, p1, gn1, L3, LW⟩ := small_facts R h
  have c : ∀ t, t ≤ Bof R → t ≤ capOf R := cap_lin R
  have v0 : hh (starParamsOf R h) ≤ capOf R := c _ (by unfold hh; simp [starParamsOf]; omega)
  have v1 : (starParamsOf R h).b ≤ capOf R := c _ (by omega)
  have v2 : R.s ≤ capOf R := c _ (by omega)
  have v3 : fL (starParamsOf R h) ≤ capOf R := c _ (by unfold fL; simp [starParamsOf]; omega)
  have v4 : fR (starParamsOf R h) ≤ capOf R := c _ (by unfold fR; simp [starParamsOf]; omega)
  have v5 : Lof R + 1 ≤ capOf R := c _ (by omega)
  have v58 : (popTable (Wof R) R).length ≤ capOf R := c _ (popTable_le R)
  have v59 : R.pops.length ≤ capOf R := c _ (by omega)
  have v60 : R.n + 1 ≤ capOf R := c _ (by omega)
  have v64 : R.n ≤ capOf R := c _ (by omega)
  have v67 : R.r ≤ capOf R := c _ (by omega)
  have v70 : R.r / 2 ≤ capOf R := c _ (by omega)
  have v71 : R.n - R.r * (starParamsOf R h).b ≤ capOf R := c _ (by omega)
  have v72 : R.s * (R.r / 2) ≤ capOf R := c _ (by omega)
  have v73 : R.r * R.s ≤ capOf R := c _ (by omega)
  have v84 : 2 ^ (R.r * R.s) ≤ capOf R := cap_pow R _ (by omega)
  have v86 : Wof R ≤ capOf R := c _ hWB
  have v87 : Bof R ≤ capOf R := c _ le_rfl
  have v88 : R.gates.length ≤ capOf R := c _ (by omega)
  have v95 : 2 * Wof R + 1 ≤ capOf R := c _ hB2
  have v85 : Lof R ≤ capOf R := c _ (by omega)
  have v0' : 0 ≤ capOf R := Nat.zero_le _
  unfold pvP
  exact ite_le' v0 (ite_le' v1 (ite_le' v2 (ite_le' v3 (ite_le' v4 (ite_le' v5 (ite_le' v58 (ite_le' v59
    (ite_le' v60 (ite_le' v64 (ite_le' v67 (ite_le' v2 (ite_le' v1 (ite_le' v70 (ite_le' v71 (ite_le' v72
    (ite_le' v73 (ite_le' v84 (ite_le' v85 (ite_le' v86 (ite_le' v87 (ite_le' v88 (ite_le' v95
    v0'))))))))))))))))))))))

/-- **The loop's width and capacity facts** hold at `capOf`. -/
theorem globalOK_of (R : SelectionReq) (h : ParamsOk R) : GlobalOK R h (capOf R) := by
  obtain ⟨hWB, hBT, _, hE, hB2⟩ := cap_facts R
  obtain ⟨k1, s1, b1, r1, rb1, sr1, g1, p1, gn1, L3, LW⟩ := small_facts R h
  have c : ∀ t, t ≤ Bof R → t ≤ capOf R := cap_lin R
  have hK := keys_W R h
  have hgn : gateNeed (starParamsOf R h) (Wof R) (Lof R) ≤ capOf R := by unfold capOf; rw [dif_pos h]; omega
  have hcout : 2 * 2 ^ (R.s + 1) + 2 * R.r + 6 ≤ capOf R := by
    have e : 2 * 2 ^ (R.s + 1) = 2 ^ (R.s + 2) := by rw [pow_succ 2 (R.s + 1)]; ring
    have a1 := hE (R.s + 2) (by omega)
    have a2 : 2 * R.r + 6 ≤ 2 ^ (Bof R + Wof R) := by omega
    have := cap_two R _ _ a1 a2
    omega
  refine ⟨lt_of_le_of_lt g1 (lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))),
    fun g hg => keyBound_L R g hg, by omega, by show R.n + R.r * R.s + 4 ≤ Wof R; omega, hgn, c _ hB2,
    by unfold capOf; omega, c _ (by omega), c _ (by omega), c _ (popTable_le R), cap_pow R _ (by omega),
    by omega, fun N _ => fits_W R h N (capOf R) (fun X hX => c _ (by have := (pop_bits R X hX).2.2.2; omega)),
    hK.1, hK.2, hcout, c _ (by omega), fun N => outWord_le R h N, c _ le_rfl, pvP_le_cap R h⟩

/-- The parse's cost, for every request. -/
def parseCostF (R : SelectionReq) : ℕ := if h : ParamsOk R then parseCost R h else 0

/-- **C1's register-machine run**: `Pw` from the framed request word to the selected coset's word. -/
theorem c1WM_Pw : Top.C1WM Pw 1 capOf (costF parseCostF) :=
  c1WM_of_parse capOf parseCostF
    (fun R h hnn => ⟨stC R h, by rw [parseCostF, dif_pos h]; exact parse_run (capOf R) R h (parseOK_of R h hnn),
      pPost_stC R h (by have := cap_facts R; unfold Bof Wof at *; nlinarith)⟩)
    (fun R h _ => globalOK_of R h)

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
