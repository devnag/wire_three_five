import Proof.SourceAssembly.SourceFactorSelMetaChain

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.MetaPipe
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## 1. The closure `PQ` -/

/-- `f` is bounded by a fixed polynomial of `q` whenever `K2 ≤ 2q`. -/
def PQ (f : ℕ → ℕ → ℕ) : Prop := ∃ C E : ℕ, ∀ q K2, K2 ≤ 2 * q → f q K2 ≤ C * (q + 1) ^ E

theorem pow_mono_e (q a b : ℕ) (h : a ≤ b) : (q + 1) ^ a ≤ (q + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos q) h

theorem PQ.const (n : ℕ) : PQ (fun _ _ => n) :=
  ⟨n, 0, fun _ _ _ => by rw [pow_zero, Nat.mul_one]⟩

theorem PQ.q : PQ (fun q _ => q) :=
  ⟨1, 1, fun q _ _ => by rw [pow_one, Nat.one_mul]; exact Nat.le_succ q⟩

theorem PQ.k2 : PQ (fun _ K2 => K2) :=
  ⟨2, 1, fun q K2 h => by
    show K2 ≤ 2 * (q + 1) ^ 1
    rw [pow_one]
    omega⟩

theorem PQ.mono {f g : ℕ → ℕ → ℕ} (h : ∀ q K2, K2 ≤ 2 * q → f q K2 ≤ g q K2) (hg : PQ g) : PQ f := by
  obtain ⟨C, E, hC⟩ := hg
  exact ⟨C, E, fun q K2 hk => (h q K2 hk).trans (hC q K2 hk)⟩

theorem PQ.add {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ (fun q K2 => f q K2 + g q K2) := by
  obtain ⟨C1, E1, h1⟩ := hf
  obtain ⟨C2, E2, h2⟩ := hg
  refine ⟨C1 + C2, E1 + E2, fun q K2 hk => ?_⟩
  show f q K2 + g q K2 ≤ (C1 + C2) * (q + 1) ^ (E1 + E2)
  rw [Nat.add_mul]
  exact Nat.add_le_add
    ((h1 q K2 hk).trans (Nat.mul_le_mul_left C1 (pow_mono_e q E1 (E1 + E2) (Nat.le_add_right _ _))))
    ((h2 q K2 hk).trans (Nat.mul_le_mul_left C2 (pow_mono_e q E2 (E1 + E2) (Nat.le_add_left _ _))))

theorem PQ.mul {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ (fun q K2 => f q K2 * g q K2) := by
  obtain ⟨C1, E1, h1⟩ := hf
  obtain ⟨C2, E2, h2⟩ := hg
  refine ⟨C1 * C2, E1 + E2, fun q K2 hk => ?_⟩
  have e : C1 * C2 * (q + 1) ^ (E1 + E2) = (C1 * (q + 1) ^ E1) * (C2 * (q + 1) ^ E2) := by
    rw [pow_add]; ring
  rw [e]
  exact Nat.mul_le_mul (h1 q K2 hk) (h2 q K2 hk)

theorem PQ.pow {f : ℕ → ℕ → ℕ} (hf : PQ f) (n : ℕ) : PQ (fun q K2 => f q K2 ^ n) := by
  induction n with
  | zero => exact PQ.mono (fun _ _ _ => by rw [pow_zero]) (PQ.const 1)
  | succ n ih => exact PQ.mono (fun _ _ _ => by rw [pow_succ]) (PQ.mul ih hf)

/-- A linear expression of a `PQ` quantity. -/
theorem PQ.lin {f : ℕ → ℕ → ℕ} (hf : PQ f) (a b : ℕ) : PQ (fun q K2 => a * f q K2 + b) :=
  PQ.add (PQ.mul (PQ.const a) hf) (PQ.const b)

/-! ## 2. One lemma per operation (value and cost) -/

theorem v_div {f g : ℕ → ℕ → ℕ} (hf : PQ f) : PQ (fun q K2 => f q K2 / g q K2) :=
  PQ.mono (fun _ _ _ => Nat.div_le_self _ _) hf

theorem v_half {f : ℕ → ℕ → ℕ} (hf : PQ f) : PQ (fun q K2 => f q K2 / 2) :=
  PQ.mono (fun _ _ _ => Nat.div_le_self _ _) hf

theorem v_sub {f g : ℕ → ℕ → ℕ} (hf : PQ f) : PQ (fun q K2 => f q K2 - g q K2) :=
  PQ.mono (fun _ _ _ => Nat.sub_le _ _) hf

theorem v_max {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ (fun q K2 => max (f q K2) (g q K2)) :=
  PQ.mono (fun _ _ _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)) (PQ.add hf hg)

theorem v_plus {f : ℕ → ℕ → ℕ} (hf : PQ f) (n : ℕ) : PQ (fun q K2 => f q K2 + n) :=
  PQ.add hf (PQ.const n)

theorem clog_le_self (x : ℕ) : Nat.clog 2 x ≤ x :=
  (Nat.clog_mono_right 2 (Nat.lt_two_pow_self).le).trans (le_of_eq (Nat.clog_pow 2 x (by decide)))

theorem v_clog1 {f : ℕ → ℕ → ℕ} (hf : PQ f) : PQ (fun q K2 => Nat.clog 2 (f q K2 + 1)) :=
  PQ.mono (fun _ _ _ => clog_le_self _) (v_plus hf 1)

theorem v_poly {f : ℕ → ℕ → ℕ} (hf : PQ f) (D C : ℕ) :
    PQ (fun q K2 => NearCubicWires.BlockPlatform.UnaryCalc.value D C (f q K2)) :=
  PQ.mul (PQ.const C) (PQ.pow (v_plus hf 1) D)

theorem c_half {f : ℕ → ℕ → ℕ} (hf : PQ f) : PQ (fun q K2 => halfOp.cost (f q K2)) :=
  PQ.mono (fun q K2 _ => by show 2 * (f q K2 + 1) + 2 ≤ 2 * f q K2 + 4; omega) (PQ.lin hf 2 4)

theorem c_plus {f : ℕ → ℕ → ℕ} (hf : PQ f) (n : ℕ) : PQ (fun q K2 => (plusOp n).cost (f q K2)) :=
  PQ.mono (fun q K2 _ => by show 2 * (f q K2 + 1 + n) + 2 ≤ 2 * f q K2 + (2 * n + 4); omega) (PQ.lin hf 2 (2 * n + 4))

theorem c_clog1 {f : ℕ → ℕ → ℕ} (hf : PQ f) : PQ (fun q K2 => clog1Op.cost (f q K2)) :=
  PQ.mono (fun q K2 _ => by
    show 2 * (f q K2 + 1 + 1) + 2 + 1 + (2 * (30 * (f q K2 + 1 + 1)) + 2) ≤ 62 * f q K2 + 129
    omega) (PQ.lin hf 62 129)

theorem c_poly {f : ℕ → ℕ → ℕ} (hf : PQ f) (D C : ℕ) :
    PQ (fun q K2 => (polyOp D C).cost (f q K2)) :=
  PQ.mono (fun q K2 _ => NearCubicWires.BlockPlatform.UnaryCalc.poly_cost_polyBounded D C (f q K2))
    (PQ.mul (PQ.const _) (PQ.pow (v_plus hf 1) (D + 1)))

theorem c_sum {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ (fun q K2 => sumOp.cost (f q K2) (g q K2)) :=
  PQ.mono (fun q K2 _ => by show 2 * (f q K2 + g q K2) + 6 ≤ 2 * (f q K2 + g q K2) + 6; exact le_refl _)
    (PQ.lin (PQ.add hf hg) 2 6)

theorem c_cold {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) :
    PQ (fun q K2 => PCPPNativeColdArithmetic.budget (f q K2) (g q K2)) :=
  PQ.mono (fun q K2 _ => by
    show 2 * max (f q K2) (g q K2) + 4 ≤ 2 * (f q K2 + g q K2) + 4
    have := max_le (Nat.le_add_right (f q K2) (g q K2)) (Nat.le_add_left (g q K2) (f q K2))
    omega) (PQ.lin (PQ.add hf hg) 2 4)

theorem c_sub {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ (fun q K2 => subOp.cost (f q K2) (g q K2)) :=
  c_cold hf hg

theorem c_max {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ (fun q K2 => maxOp.cost (f q K2) (g q K2)) :=
  c_cold hf hg

theorem c_div {f g : ℕ → ℕ → ℕ} (hf : PQ f) (hg : PQ g) : PQ (fun q K2 => divOp.cost (f q K2) (g q K2)) :=
  PQ.mono (fun q K2 _ => by
    show 2 * g q K2 + 8 + 1 + (8 * f q K2 + 6) ≤ 8 * (f q K2 + g q K2) + 15
    omega) (PQ.lin (PQ.add hf hg) 8 15)

/-! ## 3. The registers and the stages (generated) -/

section regs
variable (c : MC)

theorem pr0 : PQ (fun q K2 => r0 c q K2) := PQ.q
theorem pr1 : PQ (fun q K2 => r1 c q K2) := PQ.k2
theorem pr2 : PQ (fun q K2 => r2 c q K2) := v_half (pr1 c)
theorem pr3 : PQ (fun q K2 => r3 c q K2) := v_half (pr0 c)
theorem pr4 : PQ (fun q K2 => r4 c q K2) := v_half (pr3 c)
theorem pr5 : PQ (fun q K2 => r5 c q K2) := v_sub (pr0 c)
theorem pr6 : PQ (fun q K2 => r6 c q K2) := v_poly (pr0 c) 0 200
theorem pr7 : PQ (fun q K2 => r7 c q K2) := v_div (pr5 c)
theorem pr8 : PQ (fun q K2 => r8 c q K2) := v_sub (pr7 c)
theorem pr9 : PQ (fun q K2 => r9 c q K2) := v_plus (pr2 c) 2
theorem pr11 : PQ (fun q K2 => r11 c q K2) := v_div (pr0 c)
theorem pr13 : PQ (fun q K2 => r13 c q K2) := v_poly (pr0 c) c.mE c.mC
theorem pr14 : PQ (fun q K2 => r14 c q K2) := v_clog1 (pr13 c)
theorem pr16 : PQ (fun q K2 => r16 c q K2) := v_poly (pr0 c) c.hE c.hC
theorem pr17 : PQ (fun q K2 => r17 c q K2) := v_clog1 (pr16 c)
theorem pr19 : PQ (fun q K2 => r19 c q K2) := v_poly (pr0 c) c.tE c.tC
theorem pr20 : PQ (fun q K2 => r20 c q K2) := v_clog1 (pr19 c)
theorem pr21 : PQ (fun q K2 => r21 c q K2) := PQ.add (pr20 c) (pr5 c)
theorem pr22 : PQ (fun q K2 => r22 c q K2) := v_poly (pr0 c) c.sE c.sC
theorem pr23 : PQ (fun q K2 => r23 c q K2) := v_clog1 (pr22 c)
theorem pr24 : PQ (fun q K2 => r24 c q K2) := PQ.add (pr23 c) (pr4 c)
theorem pr25 : PQ (fun q K2 => r25 c q K2) := v_max (pr21 c) (pr24 c)
theorem pr27 : PQ (fun q K2 => r27 c q K2) := v_poly (pr0 c) c.vE c.vC
theorem pr28 : PQ (fun q K2 => r28 c q K2) := v_clog1 (pr27 c)
theorem pr30 : PQ (fun q K2 => r30 c q K2) := v_poly (pr0 c) c.rE c.rC
theorem pr31 : PQ (fun q K2 => r31 c q K2) := v_clog1 (pr30 c)
theorem pc0 : PQ (fun q K2 => halfOp.cost (r1 c q K2)) := c_half (pr1 c)
theorem pc1 : PQ (fun q K2 => halfOp.cost (r0 c q K2)) := c_half (pr0 c)
theorem pc2 : PQ (fun q K2 => halfOp.cost (r3 c q K2)) := c_half (pr3 c)
theorem pc3 : PQ (fun q K2 => subOp.cost (r0 c q K2) (r2 c q K2)) := c_sub (pr0 c) (pr2 c)
theorem pc4 : PQ (fun q K2 => (polyOp 0 200).cost (r0 c q K2)) := c_poly (pr0 c) 0 200
theorem pc5 : PQ (fun q K2 => divOp.cost (r5 c q K2) (r6 c q K2)) := c_div (pr5 c) (pr6 c)
theorem pc6 : PQ (fun q K2 => subOp.cost (r7 c q K2) (r2 c q K2)) := c_sub (pr7 c) (pr2 c)
theorem pc7 : PQ (fun q K2 => (plusOp 2).cost (r2 c q K2)) := c_plus (pr2 c) 2
theorem pc8 : PQ (fun q K2 => divOp.cost (r8 c q K2) (r9 c q K2)) := c_div (pr8 c) (pr9 c)
theorem pc9 : PQ (fun q K2 => divOp.cost (r0 c q K2) (r6 c q K2)) := c_div (pr0 c) (pr6 c)
theorem pc10 : PQ (fun q K2 => divOp.cost (r11 c q K2) (r9 c q K2)) := c_div (pr11 c) (pr9 c)
theorem pc11 : PQ (fun q K2 => (polyOp c.mE c.mC).cost (r0 c q K2)) := c_poly (pr0 c) c.mE c.mC
theorem pc12 : PQ (fun q K2 => clog1Op.cost (r13 c q K2)) := c_clog1 (pr13 c)
theorem pc13 : PQ (fun q K2 => sumOp.cost (r14 c q K2) (r4 c q K2)) := c_sum (pr14 c) (pr4 c)
theorem pc14 : PQ (fun q K2 => (polyOp c.hE c.hC).cost (r0 c q K2)) := c_poly (pr0 c) c.hE c.hC
theorem pc15 : PQ (fun q K2 => clog1Op.cost (r16 c q K2)) := c_clog1 (pr16 c)
theorem pc16 : PQ (fun q K2 => sumOp.cost (r17 c q K2) (r4 c q K2)) := c_sum (pr17 c) (pr4 c)
theorem pc17 : PQ (fun q K2 => (polyOp c.tE c.tC).cost (r0 c q K2)) := c_poly (pr0 c) c.tE c.tC
theorem pc18 : PQ (fun q K2 => clog1Op.cost (r19 c q K2)) := c_clog1 (pr19 c)
theorem pc19 : PQ (fun q K2 => sumOp.cost (r20 c q K2) (r5 c q K2)) := c_sum (pr20 c) (pr5 c)
theorem pc20 : PQ (fun q K2 => (polyOp c.sE c.sC).cost (r0 c q K2)) := c_poly (pr0 c) c.sE c.sC
theorem pc21 : PQ (fun q K2 => clog1Op.cost (r22 c q K2)) := c_clog1 (pr22 c)
theorem pc22 : PQ (fun q K2 => sumOp.cost (r23 c q K2) (r4 c q K2)) := c_sum (pr23 c) (pr4 c)
theorem pc23 : PQ (fun q K2 => maxOp.cost (r21 c q K2) (r24 c q K2)) := c_max (pr21 c) (pr24 c)
theorem pc24 : PQ (fun q K2 => (plusOp 1).cost (r25 c q K2)) := c_plus (pr25 c) 1
theorem pc25 : PQ (fun q K2 => (polyOp c.vE c.vC).cost (r0 c q K2)) := c_poly (pr0 c) c.vE c.vC
theorem pc26 : PQ (fun q K2 => clog1Op.cost (r27 c q K2)) := c_clog1 (pr27 c)
theorem pc27 : PQ (fun q K2 => sumOp.cost (r28 c q K2) (r5 c q K2)) := c_sum (pr28 c) (pr5 c)
theorem pc28 : PQ (fun q K2 => (polyOp c.rE c.rC).cost (r0 c q K2)) := c_poly (pr0 c) c.rE c.rC
theorem pc29 : PQ (fun q K2 => clog1Op.cost (r30 c q K2)) := c_clog1 (pr30 c)
theorem pc30 : PQ (fun q K2 => sumOp.cost (r31 c q K2) (r4 c q K2)) := c_sum (pr31 c) (pr4 c)

/-- **The meta pipeline cost is `PQ`.** -/
theorem metaCost_PQ : PQ (fun q K2 => metaCost c q K2) :=
  PQ.add (PQ.add (pc0 c) (PQ.const 1)) (PQ.add (PQ.add (pc1 c) (PQ.const 1)) (PQ.add (PQ.add (pc2 c) (PQ.const 1)) (PQ.add (PQ.add (pc3 c) (PQ.const 1)) (PQ.add (PQ.add (pc4 c) (PQ.const 1)) (PQ.add (PQ.add (pc5 c) (PQ.const 1)) (PQ.add (PQ.add (pc6 c) (PQ.const 1)) (PQ.add (PQ.add (pc7 c) (PQ.const 1)) (PQ.add (PQ.add (pc8 c) (PQ.const 1)) (PQ.add (PQ.add (pc9 c) (PQ.const 1)) (PQ.add (PQ.add (pc10 c) (PQ.const 1)) (PQ.add (PQ.add (pc11 c) (PQ.const 1)) (PQ.add (PQ.add (pc12 c) (PQ.const 1)) (PQ.add (PQ.add (pc13 c) (PQ.const 1)) (PQ.add (PQ.add (pc14 c) (PQ.const 1)) (PQ.add (PQ.add (pc15 c) (PQ.const 1)) (PQ.add (PQ.add (pc16 c) (PQ.const 1)) (PQ.add (PQ.add (pc17 c) (PQ.const 1)) (PQ.add (PQ.add (pc18 c) (PQ.const 1)) (PQ.add (PQ.add (pc19 c) (PQ.const 1)) (PQ.add (PQ.add (pc20 c) (PQ.const 1)) (PQ.add (PQ.add (pc21 c) (PQ.const 1)) (PQ.add (PQ.add (pc22 c) (PQ.const 1)) (PQ.add (PQ.add (pc23 c) (PQ.const 1)) (PQ.add (PQ.add (pc24 c) (PQ.const 1)) (PQ.add (PQ.add (pc25 c) (PQ.const 1)) (PQ.add (PQ.add (pc26 c) (PQ.const 1)) (PQ.add (PQ.add (pc27 c) (PQ.const 1)) (PQ.add (PQ.add (pc28 c) (PQ.const 1)) (PQ.add (PQ.add (pc29 c) (PQ.const 1)) (pc30 c))))))))))))))))))))))))))))))

end regs

/-- **CENSUS (POOL-10): the meta pipeline's cost is polynomial in `q`.** -/
theorem metaCost_poly (c : MC) : ∃ C E : ℕ, ∀ q K2, K2 ≤ 2 * q → metaCost c q K2 ≤ C * (q + 1) ^ E :=
  metaCost_PQ c

end
end NearCubicWires.SourceFactorSel.MetaPipe

