import Proof.Wire_3_5.Primitive.Writers.C3WDock

/-! # C3 request writer, part 5: the fill count's append program

`appP k` on five tapes (the count, then the four unary inputs): the count's head to its end, then `k` ones per one of
each input. Under the masked reset (`appM`, every head back at `0`), docked by `app_dock`: the count
`1^W` becomes `1^{W + k(h + Q' + m + pr)}`, the inputs kept.

Paper quantity: none (the capacity of the request writer's registers, alg:compiler P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Dock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.GeoFront

theorem rd_rep (v j : ℕ) : readTapeBit (List.replicate v true) j = decide (j < v) := by
  unfold readTapeBit
  by_cases h : j < v
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_replicate]

theorem wr_rep (c : ℕ) : writeTapeBit (List.replicate c true) c true = List.replicate (c + 1) true := by
  have e := FinalPass.Tm.writeTapeBit_end' (List.replicate c true) true
  rw [List.length_replicate] at e
  rw [e, List.replicate_succ']

/-- Move the count's head right. -/
def mvC : Fin 5 → HeadMove := fun i => if i = 0 then .right else .stay

/-- Write `1` on the count. -/
def wrC : Fin 5 → Option Bool := fun i => if i = 0 then some true else none

def toEndP : Prog 5 := .loop 0 (.act (fun _ => none) mvC)

/-- `k` ones on the count, then the input `x` one cell right. -/
def wrsP (x : Fin 5) : ℕ → Prog 5
  | 0 => .act (fun _ => none) (fun i => if i = x then .right else .stay)
  | k + 1 => .seq (.act wrC mvC) (wrsP x k)

def cpyP (x : Fin 5) (k : ℕ) : Prog 5 := .loop x (wrsP x k)

/-- **The append program.** -/
def appP (k : ℕ) : Prog 5 := .seq toEndP (.seq (cpyP 1 k) (.seq (cpyP 2 k) (.seq (cpyP 3 k) (cpyP 4 k))))

theorem act_none_A (b : Bank 5) (m : Fin 5 → HeadMove) : (b.act (fun _ => none) m).A = b.A := by
  funext i; simp [Bank.act]

theorem act_H (b : Bank 5) (w : Fin 5 → Option Bool) (m : Fin 5 → HeadMove) (i : Fin 5) :
    (b.act w m).H i = (m i).apply (b.H i) := rfl

theorem act_wrC_A (b : Bank 5) (i : Fin 5) :
    (b.act wrC mvC).A i = if i = 0 then writeTapeBit (b.A i) (b.H i) true else b.A i := by
  by_cases h : i = 0 <;> simp [Bank.act, wrC, h]

theorem toEnd_exec (W : ℕ) : ∀ (r : ℕ) (b : Bank 5), b.A 0 = List.replicate W true → b.H 0 + r = W →
    ∃ b', Exec toEndP b b' (3 * r + 1) ∧ b'.A = b.A ∧ b'.H 0 = W ∧ ∀ i, i ≠ 0 → b'.H i = b.H i
  | 0, b, hA, hr => by
    have hbit : b.bit 0 = false := by
      simp only [Bank.bit, hA, rd_rep]; simp; omega
    exact ⟨b, Exec.loopF hbit, rfl, by omega, fun _ _ => rfl⟩
  | r + 1, b, hA, hr => by
    have hbit : b.bit 0 = true := by
      simp only [Bank.bit, hA, rd_rep]; simp; omega
    obtain ⟨b', e, hA', hH0, hHo⟩ := toEnd_exec W r (b.act (fun _ => none) mvC) (by rw [act_none_A, hA])
      (by rw [act_H]; simp [mvC, HeadMove.apply]; omega)
    refine ⟨b', Exec.mono (Exec.loopT hbit (Exec.act b _ _) e) (by omega), by rw [hA', act_none_A], hH0,
      fun i hi => by rw [hHo i hi, act_H]; simp [mvC, hi, HeadMove.apply]⟩

theorem wrs_exec (x : Fin 5) (hx : x ≠ 0) : ∀ (k c : ℕ) (b : Bank 5), b.A 0 = List.replicate c true → b.H 0 = c →
    ∃ b', Exec (wrsP x k) b b' (2 * k + 1) ∧ b'.A 0 = List.replicate (c + k) true ∧ b'.H 0 = c + k ∧
      b'.H x = b.H x + 1 ∧ (∀ i, i ≠ 0 → b'.A i = b.A i) ∧ (∀ i, i ≠ 0 → i ≠ x → b'.H i = b.H i)
  | 0, c, b, hA, hH => by
    refine ⟨_, Exec.act b _ _, by rw [act_none_A, hA, Nat.add_zero], ?_, ?_, fun i _ => by rw [act_none_A], fun i h1 h2 => ?_⟩
    · rw [act_H]; simp [Ne.symm hx, HeadMove.apply, hH]
    · rw [act_H]; simp [HeadMove.apply]
    · rw [act_H]; simp [h2, HeadMove.apply]
  | k + 1, c, b, hA, hH => by
    have hA1 : (b.act wrC mvC).A 0 = List.replicate (c + 1) true := by
      rw [act_wrC_A]; simp only [if_true]; rw [hA, hH, wr_rep]
    have hH1 : (b.act wrC mvC).H 0 = c + 1 := by rw [act_H]; simp [mvC, HeadMove.apply, hH]
    obtain ⟨b', e, a1, a2, a3, a4, a5⟩ := wrs_exec x hx k (c + 1) (b.act wrC mvC) hA1 hH1
    refine ⟨b', Exec.mono (Exec.seq (Exec.act b _ _) e) (by omega), by rw [a1]; congr 1; omega, by rw [a2]; omega,
      ?_, fun i hi => by rw [a4 i hi, act_wrC_A]; simp [hi], fun i h1 h2 => by rw [a5 i h1 h2, act_H]; simp [mvC, h1, HeadMove.apply]⟩
    rw [a3, act_H]; simp [mvC, hx, HeadMove.apply]

theorem cpy_exec (x : Fin 5) (hx : x ≠ 0) (k v : ℕ) : ∀ (r c : ℕ) (b : Bank 5), b.A 0 = List.replicate c true →
    b.H 0 = c → b.A x = List.replicate v true → b.H x + r = v →
    ∃ b', Exec (cpyP x k) b b' ((2 * k + 3) * r + 1) ∧ b'.A 0 = List.replicate (c + k * r) true ∧
      b'.H 0 = c + k * r ∧ b'.H x = v ∧ (∀ i, i ≠ 0 → b'.A i = b.A i) ∧ (∀ i, i ≠ 0 → i ≠ x → b'.H i = b.H i)
  | 0, c, b, hA, hH, hX, hr => by
    have hbit : b.bit x = false := by
      simp only [Bank.bit, hX, rd_rep]; simp; omega
    exact ⟨b, Exec.mono (Exec.loopF hbit) (by omega), by rw [hA]; simp, by rw [hH]; simp, by omega,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  | r + 1, c, b, hA, hH, hX, hr => by
    have hbit : b.bit x = true := by
      simp only [Bank.bit, hX, rd_rep]; simp; omega
    obtain ⟨b1, e1, a1, a2, a3, a4, a5⟩ := wrs_exec x hx k c b hA hH
    obtain ⟨b', e2, c1, c2, c3, c4, c5⟩ := cpy_exec x hx k v r (c + k) b1 a1 a2 (by rw [a4 x hx, hX]) (by omega)
    refine ⟨b', Exec.mono (Exec.loopT hbit e1 e2) (by rw [Nat.mul_succ]; omega), ?_, ?_, c3,
      fun i hi => by rw [c4 i hi, a4 i hi], fun i h1 h2 => by rw [c5 i h1 h2, a5 i h1 h2]⟩
    · rw [c1]; congr 1; rw [Nat.mul_succ]; omega
    · rw [c2, Nat.mul_succ]; omega

/-- The append program's steps. -/
def appCostP (k W h Q m p : ℕ) : ℕ := 3 * W + 1 + 1 + ((2 * k + 3) * h + 1 + 1 + ((2 * k + 3) * Q + 1 + 1 +
  ((2 * k + 3) * m + 1 + 1 + ((2 * k + 3) * p + 1))))

theorem app_exec (k W h Q m p : ℕ) (b : Bank 5) (hH : ∀ i, b.H i = 0) (h0 : b.A 0 = List.replicate W true)
    (h1 : b.A 1 = List.replicate h true) (h2 : b.A 2 = List.replicate Q true) (h3 : b.A 3 = List.replicate m true)
    (h4 : b.A 4 = List.replicate p true) :
    ∃ b', Exec (appP k) b b' (appCostP k W h Q m p) ∧
      b'.A 0 = List.replicate (W + k * (h + Q + m + p)) true ∧ (∀ i, i ≠ 0 → b'.A i = b.A i) := by
  obtain ⟨b1, e1, a1, a2, a3⟩ := toEnd_exec W W b h0 (by rw [hH]; omega)
  have n1 : (1 : Fin 5) ≠ 0 := by decide
  have n2 : (2 : Fin 5) ≠ 0 := by decide
  have n3 : (3 : Fin 5) ≠ 0 := by decide
  have n4 : (4 : Fin 5) ≠ 0 := by decide
  obtain ⟨b2, e2, c1, c2, c3, c4, c5⟩ := cpy_exec 1 n1 k h h W b1 (by rw [a1, h0]) a2 (by rw [a1, h1])
    (by rw [a3 _ n1, hH]; omega)
  obtain ⟨b3, e3, d1, d2, d3, d4, d5⟩ := cpy_exec 2 n2 k Q Q (W + k * h) b2 c1 c2 (by rw [c4 _ n2, a1, h2])
    (by rw [c5 _ n2 (by decide), a3 _ n2, hH]; omega)
  obtain ⟨b4, e4, f1, f2, f3, f4, f5⟩ := cpy_exec 3 n3 k m m (W + k * h + k * Q) b3 d1 d2
    (by rw [d4 _ n3, c4 _ n3, a1, h3]) (by rw [d5 _ n3 (by decide), c5 _ n3 (by decide), a3 _ n3, hH]; omega)
  obtain ⟨b5, e5, g1, g2, g3, g4, g5⟩ := cpy_exec 4 n4 k p p (W + k * h + k * Q + k * m) b4 f1 f2
    (by rw [f4 _ n4, d4 _ n4, c4 _ n4, a1, h4])
    (by rw [f5 _ n4 (by decide), d5 _ n4 (by decide), c5 _ n4 (by decide), a3 _ n4, hH]; omega)
  refine ⟨b5, Exec.mono (Exec.seq e1 (Exec.seq e2 (Exec.seq e3 (Exec.seq e4 e5)))) (by unfold appCostP; omega), ?_,
    fun i hi => by rw [g4 i hi, f4 i hi, d4 i hi, c4 i hi, a1]⟩
  rw [g1]; congr 1; ring

/-- The append machine (every head back at `0`). -/
noncomputable def appM (k : ℕ) := MaskedReset.machine (appP k).compile (fun _ => true)

/-- The append machine's steps. -/
def appCost (k W h Q m p : ℕ) : ℕ := 2 * appCostP k W h Q m p + 2

/-- **The append, docked**: from `1^W` on slot `0`, the unary inputs on slots `1 … 4`, a blank slot `5`. -/
theorem app_dock {u : ℕ} (sl : Fin 6 → Fin u) (hsl : Function.Injective sl) (k W h Q m p : ℕ) (H : Fin u → ℕ)
    (hH : ∀ j, H (sl j) = 0) (B : Fin u → List Bool) (h0 : B (sl 0) = List.replicate W true)
    (h1 : B (sl 1) = List.replicate h true) (h2 : B (sl 2) = List.replicate Q true)
    (h3 : B (sl 3) = List.replicate m true) (h4 : B (sl 4) = List.replicate p true) (h5 : B (sl 5) = []) :
    ∃ B' : Fin u → List Bool, Step (RecoveryFocus.machine sl (appM k)) (appCost k W h Q m p) H B H B' ∧
      B' (sl 0) = List.replicate (W + k * (h + Q + m + p)) true ∧
      (∀ j : Fin 6, j ≠ 0 → j ≠ 5 → B' (sl j) = B (sl j)) ∧ (∀ i, (∀ j, sl j ≠ i) → B' i = B i) := by
  set b : Bank 5 := ⟨fun _ => 0, fun i => B (sl (Fin.castAdd 1 i))⟩ with hb
  obtain ⟨b', e, a0, ao⟩ := app_exec k W h Q m p b (fun _ => rfl) h0 h1 h2 h3 h4
  obtain ⟨m1, hm⟩ := maskBlank e.step (fun _ => true) (fun _ _ => rfl) 0
  have hm' := Step.congr (hout' := fun _ => 0) (Step.congr_in (hin' := fun _ => 0) hm (by
      funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp [hb]) rfl) (by
      funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp) rfl
  have d := dockZ hm' sl hsl H B hH (by
    intro j
    refine Fin.addCases (fun a => ?_) (fun u => ?_) j
    · rw [Fin.addCases_left]
    · rw [Fin.addCases_right]
      have hu : u = 0 := Subsingleton.elim _ _
      subst hu
      exact h5)
  refine ⟨_, d, ?_, ?_, fun i hi => install_other _ _ _ _ hi⟩
  · rw [show (0 : Fin 6) = Fin.castAdd 1 (0 : Fin 5) from rfl, install_slot _ hsl, Fin.addCases_left]
    exact a0
  · intro j j0 j5
    rw [install_slot _ hsl]
    have hj : j.val < 5 := by
      have := j.isLt
      by_contra hc
      exact j5 (Fin.ext (by simp; omega))
    have e : j = Fin.castAdd 1 (⟨j.val, hj⟩ : Fin 5) := rfl
    rw [e, Fin.addCases_left, ao _ (fun h => j0 (Fin.ext (by have := congrArg Fin.val h; simpa using this)))]

end NearCubicWires.WireExponent3_5.PrimAsm.C3Dock
