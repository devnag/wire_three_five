import Proof.Wire_3_5.Primitive.Writers.UnaryArith
import Proof.Wire_3_5.Primitive.Writers.StarNums

/-! # C6 front: straight-line unary arithmetic in the register language

The union machine's numbers (the grid size `s`, the grid mass `Λ̄`, the clause count `2^{cb}`, the six magnitudes
`|κ|·∏ m_k`, the thresholds of `tr:thresholds`) are small unary numbers computed by straight-line programs of PA's
register arithmetic (`mulAddW`, `divW`, `pow2W`, `subW`, `wcopyR`, `WM.clear`, `incN`). This module packages them as a
list of operations (**`ROp`**, each carrying its register map) with one semantics (**`evalL`**, a function on the
register vector) and one run lemma (**`opsT`**): under each operation's precondition (**`preL`**), the compiled list
runs from `σ` to `σ` with its registers replaced by `evalL`. Paper quantity: none (machine arithmetic for
P3:3395-3403, 3485-3491). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontOps
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.StarNums

variable {ns nr : ℕ} (cap : ℕ)

/-- One straight-line register operation, with its register map. -/
inductive ROp (nr : ℕ) where
  /-- `R₂ += R₀·R₁` (scratch `R₃ R₄`). -/
  | mulAdd (R : Fin 5 ↪ Fin nr)
  /-- `b := a` from `b = 0` (scratch `t`). -/
  | copy (a b t : Fin nr)
  /-- `a := 0`. -/
  | clear (a : Fin nr)
  /-- `a += k`. -/
  | addC (a : Fin nr) (k : ℕ)
  /-- `R₂ += R₀ / R₁`, `R₀ := R₀ mod R₁` (scratch `R₃ … R₇`). -/
  | div (R : Fin 9 ↪ Fin nr)
  /-- `R₁ := 2^{R₀}` from `R₁ = 0` (scratch `R₂ R₃`). -/
  | pow2 (R : Fin 4 ↪ Fin nr)
  /-- `R₀ := R₀ − R₁` (scratch `R₂ R₃`). -/
  | sub (R : Fin 4 ↪ Fin nr)

/-- An operation's program. -/
def compile : ROp nr → WM ns nr
  | .mulAdd R => mulAddW R
  | .copy a b t => FinalPass.Hash4.wcopyR a b t
  | .clear a => WM.clear a
  | .addC a k => incN a k
  | .div R => divW R
  | .pow2 R => pow2W R
  | .sub R => subW R

/-- An operation's semantics on the register vector. -/
def eval : ROp nr → (Fin nr → ℕ) → Fin nr → ℕ
  | .mulAdd R, v => Function.update v (R 2) (v (R 2) + v (R 0) * v (R 1))
  | .copy a b _, v => Function.update v b (v a)
  | .clear a, v => Function.update v a 0
  | .addC a k, v => Function.update v a (v a + k)
  | .div R, v => Function.update (Function.update v (R 0) (v (R 0) % v (R 1))) (R 2) (v (R 2) + v (R 0) / v (R 1))
  | .pow2 R, v => Function.update v (R 1) (2 ^ v (R 0))
  | .sub R, v => Function.update v (R 0) (v (R 0) - v (R 1))

/-- An operation's precondition: its scratch clear, its target clear where needed, within the capacity. -/
def pre : ROp nr → (Fin nr → ℕ) → Prop
  | .mulAdd R, v => v (R 3) = 0 ∧ v (R 4) = 0 ∧ v (R 1) ≤ cap ∧ v (R 2) + v (R 0) * v (R 1) ≤ cap ∧ v (R 0) ≤ cap
  | .copy a b t, v => a ≠ b ∧ a ≠ t ∧ b ≠ t ∧ v b = 0 ∧ v t = 0 ∧ v a ≤ cap
  | .clear a, v => v a ≤ cap
  | .addC a k, v => v a + k ≤ cap
  | .div R, v => 1 ≤ v (R 1) ∧ v (R 3) = 0 ∧ v (R 4) = 0 ∧ v (R 5) = 0 ∧ v (R 6) = 0 ∧ v (R 7) = 0 ∧
      v (R 0) ≤ cap ∧ v (R 1) ≤ cap ∧ v (R 2) + v (R 0) ≤ cap ∧ 1 ≤ cap
  | .pow2 R, v => v (R 1) = 0 ∧ v (R 2) = 0 ∧ v (R 3) = 0 ∧ 2 ^ (v (R 0) + 1) ≤ cap
  | .sub R, v => v (R 2) = 0 ∧ v (R 3) = 0 ∧ v (R 0) ≤ cap ∧ v (R 1) ≤ cap

/-- An operation's cost. -/
def cost : ROp nr → (Fin nr → ℕ) → ℕ
  | .mulAdd R, v => v (R 1) * (18 * v (R 0) + 8) + 18 * v (R 1) + 10
  | .copy a _ _, v => 18 * v a + 3
  | .clear a, v => 3 * v a + 1
  | .addC _ k, _ => 4 * k
  | .div R, v => (v (R 0) + 2) * (90 * v (R 0) + 90 * v (R 1) + 60)
  | .pow2 R, v => v (R 0) * (18 * 2 ^ v (R 0) + 7) + 18 * v (R 0) + 20
  | .sub R, v => 30 * v (R 1) + 10

/-- The state with its registers replaced. -/
def withVal (σ : WState ns nr) (v : Fin nr → ℕ) : WState ns nr := ⟨σ.sh, σ.st, v, σ.cell⟩

theorem withVal_self (σ : WState ns nr) : withVal σ σ.val = σ := rfl

/-- **One operation runs as its semantics.** -/
theorem opT (op : ROp nr) (σ : WState ns nr) (h : pre cap op σ.val) :
    WExec cap (compile op) σ (withVal σ (eval op σ.val)) (cost op σ.val) := by
  cases op with
  | mulAdd R =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    exact mulAddW_spec cap R σ h1 h2 h3 h4 h5
  | copy a b t =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact FinalPass.Hash4.wcopyR_spec cap a b t h1 h2 h3 σ h4 h5 h6
  | clear a => exact wclear_spec cap a (σ.val a) σ rfl h
  | addC a k => exact incN_spec cap a k σ h
  | div R =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    exact divW_spec cap R σ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | pow2 R =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact pow2W_spec cap R σ h1 h2 h3 h4
  | sub R =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact subW_spec cap R σ h1 h2 h3 h4

/-- A list of operations, in order. -/
def compileL : List (ROp nr) → WM ns nr
  | [] => .skip
  | op :: ops => .seq (compile op) (compileL ops)

/-- The operations' semantics in order. -/
def evalL : List (ROp nr) → (Fin nr → ℕ) → Fin nr → ℕ
  | [], v => v
  | op :: ops, v => evalL ops (eval op v)

/-- Every operation's precondition, each at the vector before it. -/
def preL : List (ROp nr) → (Fin nr → ℕ) → Prop
  | [], _ => True
  | op :: ops, v => pre cap op v ∧ preL ops (eval op v)

/-- The operations' costs. -/
def costL : List (ROp nr) → (Fin nr → ℕ) → ℕ
  | [], _ => 0
  | op :: ops, v => cost op v + 1 + costL ops (eval op v)

/-- **A straight-line list runs as its semantics.** -/
theorem opsT : ∀ (ops : List (ROp nr)) (σ : WState ns nr), preL cap ops σ.val →
    WExec cap (compileL ops) σ (withVal σ (evalL ops σ.val)) (costL ops σ.val)
  | [], σ, _ => by rw [show evalL [] σ.val = σ.val from rfl, withVal_self]; exact WExec.skip σ
  | op :: ops, σ, h => by
    have h1 := opT cap op σ h.1
    have h2 := opsT ops (withVal σ (eval op σ.val)) h.2
    exact WExec.seq h1 h2

/-! ## Frame, literal register maps, cost bound -/

/-- The registers an operation writes. -/
def writes : ROp nr → List (Fin nr)
  | .mulAdd R => [R 2]
  | .copy _ b _ => [b]
  | .clear a => [a]
  | .addC a _ => [a]
  | .div R => [R 0, R 2]
  | .pow2 R => [R 1]
  | .sub R => [R 0]

theorem eval_frame (op : ROp nr) (v : Fin nr → ℕ) (r : Fin nr) (h : r ∉ writes op) : eval op v r = v r := by
  cases op with
  | mulAdd R => simp only [writes, List.mem_singleton] at h; simp [eval, Function.update_of_ne h]
  | copy a b t => simp only [writes, List.mem_singleton] at h; simp [eval, Function.update_of_ne h]
  | clear a => simp only [writes, List.mem_singleton] at h; simp [eval, Function.update_of_ne h]
  | addC a k => simp only [writes, List.mem_singleton] at h; simp [eval, Function.update_of_ne h]
  | div R =>
    simp only [writes, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, or_false] at h
    simp [eval, Function.update_of_ne h.1, Function.update_of_ne h.2]
  | pow2 R => simp only [writes, List.mem_singleton] at h; simp [eval, Function.update_of_ne h]
  | sub R => simp only [writes, List.mem_singleton] at h; simp [eval, Function.update_of_ne h]

/-- **Frame**: a register no operation writes keeps its value. -/
theorem evalL_frame : ∀ (ops : List (ROp nr)) (v : Fin nr → ℕ) (r : Fin nr), r ∉ ops.flatMap writes →
    evalL ops v r = v r
  | [], _, _, _ => rfl
  | op :: ops, v, r, h => by
    simp only [List.flatMap_cons, List.mem_append, not_or] at h
    show evalL ops (eval op v) r = v r
    rw [evalL_frame ops _ r h.2, eval_frame op v r h.1]

@[simp] theorem eval_mulAdd5 (a b c d e : Fin nr) (h : Function.Injective ![a, b, c, d, e]) (v : Fin nr → ℕ) :
    eval (.mulAdd ⟨![a, b, c, d, e], h⟩) v = Function.update v c (v c + v a * v b) := rfl
@[simp] theorem pre_mulAdd5 (a b c d e : Fin nr) (h : Function.Injective ![a, b, c, d, e]) (v : Fin nr → ℕ) :
    pre cap (.mulAdd ⟨![a, b, c, d, e], h⟩) v ↔ v d = 0 ∧ v e = 0 ∧ v b ≤ cap ∧ v c + v a * v b ≤ cap ∧ v a ≤ cap :=
  Iff.rfl
@[simp] theorem eval_copy (a b t : Fin nr) (v : Fin nr → ℕ) : eval (.copy a b t) v = Function.update v b (v a) := rfl
@[simp] theorem pre_copy (a b t : Fin nr) (v : Fin nr → ℕ) :
    pre cap (.copy a b t) v ↔ a ≠ b ∧ a ≠ t ∧ b ≠ t ∧ v b = 0 ∧ v t = 0 ∧ v a ≤ cap := Iff.rfl
@[simp] theorem eval_clear (a : Fin nr) (v : Fin nr → ℕ) : eval (.clear a) v = Function.update v a 0 := rfl
@[simp] theorem pre_clear (a : Fin nr) (v : Fin nr → ℕ) : pre cap (.clear a) v ↔ v a ≤ cap := Iff.rfl
@[simp] theorem eval_addC (a : Fin nr) (k : ℕ) (v : Fin nr → ℕ) : eval (.addC a k) v = Function.update v a (v a + k) :=
  rfl
@[simp] theorem pre_addC (a : Fin nr) (k : ℕ) (v : Fin nr → ℕ) : pre cap (.addC a k) v ↔ v a + k ≤ cap := Iff.rfl
@[simp] theorem eval_div9 (a b c d e f g i j : Fin nr) (h : Function.Injective ![a, b, c, d, e, f, g, i, j])
    (v : Fin nr → ℕ) : eval (.div ⟨![a, b, c, d, e, f, g, i, j], h⟩) v =
      Function.update (Function.update v a (v a % v b)) c (v c + v a / v b) := rfl
@[simp] theorem pre_div9 (a b c d e f g i j : Fin nr) (h : Function.Injective ![a, b, c, d, e, f, g, i, j])
    (v : Fin nr → ℕ) : pre cap (.div ⟨![a, b, c, d, e, f, g, i, j], h⟩) v ↔
      1 ≤ v b ∧ v d = 0 ∧ v e = 0 ∧ v f = 0 ∧ v g = 0 ∧ v i = 0 ∧ v a ≤ cap ∧ v b ≤ cap ∧ v c + v a ≤ cap ∧
        1 ≤ cap := Iff.rfl
@[simp] theorem eval_pow2_4 (a b c d : Fin nr) (h : Function.Injective ![a, b, c, d]) (v : Fin nr → ℕ) :
    eval (.pow2 ⟨![a, b, c, d], h⟩) v = Function.update v b (2 ^ v a) := rfl
@[simp] theorem pre_pow2_4 (a b c d : Fin nr) (h : Function.Injective ![a, b, c, d]) (v : Fin nr → ℕ) :
    pre cap (.pow2 ⟨![a, b, c, d], h⟩) v ↔ v b = 0 ∧ v c = 0 ∧ v d = 0 ∧ 2 ^ (v a + 1) ≤ cap := Iff.rfl
@[simp] theorem eval_sub4 (a b c d : Fin nr) (h : Function.Injective ![a, b, c, d]) (v : Fin nr → ℕ) :
    eval (.sub ⟨![a, b, c, d], h⟩) v = Function.update v a (v a - v b) := rfl
@[simp] theorem pre_sub4 (a b c d : Fin nr) (h : Function.Injective ![a, b, c, d]) (v : Fin nr → ℕ) :
    pre cap (.sub ⟨![a, b, c, d], h⟩) v ↔ v c = 0 ∧ v d = 0 ∧ v a ≤ cap ∧ v b ≤ cap := Iff.rfl

/-- One operation costs at most `200 (cap+2)²`. -/
theorem cost_le (op : ROp nr) (v : Fin nr → ℕ) (h : pre cap op v) : cost op v ≤ 200 * (cap + 2) * (cap + 2) := by
  cases op with
  | mulAdd R =>
    obtain ⟨-, -, h3, -, h5⟩ := h
    simp only [cost]
    have := Nat.mul_le_mul h3 (show 18 * v (R 0) + 8 ≤ 18 * cap + 8 by omega)
    nlinarith
  | copy a b t => obtain ⟨-, -, -, -, -, h6⟩ := h; simp only [cost]; nlinarith
  | clear a => simp only [pre] at h; simp only [cost]; nlinarith
  | addC a k => simp only [pre] at h; simp only [cost]; nlinarith
  | div R =>
    obtain ⟨-, -, -, -, -, -, h7, h8, -, -⟩ := h
    simp only [cost]
    have := Nat.mul_le_mul (show v (R 0) + 2 ≤ cap + 2 by omega)
      (show 90 * v (R 0) + 90 * v (R 1) + 60 ≤ 180 * cap + 60 by omega)
    nlinarith
  | pow2 R =>
    obtain ⟨-, -, -, h4⟩ := h
    simp only [cost]
    set m := v (R 0)
    have hm : m < 2 ^ m := Nat.lt_two_pow_self
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have h1 : 2 ^ m ≤ cap := by omega
    have h2 : m ≤ cap := by omega
    have := Nat.mul_le_mul h2 (show 18 * 2 ^ m + 7 ≤ 18 * cap + 7 by omega)
    nlinarith
  | sub R => obtain ⟨-, -, -, h4⟩ := h; simp only [cost]; nlinarith

/-- A list's cost is at most its length times `200 (cap+2)² + 1`. -/
theorem costL_le : ∀ (ops : List (ROp nr)) (v : Fin nr → ℕ), preL cap ops v →
    costL ops v ≤ ops.length * (200 * (cap + 2) * (cap + 2) + 1)
  | [], _, _ => by simp [costL]
  | op :: ops, v, h => by
    have h1 := cost_le cap op v h.1
    have h2 := costL_le ops (eval op v) h.2
    show cost op v + 1 + costL ops (eval op v) ≤ (ops.length + 1) * (200 * (cap + 2) * (cap + 2) + 1)
    rw [Nat.add_mul, Nat.one_mul]; omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontOps
