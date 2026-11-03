import Lean
import Proof.Wire_3_5.Primitive.Writers.Compose
import Proof.Wire_3_5.Primitive.Writers.CallSize
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.ComposeEnvBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA.compose.env: the composed program fits the per-call budget

The residual `EnvPack` of the compose plan (check 62b01809…): a coefficient rule `cg` with, at every call,
`glueK·(|req.word| + c₄·seedClasses E₄ + c₅·finalClasses E₅ + 1) ≤ callBudget` whenever `cg c₄ c₅ ≤ coef`.

`prim:runtime` (P3:3105-3115): the per-call budget is `coef` times the sum of the four classes of `F.E` (the gate's
`costsOf`); the classes are monotone in the class exponents (`ClassLE`) at every `q ≥ 1`; the request word is polynomial
in `n` (`CallSize.gate_word_length_le`, `wordBound_poly`), hence at most `C_w·2^{⌊n/2⌋}`, below the selection class.

Paper quantities of the main type: `callBudget`, `seedClasses`, `finalClasses` (`envPack`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ComposeEnv
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.Compose
open NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule

/-! ## The request word below `C_w·2^{⌊n/2⌋}` -/

/-! ## The classes are monotone in the exponents -/

/-! ## The budget -/

theorem callBudget_eq (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) :
    ((gate0 l F).budget kclk coef A a ha).callBudget n =
      coef * classSum F.E n (((gate0 l F).budget kclk coef A a ha).kOf n)
        (((gate0 l F).budget kclk coef A a ha).psiOf n) := by
  show coef * _ + coef * _ + coef * _ + coef * _ = _
  unfold classSum; rw [Nat.mul_add, Nat.mul_add, Nat.mul_add]; rfl

theorem envFor : EnvFor cgRule := by
  intro l F E₄ E₅ c₄ c₅ h4 h5 kclk coef A a ha hc r
  set n := r.1.n with hnd
  set k := ((gate0 l F).budget kclk coef A a ha).kOf n with hkd
  set psi := ((gate0 l F).budget kclk coef A a ha).psiOf n with hpd
  have hq : 1 ≤ n := by
    have h1 : 2 ≤ ((gate0 l F).budget kclk coef A a ha).rOf n := r.2.2.2.2.2.2.1.2.1
    have h2 : 4 * ((gate0 l F).budget kclk coef A a ha).rOf n ≤ n := r.2.2.2.2.2.2.1.2.2.1
    omega
  have hw : r.1.word.length ≤ wordConst * classSum F.E n k psi := by
    have h1 := CallSize.gate_word_length_le l F kclk coef A a ha r.1 r.2
    have h2 := wordConst_spec n
    have h3 := half_le_classSum F.E n k psi hq
    calc r.1.word.length ≤ CallSize.wordBound 26 26 2 n := h1
      _ ≤ wordConst * 2 ^ (n / 2) := h2
      _ ≤ wordConst * classSum F.E n k psi := Nat.mul_le_mul_left _ h3
  have hs4 := seedClasses_le h4 n k psi hq
  have hs5 := finalClasses_le h5 n k psi hq
  have hS : 1 ≤ classSum F.E n k psi := le_trans Nat.one_le_two_pow (half_le_classSum F.E n k psi hq)
  rw [callBudget_eq]
  have hb4 : c₄ * seedClasses E₄ n k psi ≤ 2 * c₄ * classSum F.E n k psi := by
    have := Nat.mul_le_mul_left c₄ hs4; nlinarith
  have hb5 : c₅ * finalClasses E₅ n k psi ≤ c₅ * classSum F.E n k psi := Nat.mul_le_mul_left c₅ hs5
  have hcoef : cgRule c₄ c₅ * classSum F.E n k psi ≤ coef * classSum F.E n k psi := Nat.mul_le_mul_right _ hc
  unfold cgRule at hcoef
  nlinarith

/-- **The residual `EnvPack`** of the compose plan. -/
noncomputable def envPack : EnvPack := ⟨cgRule, envFor⟩

end NearCubicWires.WireExponent3_5.PrimAsm.ComposeEnv

end
