import Proof.Wire_3_5.Compiler.MachineTopClass
import Proof.Wire_3_5.Primitive.SeedFix.C4Child

/-! # The child's cost at a call, generic, part 1: the compiler's cost at a bounding quantity

P3:1887-1888, 1905-1906 ("Construction takes `(input description size + 𝒮)·poly(n)` deterministic bit operations",
`𝒮 ≤ A·2^m·Q'(P_ex+1)^{Q'd}`). C3's `c3Cost_le_X` bounds the compiler's cost by `52802·bigX^8` with
`bigX = 𝒮'·|input|·(n+1)^{a_par}` under `LoadP`; at a child request (`psi = 0`) the load hypothesis (c′) is not
available, so here the polynomial factor is any `B` above the displayed parameters `p, width, P_ex, h, Q', d`:
**`c3Cost_le_B`**: `c3Cost ≤ 52802·(𝒮'·|input|·B)^8` from `R.Pre` alone. The input's length is the child's fixed
fields (`pre`, `post`, C4Child's split) and the expression's word: **`c3Input_len`** (`vfield_eq`: the input's
expression field is `exprWord V`). Mode-generic.

* **`c3Cost_le_B`**, `vfield_eq`, **`c3Input_len`**.

Paper quantity of the main type: the compiler's construction cost at a child request. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.EnumCap
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary

variable (a : DecompositionAlgorithm)

/-- **The compiler's cost at any bound `B` of the displayed parameters**: `c3Cost ≤ 52802·(𝒮'·|input|·B)^8`. -/
theorem c3Cost_le_B (R : C3Req) (hR : R.Pre a) (Bn : ℕ) (hB1 : 1 ≤ Bn) (hp : R.p ≤ Bn) (hw : R.P.width ≤ Bn)
    (hPC : (poolChildren a R.P.gates R.P.flips).length ≤ Bn) (hh : R.P.h ≤ Bn) (hQ : R.P.Q ≤ Bn) (hd : R.d ≤ Bn) :
    c3Cost a R ≤ 52802 * (R.occBoundP a * (c3Input a R).length * Bn) ^ 8 := by
  have hQ1 : 1 ≤ R.P.Q := hR.2.2.1
  have hLx : R.P.h * R.P.Q * R.d ≤ R.p := hR.2.2.2.2.2.2.2.1
  obtain ⟨X, hXd⟩ : ∃ X, X = R.occBoundP a * (c3Input a R).length * Bn := ⟨_, rfl⟩
  rw [← hXd]
  have hO1 : 1 ≤ R.occBoundP a := one_le_occP a R hQ1
  have hI1 : 1 ≤ (c3Input a R).length := input_pos a R
  have hOI : 1 ≤ R.occBoundP a * (c3Input a R).length := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ofN : ∀ v, v ≤ Bn → v ≤ X := fun v hv => by
    rw [hXd]; calc v ≤ Bn := hv
      _ = 1 * Bn := (one_mul _).symm
      _ ≤ R.occBoundP a * (c3Input a R).length * Bn := Nat.mul_le_mul_right _ hOI
  have ofI : ∀ v, v ≤ (c3Input a R).length → v ≤ X := fun v hv => by
    rw [hXd]; calc v ≤ (c3Input a R).length := hv
      _ = 1 * (c3Input a R).length * 1 := by ring
      _ ≤ R.occBoundP a * (c3Input a R).length * Bn := by gcongr
  have ofO : ∀ v, v ≤ R.occBoundP a → v ≤ X := fun v hv => by
    rw [hXd]; calc v ≤ R.occBoundP a := hv
      _ = R.occBoundP a * 1 * 1 := by ring
      _ ≤ R.occBoundP a * (c3Input a R).length * Bn := by gcongr
  have hWe : (shapeOf (R.D a)).flatten.length = (poolChildren a R.P.gates R.P.flips).length :=
    Emit.shapeOf_flatten_length a R.P.gates R.P.side R.P.width R.P.flips
  have hX1 : 1 ≤ X := ofN 1 hB1
  have hn := cuts_le a R hR
  have hrs : (sfRecs a R).length ≤ 8 * X * X := by
    rw [sfRecs_length, c3v2Ref, EquationRow.doubled_length]
    have e1 := ofO _ hn
    have e2 := ofN _ hw
    have hw' : R.P.width + R.P.width + 2 ≤ 4 * X := by omega
    calc 2 * (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length * (R.P.width + R.P.width + 2)
        ≤ 2 * X * (4 * X) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 e1) hw'
      _ = 8 * X * X := by ring
  have hB : sB a R ≤ X := by
    refine (sB_le a R hR).trans ?_
    rw [hXd]
    have : ((shapeOf (R.D a)).flatten.length + 1) ^ R.d ≤ R.occBoundP a := (ng_le a R hQ1)
    calc (c3Input a R).length * ((shapeOf (R.D a)).flatten.length + 1) ^ R.d
        ≤ (c3Input a R).length * R.occBoundP a := Nat.mul_le_mul_left _ this
      _ = R.occBoundP a * (c3Input a R).length * 1 := by ring
      _ ≤ R.occBoundP a * (c3Input a R).length * Bn := Nat.mul_le_mul_left _ hB1
  exact (c3Cost_le_gB a R X hX1 (ofI _ le_rfl) (ofN _ hQ) (ofN _ (hWe ▸ hPC)) (ofI _ (m_le a R))
    (ofN _ hp) (ofN _ hw) (ofN _ hh) (ofN _ hd) (ofI _ (V_le a R)) (ofI _ (sCBW_le a R)) (ofI _ (sNF_le a R))
    (ofI _ (sCB_le a R)) (ofI _ (atoms_le a R)) hB (ofO _ (ng_le a R hQ1)) (ofO _ (nu_le a R))
    (ofO _ (ng_le a R hQ1)) (ofO _ (pow2m_le a R hQ1).2) (ofO _ (pow2m_le a R hQ1).1)
    (ofO _ (by rw [← hWe]; exact nu_le a R)) (ofN _ hPC) (ofN _ (hLx.trans hp)) (ofO _ hn)
    (ofI _ (h1_le a R)) (ofI _ (h2_le a R)) hrs).trans (gB_le _ hX1)

/-- The input's expression field is the expression's word. -/
theorem vfield_eq (V : IntExpression ℕ) : V.flatMap termRec ++ [false] = ListMachine.Rec.exprWord V := rfl

/-- **The input's length**: the child's fixed fields, the expression's frame, the header fields. -/
theorem c3Input_len (R : C3Req) : (c3Input a R).length =
    (PrimT.C4Child.pre a R).length + (2 * (ListMachine.Rec.exprWord R.V).length + 1) + (PrimT.C4Child.post a R).length := by
  rw [c3Input_eq]
  have e : c3Fields a R = (c3Fields a R).take 8 ++ [R.V.flatMap termRec ++ [false]] ++ (c3Fields a R).drop 9 := rfl
  rw [e, List.flatMap_append, List.flatMap_append, List.length_append, List.length_append]
  unfold PrimT.C4Child.pre PrimT.C4Child.post
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_length, vfield_eq]

end NearCubicWires.WireExponent3_5.FinalPass.EnumCap
