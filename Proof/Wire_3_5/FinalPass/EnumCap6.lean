import Proof.Wire_3_5.FinalPass.EnumCap5
import Proof.Wire_3_5.Primitive.Writers.C3WFields
import Proof.Wire_3_5.Primitive.Writers.ParseNat
import Proof.Wire_3_5.Primitive.Writers.SFCost5

/-! # The child's cost at a call, generic, part 2: the compiler input's fixed fields

P3:1886-1906 (the compiler's input: `1^{Q'}`, `1^{P_ex}`, `1^m`, `1^h`, `1^{p+1}`, `1^{width}`, the pool stream, the
children table, the expression, the two headers). The child's fixed fields (C4Child's `pre` = the first eight,
`post` = the headers) are polynomial in the request's displayed numbers: with
`B = Q' + P_ex + |D| + m + h + p + width + dRow + |cols| + 1`, `|pre| + |post| ≤ 256·B³` (the pool stream
`P_ex·2(2w+1)` records of `h` bits, the table `P_ex` entries of `Q' + P_ex + 1` bits). Mode-generic.

* `flatMap_len_le`, `poolStream_le`, `table_le`, `pre_le`, `post_le`, `fixB`, **`prepost_le`**.

Paper quantity of the main type: the compiler input's description size at a child request. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.EnumCap
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary

variable (a : DecompositionAlgorithm)

theorem flatMap_len_le {α β : Type} (l : List α) (f : α → List β) (c : ℕ) (h : ∀ x ∈ l, (f x).length ≤ c) :
    (l.flatMap f).length ≤ l.length * c := by
  rw [List.length_flatMap]
  have := List.sum_le_card_nsmul (l.map fun x => (f x).length) c (fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact h x hx)
  simpa using this

/-- The pool stream's length. -/
theorem poolStream_le (R : C3Req) :
    ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame).length ≤
      (R.D a).flatten.length * (2 * (R.P.width + R.P.width + 1)) * (2 * R.P.h + 1) := by
  have h1 := flatMap_len_le (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips) frame (2 * R.P.h + 1)
    (fun r hr => by
      unfold poolRecs at hr
      obtain ⟨fe, _, hfe⟩ := List.mem_flatMap.mp hr
      rw [frame_length, denseRecs_width _ _ _ _ _ r hfe])
  have h2 : (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).length ≤
      (poolChildren a R.P.gates R.P.flips).length * (2 * (R.P.width + R.P.width + 1)) := by
    unfold poolRecs
    exact flatMap_len_le (poolChildren a R.P.gates R.P.flips) (fun fe => denseRecs R.P.h R.P.side fe.1 R.P.width fe.2) _
      (fun fe _ => (denseRecs_length _ _ _ _ _).le)
  have h3 : (poolChildren a R.P.gates R.P.flips).length = (R.D a).flatten.length :=
    (Emit.shapeOf_flatten_length a R.P.gates R.P.side R.P.width R.P.flips).symm.trans (shapeOf_flatten_len _)
  rw [h3] at h2
  exact h1.trans (Nat.mul_le_mul_right _ h2)

/-- The children table's length. -/
theorem table_le (R : C3Req) :
    (tableTape (childTable R.P.Q (shapeOf (R.D a))) []).length ≤
      (R.D a).flatten.length * (2 * (R.P.Q + (R.D a).flatten.length + 1) + 1) + (R.D a).length := by
  have hW : (shapeOf (R.D a)).flatten.length = (R.D a).flatten.length := shapeOf_flatten_len _
  have hL : (shapeOf (R.D a)).length = (R.D a).length := shapeOf_length _
  unfold tableTape
  rw [List.append_nil, List.length_flatMap]
  have hE : ∀ E ∈ childTable R.P.Q (shapeOf (R.D a)), (atomStream E).length ≤
      E.length * (2 * (R.P.Q + (R.D a).flatten.length + 1) + 1) + 1 := by
    intro E hE
    unfold atomStream
    rw [List.length_append, List.length_singleton]
    have := flatMap_len_le E frame (2 * (R.P.Q + (R.D a).flatten.length + 1) + 1) (fun y hy => by
      unfold childTable at hE
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hE
      obtain ⟨cc, _, rfl⟩ := List.mem_map.mp hy
      rw [frame_length]
      unfold Unions.ew
      rw [Unions.entryWord_length _ _ _ _ (Nat.zero_le _), hW])
    omega
  calc ((childTable R.P.Q (shapeOf (R.D a))).map fun E => (atomStream E).length).sum
      ≤ ((childTable R.P.Q (shapeOf (R.D a))).map fun E =>
          E.length * (2 * (R.P.Q + (R.D a).flatten.length + 1) + 1) + 1).sum := List.sum_le_sum hE
    _ = ((childTable R.P.Q (shapeOf (R.D a))).map List.length).sum *
          (2 * (R.P.Q + (R.D a).flatten.length + 1) + 1) + (childTable R.P.Q (shapeOf (R.D a))).length := by
        rw [List.sum_map_add, List.sum_map_mul_right]
        simp
    _ = _ := by
        rw [PrimAsm.C3Field.sum_childTable, hW]
        simp [childTable, hL]

/-- The first eight fields. -/
theorem pre_le (R : C3Req) : (PrimT.C4Child.pre a R).length ≤
    2 * R.P.Q + 2 * (R.D a).flatten.length + 2 * R.m + 2 * R.P.h + 2 * (R.p + 1) + 2 * R.P.width +
      2 * ((R.D a).flatten.length * (2 * (R.P.width + R.P.width + 1)) * (2 * R.P.h + 1)) +
      2 * ((R.D a).flatten.length * (2 * (R.P.Q + (R.D a).flatten.length + 1) + 1) + (R.D a).length) + 8 := by
  have h6 := poolStream_le a R
  have h7 := table_le a R
  have hW : (shapeOf (R.D a)).flatten.length = (R.D a).flatten.length := shapeOf_flatten_len _
  unfold PrimT.C4Child.pre
  have e : (c3Fields a R).take 8 = [List.replicate R.P.Q true, List.replicate (shapeOf (R.D a)).flatten.length true,
      List.replicate R.m true, List.replicate R.P.h true, List.replicate (R.p + 1) true, List.replicate R.P.width true,
      (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame,
      tableTape (childTable R.P.Q (shapeOf (R.D a))) []] := rfl
  rw [e]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, frame_length,
    List.length_replicate, hW]
  omega

/-- The two header fields. -/
theorem post_le (R : C3Req) : (PrimT.C4Child.post a R).length ≤
    2 * (2 * (2 * R.dRow + 3 + (2 * (R.p + 1) + 3)) + 1) + 1 +
      (2 * (2 * (2 * R.P.width + 3 + R.cols.length * (2 * R.P.width + 1)) + 1) + 1) := by
  unfold PrimT.C4Child.post
  have e : (c3Fields a R).drop 9 = [frame (natWord R.dRow ++ natWord (R.p + 1)),
      frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)] := rfl
  rw [e]
  have n1 := PrimAsm.ParseNat.natWord_length R.dRow
  have n2 := PrimAsm.ParseNat.natWord_length (R.p + 1)
  have n3 := PrimAsm.ParseNat.natWord_length R.P.width
  have b1 := PrimAsm.SFCost.nbl_le R.dRow
  have b2 := PrimAsm.SFCost.nbl_le (R.p + 1)
  have b3 := PrimAsm.SFCost.nbl_le R.P.width
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, frame_length,
    MatrixScorePhi.columnsWord_length]
  omega

/-- The fixed fields' base: the request's displayed numbers. -/
def fixB (R : C3Req) : ℕ :=
  R.P.Q + (R.D a).flatten.length + (R.D a).length + R.m + R.P.h + R.p + R.P.width + R.dRow + R.cols.length + 1

/-- **The child's fixed fields**: `|pre| + |post| ≤ 256·B³`. -/
theorem prepost_le (R : C3Req) :
    (PrimT.C4Child.pre a R).length + (PrimT.C4Child.post a R).length ≤ 256 * fixB a R ^ 3 := by
  have h1 := pre_le a R
  have h2 := post_le a R
  obtain ⟨B, hB⟩ : ∃ B, B = fixB a R := ⟨_, rfl⟩
  rw [← hB]
  have hQ : R.P.Q ≤ B := by rw [hB]; unfold fixB; omega
  have hWd : (R.D a).flatten.length ≤ B := by rw [hB]; unfold fixB; omega
  have hD : (R.D a).length ≤ B := by rw [hB]; unfold fixB; omega
  have hm : R.m ≤ B := by rw [hB]; unfold fixB; omega
  have hh : R.P.h ≤ B := by rw [hB]; unfold fixB; omega
  have hp : R.p + 1 ≤ B := by rw [hB]; unfold fixB; omega
  have hw : R.P.width ≤ B := by rw [hB]; unfold fixB; omega
  have hr : R.dRow ≤ B := by rw [hB]; unfold fixB; omega
  have hc : R.cols.length ≤ B := by rw [hB]; unfold fixB; omega
  have hB1 : 1 ≤ B := by rw [hB]; unfold fixB; omega
  have k6 : (R.D a).flatten.length * (2 * (R.P.width + R.P.width + 1)) * (2 * R.P.h + 1) ≤ 18 * B ^ 3 :=
    calc _ ≤ B * (6 * B) * (3 * B) := Nat.mul_le_mul (Nat.mul_le_mul hWd (by omega)) (by omega)
      _ = 18 * B ^ 3 := by ring
  have k7 : (R.D a).flatten.length * (2 * (R.P.Q + (R.D a).flatten.length + 1) + 1) ≤ 7 * B ^ 2 :=
    calc _ ≤ B * (7 * B) := Nat.mul_le_mul hWd (by omega)
      _ = 7 * B ^ 2 := by ring
  have kc : R.cols.length * (2 * R.P.width + 1) ≤ 3 * B ^ 2 :=
    calc _ ≤ B * (3 * B) := Nat.mul_le_mul hc (by omega)
      _ = 3 * B ^ 2 := by ring
  have p1 : B ≤ B ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB1 (by norm_num)
  omega

end NearCubicWires.WireExponent3_5.FinalPass.EnumCap
