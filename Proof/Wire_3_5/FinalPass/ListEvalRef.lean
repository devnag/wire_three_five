import Mathlib

/-! # Final pass, stage 5: the list report's machine reference (P3:3170-3178, 1419-1477)

The reported count of a repaired list at one input, as the stage-5 machine computes it (P3:3175-3178): "compute the
nested counts and discrepancies, evaluate the binary residue decoder, follow its unique reconstructed count or empty
state, and then apply repair". Levels are processed from the top `J` down to `0`. At level `j` the residue
`v_j = (c_j + W_j − 2c_{j+1}) mod 2^{ℓ_j}` is the decoder's value `val(G_{j,·})` (P3:1449-1457). The state follows
`s_j = 2s_{j+1} + v_j − W_j`. It is empty once `s_{j+1} > M` or `s_j < 0` (P3:1463-1470), and the report is `s_0`
when it lies in `[0, M]`, else `0` (P3:1472-1477). A dummy record for level `J` (window `0`, modulus `1`) seeds
`s_J = 0` and `c_J`.

This module needs only Mathlib, so it compiles in every farm. The bridge to `ListFast.listReportFast` is
`Proof.Wire_3_5.FinalPass.ListEvalBridge`.

Paper quantities: the counts `hits`, the modulus `pow W = 2^{ℓ}`, one level `levelStep`, the fold `levelFold`, the
report `reportRef`, and the table word `levelWord` that stage 4 writes and stage 5 reads. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval

/-- `1^n 0`. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- The decoder modulus `2^{ℓ}`, `ℓ = ⌈log₂(2W+1)⌉` (P3:1421). -/
def pow (W : ℕ) : ℕ := 2 ^ Nat.clog 2 (2 * W + 1)

theorem pow_pos (W : ℕ) : 0 < pow W := by unfold pow; positivity

/-- The count `Σ_i [row_i ∧ Z_i]` over the common prefix. -/
def hits : List Bool → List Bool → ℕ
  | a :: as, b :: bs => (if a && b then 1 else 0) + hits as bs
  | _, _ => 0

/-- The residue `x mod P` in `[0, P)`. -/
def cyc (P : ℕ) (x : ℤ) : ℕ := (x % (P : ℤ)).toNat

/-- One level of the followed state: from `s_{j+1}` to `s_j` with window `W`, counts `c_{j+1} = cp` and `c_j = c`. -/
def levelStep (M W cp c : ℕ) : Option ℕ → Option ℕ
  | none => none
  | some t =>
    if t ≤ M ∧ W ≤ 2 * t + cyc (pow W) ((c : ℤ) + W - 2 * cp) then some (2 * t + cyc (pow W) ((c : ℤ) + W - 2 * cp) - W)
    else none

/-- The windows with the dummy top record: `W'_J = 0`. -/
def topW (J : ℕ) (W : ℕ → ℕ) (j : ℕ) : ℕ := if j = J then 0 else W j

/-- The levels in processing order: `J, J−1, …, 0`. -/
def levels (J : ℕ) : List ℕ := (List.range (J + 1)).reverse

/-- The fold over the processed levels: the followed state and the last count. -/
def levelFold (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (init : Option ℕ × ℕ)
    (js : List ℕ) : Option ℕ × ℕ :=
  js.foldl (fun acc j => (levelStep M (topW J W j) acc.2 (hits (row j) Z) acc.1, hits (row j) Z)) init

/-- **The reported count** (P3:1472-1477): the followed state if it lies in `[0, M]`, else `0`. -/
def reportRef (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) : ℕ :=
  match (levelFold M J W row Z (some 0, 0) (levels J)).1 with
  | some v => if v ≤ M then v else 0
  | none => 0

/-- One record of the table word. -/
def record (J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (j : ℕ) : List Bool :=
  true :: (unary (pow (topW J W j)) ++ unary (topW J W j) ++ row j)

/-- **The table word** read by stage 5: `M`, then the records of levels `J, …, 0`, then `false`. -/
def levelWord (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) : List Bool :=
  unary M ++ ((levels J).flatMap (record J W row)) ++ [false]

/-- The register capacity of the stage-5 machine for a table word and a point length. -/
def capOf (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (L : ℕ) : ℕ :=
  4 * ((levelWord M J W row).length + L + 1)

/-! ## Executable check -/

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
