import Proof.Wire_3_5.Primitive.SeedFix.FlipsLoop
import Proof.Wire_3_5.Primitive.SeedFix.C4GeoV

/-! # FLIPS, part 6: the loops' output is C3a's flips field (P3:1224, 1655-1664)

C4Geo's flips field lists, at index `4·cn + k` (`cn = N·L + R`, `N = 2^{kh}`), the corner `k` of
`star:delta` at the coset offset and the cell's errors (`flipAt`, P3:1224). The loops print, left-major and
right-minor, the four corners of every cell as `xw` of the offset's word and C5's decoded error words. Here:

* `range_mul`, `ofFn_range` (the index `4·(N·L + R) + k` unfolded); `xw_ofFn`;
* `errAt_eq` (C4Geo's cell error is `errorsEquiv.symm` of the index), `flipAt_word` (a corner's pattern is `xw` of
  the offset word and `elW`/`erW`, by C5's `errorVector_decode`);
* **`flipsField_eq`**: `C4Geo.flipsField P σ = outL … (List.ofFn (offset P σ)) N ++ [false]`.

Paper quantity of the main type: C3a's flips field (the corner points of every cell). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem range_mul (a b : ℕ) :
    List.range (a * b) = (List.range a).flatMap (fun i => (List.range b).map (fun j => b * i + j)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
    simp [Nat.mul_comm]

theorem ofFn_range {α : Type} (G : ℕ → α) : ∀ m : ℕ, List.ofFn (fun i : Fin m => G i) = (List.range m).map G
  | 0 => rfl
  | m + 1 => by
    have e : (List.ofFn fun i : Fin (m + 1) => G ↑i) = (List.ofFn fun i : Fin m => G ↑i) ++ [G m] := by
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]
    rw [e, ofFn_range G m, List.range_succ, List.map_append]
    simp

theorem xw_ofFn (u v : Bool) : ∀ {n : ℕ} (A B C : Fin n → Bool),
    xw u v (List.ofFn A) (List.ofFn B) (List.ofFn C) = List.ofFn (fun x => xb u v (A x) (B x) (C x))
  | 0, _, _, _ => rfl
  | n + 1, A, B, C => by
    simp only [List.ofFn_succ, xw]
    rw [xw_ofFn u v]

variable (P : StarParams) (σ : P.Translation)

theorem errAt_eq (L : ℕ) (hL : L < 2 ^ SeedFix.callKh P) :
    C4Geo.errAt P L = (FinalPass.errorsEquiv P).symm ⟨L, by rw [SeedFix.callN_eq]; exact hL⟩ := by
  unfold C4Geo.errAt SeedFix.callEqv
  rw [Equiv.symm_trans_apply]
  congr 1
  ext
  simp [Nat.mod_eq_of_lt hL]

/-- The left errors' word of the row `L`, at the call's star numbers. -/
abbrev elP (L : ℕ) : List Bool := elW P.s P.b (P.r / 2) (P.n - P.r * P.b) L
/-- The right errors' word of the column `R`. -/
abbrev erP (R : ℕ) : List Bool := erW P.s P.b (P.r / 2) (P.n - P.r * P.b) R

theorem ev_left (L : ℕ) (hL : L < 2 ^ SeedFix.callKh P) :
    List.ofFn (P.errorVector P.leftBlock (C4Geo.errAt P L)) = elP P L := by
  rw [errAt_eq P L hL]
  have := FinalPass.Sample.errorVector_decode P false ⟨L, by rw [SeedFix.callN_eq]; exact hL⟩
  rw [show (if false = true then P.rightBlock else P.leftBlock) = P.leftBlock from rfl] at this
  exact this

theorem ev_right (R : ℕ) (hR : R < 2 ^ SeedFix.callKh P) :
    List.ofFn (P.errorVector P.rightBlock (C4Geo.errAt P R)) = erP P R := by
  rw [errAt_eq P R hR]
  have := FinalPass.Sample.errorVector_decode P true ⟨R, by rw [SeedFix.callN_eq]; exact hR⟩
  rw [show (if true = true then P.rightBlock else P.leftBlock) = P.rightBlock from rfl] at this
  exact this

/-- **A corner's flip pattern** is the corner word of the offset and the cell's decoded error words. -/
theorem flipAt_word (L R k : ℕ) (hL : L < 2 ^ SeedFix.callKh P) (hR : R < 2 ^ SeedFix.callKh P) (hk : k < 4) :
    List.ofFn (C4Geo.flipAt P σ (2 ^ SeedFix.callKh P * L + R) k) =
      xw (decide (k < 2)) (decide (k % 2 = 0)) (List.ofFn (C4Geo.offset P σ)) (elP P L) (erP P R) := by
  have hN : 0 < 2 ^ SeedFix.callKh P := Nat.two_pow_pos _
  have e1 : (2 ^ SeedFix.callKh P * L + R) / 2 ^ SeedFix.callKh P = L := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hR, Nat.zero_add]
  have e2 : (2 ^ SeedFix.callKh P * L + R) % 2 ^ SeedFix.callKh P = R := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]
  unfold C4Geo.flipAt
  rw [e1, e2, ← ev_left P L hL, ← ev_right P R hR, xw_ofFn]
  congr 1
  funext x
  have hk4 : k % 4 = k := Nat.mod_eq_of_lt hk
  interval_cases k <;> simp [C4Geo.cornerPt, xb, xorInput] <;> cases C4Geo.offset P σ x <;> simp

theorem flips_eq : C4Geo.flips P σ = (List.range (2 ^ SeedFix.callKh P)).flatMap (fun L =>
    (List.range (2 ^ SeedFix.callKh P)).flatMap (fun R => (List.range 4).map (fun k =>
      List.ofFn (C4Geo.flipAt P σ (2 ^ SeedFix.callKh P * L + R) k)))) := by
  unfold C4Geo.flips
  rw [ofFn_range (fun idx => List.ofFn (C4Geo.flipAt P σ (idx / 4) (idx % 4))),
    show 4 * (2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P) = (2 ^ SeedFix.callKh P * 2 ^ SeedFix.callKh P) * 4 by ring,
    range_mul, range_mul]
  simp only [List.flatMap_assoc, List.map_flatMap, List.flatMap_map, List.map_map]
  refine List.flatMap_congr fun L _ => List.flatMap_congr fun R _ => List.map_congr_left fun k hk => ?_
  have hk4 : k < 4 := List.mem_range.mp hk
  simp only [Function.comp]
  congr 2
  · omega
  · omega

/-- **The loops' output is C3a's flips field.** -/
theorem flipsField_eq : C4Geo.flipsField P σ =
    outL P.s P.b (P.r / 2) (P.n - P.r * P.b) (List.ofFn (C4Geo.offset P σ)) (2 ^ SeedFix.callKh P) ++ [false] := by
  unfold C4Geo.flipsField CompilerMachine.Kit.streamTape
  rw [flips_eq]
  congr 1
  unfold outL outR
  simp only [List.flatMap_assoc]
  refine List.flatMap_congr fun L hL => List.flatMap_congr fun R hR => ?_
  have hL' : L < 2 ^ SeedFix.callKh P := List.mem_range.mp hL
  have hR' : R < 2 ^ SeedFix.callKh P := List.mem_range.mp hR
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil, Function.comp]
  rw [flipAt_word P σ L R 0 hL' hR' (by decide), flipAt_word P σ L R 1 hL' hR' (by decide),
    flipAt_word P σ L R 2 hL' hR' (by decide), flipAt_word P σ L R 3 hL' hR' (by decide)]
  simp [blk, List.append_assoc]

end NearCubicWires.WireExponent3_5.PrimT.Flips
