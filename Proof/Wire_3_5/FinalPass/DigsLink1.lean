import Proof.Wire_3_5.FinalPass.DigsTop1

/-! # `DigsW`'s body, part 15: list and residue identities for the digit word (P3:2596-2599)

The program's output `Wd … [] τ₀` is compared with `digsWord (List.ofFn fun d => thrDigGis … d)` through the flat
emission `emitAs off d o as` (occurrence `o + k` with residue `as[k]`): `emitList_as` (a circuit's weights),
`emitAs_append`, `emitAs_ofFn` (the `finRange` form of `thrDigGis`), `Ls_as` (the circuits' blocks), `ofFn_range`,
and the residue identities `bfold_eq` (the stack base), `Bs_eq` (`Bs i = bm^i mod p`), `Gs_eq` (the selection
digits), `resid_mul` (`((b^i · w) mod p).toNat = (b mod p)^i mod p · (w mod p).toNat mod p`). Paper quantities: the
reduced coefficients `a_i`, their digits, the stack base modulo `p`, the child indices `g_i`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.RepairRepresentation (natWord intWord)

/-- The flat emission: occurrence `o + k` with residue `as[k]`. -/
def emitAs (off d : ℕ) : ℕ → List ℕ → List Bool
  | _, [] => []
  | o, a :: as => emitW off o d a ++ emitAs off d (o + 1) as

theorem emitAs_append (off d : ℕ) : ∀ (o : ℕ) (xs ys : List ℕ),
    emitAs off d o (xs ++ ys) = emitAs off d o xs ++ emitAs off d (o + xs.length) ys
  | o, [], ys => by simp [emitAs]
  | o, x :: xs, ys => by
    rw [List.cons_append, emitAs, emitAs, emitAs_append off d (o + 1) xs ys, List.append_assoc]
    congr 3; simp; ring

theorem emitList_as (off d B p : ℕ) : ∀ (o : ℕ) (ws : List ℤ),
    emitList off d B p o ws = emitAs off d o (ws.map fun w => B * (w % (p : ℤ)).toNat % p)
  | o, [] => by simp [emitList, emitAs]
  | o, w :: ws => by rw [emitList, List.map_cons, emitAs, emitList_as off d B p (o + 1) ws]

theorem emitAs_ofFn (off d : ℕ) : ∀ (n o : ℕ) (rc : Fin n → ℕ),
    (List.ofFn fun k : Fin n => emitW off (o + k.val) d (rc k)).flatten = emitAs off d o (List.ofFn rc)
  | 0, o, rc => by simp [emitAs]
  | n + 1, o, rc => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, emitAs, ← emitAs_ofFn off d n (o + 1) (fun k => rc k.succ)]
    have e : (fun k : Fin n => emitW off (o + (k.succ : Fin (n + 1)).val) d (rc k.succ)) =
        (fun k : Fin n => emitW off (o + 1 + k.val) d (rc k.succ)) := by
      funext k; rw [Fin.val_succ]; congr 1; ring
    simp only [Fin.val_zero, Nat.add_zero]
    rw [e]

theorem ofFn_range {α : Type} (f : ℕ → α) : ∀ n : ℕ, (List.ofFn fun k : Fin n => f k.val) = (List.range n).map f
  | 0 => by simp
  | n + 1 => by
    rw [List.ofFn_succ', List.concat_eq_append, List.range_succ, List.map_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.map_cons, List.map_nil]
    rw [ofFn_range f n]

theorem Ls_as (off d bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (hS : ∀ i, (ws i).length = S i) :
    ∀ n, Ls off d bm p S ws [] n =
      emitAs off d 0 ((List.range n).flatMap fun i => (ws i).map fun w => Bs bm p i * (w % (p : ℤ)).toNat % p)
  | 0 => by simp [Ls, emitAs]
  | n + 1 => by
    rw [Ls, Ls_as off d bm p S ws hS n, List.range_succ, List.flatMap_append, emitAs_append, emitList_as]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 2
    have : ∀ k, ((List.range k).flatMap fun i => (ws i).map fun w => Bs bm p i * (w % (p : ℤ)).toNat % p).length =
        Os S k := by
      intro k
      induction k with
      | zero => simp [Os]
      | succ k ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [Os, hS]
    rw [this]; simp

/-- `bfold` sums absolute values modulo `p`. -/
theorem bfold_eq (p : ℕ) (hp : 0 < p) : ∀ (x : ℕ) (zs : List ℤ), x < p →
    bfold p x zs = (x + (zs.map Int.natAbs).sum) % p
  | x, [], hx => by simp [bfold, Nat.mod_eq_of_lt hx]
  | x, z :: zs, hx => by
    have ih := bfold_eq p hp ((x + z.natAbs % p) % p) zs (Nat.mod_lt _ hp)
    unfold bfold at ih ⊢
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    have h1 : (x + z.natAbs % p) % p + (zs.map Int.natAbs).sum ≡ x + z.natAbs % p + (zs.map Int.natAbs).sum [MOD p] :=
      Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
    have h2 : x + z.natAbs % p + (zs.map Int.natAbs).sum ≡ x + z.natAbs + (zs.map Int.natAbs).sum [MOD p] :=
      Nat.ModEq.add_right _ (Nat.ModEq.add_left _ (Nat.mod_modEq _ _))
    rw [show x + (z.natAbs + (zs.map Int.natAbs).sum) = x + z.natAbs + (zs.map Int.natAbs).sum by ring]
    exact h1.trans h2

theorem Bf_eq (p : ℕ) (hp : 2 ≤ p) (ys : ℕ → List ℤ) : ∀ n,
    Bf p ys n = (1 + ((List.range n).map fun i => ((ys i).map Int.natAbs).sum).sum) % p
  | 0 => by simp [Bf]; rw [Nat.mod_eq_of_lt (by omega)]
  | n + 1 => by
    rw [Bf, bfold_eq p (by omega) _ _ (Bf_lt p hp ys n), Bf_eq p hp ys n, List.range_succ, List.map_append,
      List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have h1 : (1 + ((List.range n).map fun i => ((ys i).map Int.natAbs).sum).sum) % p + ((ys n).map Int.natAbs).sum ≡
        1 + ((List.range n).map fun i => ((ys i).map Int.natAbs).sum).sum + ((ys n).map Int.natAbs).sum [MOD p] :=
      Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
    rw [← Nat.add_assoc]; exact h1

theorem Bs_eq (bm p : ℕ) (hp : 2 ≤ p) : ∀ i, Bs bm p i = bm ^ i % p
  | 0 => by simp [Bs]; rw [Nat.mod_eq_of_lt (by omega)]
  | i + 1 => by
    rw [Bs, Bs_eq bm p hp i, pow_succ]
    exact Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)

/-- The reduced coefficient from the power's residue and the weight's residue. -/
theorem resid_mul (b i : ℕ) (w : ℤ) (p : ℕ) (hp : 0 < p) :
    (((b : ℤ) ^ i * w) % (p : ℤ)).toNat = b ^ i % p * (w % (p : ℤ)).toNat % p := by
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h1 : 0 ≤ w % (p : ℤ) := Int.emod_nonneg _ hp'.ne'
  have e : (((b ^ i % p * (w % (p : ℤ)).toNat % p : ℕ)) : ℤ) = ((b : ℤ) ^ i * w) % (p : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg h1, Int.mul_emod ((b : ℤ) ^ i) w]
  rw [← e, Int.toNat_natCast]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
