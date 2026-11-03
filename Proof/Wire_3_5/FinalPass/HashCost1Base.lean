import Proof.Wire_3_5.FinalPass.HashSBase

/-! # The HASH child's cost, part 1: the printed objective's word at a THR call

The HASH child's steps (`C4H.hCoreCost`, P3:2253-2290, 3011-3016) read the printed objective's word
`exprWord (hV D p')`. Every printed term has coefficient `|c| ≤ Π_jW_j^{2t}·2^{2tℓ₀}` (the coefficient word is
`2·size|c| + 3` bits), `1 + 2t` factors, each an aux FILTER row (`≤ (8Σ|X_j|+1)^{384w+1}` monomials) or a corner form
(`10` monomials), all of degree `≤ 384w + 1` over atoms below `4N²G`; so the word has at most `2^{2k + c_W X³}` bits.

* `zPoly_length`, `hashFactor_len`, `coefWord_len`, `termWord_le'`, `cW2`;
* `walkD_le`, `atomA_le`, `fsLen_le`, **`ew_le`**.

Paper quantity of the main type: the printed HASH objective's word length. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

theorem zPoly_length (G q : ℕ) (sgn : Bool) (gi : ℕ) : (PrimT.HashB.zPoly G q sgn gi).length = 10 := by
  unfold PrimT.HashB.zPoly
  cases sgn <;> simp [Stars.zPlusF2, Stars.zMinusF2]

/-- **Every factor of every printed HASH term** has at most `K + 10` monomials. -/
theorem hashFactor_len (MP : Filters.MajorantParams) (G N nE : ℕ) (Fs : List (F2Poly ℕ))
    (pops : List (Bool × List ℕ)) (plen pre K : ℕ) (hFs : ∀ i, (Fs.getD i []).length ≤ K) :
    ∀ t ∈ PrimT.HashB.hashTermsM MP G N nE Fs pops plen pre, ∀ f ∈ t.2, f.length ≤ K + 10 := by
  intro t ht f hf
  obtain ⟨q, _, e, _, p, _, hfac⟩ := hashTerm_factors MP G N nE Fs pops plen pre t ht
  rcases hfac f hf with rfl | ⟨gi, _, rfl⟩
  · exact (hFs _).trans (Nat.le_add_right _ _)
  · rw [zPoly_length]; omega

theorem coefWord_len (c : ℤ) : (ListMachine.Rec.coefWord c).length = 2 * Nat.size c.natAbs + 3 := by
  unfold ListMachine.Rec.coefWord
  rw [frame_len, List.length_cons, Nat.size_eq_bits_len]
  ring

/-- A term's word from its coefficient's size, its factor count and its factors' words. -/
theorem termWord_le' (t : ℤ × List (List (List ℕ))) (e W PW : ℕ) (hc : t.1.natAbs < 2 ^ e) (hW : t.2.length ≤ W)
    (hp : ∀ f ∈ t.2, (ListMachine.Rec.polyWord f).length ≤ PW) :
    (ListMachine.Rec.termWord t).length ≤ 2 * e + 3 + W * (PW + 1) + 1 := by
  unfold ListMachine.Rec.termWord
  rw [List.length_append, coefWord_len, List.length_append, List.length_singleton, List.length_flatMap]
  have hs := PrimAsm.BShape.sum_map_le_card t.2 (fun f : List (List ℕ) => (true :: ListMachine.Rec.polyWord f).length)
    (PW + 1) (fun f hf => by rw [List.length_cons]; have := hp f hf; omega)
  have hsz : Nat.size t.1.natAbs ≤ e := Nat.size_le.mpr hc
  have := Nat.mul_le_mul_right (PW + 1) hW
  omega

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
