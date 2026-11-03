import Proof.Wire_3_5.Primitive.SeedFix.C4HfD
import Proof.Wire_3_5.Primitive.SeedFix.C4Enum

/-! # The HASH child family, part 5: the Hb bank at a child prefix

`filt:soft`, P3:2255-2262: the Hb printer's bank before cell `0` at the child prefix `(plen, pfx)` (`C4H.hb0`) is the
kept one (at `0, 0`) but for two elimination tapes: tape `80`, the prefix word `frame (binary plen pfx)`, and tape
`93`, the free-bit ruler `pad c_C (1^{2t·ℓ₀ − plen})` (**`hb0_other`**, `hb0_80`, `hb0_93`); and it meets the loop
invariant before cell `0` (**`hb0_inv`**).

Paper quantity of the main type: the Hb printer's bank at the child prefix. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem ex28_other (p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC : ℕ) (R : SeedFix.Regs) (O W P : List Bool)
    (i : Fin 28) (h1 : i.val ≠ 14) (h2 : i.val ≠ 27) :
    ex28 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC R O W P i =
      ex28 p ℓ twoH 0 0 m c1 c2 c3 c4 RV cL cE cK cC R O W P i := by
  show SeedFix.bank31 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE R O [] W P _ _ [] [] (e28 i) =
    SeedFix.bank31 p ℓ twoH 0 0 m c1 c2 c3 c4 RV cL cE R O [] W P _ _ [] [] (e28 i)
  unfold SeedFix.bank31
  fin_cases i <;> simp [e28] at h1 h2 ⊢

/-- **The kept tapes at every child prefix** but tapes `80` and `93`. -/
theorem hb0_other (D : HashData) (c : HbCaps) (plen pfx : ℕ) (j : Fin 94) (h1 : j.val ≠ 80) (h2 : j.val ≠ 93) :
    hb0 (hbX D c plen pfx) j = hb0 (hbX D c 0 0) j := by
  obtain ⟨v, hv⟩ := j
  unfold hb0 hbBank
  by_cases hlt : v < 66
  · have e : (⟨v, hv⟩ : Fin 94) = Fin.castAdd 28 ⟨v, hlt⟩ := rfl
    rw [e, Fin.addCases_left, Fin.addCases_left]
    rfl
  · have hv28 : v - 66 < 28 := by omega
    have e : (⟨v, hv⟩ : Fin 94) = Fin.natAdd 66 (⟨v - 66, hv28⟩ : Fin 28) := Fin.ext (by simp; omega)
    rw [e, Fin.addCases_right, Fin.addCases_right]
    have h1' : v ≠ 80 := h1
    have h2' : v ≠ 93 := h2
    refine ex28_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨v - 66, by omega⟩ ?_ ?_
    · show v - 66 ≠ 14; omega
    · show v - 66 ≠ 27; omega

theorem hb0_80 (D : HashData) (c : HbCaps) (plen pfx : ℕ) :
    hb0 (hbX D c plen pfx) ⟨80, by norm_num⟩ = frame (binary plen pfx) := rfl

theorem hb0_93 (D : HashData) (c : HbCaps) (plen pfx : ℕ) :
    hb0 (hbX D c plen pfx) ⟨93, by norm_num⟩ =
      ZeroPadding.pad c.cC (List.replicate (2 * D.MP.t * D.MP.ell0 - plen) true) := rfl

/-- **The Hb bank before cell `0`** meets the loop invariant. -/
theorem hb0_inv (X : HbX) : X.Inv 0 (hb0 X) := by
  refine ⟨st0 X, R0 X, [], [], [], false, false, rfl, ?_, ?_, rfl, rfl⟩
  · refine ⟨by simp [R0], by simp [R0], by simp [R0]⟩
  · have hB : 0 < X.B := Nat.two_pow_pos _
    exact ⟨rfl, rfl, rfl, rfl, rfl, by simp [st0, HbX.d0], by simp [st0, HbX.lamOf], by simp [st0, HbX.pOf],
      by simp [st0, HbX.eOf], by simp [st0, HbX.qOf], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
