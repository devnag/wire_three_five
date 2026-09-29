import Proof.Wire_3_5.Primitive.SeedFix.C4HBf

/-! # C4HB, part 7: the Hb unit's prep bound (`hb_prep`)

`alg:compiler`'s polynomial construction (P3:1887-1888) at the Hb unit's prep. **`hb_prep`** (C4HB's `HbPrepBound`):
with `plen ≤ 2tℓ₀` and every capacity at most `v`, each of the 94 tapes of the Hb bank before cell `0` (`hb0`: the
word state's streams `st0`, its registers, the log, the elimination's tapes at `R0`) is at most `3·(hbS D + v + 1)²`
long, so `hbPrepCost ≤ 2^32·(hbS D + v + 1)^3`.

* `addCases_len_le`, `flat_ofFn_le`, `st0_le`, `wenc0_le`, `bank31_le`, `hb0_le`, **`hb_prep`**.

Paper quantity of the main type: the Hb unit's prep step count at the call's data size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

theorem addCases_len_le {m n : ℕ} (f : Fin m → List Bool) (g : Fin n → List Bool) (M : ℕ)
    (hf : ∀ a, (f a).length ≤ M) (hg : ∀ b, (g b).length ≤ M) (j : Fin (m + n)) :
    (Fin.addCases (motive := fun _ => List Bool) f g j).length ≤ M := by
  refine Fin.addCases (motive := fun j => (Fin.addCases (motive := fun _ => List Bool) f g j).length ≤ M)
    (fun a => ?_) (fun b => ?_) j
  · rw [Fin.addCases_left]; exact hf a
  · rw [Fin.addCases_right]; exact hg b

theorem flat_ofFn_le {k : ℕ} (f : Fin k → List Bool) (M : ℕ) (h : ∀ j, (f j).length ≤ M) :
    (List.ofFn f).flatten.length ≤ k * M := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc ∑ j, (List.length ∘ f) j ≤ ∑ _j : Fin k, M := Finset.sum_le_sum fun j _ => h j
    _ = k * M := by simp

section Prep
variable (D : HashData) (c : HbCaps) (plen pfx v : ℕ)

theorem st0_le (i : Fin 24) : (st0 (hbX D c plen pfx) i).length ≤ hbS D + 1 := by
  have h1 : (htWord (hbX D c plen pfx).Fs).length ≤ hbS D := hbS_ht D
  have h2 : (popsWord (hbX D c plen pfx).pops).length ≤ hbS D := hbS_pw D
  have h3 : (wtWord (hbX D c plen pfx).Ws).length ≤ hbS D := hbS_wt D
  have h4 : (hbX D c plen pfx).L ≤ hbS D := hbS_L D
  have h5 : (hbX D c plen pfx).J ≤ hbS D := hbS_J D
  have h6 : (hbX D c plen pfx).P ≤ hbS D := hbS_P D
  have h7 : (hbX D c plen pfx).nE ≤ hbS D := hbS_nE D
  have h8 : (hbX D c plen pfx).N2 ≤ hbS D := hbS_N2 D
  have h9 : (hbX D c plen pfx).T2 ≤ hbS D := hbS_T2 D
  have h10 : (hbX D c plen pfx).ℓ ≤ hbS D := hbS_l D
  have h11 : (hbX D c plen pfx).G ≤ hbS D := hbS_G D
  fin_cases i <;> simp [st0, unary, binary_length] <;> omega

theorem wenc0_le (a : Fin (23 + 2 + 40)) :
    ((wenc (hbX D c plen pfx).cap (bnd (st0 (hbX D c plen pfx)))).A a).length ≤
      hbS D + 1 + (hbX D c plen pfx).cap + 1 := by
  simp only [wenc]
  cases hr : role a with
  | stream i => have := st0_le D c plen pfx i; simp only [bnd]; omega
  | cell => simp [bnd]
  | reg r => simp [bnd, regTape]

theorem bank31_le (hplen : plen ≤ 2 * D.MP.t * D.MP.ell0) (hc : CapsLe c v) (k : Fin 31) :
    (SeedFix.bank31 (hbX D c plen pfx).mod (hbX D c plen pfx).ℓ (hbX D c plen pfx).T2 (hbX D c plen pfx).plen
      (hbX D c plen pfx).pfx (hbX D c plen pfx).m (hbX D c plen pfx).c1 (hbX D c plen pfx).c2 (hbX D c plen pfx).c3
      (hbX D c plen pfx).c4 (hbX D c plen pfx).RV (hbX D c plen pfx).cL (hbX D c plen pfx).cE
      (R0 (hbX D c plen pfx)) [] [] [] [] (ZeroPadding.pad (hbX D c plen pfx).cK [])
      (ZeroPadding.pad (hbX D c plen pfx).cC (List.replicate ((hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ -
        (hbX D c plen pfx).plen) true)) [] [] k).length ≤ 3 * (hbS D + v + 1) ^ 2 := by
  obtain ⟨_, _, hm0, hc10, hc20, hc30, hc40, hRV0, hcL0, hcE0, hcK0, hcC0⟩ := hc
  have hm : (hbX D c plen pfx).m ≤ v := hm0
  have hc1 : (hbX D c plen pfx).c1 ≤ v := hc10
  have hc2 : (hbX D c plen pfx).c2 ≤ v := hc20
  have hc3 : (hbX D c plen pfx).c3 ≤ v := hc30
  have hc4 : (hbX D c plen pfx).c4 ≤ v := hc40
  have hRV : (hbX D c plen pfx).RV ≤ v := hRV0
  have hcL : (hbX D c plen pfx).cL ≤ v := hcL0
  have hcE : (hbX D c plen pfx).cE ≤ v := hcE0
  have hcK : (hbX D c plen pfx).cK ≤ v := hcK0
  have hcC : (hbX D c plen pfx).cC ≤ v := hcC0
  have hl : (hbX D c plen pfx).ℓ ≤ hbS D := hbS_l D
  have hT : (hbX D c plen pfx).T2 ≤ hbS D := hbS_T2 D
  have hTl : (hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ ≤ hbS D := hbS_Tl D
  have hpl : (hbX D c plen pfx).plen ≤ hbS D := hplen.trans (hbS_Tl D)
  have hr : (hbX D c plen pfx).T2 * ((hbX D c plen pfx).ℓ * (2 * (hbX D c plen pfx).ℓ + 1)) ≤
      2 * (hbS D + v + 1) ^ 2 := by
    have e : (hbX D c plen pfx).T2 * ((hbX D c plen pfx).ℓ * (2 * (hbX D c plen pfx).ℓ + 1)) =
        ((hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ) * (2 * (hbX D c plen pfx).ℓ + 1) := by ring
    rw [e]
    have m : ((hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ) * (2 * (hbX D c plen pfx).ℓ + 1) ≤
        (hbS D + v + 1) * (2 * (hbS D + v + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have e2 : (hbS D + v + 1) * (2 * (hbS D + v + 1)) = 2 * (hbS D + v + 1) ^ 2 := by ring
    omega
  have hQ : hbS D + v + 1 ≤ (hbS D + v + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize (hbS D + v + 1) ^ 2 = Q2 at *
  fin_cases k <;> simp [SeedFix.bank31, R0, frame_length, binary_length] <;> omega

theorem hb0_le (hplen : plen ≤ 2 * D.MP.t * D.MP.ell0) (hc : CapsLe c v) (j : Fin 94) :
    (hb0 (hbX D c plen pfx) j).length ≤ 3 * (hbS D + v + 1) ^ 2 := by
  have hQ : hbS D + v + 1 ≤ (hbS D + v + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcap : (hbX D c plen pfx).cap ≤ v := hc.1
  have hcapL : (hbX D c plen pfx).capL ≤ v := hc.2.1
  unfold hb0 hbBank
  refine addCases_len_le (m := 66) (n := 28) _ _ _ (fun a => ?_) (fun b => ?_) j
  · refine addCases_len_le (m := 65) (n := 1) _ _ _ (fun a' => ?_) (fun _ => ?_) a
    · have := wenc0_le D c plen pfx a'
      omega
    · simp only [List.length_replicate]
      omega
  · exact bank31_le D c plen pfx v hplen hc _

end Prep

/-- **The Hb unit's prep bound** (C4HB's `HbPrepBound`). -/
theorem hb_prep : HbPrepBound := by
  intro D c plen pfx v hplen hc
  have h1 := flat_ofFn_le (hb0 (hbX D c plen pfx)) _ (hb0_le D c plen pfx v hplen hc)
  have hTl : (hbX D c plen pfx).T2 * (hbX D c plen pfx).ℓ ≤ hbS D := hbS_Tl D
  have hQ : 1 ≤ hbS D + v + 1 := by omega
  have p12 : hbS D + v + 1 ≤ (hbS D + v + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : (hbS D + v + 1) ^ 2 ≤ (hbS D + v + 1) ^ 3 := Nat.pow_le_pow_right hQ (by norm_num)
  unfold hbPrepCost
  generalize (hbS D + v + 1) ^ 2 = Q2 at *
  generalize (hbS D + v + 1) ^ 3 = Q3 at *
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4HB
