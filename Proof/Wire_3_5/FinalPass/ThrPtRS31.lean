import Proof.Wire_3_5.FinalPass.ThrPtRS30

/-! # S2 (THR per point), part 45: the step bounds grow with their parameters

Each bound is a sum of products of its parameters: `popCap_le`, `popCost_le`, `repCost_le`, `digCost_le`,
`digLoopCost_le`, `eraseRowCost_le`, `fmtCost_le`, `cwCost_le`, `setupCost_le`, `cleanCost_le` (each at parameters
`≤ U` is at most its value at `U`); `PolyB.pow`. Paper quantity: none beyond the machine model (the per-point run
is polynomial in the call's size, P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem PolyB_pow {f : ℕ → ℕ} (hf : DigsBody.PolyB f) : ∀ d : ℕ, DigsBody.PolyB fun U => f U ^ d
  | 0 => by simpa using DigsBody.PolyB.const 1
  | d + 1 => by
    have := DigsBody.PolyB.mul (PolyB_pow hf d) hf
    simpa [pow_succ] using this

variable {U V : ℕ}

theorem popCap_le (p r0 M A0 D : ℕ) (hp : p ≤ U) (hr : r0 ≤ U) (hM : M ≤ U) (hA : A0 ≤ U) (hD : D ≤ U) :
    popCap p r0 M A0 D ≤ popCap U U U U U := by
  unfold popCap; gcongr

theorem popCost_le (p r0 M A0 D : ℕ) (hp : p ≤ U) (hr : r0 ≤ U) (hM : M ≤ U) (hA : A0 ≤ U) (hD : D ≤ U) :
    popCost p r0 M A0 D ≤ popCost U U U U U := by
  unfold popCost occCost bitDCost; gcongr

theorem repCost_le (M c5 : ℕ) (hM : M ≤ U) (hc : c5 ≤ V) : repCost M c5 ≤ repCost U V := by
  unfold repCost repBodyCost ListEval.mainCost; gcongr

theorem digCost_le (p r0 M A0 D DM c5 tp tm : ℕ) (hp : p ≤ U) (hr : r0 ≤ U) (hM : M ≤ U) (hA : A0 ≤ U) (hD : D ≤ U)
    (hDM : DM ≤ U) (hc : c5 ≤ V) (ht : tp ≤ U) (hs : tm ≤ U) :
    digCost p r0 M A0 D DM c5 tp tm ≤ digCost U U U U U U V U U := by
  unfold digCost
  have h1 := popCost_le p r0 M A0 D hp hr hM hA hD
  have h2 := repCost_le DM c5 hDM hc
  gcongr

theorem digLoopCost_le (m p r0 M A0 τ DM c5 : ℕ) (hm : m ≤ U) (hp : p ≤ U) (hr : r0 ≤ U) (hM : M ≤ U) (hA : A0 ≤ U)
    (hτ : τ ≤ U) (hDM : DM ≤ U) (hc : c5 ≤ V) :
    digLoopCost m p r0 M A0 τ DM c5 ≤ digLoopCost U U U U U U U V := by
  unfold digLoopCost
  have h := digCost_le p r0 M A0 τ DM c5 DM DM hp hr hM hA hτ hDM hc hDM hDM
  gcongr

theorem eraseRowCost_le (p r0 M τ A0 len : ℕ) (hp : p ≤ U) (hr : r0 ≤ U) (hM : M ≤ U) (hτ : τ ≤ U) (hA : A0 ≤ U)
    (hl : len ≤ V) : eraseRowCost p r0 M τ A0 len ≤ eraseRowCost U U U U U V := by
  unfold eraseRowCost; gcongr

theorem fmtCost_le (n l : ℕ) (hn : n ≤ U) (hl : l ≤ V) : fmtCost n l ≤ fmtCost U V := by
  unfold fmtCost; gcongr

theorem cwCost_le (h n m : ℕ) (hh : h ≤ U) (hn : n ≤ U) (hm : m ≤ U) : Corner.cwCost h n m ≤ Corner.cwCost U U U := by
  unfold Corner.cwCost Corner.gateCost Corner.coreCost; gcongr

theorem setupCost_le (τ M H cwc : ℕ) (hτ : τ ≤ U) (hM : M ≤ U) (hH : H ≤ U) (hc : cwc ≤ V) :
    setupCost τ M H cwc ≤ setupCost U U U V := by
  unfold setupCost
  have h1 := fmtCost_le H [true, false].length hH (le_refl _)
  have h2 := fmtCost_le M (List.replicate 8 false).length hM (le_refl _)
  have h3 := fmtCost_le M [false, false].length hM (le_refl _)
  gcongr

theorem cleanCost_le (G τ M H : ℕ) (hG : G ≤ U) (hτ : τ ≤ U) (hM : M ≤ U) (hH : H ≤ U) :
    cleanCost G τ M H ≤ cleanCost U U U U := by
  unfold cleanCost
  have h1 := fmtCost_le H [false, false].length hH (le_refl _)
  have h2 := fmtCost_le M (List.replicate 8 false).length hM (le_refl _)
  have h3 := fmtCost_le M [false, false].length hM (le_refl _)
  gcongr

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
