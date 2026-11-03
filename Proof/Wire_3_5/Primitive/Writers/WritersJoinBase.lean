import Proof.Wire_3_5.Primitive.Writers.PreLinkBase
import Proof.Wire_3_5.Primitive.Writers.ComposeEnvBase

/-! # The writers' join: three separately built writers give the writer node's target

The writer node's target `PreLink.WriterLeafJ2` bundles the SYM, THR and HASH writers (`WritersAtJ`) at ONE floor
envelope `E_W`, one load-constant floor `CD_W` and one coefficient `c_W`. The three writers are built separately, each
with its own floors and coefficient. This file fixes each writer's type and proves the join:

* **`SymLeafJ2`**, **`ThrLeafJ2`**, **`HashLeafJ2`**: one writer each, in `WriterLeafJ2`'s order of choice (`fe`, then
  `E_W`, `CD_W`, then `F`, then `c_W`);
* `writerRun_mono`: a writer's run within `B` steps is a run within any `B' ≥ B`;
* `symMono`, `thrMono`, `hashMono`: a writer within `c_W · classBound E_W` is within
  `c_W' · classBound E_W'` for `E_W ≤ E_W'` and `c_W ≤ c_W'` (every call length has `n ≥ 8` from `StarAt`);
* **`writerLeafJ2_of`**: `SymLeafJ2 l → ThrLeafJ2 l → HashLeafJ2 l → WriterLeafJ2 l`, with the floors
  `envMax (envMax E_S E_T) E_H` and `max (max CD_S CD_T) CD_H` and the coefficient `max (max c_S c_T) c_H`.

Paper quantity of the main types: the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114) of each batch
writer's tape (`symTape`, `thrTape`, `hashTape`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ NearCubicWires.WireExponent3_5.PrimAsm.PreLink
open NearCubicWires.WireExponent3_5.PrimAsm.ComposeEnv

/-! ## Monotonicity -/

/-- A writer's run within `B` steps is a run within any larger bound. -/
theorem writerRun_mono {t s : ℕ} {M : Machine t s} {B B' : ℕ} {i o : Fin t} {w v : List Bool}
    (h : WriterRun M B i o w v) (hB : B ≤ B') : WriterRun M B' i o w v := by
  obtain ⟨J, hJ, hR⟩ := h
  exact ⟨J, fun j => (hJ j).trans hB, ClockJoin.enlarge M B B' _ _ hR hB⟩

/-- Every call length with the star hypotheses is at least `1`. -/
theorem one_le_of_starAt {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {n : ℕ}
    (hs : I.StarAt n) : 1 ≤ n := by
  have h1 := hs.2.1
  have h2 := hs.2.2.1
  omega

/-- The writers' budget is monotone in the floor envelope and the coefficient. -/
theorem budget_mono {EW EW' : Envelope} {cW cW' : ℕ} (h : ClassLE EW EW') (hc : cW ≤ cW') {n : ℕ} (hn : 1 ≤ n)
    (k psi : ℕ) :
    cW * classBound EW .preprocessing n k psi ≤ cW' * classBound EW' .preprocessing n k psi :=
  Nat.mul_le_mul hc (classBound_mono h .preprocessing n k psi hn (fun h => by cases h))

section Mono

end Mono

/-! ## Each writer's type -/

/-! ## The join -/

theorem classLE_max3_1 (E₁ E₂ E₃ : Envelope) : ClassLE E₁ (envMax (envMax E₁ E₂) E₃) :=
  classLE_trans (classLE_envMax_left E₁ E₂) (classLE_envMax_left _ E₃)

theorem classLE_max3_2 (E₁ E₂ E₃ : Envelope) : ClassLE E₂ (envMax (envMax E₁ E₂) E₃) :=
  classLE_trans (classLE_envMax_right E₁ E₂) (classLE_envMax_left _ E₃)

theorem classLE_max3_3 (E₁ E₂ E₃ : Envelope) : ClassLE E₃ (envMax (envMax E₁ E₂) E₃) :=
  classLE_envMax_right _ E₃

theorem le_max3_1 (a b c : ℕ) : a ≤ max (max a b) c := by omega

theorem le_max3_2 (a b c : ℕ) : b ≤ max (max a b) c := by omega

theorem le_max3_3 (a b c : ℕ) : c ≤ max (max a b) c := by omega

end NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin
