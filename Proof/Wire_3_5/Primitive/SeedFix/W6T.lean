import Proof.Wire_3_5.Primitive.SeedFix.W6S

/-! # W6, part 20: from `1^{|𝒢|}` and `1^E` to the cutoff and `τ₀`

P3:2552-2557 (`K = 8(|𝒢|+1)n^D`), P3:2552-2553 (the cutoff), P3:2596-2597 (`τ₀`): the counts proof 1's program left on
block C's and block E's tape `1` read into `rNG`, `rE` (`SymDec.readU_spec`), then `kW`, `cutW`, `tauW`:
* **`MidBoundsA`** (the capacity facts of this part and of the prime rows), **`midA_exec`**.

Paper quantities of the main type: `|𝒢|`, `E`, `K`, the cutoff, `τ₀`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

variable (cap : ℕ)

/-- **The capacity facts** of the counts, `K`, the cutoff, `τ₀` and the prime rows. -/
structure MidBoundsA (n g E D cut : ℕ) : Prop where
  u1 : g ≤ cap
  u2 : E ≤ cap
  k1 : 1 ≤ cap
  k2 : ∀ k ≤ D, n ^ k ≤ cap
  k3 : 8 * ((g + 1) * n ^ D) + 8 ≤ cap
  k4 : n ≤ cap
  k5 : g + 1 ≤ cap
  c1 : cut ≤ cap
  c2 : cut + 2 ≤ cap
  p1 : (Data.unaryList (PrimThrW.Joins.primesList cut)).length + cut + 3 ≤ cap
  p2 : (PrimThrW.Joins.primesList cut).sum + cut + 2 ≤ cap

def midAW (D : ℕ) : WP :=
  .seq (SymDec.readUW (sBC 1) rNG) (.seq (SymDec.readUW (sBE 1) rE) (.seq (kW D) (.seq cutW tauW)))

theorem midA_exec (σ : WL) (n g E D K cut d : ℕ) (h48 : σ.val 48 = n) (hz : ∀ r : Fin 80, r.val < 48 → σ.val r = 0)
    (z53 : σ.val 53 = 0) (z54 : σ.val 54 = 0) (z55 : σ.val 55 = 0) (z56 : σ.val 56 = 0) (z57 : σ.val 57 = 0)
    (hC : σ.st (sBC 1) = List.replicate g true) (hCh : σ.sh (sBC 1) = 0)
    (hE : σ.st (sBE 1) = List.replicate E true) (hEh : σ.sh (sBE 1) = 0)
    (hK : K = 8 * (g + 1) * n ^ D) (hcut : cut = SupplierPrime.canonicalPrimeCutoff E K) (hd : d = Nat.clog 2 cut)
    (hb : MidBoundsA cap n g E D cut) :
    WExec cap (midAW D) σ ⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 d, σ.cell⟩
      (7 * g + 7 * E + (D + 1) * opU cap + 40 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  have hCE : sBE 1 ≠ sBC 1 := by decide
  have e1 := SymDec.readU_spec cap (sBC 1) rNG g 0 σ hC hCh z53 (by have := hb.u1; omega)
  rw [Nat.zero_add] at e1
  have e2 := SymDec.readU_spec cap (sBE 1) rE E 0 ((σ.seth (sBC 1) g).setv rNG g) hE
    (by show Function.update σ.sh (sBC 1) g (sBE 1) = 0; rw [Function.update_of_ne hCE]; exact hEh)
    (by show Function.update σ.val 53 g 54 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z54) (by have := hb.u2; omega)
  rw [Nat.zero_add] at e2
  have e3 := (kW_rr cap D (Function.update (Function.update σ.val 53 g) 54 E) n g (by show (Function.update (Function.update σ.val 53 g) 54 E) 48 = n; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact h48)
    (by show (Function.update (Function.update σ.val 53 g) 54 E) 53 = g; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (fun r hr => by have n53 : r ≠ 53 := fun h => absurd hr (by rw [h]; decide); have n54 : r ≠ 54 := fun h => absurd hr (by rw [h]; decide); simp only [Function.update_apply, n53, n54, if_false]; exact hz r (by omega))
    (by show (Function.update (Function.update σ.val 53 g) 54 E) 55 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z55) hb.k1 hb.k2 hb.k3 hb.k4 hb.k5)
    ((((σ.seth (sBC 1) g).setv rNG g).seth (sBE 1) E).setv rE E) rfl
  rw [← hK] at e3
  have e4 := (cutW_rr cap (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) E K (by show (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 54 = E; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 55 = K; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (fun r hr => by have n53 : r ≠ 53 := fun h => absurd hr (by rw [h]; decide); have n54 : r ≠ 54 := fun h => absurd hr (by rw [h]; decide); have n55 : r ≠ 55 := fun h => absurd hr (by rw [h]; decide); simp only [Function.update_apply, n53, n54, n55, if_false]; exact hz r (by omega))
    (by show (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z56) (hcut ▸ hb.c1))
    (⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K, σ.cell⟩ : WL) rfl
  rw [← hcut] at e4
  have e5 := (tauW_rr cap (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) cut (by show (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 56 = cut; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by show (Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut) 57 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z57)
    (fun r hr => by have n53 : r ≠ 53 := fun h => absurd hr (by rw [h]; decide); have n54 : r ≠ 54 := fun h => absurd hr (by rw [h]; decide); have n55 : r ≠ 55 := fun h => absurd hr (by rw [h]; decide); have n56 : r ≠ 56 := fun h => absurd hr (by rw [h]; decide); simp only [Function.update_apply, n53, n54, n55, n56, if_false]; exact hz r (by omega)) hb.c2)
    (⟨Function.update (Function.update σ.sh (sBC 1) g) (sBE 1) E, σ.st, Function.update (Function.update (Function.update (Function.update σ.val 53 g) 54 E) 55 K) 56 cut, σ.cell⟩ : WL) rfl
  rw [← hd] at e5
  exact WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by omega)

end NearCubicWires.WireExponent3_5.PrimT.W6
