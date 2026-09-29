import Proof.Wire_3_5.Primitive.Writers.SBFieldD

/-! # SB, part 11: the field phase as one machine step

* **`field_step`**: from `23` blank streams `Fs` and `Rb 0 = ℓ ≥ 1` (the rest of `Rb` at `0`), `fieldM` leaves the trace
  mask `frame (binary ℓ (GF2.tau p ℓ))` on `Fs 0` and the modulus `frame (binary ℓ p)` on `Fs 1` (`p =
  GF.firstPrimitive ℓ`), `0^{4ℓ+6}` on `Fs 2 … 22`, every head of `Fs` at `0`, every `Rb` at `0`, the cell and
  everything else unchanged, within `fieldCost`.

Paper quantity of the main type: S4's field words `4`, `5` (`Filt.tauWord`, `Filt.modWord`, P3:2053-2055, 2932-2941). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBField
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SBWords
open NearCubicWires.WireExponent3_5.PrimAsm.SBFieldA NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound

section Step
variable {ns nr : ℕ} (cap : ℕ) (Fs : Fin 23 ↪ Fin (ns + 1)) (Rb : Fin 16 ↪ Fin nr)

theorem mIdx_ne2 (j : Fin 17) (hj : j.val ≠ 0) : mIdx j ≠ 2 := by
  intro e; have := congrArg Fin.val e; rw [mIdx_val] at this; split_ifs at this <;> omega

theorem mIdx_range (j : Fin 17) : 1 ≤ (mIdx j).val ∧ (mIdx j).val ≤ 17 := by
  rw [mIdx_val]; split_ifs <;> omega

theorem field_step (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (σ : WState ns nr) (hc : 4 * ℓ + 6 ≤ cap)
    (hbl : ∀ k, σ.st (Fs k) = [] ∧ σ.sh (Fs k) = 0) (hL : σ.val (Rb 0) = ℓ)
    (hz : ∀ j : Fin 16, j ≠ 0 → σ.val (Rb j) = 0) :
    ∃ τ : WState ns nr, Step (fieldM Fs Rb) (fieldCost cap ℓ ((eraseL Fs).map fun i => i.val))
        (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      τ.st (Fs 0) = frame (binary ℓ (GF2.tau (GF.firstPrimitive ℓ) ℓ)) ∧
      τ.st (Fs 1) = frame (binary ℓ (GF.firstPrimitive ℓ)) ∧
      (∀ k : Fin 23, 2 ≤ k.val → τ.st (Fs k) = List.replicate (4 * ℓ + 6) false) ∧ (∀ k, τ.sh (Fs k) = 0) ∧
      (∀ j, τ.val (Rb j) = 0) ∧ (∀ i, (∀ k, Fs k ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, (∀ j, Rb j ≠ r) → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have R : ∀ {a b : Fin 16}, a ≠ b → Rb a ≠ Rb b := fun h => rbne Rb h
  -- 1: `1^ℓ` on `Fs 2`
  have e1 := copyOnes_spec cap (Fs 2) (Rb 0) (Rb 1) (Rb 3) (Rb 2) (R (by decide)) (R (by decide)) (R (by decide))
    (R (by decide)) ℓ σ hL (hz 1 (by decide)) (hz 3 (by decide)) (hz 2 (by decide)) (hbl 2).1 (hbl 2).2 (by omega)
  set σ1 := σ.sets (Fs 2) (List.replicate ℓ true) with hσ1
  have s1 := Exec.step (WExec.exec cap e1)
  -- 2: the modulus machine on `mMap Fs`
  obtain ⟨tout, hM, t0, t12, tlen⟩ := Modulus.modulus_full ℓ hℓ
  have eH : (fun j => σ1.sh (mMap Fs j)) = fun _ => 0 := funext fun j => by simp [hσ1, mMap, (hbl _).2]
  have eA : (fun j => σ1.st (mMap Fs j)) = fun i : Fin 17 => if i.val = 0 then List.replicate ℓ true else [] := by
    funext j
    by_cases hj : j.val = 0
    · have : j = 0 := Fin.ext hj
      subst this
      simp [hσ1, mMap, show mIdx 0 = 2 from rfl]
    · rw [if_neg hj]
      have hne : Fs (mIdx j) ≠ Fs 2 := fsne Fs (mIdx_ne2 j hj)
      simp [hσ1, mMap, Function.update_of_ne hne, (hbl _).1]
  have hM' : Step Modulus.modM (Modulus.modCost ℓ) (fun j => σ1.sh (mMap Fs j)) (fun j => σ1.st (mMap Fs j))
      (fun _ => 0) tout := by rw [eH, eA]; exact hM
  have s2 := dockS cap (mMap Fs) (mMap_inj Fs) σ1 hM'
  set σ2 := updS (mMap Fs) σ1 (fun _ => 0) tout with hσ2
  have st2 : ∀ j, σ2.st (mMap Fs j) = tout j := fun j => by simp [hσ2, updS, install_slot _ (mMap_inj Fs)]
  have sh2 : ∀ j, σ2.sh (mMap Fs j) = 0 := fun j => by simp [hσ2, updS, dockH_slot _ (mMap_inj Fs)]
  have oth2 : ∀ i, (∀ j, mMap Fs j ≠ i) → σ2.st i = σ1.st i ∧ σ2.sh i = σ1.sh i := fun i hi =>
    ⟨by simp [hσ2, updS, install_other _ _ _ _ hi], by simp [hσ2, updS, dockH_other _ _ _ _ hi]⟩
  have v2 : σ2.val = σ.val := rfl
  have c2 : σ2.cell = σ.cell := rfl
  have offk : ∀ k : Fin 23, (k.val = 0 ∨ 18 ≤ k.val) → ∀ j, mMap Fs j ≠ Fs k := by
    intro k hk j e
    have := Fs.injective e
    have hr := mIdx_range j
    rw [this] at hr
    omega
  -- 3: the word tail
  obtain ⟨τ, e3, h0, h1, hE, hsh, hv, hout, hvo, hcl⟩ := w3_spec cap Fs Rb ℓ hℓ σ2 hc
    (by rw [show Fs 1 = mMap Fs 12 from rfl, st2]; exact t12)
    (fun k h2 h17 => by
      rw [← mIdx_of k h2 h17]
      show (σ2.st (mMap Fs _)).length ≤ _
      rw [st2]; exact tlen _)
    (fun k hk => by
      rw [(oth2 (Fs k) (offk k hk)).1, hσ1, WState.sets_st,
        Function.update_of_ne (fsne Fs (by intro e; rw [e] at hk; simp at hk))]
      exact (hbl k).1)
    (fun k => by
      by_cases hk : 1 ≤ k.val ∧ k.val ≤ 17
      · by_cases h1 : k.val = 1
        · rw [show k = mIdx 12 from Fin.ext (by rw [mIdx_val]; simp [h1])]; exact sh2 12
        · rw [← mIdx_of k (by omega) hk.2]; exact sh2 _
      · rw [(oth2 (Fs k) (offk k (by omega))).2]
        simp [hσ1, (hbl k).2])
    (by rw [v2]; exact hL) (fun j hj => by rw [v2]; exact hz j hj)
  have s3 := Exec.step (WExec.exec cap e3)
  refine ⟨τ, (s1.seq s2).seq s3, h0, by rw [h1, show Fs 1 = mMap Fs 12 from rfl, st2]; exact t12, hE, hsh, hv, ?_, ?_, ?_⟩
  · intro i hi
    have hm : ∀ j, mMap Fs j ≠ i := fun j e => hi _ e
    obtain ⟨a, b⟩ := hout i hi
    obtain ⟨c, d⟩ := oth2 i hm
    refine ⟨by rw [a, c, hσ1, WState.sets_st, Function.update_of_ne (fun e => hi 2 e.symm)], by rw [b, d]; rfl⟩
  · intro r hr; rw [hvo r hr, v2]
  · rw [hcl, c2]

end Step

end NearCubicWires.WireExponent3_5.PrimAsm.SBField
