import Proof.Packets.SrcStartStages

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Regs
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
noncomputable section

/-- The slot map of a stage: named local tapes are registers, the others the scratch block from `s`. -/
def nslot {NL n : ℕ} (nm : Fin n → Option (Fin NL)) (s : ℕ) (hs : s + n ≤ NL) (j : Fin n) : Fin NL :=
  match nm j with
  | some r => r
  | none => ⟨s + j.val, by have := j.isLt; omega⟩

theorem nslot_some {NL n : ℕ} (nm : Fin n → Option (Fin NL)) (s : ℕ) (hs : s + n ≤ NL) (j : Fin n) (r : Fin NL)
    (h : nm j = some r) : nslot nm s hs j = r := by
  unfold nslot; rw [h]

theorem nslot_none {NL n : ℕ} (nm : Fin n → Option (Fin NL)) (s : ℕ) (hs : s + n ≤ NL) (j : Fin n)
    (h : nm j = none) : (nslot nm s hs j).val = s + j.val := by
  unfold nslot; rw [h]

theorem nslot_inj {NL n : ℕ} (nm : Fin n → Option (Fin NL)) (s : ℕ) (hs : s + n ≤ NL)
    (hinj : ∀ i j r, nm i = some r → nm j = some r → i = j) (hlow : ∀ j r, nm j = some r → r.val < s) :
    Function.Injective (nslot nm s hs) := by
  intro i j h
  rcases hi : nm i with _ | ri <;> rcases hj : nm j with _ | rj
  · have e1 := nslot_none nm s hs i hi
    have e2 := nslot_none nm s hs j hj
    have hv := congrArg Fin.val h
    exact Fin.ext (by omega)
  · have e1 := nslot_none nm s hs i hi
    have e2 := nslot_some nm s hs j rj hj
    have l := hlow j rj hj
    have hv := congrArg Fin.val h
    rw [e2] at hv
    omega
  · have e1 := nslot_some nm s hs i ri hi
    have e2 := nslot_none nm s hs j hj
    have l := hlow i ri hi
    have hv := congrArg Fin.val h
    rw [e1] at hv
    omega
  · have e1 := nslot_some nm s hs i ri hi
    have e2 := nslot_some nm s hs j rj hj
    rw [e1, e2] at h
    subst h
    exact hinj i j ri hi hj

/-- **One stage of the register file.** -/
theorem nstage {NL R n st c : ℕ} {M : Machine n st} {tin tout : Fin n → List Bool}
    (h : Step M c (fun _ => 0) tin (fun _ => 0) tout)
    (nm : Fin n → Option (Fin NL)) (s : ℕ) (hs : s + n ≤ NL)
    (hinj : ∀ i j r, nm i = some r → nm j = some r → i = j) (hlow : ∀ j r, nm j = some r → r.val < s)
    (E : Fin NL → List Bool)
    (hin : ∀ j r, nm j = some r → E r = ZeroPadding.pad R (tin j))
    (hsc : ∀ j, nm j = none → ZeroPadding.pad R (tin j) = List.replicate R false)
    (hfresh : ∀ x : Fin NL, s ≤ x.val → E x = List.replicate R false) :
    ∃ E' : Fin NL → List Bool, Step (RecoveryFocus.machine (nslot nm s hs) M) c (fun _ => 0) E (fun _ => 0) E' ∧
      (∀ j r, nm j = some r → E' r = ZeroPadding.pad R (tout j)) ∧
      (∀ x : Fin NL, x.val < s → (∀ j, nm j ≠ some x) → E' x = E x) ∧
      (∀ x : Fin NL, s + n ≤ x.val → E' x = List.replicate R false) := by
  have hi := nslot_inj nm s hs hinj hlow
  have st := Stages.stage0 h (nslot nm s hs) hi R E (by
    intro j
    rcases e : nm j with _ | r
    · rw [hsc j e]
      exact hfresh _ (by rw [nslot_none nm s hs j e]; omega)
    · rw [nslot_some nm s hs j r e]
      exact hin j r e)
  refine ⟨_, st, ?_, ?_, ?_⟩
  · intro j r e
    rw [← nslot_some nm s hs j r e, install_slot _ hi]
  · intro x hx hn
    apply install_other
    intro j hj
    rcases e : nm j with _ | r
    · have := nslot_none nm s hs j e
      rw [hj] at this
      omega
    · rw [nslot_some nm s hs j r e] at hj
      subst hj
      exact hn j e
  · intro x hx
    rw [install_other _ _ _ _ ?_]
    · exact hfresh x (by omega)
    intro j hj
    rcases e : nm j with _ | r
    · have := nslot_none nm s hs j e
      rw [hj] at this
      have := j.isLt
      omega
    · rw [nslot_some nm s hs j r e] at hj
      have := hlow j r e
      rw [hj] at this
      omega

/-! ## Naming shapes -/

end
end NearCubicWires.SourceStart.Regs

