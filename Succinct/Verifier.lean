import Succinct.Body
import CheckedPCPP.WMXReady
import Proof.MachineModel.UAcceptanceCarrier

/-!
# 𝒱_G, part 9: the succinct verifier as one ordinary verifier

Paper: lem:succinct-verifier (app:multitape), stage (4): "It runs `𝒟` on `tt_N(B)`, using that work tape as the
input tape of `𝒟`, its own witness tape as the witness tape of `𝒟` … and it accepts exactly when `𝒟` accepts."
The machine is the body (`Succinct.Body`, one compiled `WMX` program) followed by the hierarchy verifier `H.verifier`
docked on the body's streams `5 … tH + 4` (`RecoveryFocus.machine`), joined by `Composition.machine`; the tapes are
renamed so that the verifier's witness tape `1` is the body's stream `1` (the body's layout uses tape `1` for its
result cell). Acceptance is `H.verifier`'s acceptance of its final control state.
**`verifierV_run`**: on every input `u` and witness `y`, the run halts within
`bodyCost + 1 + H.time N` steps and accepts iff `H.verifier` accepts `(bodyTable G u, prefixBits y (H.time N))`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.Platform
open NearCubicGates.Close.CheckedPCPP (coldBank ConfRel runFrom_rel coldBank_s coldBank_c coldBank_r)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_val cTape_val rTape_val wenc_A_c)

/-- A `WMX` derivation from the cold start (heads and registers `0`, blank cell) is a run of the compiled machine
from the cold bank, ending with the end state's heads and streams. -/
theorem cold_run {ns nr cap : ℕ} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WXExec cap P σ τ n)
    (hsh : ∀ i, σ.sh i = 0) (hval : ∀ r, σ.val r = 0) (hcell : σ.cell = false) :
    ∃ r, runFrom P.compile n (initialConfiguration P.compile (coldBank σ)) = some r ∧
      r.final.heads = (wenc cap τ).H ∧ ∀ i, r.final.tapes (sTape i) = τ.st i := by
  obtain ⟨r, hr, hh, ht, _⟩ := WXExec.run cap h hsh hval
  let E : Fin (ns + 2 + nr) → Prop := fun j => ∃ i, j = sTape i
  have hrel : ConfRel E (initialConfiguration P.compile (wenc cap σ).A)
      (initialConfiguration P.compile (coldBank σ)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro j
      simp only [initialConfiguration]
      rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s, coldBank_s]; exact RdEq.refl _
      · rw [wenc_A_c, coldBank_c, hcell]; exact rdEq_blank _ (by simp)
      · rw [wenc_A_r, coldBank_r, hval q, regTape_zero]; exact rdEq_blank _ (by simp)
    · rintro j ⟨i, rfl⟩
      simp only [initialConfiguration]
      rw [wenc_A_s, coldBank_s]
  obtain ⟨r', hr', hrel', _⟩ := runFrom_rel P.compile E n hrel r hr
  refine ⟨r', hr', by rw [← hrel'.heads, hh], fun i => ?_⟩
  rw [← hrel'.exact (sTape i) ⟨i, rfl⟩, ht, wenc_A_s]

section Machine
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (G : ℕ)

/-- The hierarchy verifier's tape count. -/
def tH : ℕ := H.verifier.tapeCount

theorem two_le_tH : 2 ≤ tH H := H.verifier.twoTapes

/-- The succinct verifier's tape count. -/
abbrev vT : ℕ := (tH H + 4) + 2 + nrV

/-- The compiled body. -/
noncomputable def bodyM := (body G H.coefficient k (tH H) (two_le_tH H)).compile

/-- The hierarchy verifier's tapes: the body's streams `5 … tH + 4`. -/
def hmap : Fin (tH H) → Fin (vT H) := fun j => sTape (nr := nrV) (bs (tH H) (j.val + 5) (by omega))

theorem hmap_inj : Function.Injective (hmap H) := by
  intro a b h
  have := congrArg Fin.val h
  simp [hmap, sTape, bs] at this
  ext; omega

/-- The docked hierarchy verifier. -/
noncomputable def hDock := RecoveryFocus.machine (hmap H) H.verifier.machine

/-- The body, then the hierarchy verifier. -/
noncomputable def m0 := Composition.machine (bodyM H G) (hDock H)

/-- The tape renaming: the verifier's tapes `1` and `2` are swapped (the body's result cell is its tape `1`, its
witness stream its tape `2`). -/
def swap12 (t : ℕ) (ht : 3 ≤ t) : Fin t → Fin t :=
  fun j => if j.val = 1 then ⟨2, by omega⟩ else if j.val = 2 then ⟨1, by omega⟩ else j

theorem swap12_swap12 (t : ℕ) (ht : 3 ≤ t) (j : Fin t) : swap12 t ht (swap12 t ht j) = j := by
  unfold swap12; ext; split_ifs <;> simp_all <;> omega

theorem swap12_inj (t : ℕ) (ht : 3 ≤ t) : Function.Injective (swap12 t ht) := by
  intro a b h; rw [← swap12_swap12 t ht a, h, swap12_swap12]

theorem three_le_vT : 3 ≤ vT H := by have := two_le_tH H; unfold vT; omega

/-- **The succinct verifier `𝒱_G`** (paper lem:succinct-verifier). -/
noncomputable def verifierV : OrdinaryVerifier where
  tapeCount := vT H
  stateCount := (body G H.coefficient k (tH H) (two_le_tH H)).size + H.verifier.stateCount
  twoTapes := by have := three_le_vT H; omega
  machine := RecoveryFocus.machine (swap12 (vT H) (three_le_vT H)) (m0 H G)
  accepting := fun st => if h : (body G H.coefficient k (tH H) (two_le_tH H)).size ≤ st.val then
    H.verifier.accepting ⟨st.val - (body G H.coefficient k (tH H) (two_le_tH H)).size, by have := st.isLt; omega⟩
    else false

end Machine

end NearCubicGates.Close.Succinct
