import Proof.Wire_3_5.UnionMachine.RadSeed
import Proof.Wire_3_5.FinalPass.ThrPtLift

/-! # RADIX, stage 5a (3): the fixed hash's table word at `Lmax`, built once (P3:2604)

The table builder (`Hash4.build_spec`, C1's stage 4) on the setup's cell: its eight streams are renamed into the cell
(`fs`), its sixteen registers into the setup's scratch (`fr`); its field scratch starts as `frame (binary ℓ₀ 0)`.

* `frameZ` / **`frameZ_spec`**: `frame 0^ℓ` on a blank stream, head back at `0`;
* **`buildL_spec`**: the lifted builder: from the renamed ready state, `levelWord M J W (rowF p ℓ M L all)` on the
  output's image, and the run's end state is `updW fs fr ω τ` for the builder's own end `τ`.

Paper quantity of the main type: the fixed hash's level table at the pool length (the list data's rows). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadTab
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.UnionMachine.RadFields NearCubicWires.WireExponent3_5.UnionMachine.RadWin
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.WireExponent3_5.FinalPass.ListEval

variable {ns nr : ℕ} (cap : ℕ)

/-- `frame 0^A` on `O` (position `OP`), head back at `0`. -/
def frameZ (O : Fin (ns + 1)) (OP A K T : Fin nr) : WM ns nr :=
  .seq (repRegW O OP A K T [true, false]) (.seq (emitW O OP [false]) (WM.rewind O OP))

theorem frame_zeros (ℓ : ℕ) : frame (List.replicate ℓ false) = reps ℓ [true, false] ++ [false] := by
  rw [frame_flat, flatMap_replicate]

theorem frameZ_spec (O : Fin (ns + 1)) (OP A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ OP)
    (hAO : A ≠ OP) (σ : WState ns nr) (ℓ : ℕ) (hO : σ.st O = []) (hOh : σ.sh O = 0) (hOP : σ.val OP = 0)
    (hK : σ.val K = 0) (hT : σ.val T = 0) (hA : σ.val A = ℓ) (hc : 2 * ℓ + 1 ≤ cap) :
    WExec cap (frameZ O OP A K T) σ (σ.sets O (frame (List.replicate ℓ false))) (60 * ℓ + 40) := by
  have s1 := repRegW_spec cap O OP A K T hAK hAT hKT hKO [true, false] σ hK hT (by rw [hO, hOh]; rfl) (by omega)
    (by rw [hOP, hA]; simp; omega)
  rw [hA] at s1
  have s2 := emitW_spec cap O OP [false] (appendO σ O OP (reps ℓ [true, false])) (ao_ho O OP σ _ (by rw [hO, hOh]; rfl))
    (by rw [ao_val_op, hOP, reps_len]; simp; omega)
  rw [appendO_append, ← frame_zeros] at s2
  have hlen : (frame (List.replicate ℓ false)).length = 2 * ℓ + 1 := by simp
  have s3 := wrewind_spec cap O OP (2 * ℓ + 1) (appendO σ O OP (frame (List.replicate ℓ false)))
    (by rw [ao_val_op, hOP, hlen]; omega) (by rw [ao_val_op, hOP, hlen]; omega)
  have e3 : ((appendO σ O OP (frame (List.replicate ℓ false))).setv OP 0).seth O
      ((appendO σ O OP (frame (List.replicate ℓ false))).sh O - (2 * ℓ + 1)) = σ.sets O (frame (List.replicate ℓ false)) := by
    apply WState.eq
    · funext j; by_cases hj : j = O
      · subst hj; simp [hOh]
      · simp [Function.update_apply, hj]
    · funext j; by_cases hj : j = O
      · subst hj; simp [hO]
      · simp [Function.update_apply, hj]
    · funext j; by_cases hj : j = OP
      · subst hj; simp [hOP]
      · simp [Function.update_apply, hj]
    · simp
  rw [e3] at s3
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by simp; omega)

/-- The builder's state read off the cell through the renamings. -/
def projW (fs : Fin 8 → Fin (ns + 1)) (fr : Fin 16 → Fin nr) (ω : WState ns nr) : HState :=
  ⟨fun i => ω.sh (fs i), fun i => ω.st (fs i), fun r => ω.val (fr r), ω.cell⟩

/-- **The table builder on the cell**: from the renamed ready state (window word, blank output, seed word, the field
scratch as frames, the modulus, heads `0`, the sixteen registers `0`), the lifted builder ends in `updW fs fr ω τ`
with the table word at `L` on the output's image (head `0`), the window, seed and modulus words kept. -/
theorem buildL_spec (fs : Fin 8 → Fin (ns + 1)) (hfs : Function.Injective fs) (fr : Fin 16 ↪ Fin nr)
    (ω : WState ns nr) (p ℓ M L J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ)
    (hcapS : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hcapW : (winWord M L J Wf).length ≤ cap)
    (hcapO : (levelWord M J Wf (rowF p ℓ M L all)).length + 1 ≤ cap) (hL : L ≤ cap) (hM : M ≤ cap) (hJ : J ≤ cap)
    (C : ℕ) (hC : ∀ j ≤ J, levelCost ℓ L M all.length j (pow (topW J Wf j)) (topW J Wf j) ≤ C)
    (hW : ω.st (fs 1) = winWord M L J Wf) (hO : ω.st (fs 0) = []) (hS : ω.st (fs 2) = seedWord ℓ all)
    (hP : ω.st (fs 3) = frame (binary ℓ p)) (hX : ∀ k : Fin 8, 4 ≤ k.val → ∃ v, ω.st (fs k) = frame (binary ℓ v))
    (hh : ∀ k : Fin 8, ω.sh (fs k) = 0) (hz : ∀ r : Fin 16, ω.val (fr r) = 0) :
    ∃ τ : HState, WExec cap (build.liftW fs fr) ω (updW fs fr ω τ)
        (buildCost M L J C (winWord M L J Wf).length (levelWord M J Wf (rowF p ℓ M L all)).length) ∧
      τ.st 0 = levelWord M J Wf (rowF p ℓ M L all) ∧ τ.sh 0 = 0 ∧ τ.st 1 = winWord M L J Wf ∧ τ.sh 1 = 0 ∧
      τ.st 2 = seedWord ℓ all ∧ τ.st 3 = frame (binary ℓ p) := by
  have hR : BReady p ℓ M L J Wf all (projW fs fr ω) :=
    ⟨hW, hh 1, hz _, hO, hh 0, hz _, hz _, hz _, hz _, hS, hh 2, hz _, hX 5 (by decide), hh 5, hX 6 (by decide), hh 6,
      hX 7 (by decide), hh 7, hX 4 (by decide), hh 4, hP, hh 3, hz _, hz _, hz _, hz _, hz _, hz _, hz _, hz _, hz _,
      hz _⟩
  obtain ⟨τ, hx, h0, h0h, h1, h1h, h2, h3, -, -, -, -, -⟩ :=
    build_spec cap p ℓ M L J Wf all (projW fs fr ω) hℓ hcapS hcapW hcapO hL hM hJ C hC hR
  have hLW : LiftW fs fr ω (projW fs fr ω) := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  exact ⟨τ, WExec.liftW_upd cap hfs fr.injective hx ω hLW, h0, h0h, h1, h1h, h2, h3⟩

end NearCubicWires.WireExponent3_5.UnionMachine.RadTab
