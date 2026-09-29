import Proof.Wire_3_5.FinalPass.S5TWin2

/-! # S5-THR, part 15: stage 4's table builder on renamed streams (P3:2150-2157, 1419-1488)

`Hash4.build` (the table builder, `build_spec`) runs on its own layout `WState 7 16`. On a larger layout it runs
renamed (`WM.liftW`, `WExec.liftW`): its eight streams by an injective `fs`, its sixteen registers by an injective `fr`.

* `hview` (the builder's view of a larger state), `hview_ready` (its ready state from the renamed streams: the input
  word, the seed word, the modulus, four framed zeros, a blank output, every head and register at `0`);
* `levelCost_le` (one level record's cost at the longest record), `winRec_le` (a record inside the input word);
* **`build_lift`**: the renamed builder writes `levelWord M J W (rowF p ℓ M M all)` on the renamed output, and keeps
  every stream and register outside the images.

Paper quantity of the main type: stage 4's table word (the fixed hash's level sets, `filt:soft`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-- The builder's view of a larger state through `fs`, `fr`. -/
def hview (fs : Fin 8 → Fin (ns + 1)) (fr : Fin 16 → Fin nr) (ω : WState ns nr) : Hash4.HState :=
  ⟨fun i => ω.sh (fs i), fun i => ω.st (fs i), fun r => ω.val (fr r), ω.cell⟩

theorem hview_lift (fs : Fin 8 → Fin (ns + 1)) (fr : Fin 16 → Fin nr) (ω : WState ns nr) :
    LiftW fs fr ω (hview fs fr ω) := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem hview_ready (fs : Fin 8 → Fin (ns + 1)) (fr : Fin 16 → Fin nr) (ω : WState ns nr) (p ℓ M L J : ℕ)
    (Wf : ℕ → ℕ) (all : List ℕ)
    (hO : ω.st (fs 0) = []) (hW : ω.st (fs 1) = Hash4.winWord M L J Wf) (hS : ω.st (fs 2) = Hash4.seedWord ℓ all)
    (hP : ω.st (fs 3) = frame (binary ℓ p)) (hX : ω.st (fs 4) = frame (binary ℓ 0))
    (hA : ω.st (fs 5) = frame (binary ℓ 0)) (hN : ω.st (fs 6) = frame (binary ℓ 0))
    (hT : ω.st (fs 7) = frame (binary ℓ 0)) (hsh : ∀ i, ω.sh (fs i) = 0) (hv : ∀ r, ω.val (fr r) = 0) :
    Hash4.BReady p ℓ M L J Wf all (hview fs fr ω) := by
  refine ⟨hW, hsh 1, hv 13, hO, hsh 0, hv 12, hv 0, hv 3, hv 1, hS, hsh 2, hv 8, ⟨0, hA⟩, hsh 5, ⟨0, hN⟩, hsh 6,
    ⟨0, hT⟩, hsh 7, ⟨0, hX⟩, hsh 4, hP, hsh 3, hv 4, hv 5, hv 6, hv 7, hv 9, hv 10, hv 11, hv 14, hv 2, hv 15⟩

/-- One level record's cost is at most the cost at the last level and the longest record. -/
theorem levelCost_le (ℓ L M n j pw w J Z : ℕ) (hj : j ≤ J) (hp : pw ≤ Z) (hw : w ≤ Z) :
    Hash4.levelCost ℓ L M n j pw w ≤ Hash4.levelCost ℓ L M n J Z Z := by
  unfold Hash4.levelCost Hash4.stepCost
  have h1 : L * (Hash4.hornerCost ℓ n + (18 * j + ℓ * 25 + 3 * j + 8 + 10 * ℓ + 6) + ℓ * 41 + 60 + ℓ * 41 + 27) ≤
      L * (Hash4.hornerCost ℓ n + (18 * J + ℓ * 25 + 3 * J + 8 + 10 * ℓ + 6) + ℓ * 41 + 60 + ℓ * 41 + 27) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- A level record lies inside the input word. -/
theorem winRec_le (M L J : ℕ) (Wf : ℕ → ℕ) (j : ℕ) (hj : j ≤ J) :
    ListEval.pow (ListEval.topW J Wf j) ≤ (Hash4.winWord M L J Wf).length ∧
      ListEval.topW J Wf j ≤ (Hash4.winWord M L J Wf).length := by
  have hmem : j ∈ ListEval.levels J := by simp [ListEval.levels]; omega
  have h1 : (Hash4.winRec J Wf j).length ≤ ((ListEval.levels J).flatMap (Hash4.winRec J Wf)).length := by
    rw [List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map.2 ⟨j, hmem, rfl⟩)
  have h2 : (Hash4.winRec J Wf j).length = ListEval.pow (ListEval.topW J Wf j) + ListEval.topW J Wf j + 3 := by
    simp [Hash4.winRec, ListEval.unary]; omega
  have h3 : ((ListEval.levels J).flatMap (Hash4.winRec J Wf)).length ≤ (Hash4.winWord M L J Wf).length := by
    simp [Hash4.winWord]; omega
  omega

/-- **The table builder on renamed streams and registers.** -/
theorem build_lift (fs : Fin 8 → Fin (ns + 1)) (hfs : Function.Injective fs) (fr : Fin 16 → Fin nr)
    (hfr : Function.Injective fr) (ω : WState ns nr) (p ℓ M J : ℕ) (Wf : ℕ → ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ)
    (hO : ω.st (fs 0) = []) (hW : ω.st (fs 1) = Hash4.winWord M M J Wf) (hS : ω.st (fs 2) = Hash4.seedWord ℓ all)
    (hP : ω.st (fs 3) = frame (binary ℓ p)) (hX : ω.st (fs 4) = frame (binary ℓ 0))
    (hA : ω.st (fs 5) = frame (binary ℓ 0)) (hN : ω.st (fs 6) = frame (binary ℓ 0))
    (hT : ω.st (fs 7) = frame (binary ℓ 0)) (hsh : ∀ i, ω.sh (fs i) = 0) (hv : ∀ r, ω.val (fr r) = 0)
    (hcapS : (Hash4.seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hcapW : (Hash4.winWord M M J Wf).length ≤ cap)
    (hcapO : (ListEval.levelWord M J Wf (Hash4.rowF p ℓ M M all)).length + 1 ≤ cap) (hM : M ≤ cap) (hJ : J ≤ cap) :
    ∃ ω', WExec cap (WM.liftW fs fr Hash4.build) ω ω'
        (Hash4.buildCost M M J (Hash4.levelCost ℓ M M all.length J (Hash4.winWord M M J Wf).length
          (Hash4.winWord M M J Wf).length) (Hash4.winWord M M J Wf).length
          (ListEval.levelWord M J Wf (Hash4.rowF p ℓ M M all)).length) ∧
      ω'.st (fs 0) = ListEval.levelWord M J Wf (Hash4.rowF p ℓ M M all) ∧
      (∀ j, (∀ i, fs i ≠ j) → ω'.sh j = ω.sh j ∧ ω'.st j = ω.st j) ∧
      (∀ q, (∀ r, fr r ≠ q) → ω'.val q = ω.val q) := by
  obtain ⟨τ, e, h1, _⟩ := Hash4.build_spec cap p ℓ M M J Wf all (hview fs fr ω) hℓ hcapS
    hcapW hcapO hM hM hJ _ (fun j hj => levelCost_le ℓ M M all.length j _ _ J _ hj (winRec_le M M J Wf j hj).1
      (winRec_le M M J Wf j hj).2)
    (hview_ready fs fr ω p ℓ M M J Wf all hO hW hS hP hX hA hN hT hsh hv)
  obtain ⟨ω', e', hL, hOut⟩ := WExec.liftW cap cap le_rfl fs hfs fr hfr e ω (hview_lift fs fr ω)
  exact ⟨ω', e', by rw [hL.st, h1], hOut.1, hOut.2⟩

end NearCubicWires.WireExponent3_5.FinalPass.S5T
