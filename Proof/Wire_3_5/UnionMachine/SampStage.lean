import Proof.Wire_3_5.UnionMachine.SampRegs

/-! # C6 tail, item 2: the sample expansion, the `SampStage`

"Fix the seed [...] The sample positions are `S_j = π(f(λ_j))`" (`samp:seed`, P3:2932-2937): "Evaluate a uniformly
random polynomial of degree `2h−1` at those labels and project each value to `k` binary coordinates", printed in the
final pass's format (`sampleWord`, P3:3044-3053). One machine on `31` tapes: `0` the framed seed bits, `2` `1^{kh}`,
`3` `1^Q`, `4` `1^ℓ`, `5` the modulus word, `6` the output (the expansion's word program's streams, `SampRun`), its
cell `1`, its registers `12`–`27` and its log `28`; the register writer's cell `29` and log `30`:
1. the register writer's cell, then the register writer (`SampRegs.regs_spec`, docked): the register tapes
   `regTape (18ℓ + 20) 0`;
2. the word program's cell, then the word program (`SampRun.main_spec`, docked): the output `sampleWord kh` of the
   positions `posC P (bitsNum s) j`, `j < Q`;
within `sampCost P = 2^{20}·(Q + 1)·(ℓ + 1)^4` (**`samp_run`**, **`sampStage`**).

Paper quantity of the main type: the sample positions `posC P (bitsNum s)` printed in the final pass's format. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SampStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.PrimT.C4Iface (SampStage sampIn sampCost seedPairs)
open NearCubicWires.WireExponent3_5.UnionMachine.TailAsm (cell_dock zeroH)

/-! ## The layout -/

/-- The register writer's tapes: its ruler at `4`, its cell at `29`, its targets at `12`–`27`, its log at `30`. -/
def sl1 (j : Fin 19) : Fin 31 :=
  ⟨if j.val = 0 then 4 else if j.val = 1 then 29 else if j.val = 18 then 30 else j.val + 10, by split_ifs <;> omega⟩

theorem sl1_inj : Function.Injective sl1 := by decide

/-- The word program's tapes: `0`–`28`. -/
def sl2 (j : Fin 29) : Fin 31 := ⟨j.val, by omega⟩

theorem sl2_inj : Function.Injective sl2 := fun a b h => Fin.ext (by have e := congrArg Fin.val h; exact e)

/-- The expansion. -/
noncomputable def sampM :=
  Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (29 : Fin 31)) NearCubicWires.WireExponent3_5.PrimT.cellM)
    (Composition.machine (RecoveryFocus.machine sl1 (Rewind.machine SampRegs.regW.toProg.compile))
      (Composition.machine (RecoveryFocus.machine (fun _ : Fin 1 => (1 : Fin 31)) NearCubicWires.WireExponent3_5.PrimT.cellM)
        (RecoveryFocus.machine sl2 (Rewind.machine SampRun.mainW.toProg.compile))))

/-! ## The banks -/

theorem inst1 (c : Fin 31) (B : Fin 31 → List Bool) (v : List Bool) (i : Fin 31) :
    install (fun _ : Fin 1 => c) B (fun _ => v) i = if i = c then v else B i := by
  by_cases h : i = c
  · subst h; rw [if_pos rfl]
    exact install_slot (fun _ : Fin 1 => i) (fun a b _ => Subsingleton.elim a b) B (fun _ => v) 0
  · rw [if_neg h]; exact install_other _ _ _ i (fun _ e => h e.symm)

/-- The register writer's entry state. -/
def σR (ℓ : ℕ) : WState 16 0 := ⟨fun _ => 0, fun i => if i.val = 0 then List.replicate ℓ true else [], fun r => r.elim0, false⟩

/-- The word program's entry tapes, and the expansion's input elsewhere. -/
def E (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (i : Fin 31) : List Bool :=
  if i.val = 1 then [false] else if 12 ≤ i.val ∧ i.val < 28 then regTape (18 * P.ell + 20) 0
  else sampIn (0 : Fin 31) 2 3 4 5 P s i

theorem wenc2_val (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (j : Fin 29) :
    Fin.addCases (m := 10 + 2 + 16) (n := 1) (motive := fun _ => List Bool)
      (wenc (18 * P.ell + 20) (SampRun.σE P s)).A (fun _ => []) j = E P s (sl2 j) := by
  fin_cases j <;> rfl

theorem wenc1_val (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (j : Fin 19) :
    install (fun _ : Fin 1 => (29 : Fin 31)) (sampIn (0 : Fin 31) 2 3 4 5 P s) (fun _ => [false]) (sl1 j) =
      Fin.addCases (m := 16 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σR P.ell)).A (fun _ => []) j := by
  rw [inst1]; fin_cases j <;> rfl

theorem sl1_reg (k : ℕ) (hk : k < 16) : (sl1 ⟨k + 2, by omega⟩).val = k + 12 := by
  show (if k + 2 = 0 then 4 else if k + 2 = 1 then 29 else if k + 2 = 18 then 30 else k + 2 + 10) = k + 12
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem sl1_ne (i : Fin 31) (hi : i.val < 29) (h4 : i.val ≠ 4) (hr : ¬ (12 ≤ i.val ∧ i.val < 28)) :
    ∀ j, sl1 j ≠ i := by
  intro j hj
  have := congrArg Fin.val hj
  simp only [sl1] at this
  split_ifs at this <;> omega

/-! ## The step bound -/

theorem horner_le (ℓ : ℕ) : FinalPass.Hash4.hornerCost ℓ 8 ≤ 4096 * ((ℓ + 1) * (ℓ + 1)) := by
  unfold FinalPass.Hash4.hornerCost FinalPass.Hash4.recCost FinalPass.Tm.mulStepCost
  nlinarith [Nat.zero_le ℓ]

theorem step_le (ℓ kh : ℕ) (h : kh ≤ ℓ) : SampLoop.stepCost ℓ kh + 4 ≤ 8192 * ((ℓ + 1) * (ℓ + 1)) := by
  have h1 := horner_le ℓ
  unfold SampLoop.stepCost SampLoop.outCost
  nlinarith [h1]

theorem zw_le (ℓ : ℕ) : SampSeed.zwCost ℓ ≤ 64 * (ℓ + 1) := by unfold SampSeed.zwCost; omega

theorem seed_le (ℓ : ℕ) : SampSeed.seedCost ℓ ≤ 1024 * (ℓ + 1) := by
  unfold SampSeed.seedCost SampSeed.crecCost; omega

theorem main_le (P : Sampler.SeedParams) :
    SampRun.mainCost P ≤ 16384 * ((P.Q + 1) * ((P.ell + 1) * (P.ell + 1))) := by
  have hk : P.kh ≤ P.ell := by have := P.k_le; omega
  have h1 := step_le P.ell P.kh hk
  have hz := zw_le P.ell
  have hs := seed_le P.ell
  obtain ⟨X, hX⟩ : ∃ X, X = (P.ell + 1) * (P.ell + 1) := ⟨_, rfl⟩
  rw [← hX] at h1 ⊢
  have hX1 : P.ell + 1 ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have h2 : P.Q * (SampLoop.stepCost P.ell P.kh + 4) ≤ 8192 * (P.Q * X) := by
    calc P.Q * (SampLoop.stepCost P.ell P.kh + 4) ≤ P.Q * (8192 * X) := Nat.mul_le_mul_left _ h1
      _ = 8192 * (P.Q * X) := by ring
  have h3 : 16384 * ((P.Q + 1) * X) = 16384 * (P.Q * X) + 16384 * X := by ring
  rw [h3]
  unfold SampRun.mainCost
  omega

theorem cost_le (P : Sampler.SeedParams) :
    1 + 1 + (2 * (P.ell * (16 * 73 + 4) + 1 + 1 + 16 * (4 * 21 + 1)) + 2 + 1 +
      (1 + 1 + (2 * SampRun.mainCost P + 2))) ≤ sampCost P := by
  have hm := main_le P
  obtain ⟨X, hX⟩ : ∃ X, X = (P.ell + 1) * (P.ell + 1) := ⟨_, rfl⟩
  rw [← hX] at hm
  have hX1 : P.ell + 1 ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hX4 : X ≤ (P.ell + 1) ^ 4 := by
    rw [hX, show (P.ell + 1) ^ 4 = ((P.ell + 1) * (P.ell + 1)) * ((P.ell + 1) * (P.ell + 1)) by ring]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  have hQX : (P.Q + 1) * X ≤ (P.Q + 1) * (P.ell + 1) ^ 4 := Nat.mul_le_mul_left _ hX4
  have hX1' : X ≤ (P.Q + 1) * X := Nat.le_mul_of_pos_left X (Nat.succ_pos _)
  have e : sampCost P = 1048576 * ((P.Q + 1) * (P.ell + 1) ^ 4) := by unfold sampCost; ring
  rw [e]
  omega

/-! ## The run -/

theorem samp_run (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) :
    ∃ A' : Fin 31 → List Bool,
      Step sampM (sampCost P) (fun _ => 0) (sampIn (0 : Fin 31) 2 3 4 5 P s) (fun _ => 0) A' ∧
      A' 6 = FinalPass.Sample.sampleWord P.kh (seedPairs P s) := by
  -- the register writer
  obtain ⟨τR, sR, eR0, eRT⟩ := SampRegs.regs_spec 0 P.ell (σR P.ell) rfl (fun _ => rfl) (fun t ht => by
    have ht0 : t ≠ 0 := fun h => SampRegs.zero_notin (h ▸ ht)
    have hv : t.val ≠ 0 := fun h => ht0 (Fin.ext h)
    simp only [σR]; rw [if_neg hv])
  obtain ⟨out1, st1, ho1⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step 0 SampRegs.regW (σR P.ell) τR _ sR
    (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  have d1 := cell_dock (29 : Fin 31) (sampIn (0 : Fin 31) 2 3 4 5 P s) rfl
  have d2 := st1.dock sl1 sl1_inj (fun _ => 0)
    (install (fun _ : Fin 1 => (29 : Fin 31)) (sampIn (0 : Fin 31) 2 3 4 5 P s) (fun _ => [false]))
    (fun _ => rfl) (wenc1_val P s)
  rw [zeroH] at d2
  -- the register writer's outputs
  have out1_0 : out1 0 = List.replicate P.ell true := by
    rw [show (0 : Fin 19) = Fin.castAdd 1 (0 : Fin 18) from rfl, ho1]; exact eR0
  have out1_reg : ∀ k (hk : k < 16), out1 ⟨k + 2, by omega⟩ = regTape (18 * P.ell + 20) 0 := by
    intro k hk
    rw [show (⟨k + 2, by omega⟩ : Fin 19) = Fin.castAdd 1 (sTape (ns := 16) (nr := 0) ⟨k + 1, by omega⟩) from
      Fin.ext (by simp [sTape]), ho1, wenc_A_s]
    exact eRT ⟨k + 1, by omega⟩ (List.mem_map.mpr ⟨⟨k, hk⟩, List.mem_finRange _, rfl⟩)
  -- the word program's entry bank
  have B3_E : ∀ i : Fin 31, i.val < 29 →
      install (fun _ : Fin 1 => (1 : Fin 31)) (install sl1 (install (fun _ : Fin 1 => (29 : Fin 31))
        (sampIn (0 : Fin 31) 2 3 4 5 P s) (fun _ => [false])) out1) (fun _ => [false]) i = E P s i := by
    intro i hi
    rw [inst1]
    by_cases h1 : i = 1
    · rw [if_pos h1]; subst h1; rfl
    · rw [if_neg h1]
      have hv1 : i.val ≠ 1 := fun h => h1 (Fin.ext h)
      by_cases h4 : i.val = 4
      · have e : i = sl1 0 := Fin.ext (by simp [sl1, h4])
        rw [e, install_slot sl1 sl1_inj, out1_0]
        rw [← e]; simp only [E]; rw [if_neg hv1, if_neg (by omega)]
        simp [sampIn, show i = 4 from Fin.ext h4]
      · by_cases hr : 12 ≤ i.val ∧ i.val < 28
        · have e : i = sl1 ⟨i.val - 12 + 2, by omega⟩ :=
            Fin.ext (by rw [sl1_reg (i.val - 12) (by omega)]; omega)
          rw [e, install_slot sl1 sl1_inj, out1_reg (i.val - 12) (by omega)]
          rw [← e]; simp only [E]; rw [if_neg hv1, if_pos hr]
        · rw [install_other sl1 _ out1 i (sl1_ne i hi h4 hr), inst1, if_neg (fun h => by
            have := congrArg Fin.val h; simp at this; omega)]
          simp only [E]; rw [if_neg hv1, if_neg hr]
  have hA2 : ∀ j : Fin 29, install (fun _ : Fin 1 => (1 : Fin 31)) (install sl1 (install (fun _ : Fin 1 => (29 : Fin 31))
      (sampIn (0 : Fin 31) 2 3 4 5 P s) (fun _ => [false])) out1) (fun _ => [false]) (sl2 j) =
      Fin.addCases (m := 10 + 2 + 16) (n := 1) (motive := fun _ => List Bool)
        (wenc (18 * P.ell + 20) (SampRun.σE P s)).A (fun _ => []) j := by
    intro j; rw [wenc2_val, B3_E (sl2 j) (by simp [sl2])]
  -- the word program
  obtain ⟨τM, sM, eM⟩ := SampRun.main_spec (18 * P.ell + 20) P s le_rfl
  obtain ⟨out2, st2, ho2⟩ := NearCubicWires.WireExponent3_5.PrimT.wm_step (18 * P.ell + 20) SampRun.mainW
    (SampRun.σE P s) τM _ sM (NearCubicWires.WireExponent3_5.PrimT.wenc_H_zero _ _ (fun _ => rfl) (fun _ => rfl))
  have d3 := cell_dock (1 : Fin 31) (install sl1 (install (fun _ : Fin 1 => (29 : Fin 31))
      (sampIn (0 : Fin 31) 2 3 4 5 P s) (fun _ => [false])) out1)
    (by rw [install_other sl1 _ out1 1 (sl1_ne 1 (by decide) (by decide) (by decide)), inst1]; rfl)
  have d4 := st2.dock sl2 sl2_inj (fun _ => 0) _ (fun _ => rfl) hA2
  rw [zeroH] at d4
  refine ⟨_, (d1.seq (d2.seq (d3.seq d4))).enlarge ?_, ?_⟩
  · exact cost_le P
  · rw [show (6 : Fin 31) = sl2 6 from rfl, install_slot sl2 sl2_inj,
      show (6 : Fin 29) = Fin.castAdd 1 (6 : Fin 28) from rfl, ho2]
    exact eM

end NearCubicWires.WireExponent3_5.UnionMachine.SampStage
