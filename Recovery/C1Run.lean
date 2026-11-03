import Recovery.C1Build
import CheckedPCPP.Dock
import CheckedPCPP.WMXReady
import Proof.Amplification.RecoveryCaseOneAmplifierReady
import Proof.Amplification.RecoveryCaseOnePaddedEvaluationRun
import Proof.CaseAnalysis.CaseOneAmplifierBound
import Proof.Amplification.RecoveryReadyCalls

/-!
# The Case 1 machine, part 5: `Recovery.caseOneRuns : CaseOneRuns`

The near-cubic-gates paper's extraction of the hard table (Case 1 (i) `X_z`, Case 1 (iii) `O*`, both `q^G`-hard) and the uniform recovery ("run the general amplifier" and pad):
the program `c1W` is `buildW` (the amplifier's input word `frame (amplifierInput ⟨q, cycFn a w q⟩)` on `X`), then
proof 1's dock of the selected amplifier's constructor (`RecoveryCaseOneAmplifier.constructor_ready`: the framed
generated table on its output tape), then proof 1's padded evaluator (`RecoveryCaseOnePaddedEvaluation.ready`: the
framed bit `padCore f hn point` of the generated function `f` at the final address). Compiled and rewound
(`WXExec.readyRewound`), with its tapes relabelled so that the three ports are the tapes `0, 1, 2` (`slotC1`). The cost
is a fixed polynomial in `2^n` (`CloseoutCaseOne.amplifier_budget_bound`, `padded_evaluation_bound`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.C1

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5 NearCubicWires.ExtDecompositionBatch
open NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named)

/-! ## The dock maps -/

section Maps
variable (tA : ℕ)

/-- The amplifier dock: its input tape `0` is `X`, every other tape is in the block `bA`. -/
def ampMap (j : Fin tA) : Fin (NS tA + 1) := if j.val = 0 then X tA else bA tA j

/-- The evaluator dock: its tape `0` is the amplifier's output tape `bA o`, its tape `17` is the address port `A`, every
other tape is in the block `bV`. -/
def evalMap (o : Fin tA) (j : Fin 46) : Fin (NS tA + 1) :=
  if j.val = 0 then bA tA o else if j.val = 17 then A tA else bV tA j

theorem ampMap_val (j : Fin tA) : (ampMap tA j).val = if j.val = 0 then 3 else 4 + j.val := by
  unfold ampMap; split_ifs <;> rfl

theorem evalMap_val (o : Fin tA) (j : Fin 46) :
    (evalMap tA o j).val = if j.val = 0 then 4 + o.val else if j.val = 17 then 1 else 4 + tA + j.val := by
  unfold evalMap; split_ifs <;> rfl

theorem ampMap_inj : Function.Injective (ampMap tA) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [ampMap_val, ampMap_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem evalMap_inj (o : Fin tA) : Function.Injective (evalMap tA o) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [evalMap_val, evalMap_val] at hv
  have := o.isLt; have := a.isLt; have := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

end Maps

/-! ## The program -/

section Program
variable {c d : ℕ} (amplifier : RepairSource.OrdinaryScheduleAmplifier c d)

/-- The amplifier constructor's program. -/
noncomputable abbrev ampP := amplifier.constructor.program

/-- The amplifier dock's tape count. -/
noncomputable abbrev tA := RepairSource.RecoveryCaseOneAmplifier.tapes (ampP amplifier)

/-- **The Case 1 program.** -/
noncomputable def c1W : WMX (NS (tA amplifier)) 16 :=
  .seq (buildW (tA amplifier))
    (.seq (.mach (RepairSource.RecoveryCaseOneAmplifier.machine (ampP amplifier)) (ampMap (tA amplifier)))
      (.mach RepairSource.RecoveryCaseOnePaddedEvaluation.machine
        (evalMap (tA amplifier) (RepairSource.RecoveryCaseOneAmplifier.output (ampP amplifier)))))

end Program

/-- The cost bound of `c1W`. -/
noncomputable def c1Cost {c d : ℕ} (amplifier : RepairSource.OrdinaryScheduleAmplifier c d) (q n : ℕ) : ℕ :=
  buildCost q + 1 + (65536 * (2 ^ n + 1) ^ (2 * max 1 amplifier.constructionExponent) + 1 +
    4096 * (2 ^ n + 1) ^ 2)

/-- **The Case 1 program's run** (the near-cubic-gates paper's extraction of the hard table to its uniform recovery). -/
theorem c1_exec {c d : ℕ} (amplifier : RepairSource.OrdinaryScheduleAmplifier c d) (a q : ℕ) (w : BitInput (2 ^ a))
    (rest : List Bool) (n : ℕ) (point : BitInput n) (hq : 1 ≤ q) (hqn : q ≤ n)
    (hn : (amplifier.output q (Recovery.cycFn a w q)).arity ≤ n) (cap : ℕ) (hcap : buildCap a q ≤ cap) :
    ∃ τ n', WXExec cap (c1W amplifier)
        (initC1 (tA amplifier) (frame (List.ofFn w) ++ rest) (frame (List.ofFn point)) q) τ n' ∧
      n' ≤ c1Cost amplifier q n ∧
      τ.st (bV (tA amplifier) 44) =
        frame (Transfer.GateParams.amplified amplifier q (Recovery.cycFn a w q) n point).toNat.bits := by
  set T := tA amplifier with hTd
  set req : AmplifierRequest := ⟨q, Recovery.cycFn a w q⟩ with hreq
  set p := ampP amplifier with hp
  obtain ⟨t1, n1, e1, hn1, hX1, hXh1, _, hk1⟩ := build_exec T a q w rest (frame (List.ofFn point)) cap hcap
  have hinit : ∀ i : Fin (NS T + 1), 3 ≤ i.val →
      (initC1 T (frame (List.ofFn w) ++ rest) (frame (List.ofFn point)) q).st i = [] := by
    intro i hi; simp [initC1]; omega
  have hXne : ∀ j : Fin T, j.val ≠ 0 → bA T j ≠ X T := fun j hj => by cdst
  -- the amplifier dock
  obtain ⟨outA, hrunA, hvalA⟩ := RepairSource.RecoveryCaseOneAmplifier.constructor_ready amplifier req
  obtain ⟨t2, e2, hd2⟩ := NearCubicGates.Close.CheckedPCPP.Dock.ready_mach (cap := cap) hrunA (ampMap_inj T) t1
    (fun j => by
      unfold ampMap; split_ifs with h
      · exact hXh1
      · exact (hk1 _ (hXne j h)).2)
    (fun j => by
      rw [RepairSource.RecoveryCaseOneAmplifier.input_lookup]
      unfold ampMap; split_ifs with h
      · rw [hX1]; rfl
      · rw [(hk1 _ (hXne j h)).1, hinit _ (by simp only [bA_val]; omega)])
  have hO : (RepairSource.RecoveryCaseOneAmplifier.output p).val ≠ 0 := by
    simp [RepairSource.RecoveryCaseOneAmplifier.output, NearCubicWires.RepairOrdinary.AmplifierReplay.Dock.output]
  have hampO : ampMap T (RepairSource.RecoveryCaseOneAmplifier.output p) = bA T (RepairSource.RecoveryCaseOneAmplifier.output p) := by
    unfold ampMap; rw [if_neg hO]
  -- the padded evaluator dock
  set gen := amplifier.output q (Recovery.cycFn a w q) with hgen
  obtain ⟨outV, hrunV, hvalV⟩ := RepairSource.RecoveryCaseOnePaddedEvaluation.ready gen.function hn point
  have nA : ∀ j, ampMap T j ≠ A T := by
    intro j e; have := congrArg Fin.val e; rw [ampMap_val] at this; simp at this; split_ifs at this <;> omega
  have nV : ∀ (k : Fin 46) j, ampMap T j ≠ bV T k := by
    intro k j e; have hv := congrArg Fin.val e; rw [ampMap_val] at hv; simp at hv
    have hj := j.isLt; split_ifs at hv <;> omega
  obtain ⟨t3, e3, hd3⟩ := NearCubicGates.Close.CheckedPCPP.Dock.ready_mach (cap := cap) hrunV (evalMap_inj T (RepairSource.RecoveryCaseOneAmplifier.output p)) t2
    (fun j => by
      unfold evalMap; split_ifs with h0 h17
      · rw [← hampO]; exact hd2.sh _
      · rw [(hd2.other _ nA).2, (hk1 _ (by cdst)).2]
      · rw [(hd2.other _ (nV j)).2, (hk1 _ (by cdst)).2])
    (fun j => by
      unfold evalMap RepairSource.RecoveryCaseOnePaddedEvaluation.input
      split_ifs with h0 h17
      · rw [← hampO, hd2.st, hvalA]; rfl
      · rw [(hd2.other _ nA).1, (hk1 _ (by cdst)).1]; simp [initC1, threeWords]
      · rw [(hd2.other _ (nV j)).1, (hk1 _ (by cdst)).1, hinit _ (by simp only [bV_val]; omega)])
  refine ⟨t3, _, WXExec.seq e1 (WXExec.seq e2 e3), ?_, ?_⟩
  · have hA := RepairSource.CloseoutCaseOne.amplifier_budget_bound amplifier req n (by omega) hqn hn
    have hV := RepairSource.CloseoutCaseOne.padded_evaluation_bound gen.function hn point
    have hV' : 4096 * (2 ^ gen.arity + 1) ^ 2 ≤ 4096 * (2 ^ n + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn; omega) _)
    unfold c1Cost
    omega
  · have h44 : evalMap T (RepairSource.RecoveryCaseOneAmplifier.output p) (44 : Fin 46) = bV T 44 := by
      unfold evalMap; rw [if_neg (by decide), if_neg (by decide)]
    rw [← h44, hd3.st, hvalV]
    unfold Transfer.GateParams.amplified
    rw [dif_pos hn]

end NearCubicGates.Close.Recovery.C1
