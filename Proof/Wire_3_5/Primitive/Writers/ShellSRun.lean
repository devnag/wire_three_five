import Proof.Wire_3_5.Primitive.Writers.ShellSBoot

/-! # The SYM writer shell v2, part 2: the run over any dimension stage

ShellX's run (`ShellXRun.shell_runX`) with the boot `ShellSBoot.bootX_stepS`: the scrub capacity `R = C(2^m+1)^D` and
the loop bound `b = CL(2^m+1)^DL` at any dimension `m` whose stage meets `ShellT.DimOK` (`m_S`, which reaches the
SYM tape's FILTER and POP units).

* `shellMS`, `shellStageS` (a `WriterStage`), **`shell_runS`** (`WriterIfaceJ.WriterRun … w
  ((List.range b).flatMap emit ++ [false])` for any decode meeting `CellUnit.DecOK` at every unit `j < b`, the cost
  `ShellT.shellCostG`).

Paper quantity of the main type: the writer's output tape `(List.range b).flatMap emit ++ [false]` (for the SYM writer
C4's `BAT` word of the call, `SymDec.sym_loop_tape`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellS
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.SupplierPipeline

section Run
variable {x D D2 Dv DL : ℕ}

/-- **The SYM shell v2's machine**: ShellX's machine with the dimension stage `M2`. One machine per unit machine, per
`(D, C, D₂, C₂, Dv, Cv, DL, CL)` and per dimension stage, independent of the request. -/
noncomputable def shellMS (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D2 C2 Dv Cv DL CL : ℕ) {s2 : ℕ}
    (M2 : Machine NUn s2) :=
  MaskedReset.machine (Composition.machine (Composition.machine (bootXMS W.x D D2 Dv DL C2 Cv CL M2)
    (entryEX W.x D D2 Dv DL C)) (loopEX W decW D D2 Dv DL)) (fun _ => true)

/-- **The SYM shell v2's run** (`WriterIfaceJ.WriterRun`): ShellX's run at any dimension stage meeting `DimOK`. -/
theorem shell_runS (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D2 C2 Dv Cv DL CL : ℕ) {s2 : ℕ}
    (M2 : Machine NUn s2) (c2 mD cap nU Bud : ℕ)
    {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (emit : ℕ → List Bool)
    (hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : DataOK Cs carriers (UnaryCalc.value D2 C2 n))
    (hx2 : ShellT.DimOK W.x D D2 Dv DL M2 c2 mD w (UnaryCalc.value Dv Cv n))
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ mD))
    (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ mD))
    (hboot : bootCost w n 0 0 ≤ UnaryCalc.value D C (2 ^ mD))
    (hdec : ∀ j < UnaryCalc.value DL CL (2 ^ mD), ∀ out : List Bool, ∃ σD m Bp,
      WExec cap decW (blankCellD W.x w out j (Data.unaryList (Data.symCounts a' Cs carriers))) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧
      cpCost (Data.unaryList (Data.symCounts a' Cs carriers)).length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU)
    (hB : 2 * ShellT.shellCostG w n D C D2 C2
      (Data.coreCost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv c2 mD DL CL nU + 2 ≤
        Bud) :
    WriterIfaceJ.WriterRun (shellMS W decW D C D2 C2 Dv Cv DL CL M2) Bud (shellInX W.x D D2 Dv DL)
      (shellOutX W.x D D2 Dv DL) w ((List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit ++ [false]) := by
  set u := Data.unaryList (Data.symCounts a' Cs carriers) with hu
  obtain ⟨Bf, sb, f0, f1, f2, fscr, fwk, flg, fdr, fk, fdt⟩ :=
    bootX_stepS M2 c2 mD (x := W.x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) Cs carriers tl w C2 Cv CL hw hD hx2
  obtain ⟨Wk, se⟩ := entry_runD (x := W.x) (D := D) (D1 := 0) (D2 := D2) cap C (2 ^ mD)
    (UnaryCalc.value DL CL (2 ^ mD)) w (false :: (RepairOrdinary.Streaming.marks u ++ [false]))
    (fun i => Bf (ShellX.lo i)) f0 f1 f2 (fun c hc => le_trans (fscr c hc) hboot) fwk flg fdr fk (by rw [fdt, dataWord_eq])
  have se2 := se.embed (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k))
    (fun k => Bf (Fin.natAdd _ k))
  have eBf : (Fin.addCases (fun i => Bf (ShellX.lo i)) (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k)) :
      Fin (STx W.x D D2 Dv DL) → List Bool) = Bf := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun z => ?_) i
    · simp only [Fin.addCases_left]; rfl
    · simp only [Fin.addCases_right]
  have eHF : (Fin.addCases (hK W.x D 0 D2) (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)) :
      Fin (STx W.x D D2 Dv DL) → ℕ) = HF W.x D D2 Dv DL := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun z => ?_) i
    · simp only [Fin.addCases_left]; exact (HF_lo a).symm
    · simp only [Fin.addCases_right]
  have se3 : Step (entryEX W.x D D2 Dv DL C) (Scrub.entryCost D C (2 ^ mD)) (HF W.x D D2 Dv DL) Bf
      (Fin.addCases (loopHSd W.x D 0 D2 []) (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk 0 (UnaryCalc.value DL CL (2 ^ mD)) []
        (fun k => Bf (ShellX.lo (xT k)))) (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k))) :=
    se2.congr_in eHF eBf
  have sl := ((loop_stepD cap W decW (UnaryCalc.value D C (2 ^ mD)) nU (UnaryCalc.value DL CL (2 ^ mD))
    w u Wk emit hcap hR hdec).embed (fun _ : Fin (E1 0 + E2 D2 + E3) => 0) (fun k => Bf (ShellX.lo (xT k)))).embed
    (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)) (fun k => Bf (Fin.natAdd _ k))
  have sl' : Step (loopEX W decW D D2 Dv DL) (UnaryCalc.value DL CL (2 ^ mD) * ((2 * nU + 2 + 1 +
      (2 * UnaryCalc.value D C (2 ^ mD) + 4)) + 3) + 3)
      (Fin.addCases (loopHSd W.x D 0 D2 []) (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk 0 (UnaryCalc.value DL CL (2 ^ mD)) []
        (fun k => Bf (ShellX.lo (xT k)))) (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k)))
      (Fin.addCases (loopHSd W.x D 0 D2 ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit))
        (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk (UnaryCalc.value DL CL (2 ^ mD))
        (UnaryCalc.value DL CL (2 ^ mD))
        ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit) (fun k => Bf (ShellX.lo (xT k))))
        (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k))) := sl
  have si := (sb.seq se3).seq sl'
  obtain ⟨m, sm⟩ := ListMachine.Row.maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  have e1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (STx W.x D D2 Dv DL + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have e2 : (Fin.addCases (A0 w) (fun _ : Fin 1 => List.replicate 0 false) : Fin (STx W.x D D2 Dv DL + 1) → List Bool) =
      WriterIface.inBank (shellInX W.x D D2 Dv DL) w := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · by_cases ha : a = T0 W.x D D2 Dv DL
      · subst ha
        simp [A0, WriterIface.inBank, shellInX, T0]
      · have hne : Fin.castAdd 1 a ≠ shellInX W.x D D2 Dv DL := fun e => ha (Fin.castAdd_injective _ _ e)
        have ha' : a ≠ ShellX.lo (cs 0) := ha
        simp [A0, WriterIface.inBank, ha', hne]
    · have hne : Fin.natAdd (STx W.x D D2 Dv DL) u ≠ shellInX W.x D D2 Dv DL := by
        intro e
        have := congrArg Fin.val e
        simp only [Fin.val_natAdd, shellInX, Fin.val_castAdd] at this
        have := (T0 W.x D D2 Dv DL).isLt
        omega
      simp [WriterIface.inBank, hne]
  have e3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else
      Fin.addCases (loopHSd W.x D 0 D2 ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit))
        (fun k : Fin (EX W.x D D2 Dv DL) => HF W.x D D2 Dv DL (Fin.natAdd _ k)) i) (fun _ : Fin 1 => 0) :
      Fin (STx W.x D D2 Dv DL + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  set Tf : Fin (STx W.x D D2 Dv DL + 1) → List Bool := Fin.addCases
    (Fin.addCases (loopASd cap W.x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk (UnaryCalc.value DL CL (2 ^ mD))
        (UnaryCalc.value DL CL (2 ^ mD))
        ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit) (fun k => Bf (ShellX.lo (xT k))))
      (fun k : Fin (EX W.x D D2 Dv DL) => Bf (Fin.natAdd _ k)))
    (fun _ : Fin 1 => List.replicate m false) with hTf
  have hstep : Step (shellMS W decW D C D2 C2 Dv Cv DL CL M2) Bud (fun _ => 0)
      (WriterIface.inBank (shellInX W.x D D2 Dv DL) w) (fun _ => 0) Tf :=
    ((sm.congr_in e1 e2).congr e3 rfl).enlarge (by unfold ShellT.shellCostG at hB; omega)
  refine ⟨fun j => if j = shellInX W.x D D2 Dv DL ∨ j = shellOutX W.x D D2 Dv DL then [] else Tf j, ?_, ?_⟩
  · intro j
    by_cases hj : j = shellInX W.x D D2 Dv DL ∨ j = shellOutX W.x D D2 Dv DL
    · simp [hj]
    · have hin : j ≠ shellInX W.x D D2 Dv DL := fun e => hj (Or.inl e)
      have := Shell.Step.len hstep j 0 (le_refl _) (by simp [WriterIface.inBank, hin])
      simp only [hj, if_false]
      omega
  · have eo : Tf = WriterIfaceJ.outBankJ (shellInX W.x D D2 Dv DL) (shellOutX W.x D D2 Dv DL) w
        ((List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit ++ [false])
        (fun j => if j = shellInX W.x D D2 Dv DL ∨ j = shellOutX W.x D D2 Dv DL then [] else Tf j) := by
      funext j
      unfold WriterIfaceJ.outBankJ
      by_cases hi : j = shellInX W.x D D2 Dv DL
      · subst hi
        simp only [if_true, hTf, shellInX, Fin.addCases_left, T0, ShellX.lo]
        exact loopASd_cs0 _ _ _ _ _ _ _ _ _
      · by_cases ho : j = shellOutX W.x D D2 Dv DL
        · subst ho
          rw [if_neg hi, if_pos rfl]
          simp only [hTf, shellOutX, Fin.addCases_left, ShellX.lo]
          rw [loopASd_cs1, List.nil_append]
        · simp [hi, ho]
    rw [← eo]
    exact Shell.ready_of_step hstep

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ShellS
