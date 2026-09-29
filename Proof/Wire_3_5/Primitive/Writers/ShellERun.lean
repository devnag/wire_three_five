import Proof.Wire_3_5.Primitive.Writers.ShellEBoot

/-! # The ShellE: the THR writer shell over `ThrDataStage2`, part 2: the run and both
instances

The run (`ShellTRun.shell_runG`) over the boot `ShellEBoot.bootX_stepE` (a `ThrDataStage2`, `ThrDataOK2`, every
`a' ≤ 4`), then the two relaxed shell types from it, one term each (the proofs of `shell_runT` and
`thrShellX2`, M28/M29, at the v2 stage):

* **`shell_runE`** (any `DimOK` stage, the machine `shellMG (toV1 S) …`);
* **`thrShellRun2 : PrimThrW.ShellE.ThrShellRun2 S x U D C D2 C2 Dv Cv cr DL CL`** (v1 relaxed, ShellX's dimension
  `mOf P`; for the hash writer);
* **`thrShellX2b : PrimThrW.ShellE.ThrShellX2b S x U D C D2 C2 Dv Cv cr DL CL KL`** (v2 relaxed, the dimension
  `mOfT KL P`; for).

Paper quantity of the main type: the writer's output tape `(List.range b).flatMap emit ++ [false]` for every tuple of
arity at most four (lem:primitive P3:3068-3084). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.WireExponent3_5.PrimAsm.ShellX NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Run

/-- **The THR shell's run over a `ThrDataStage2`** (every `a' ≤ 4`): `shell_runG` with the boot `bootX_stepE`. -/
theorem shell_runE (S : ThrData.ThrDataStage2) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU)
    (D C D2 C2 Dv Cv DL CL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) (c2 mD cap nU Bud : ℕ) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (emit : ℕ → List Bool)
    (hw : w = Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value D2 C2 n))
    (hx2 : DimOK x D D2 Dv DL M2 c2 mD w (UnaryCalc.value Dv Cv n))
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ mD)) (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ mD))
    (hboot : bootCost w n 0 0 ≤ UnaryCalc.value D C (2 ^ mD))
    (hdec : ∀ j < UnaryCalc.value DL CL (2 ^ mD), ∀ out : List Bool,
      PrimThrW.Shell.UnitOK cap x U nU w (Data.unaryList (ThrData.thrCounts Cs carriers)) emit j out)
    (hB : 2 * shellCostG w n D C D2 C2 (S.cost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n))
      Dv Cv c2 mD DL CL nU + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (shellMG (PrimThrW.ShellE.toV1 S) x U D C D2 C2 Dv Cv DL CL M2) Bud (shellInX x D D2 Dv DL)
      (shellOutX x D D2 Dv DL) w ((List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit ++ [false]) := by
  set u := Data.unaryList (ThrData.thrCounts Cs carriers) with hu
  obtain ⟨Bf, sb, f0, f1, f2, fscr, fwk, flg, fdr, fk, fdt⟩ :=
    bootX_stepE S M2 c2 mD (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) Cs carriers tl w C2 Cv CL hw hD hx2
  obtain ⟨Wk, se⟩ := entry_runD (x := x) (D := D) (D1 := 0) (D2 := D2) cap C (2 ^ mD)
    (UnaryCalc.value DL CL (2 ^ mD)) w (false :: (RepairOrdinary.Streaming.marks u ++ [false]))
    (fun i => Bf (ShellX.lo i)) f0 f1 f2 (fun c hc => le_trans (fscr c hc) hboot) fwk flg fdr fk (by rw [fdt, dataWord_eq])
  have se2 := se.embed (fun k : Fin (EX x D D2 Dv DL) => HF x D D2 Dv DL (Fin.natAdd _ k))
    (fun k => Bf (Fin.natAdd _ k))
  have eBf : (Fin.addCases (fun i => Bf (ShellX.lo i)) (fun k : Fin (EX x D D2 Dv DL) => Bf (Fin.natAdd _ k)) :
      Fin (STx x D D2 Dv DL) → List Bool) = Bf := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun z => ?_) i
    · simp only [Fin.addCases_left]; rfl
    · simp only [Fin.addCases_right]
  have eHF : (Fin.addCases (hK x D 0 D2) (fun k : Fin (EX x D D2 Dv DL) => HF x D D2 Dv DL (Fin.natAdd _ k)) :
      Fin (STx x D D2 Dv DL) → ℕ) = HF x D D2 Dv DL := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun z => ?_) i
    · simp only [Fin.addCases_left]; exact (HF_lo a).symm
    · simp only [Fin.addCases_right]
  have se3 : Step (entryEX x D D2 Dv DL C) (Scrub.entryCost D C (2 ^ mD)) (HF x D D2 Dv DL) Bf
      (Fin.addCases (loopHSd x D 0 D2 []) (fun k : Fin (EX x D D2 Dv DL) => HF x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk 0 (UnaryCalc.value DL CL (2 ^ mD)) []
        (fun k => Bf (ShellX.lo (xT k)))) (fun k : Fin (EX x D D2 Dv DL) => Bf (Fin.natAdd _ k))) :=
    se2.congr_in eHF eBf
  have sl := ((loop_stepU cap x U (UnaryCalc.value D C (2 ^ mD)) nU (UnaryCalc.value DL CL (2 ^ mD))
    w u Wk emit hcap hR hdec).embed (fun _ : Fin (E1 0 + E2 D2 + E3) => 0) (fun k => Bf (ShellX.lo (xT k)))).embed
    (fun k : Fin (EX x D D2 Dv DL) => HF x D D2 Dv DL (Fin.natAdd _ k)) (fun k => Bf (Fin.natAdd _ k))
  have sl' : Step (PrimThrW.Shell.loopEU x U D D2 Dv DL) (UnaryCalc.value DL CL (2 ^ mD) * ((2 * nU + 2 + 1 +
      (2 * UnaryCalc.value D C (2 ^ mD) + 4)) + 3) + 3)
      (Fin.addCases (loopHSd x D 0 D2 []) (fun k : Fin (EX x D D2 Dv DL) => HF x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk 0 (UnaryCalc.value DL CL (2 ^ mD)) []
        (fun k => Bf (ShellX.lo (xT k)))) (fun k : Fin (EX x D D2 Dv DL) => Bf (Fin.natAdd _ k)))
      (Fin.addCases (loopHSd x D 0 D2 ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit))
        (fun k : Fin (EX x D D2 Dv DL) => HF x D D2 Dv DL (Fin.natAdd _ k)))
      (Fin.addCases (loopASd cap x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk (UnaryCalc.value DL CL (2 ^ mD))
        (UnaryCalc.value DL CL (2 ^ mD))
        ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit) (fun k => Bf (ShellX.lo (xT k))))
        (fun k : Fin (EX x D D2 Dv DL) => Bf (Fin.natAdd _ k))) := sl
  have si := (sb.seq se3).seq sl'
  obtain ⟨m, sm⟩ := ListMachine.Row.maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  have e1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (STx x D D2 Dv DL + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have e2 : (Fin.addCases (A0 w) (fun _ : Fin 1 => List.replicate 0 false) : Fin (STx x D D2 Dv DL + 1) → List Bool) =
      WriterIface.inBank (shellInX x D D2 Dv DL) w := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · by_cases ha : a = T0 x D D2 Dv DL
      · subst ha
        simp [A0, WriterIface.inBank, shellInX, T0]
      · have hne : Fin.castAdd 1 a ≠ shellInX x D D2 Dv DL := fun e => ha (Fin.castAdd_injective _ _ e)
        have ha' : a ≠ ShellX.lo (cs 0) := ha
        simp [A0, WriterIface.inBank, ha', hne]
    · have hne : Fin.natAdd (STx x D D2 Dv DL) u ≠ shellInX x D D2 Dv DL := by
        intro e
        have := congrArg Fin.val e
        simp only [Fin.val_natAdd, shellInX, Fin.val_castAdd] at this
        have := (T0 x D D2 Dv DL).isLt
        omega
      simp [WriterIface.inBank, hne]
  have e3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else
      Fin.addCases (loopHSd x D 0 D2 ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit))
        (fun k : Fin (EX x D D2 Dv DL) => HF x D D2 Dv DL (Fin.natAdd _ k)) i) (fun _ : Fin 1 => 0) :
      Fin (STx x D D2 Dv DL + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  set Tf : Fin (STx x D D2 Dv DL + 1) → List Bool := Fin.addCases
    (Fin.addCases (loopASd cap x D 0 D2 (UnaryCalc.value D C (2 ^ mD)) w
        (false :: (RepairOrdinary.Streaming.marks u ++ [false])) Wk (UnaryCalc.value DL CL (2 ^ mD))
        (UnaryCalc.value DL CL (2 ^ mD))
        ([] ++ (List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit) (fun k => Bf (ShellX.lo (xT k))))
      (fun k : Fin (EX x D D2 Dv DL) => Bf (Fin.natAdd _ k)))
    (fun _ : Fin 1 => List.replicate m false) with hTf
  have hstep : Step (shellMG (PrimThrW.ShellE.toV1 S) x U D C D2 C2 Dv Cv DL CL M2) Bud (fun _ => 0)
      (WriterIface.inBank (shellInX x D D2 Dv DL) w) (fun _ => 0) Tf :=
    ((sm.congr_in e1 e2).congr e3 rfl).enlarge (by unfold shellCostG at hB; omega)
  refine ⟨fun j => if j = shellInX x D D2 Dv DL ∨ j = shellOutX x D D2 Dv DL then [] else Tf j, ?_, ?_⟩
  · intro j
    by_cases hj : j = shellInX x D D2 Dv DL ∨ j = shellOutX x D D2 Dv DL
    · simp [hj]
    · have hin : j ≠ shellInX x D D2 Dv DL := fun e => hj (Or.inl e)
      have := Shell.Step.len hstep j 0 (le_refl _) (by simp [WriterIface.inBank, hin])
      simp only [hj, if_false]
      omega
  · have eo : Tf = WriterIfaceJ.outBankJ (shellInX x D D2 Dv DL) (shellOutX x D D2 Dv DL) w
        ((List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit ++ [false])
        (fun j => if j = shellInX x D D2 Dv DL ∨ j = shellOutX x D D2 Dv DL then [] else Tf j) := by
      funext j
      unfold WriterIfaceJ.outBankJ
      by_cases hi : j = shellInX x D D2 Dv DL
      · subst hi
        simp only [if_true, hTf, shellInX, Fin.addCases_left, T0, ShellX.lo]
        exact loopASd_cs0 _ _ _ _ _ _ _ _ _
      · by_cases ho : j = shellOutX x D D2 Dv DL
        · subst ho
          rw [if_neg hi, if_pos rfl]
          simp only [hTf, shellOutX, Fin.addCases_left, ShellX.lo]
          rw [loopASd_cs1, List.nil_append]
        · simp [hi, ho]
    rw [← eo]
    exact Shell.ready_of_step hstep

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
