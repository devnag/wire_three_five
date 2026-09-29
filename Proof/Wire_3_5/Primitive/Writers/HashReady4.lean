import Proof.Wire_3_5.Primitive.Writers.HashReady
import Proof.Wire_3_5.Primitive.Writers.ShellH4Run

/-! # The HASH writer's run at one call over the v4 data stage

`HashReady.hash_ready` with the v4 data stage (`ThrData.ThrDataStage4`) and the v4 shell (`ShellH4`,
; `shell_runH4`): the same hypotheses (the data stage's `need`, `cost3` are v3's verbatim), the writer
`shellMGH4 S W.x (CellUnit.unitM W (hdecW W FS cr)) …` on `STx + x3 + 1` tapes, the ports `shellInX4`, `shellOutX4`.

* **`hash_ready4`**.

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226), written within
the budget `Bud`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline

section Ready
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface NearCubicWires.WireExponent3_5.PrimAsm.Records
open NearCubicWires.WireExponent3_5.PrimAsm.HashFlat NearCubicWires.WireExponent3_5.PrimAsm.HashCall
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **The HASH writer's run at one THR call over the v4 data stage**, the budgets as hypotheses: from
`frame (thrReq …).word`, within `Bud`, the output tape is the HASH tape. -/
theorem hash_ready4 (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {Dexp : ℕ}
    {capT : ℕ → ℕ} (S : ThrData.ThrDataStage4 alg Dexp capT) (W : PrimT.WalkBank.WalkBankProducer)
    (FS : FiltSetup.FiltSetupSpec5 W) (cr D C D2 C2 Dv Cv DL CL KL KH cap nU Bud Bf BP : ℕ) {n a' : ℕ}
    (hs : I.StarAt n) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hDexp : Dexp = I.D) (hcapT : capT n = (I.filterParams .thr n).cap) (hU : 1 ≤ capT n)
    (hrP : (I.starParams n hs).r = Ledger.rowBr cr n)
    (hD : PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value D2 C2 n))
    (hcu3 : 2 * (Data.unaryList (ThrData.hashNums (I.starParams n hs) Cs carriers alg Dexp (capT n) ++
      ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * UnaryCalc.value D2 C2 n + 2)
    (hdesc : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26)
    (hneed : S.need n ≤ 2 * UnaryCalc.value D2 C2 n + 2)
    (hW : 2 * n + cr + 16 + KL * (n + 2) ^ 2 + KH * (n + 2) ^ 3 ≤ UnaryCalc.value Dv Cv n)
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ NumsXH.mOfH KL KH (I.starParams n hs)))
    (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ NumsXH.mOfH KL KH (I.starParams n hs)))
    (hboot : bootCost (thrReq n a' ha' Cs carriers translation).word n 0 0 ≤
      UnaryCalc.value D C (2 ^ NumsXH.mOfH KL KH (I.starParams n hs)))
    (hTOT : 2 ^ (auxP alg I hs Cs carriers).seedBits *
      2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2))) * 5 ≤
        UnaryCalc.value DL CL (2 ^ NumsXH.mOfH KL KH (I.starParams n hs)))
    (hc1 : 2 * (thrReq n a' ha' Cs carriers translation).word.length + 2 ≤ cap)
    (hc2 : 2 ^ (natBitLength n + 1) ≤ cap) (hc3 : 4 * (n + 3) + 2 * cr + 20 ≤ cap)
    (hcl : ∀ v ∈ ThrData.hashNums (I.starParams n hs) Cs carriers alg Dexp (capT n) ++ ThrData.thrCounts Cs carriers,
      v ≤ cap)
    (hcs : (carriers.map (·.length)).sum + (PrimT.ThrTab.tupleG Cs).length + 4 ≤ cap)
    (hcD1 : (auxP alg I hs Cs carriers).errExp + (auxP alg I hs Cs carriers).len + (auxP alg I hs Cs carriers).cap +
      (carriers.length + 1) * 4096 + capT n + 10 ≤ cap)
    (hcG1 : (auxP alg I hs Cs carriers).cap * 32 + 2 ≤ cap) (hcG2 : (auxP alg I hs Cs carriers).len + 8 ≤ cap)
    (hcG3 : (auxP alg I hs Cs carriers).errExp + 4 ≤ cap)
    (hcG4 : 2 ^ ((auxP alg I hs Cs carriers).seedBits + 1) ≤ cap)
    (hcG5 : (auxP alg I hs Cs carriers).labelBits + (auxP alg I hs Cs carriers).fieldBits +
      (auxP alg I hs Cs carriers).walkLen + 512 ≤ cap)
    (hcD3 : (thrPool (I.starParams n hs) Cs carriers).length + 2 ^ (auxP alg I hs Cs carriers).seedBits +
      2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2)) + 1) +
      2 ^ (auxP alg I hs Cs carriers).seedBits * 2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2))) * 5 +
      10 ≤ cap)
    (hcJ : 4 * UnaryCalc.value DL CL (2 ^ NumsXH.mOfH KL KH (I.starParams n hs)) +
      2 ^ (auxP alg I hs Cs carriers).seedBits * 2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2))) * 5 +
      2 ^ (auxP alg I hs Cs carriers).seedBits + 30 ≤ cap)
    (hFc : SymDec.hbCost cap + FS.bound cap ≤ Bf)
    (hFN : ∀ q ≤ UnaryCalc.value DL CL (2 ^ NumsXH.mOfH KL KH (I.starParams n hs)),
      FS.need (auxP alg I hs Cs carriers).len (auxP alg I hs Cs carriers).cap (auxP alg I hs Cs carriers).errExp
          (auxP alg I hs Cs carriers).len (2 * (2 * (q / Fintype.card (GapSeed (auxP alg I hs Cs carriers)))))
          (thrPool (I.starParams n hs) Cs carriers).length 0 (Fintype.card (GapSeed (auxP alg I hs Cs carriers))) ≤ cap ∧
        FiltPipe.filtPipeBound (auxP alg I hs Cs carriers) (SymDec.hseed (auxP alg I hs Cs carriers) q)
          (auxP alg I hs Cs carriers).len (2 * (2 * (q / Fintype.card (GapSeed (auxP alg I hs Cs carriers)))))
          (thrPool (I.starParams n hs) Cs carriers).length 0 (FiltSetup.rulerW (auxP alg I hs Cs carriers))
          (FiltSetup.rulerW (auxP alg I hs Cs carriers)) ≤ BP)
    (hnU : CellLoopD.cpCost (Data.unaryList (ThrData.hashNums (I.starParams n hs) Cs carriers alg Dexp (capT n) ++
        ThrData.thrCounts Cs carriers)).length + 1 +
      (SymDec.hNCost n (thrReq n a' ha' Cs carriers translation).word.length cr cap + 1 + (Bf + 12) + 1 + (BP + 4) +
        1 + (3 * UnaryCalc.value DL CL (2 ^ NumsXH.mOfH KL KH (I.starParams n hs)) + 3)) ≤ nU)
    (hB : costH D C D2 C2 Dv Cv cr DL CL KL KH (thrReq n a' ha' Cs carriers translation).word.length n
      (S.cost3 a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) nU
      (NumsXH.mOfH KL KH (I.starParams n hs)) ≤ Bud) :
    WriterIfaceJ.WriterRun (shellMGH4 S W.x (CellUnit.unitM W (SymDec.hdecW W FS cr)) D C D2 C2 Dv Cv DL CL
      (NumsXH.numsMH KL KH cr)) Bud (shellInX4 W.x D D2 Dv DL S.x3) (shellOutX4 W.x D D2 Dv DL S.x3)
      (thrReq n a' ha' Cs carriers translation).word (hashTape alg I hs Cs carriers) := by
  subst hDexp
  -- the request word
  have hw : (thrReq n a' ha' Cs carriers translation).word = Data.reqW n true (ReqBridge.thrCodes Cs)
      (carriers.map Stars.Carrier.code) (RepairRepresentation.natListWord translation) := by
    have h := ReqBridge.reqW_thrReq ha' Cs carriers translation []
    rw [List.append_nil, List.append_nil] at h
    exact h.symm
  -- the numbers
  have hhs := ThrData.hashNums_length (I.starParams n hs) Cs carriers alg I.D (capT n)
  have hxs : (carriers.map (·.length)).length ≤ 2 := by rw [List.length_map]; exact hD.hk
  have h0v : (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (capT n)).getD 0 0 =
      (carriers.map (·.length)).length := by
    rw [List.length_map]; rfl
  have e1 : (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (capT n)).getD 1 0 = capT n := rfl
  have hPc : (auxP alg I hs Cs carriers).cap = ((carriers.map (·.length)).length + 1) * 4096 *
      (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (capT n)).getD 1 0 := by
    rw [List.length_map, e1, hcapT, auxP_cap]
  have hPe : (auxP alg I hs Cs carriers).errExp =
      (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (capT n)).getD 13 0 := by
    rw [auxP_err, hcapT, hashNums_ee]
  have hPc1 : 1 ≤ (auxP alg I hs Cs carriers).cap := by
    rw [hPc, e1]
    have h1 : 1 ≤ ((carriers.map (·.length)).length + 1) * 4096 := by omega
    have := Nat.mul_le_mul h1 hU
    omega
  have hdec := hash_unitOK cap W FS cr (I.starParams n hs) hrP (thrReq n a' ha' Cs carriers translation).word
    (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) (RepairRepresentation.natListWord translation) hw
    (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (capT n)) (carriers.map List.length)
    (PrimT.ThrTab.tupleG Cs).length hhs hxs h0v (auxP alg I hs Cs carriers) (auxP_len alg I hs Cs carriers)
    (by rw [List.length_map, e1, hcapT, auxP_cap]) hPe
    hPc1 (thrPool (I.starParams n hs) Cs carriers).length
    (hash_pool alg (I.starParams n hs) Cs carriers I.D (capT n)) nU Bf BP
    (UnaryCalc.value DL CL (2 ^ NumsXH.mOfH KL KH (I.starParams n hs))) hc1 hc2 hc3 hcl hcs
    (by rw [List.length_map]; exact hcD1) hcG1 hcG2 hcG3 hcG4 hcG5 hcD3 hcJ hFc hFN hnU
  -- the shell
  have hmin : min nU (UnaryCalc.value D C (2 ^ NumsXH.mOfH KL KH (I.starParams n hs))) = nU :=
    Nat.min_eq_left (Nat.le_of_succ_le hR)
  have hB' : 2 * shellCostG (thrReq n a' ha' Cs carriers translation).word n D C D2 C2
      (S.cost3 a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv
      (2 * NumsXH.numsStageCostH n cr KL KH (UnaryCalc.value Dv Cv n) + 2) (NumsXH.mOfH KL KH (I.starParams n hs))
      DL CL nU + 2 ≤ Bud := by
    unfold costH at hB
    rw [hmin, ← shellCostG_len] at hB
    exact hB
  have hrun := shell_runH4 S W.x (CellUnit.unitM W (SymDec.hdecW W FS cr)) D C D2 C2 Dv Cv DL CL
    (NumsXH.numsMH KL KH cr) (2 * NumsXH.numsStageCostH n cr KL KH (UnaryCalc.value Dv Cv n) + 2)
    (NumsXH.mOfH KL KH (I.starParams n hs)) cap nU Bud (I.starParams n hs) Cs carriers
    (RepairRepresentation.natListWord translation) (thrReq n a' ha' Cs carriers translation).word _ hw hD hcu3 hdesc
    hneed (dimOK_numsH KL KH cr (I.starParams n hs) hrP _ _ (hw.trans (reqW_natWord _ _ _ _ _)) _ hW) hcap hR hboot
    hdec hB'
  rw [hash_units alg I hs Cs carriers _ hTOT] at hrun
  exact hrun

end Ready

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
