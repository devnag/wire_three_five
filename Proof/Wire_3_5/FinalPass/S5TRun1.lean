import Lean
import Proof.Wire_3_5.FinalPass.S5TRun0
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.S5TChA
import Proof.Wire_3_5.FinalPass.S5TChC
import Proof.Wire_3_5.FinalPass.S5TJoin2
import Proof.Wire_3_5.FinalPass.S5TNum1
import Proof.Wire_3_5.FinalPass.S5TNum3
import Proof.Wire_3_5.FinalPass.S5TStage
import Proof.Wire_3_5.FinalPass.SeamsProg2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.TS4K
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Proof.Wire_3_5.Primitive.SeedFix.TS4O
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.S5TNum4


noncomputable section
set_option maxRecDepth 120000


/-! # S5-THR, part 40: the THR stage at a THR request (P3:3170-3181)

At every THR request of every call family the THR half's stage (parse ; THR path) runs from the prelude's exit at
`D = Dl l`, `j₀ = j_L = H − 1`, `j₁ = H`, `c₀ = c0T l F` (**`stage_thr_at`**): within `W − 1` steps
(`W = y^{D+1}`, `y = |fpIn| + 1 + c₀`) it writes THR slots `8 … 15` of `frontWordsW` (the joins of `Join`, `Join2`),
keeps the input and the top power's zeros, and keeps every register `≤ 2W + 2`. Every side condition of
`stage_thr` is discharged from the call's precondition (`call_facts`, `vals_le`) and the size bounds (`Num1`–`Num4`).

Paper quantity of the main type: THR slots `8 … 15` of the front's words at a THR call (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2OutPorts)

section Run1
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The padded count base at a request. -/
noncomputable abbrev yOf (r : PlanFP.FReq l F kclk coef A a ha) : ℕ :=
  (PlanFP.fpIn l F kclk coef A a ha r).length + 1 + c0T l F

/-- **The THR stage at a THR request.** -/
theorem stage_thr_at (Sw : SymWords) (n : ℕ) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩) :
    ∃ (σE : WState (nsL (Dl l) (x6L l) (xtL l)) nrL) (c : ℕ),
      Step (stageM (Dl l) (PrimT.W6.litAlg l) 1 l F.cr (Hd l - 1) (Hd l - 1) (Hd l)) c
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2)
          (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) (PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩))).H
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2)
          (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) (PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩))).A
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2) σE).H
        (wenc (2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2) σE).A ∧
      c + 1 ≤ yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) ∧
      (∀ m : Fin 8, σE.st (sSlot (Dl l) (x6L l) (xtL l) m) =
        frontWordsW l F kclk coef A a ha Sw ⟨_, hc⟩ ⟨m.val + 8, by omega⟩) ∧
      σE.st (sIn (Dl l) (x6L l) (xtL l)) = frame (PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩) ∧
      σE.st (xsN (Dl l) (x6L l) (xtL l) (Dl l)) =
        List.replicate (yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 1) false ∧
      (∀ j, σE.val j ≤ 2 * yOf l F kclk coef A a ha ⟨_, hc⟩ ^ (Dl l + 1) + 2) := by
  obtain ⟨hcar, hd, he, hs⟩ := call_facts l F kclk coef A a ha ha' Cs carriers translation hc
  have hn1 := one_le_n l F kclk coef A a ha hs
  have hfp := fpIn_thr l F kclk coef A a ha n a' ha' carriers translation Cs hc
  have hsp : PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩ = preC l F kclk coef A a ha hs ha' Cs carriers translation ++
      frame (List.ofFn (hbC l F kclk coef A a ha hs Cs carriers translation)) :=
    fpIn_thr_split l F kclk coef A a ha n a' ha' carriers translation Cs hc hs
  have hnu := FpInLen.n_le_fpIn (⟨_, hc⟩ : PlanFP.FReq l F kclk coef A a ha)
  have w0 := thr_w0 (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw n a' ha' Cs carriers translation hs
  have wpay := thr_wpay (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw n a' ha' Cs carriers translation hs
  have w5 := thr_w5 (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw n a' ha' Cs carriers translation hs
  have w6 := thr_w6 (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw n a' ha' Cs carriers translation hs
  have w7 := thr_w7 (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw n a' ha' Cs carriers translation hs
  have hmp := mp_eqL l F kclk coef A a ha hs Cs carriers
  have hlv := level_castS hmp (hbC l F kclk coef A a ha hs Cs carriers translation)
  have hofn := ofFn_castS hmp (hbC l F kclk coef A a ha hs Cs carriers translation)
  unfold yOf
  generalize PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩ = u at hfp hsp hnu ⊢
  -- the constants
  have hc0 : 100000 ≤ c0T l F ∧ KtT l F ≤ c0T l F ∧ PrimT.TS4.capKc l F.cr ≤ c0T l F ∧
      PrimT.TS4.NCoef l F.cr ≤ c0T l F ∧ PrimT.TS4.Kp l F.cr ≤ c0T l F ∧
      (PrimT.W6.numsW6 (PrimT.W6.litAlg l) 1).Cc ≤ c0T l F ∧
      (PrimThrW.TF3Cost.topFront3 (PrimT.W6.litAlg l)).Cc ≤ c0T l F ∧
      PrimAsm.ThrData.thrDataStage2.Cc ≤ c0T l F := by
    unfold c0T; omega
  obtain ⟨k0, kK, kC, kN, kP, k6, k3, kd⟩ := hc0
  have hH30 := one_le_Hd l
  have hHd : PrimT.TS4.NDeg l + 1 ≤ Hd l ∧ PrimT.TS4.Dp l ≤ Hd l ∧
      (PrimT.W6.numsW6 (PrimT.W6.litAlg l) 1).Dc ≤ Hd l ∧
      (PrimThrW.TF3Cost.topFront3 (PrimT.W6.litAlg l)).Dc ≤ Hd l ∧ PrimAsm.ThrData.thrDataStage2.Dc ≤ Hd l ∧
      DtT l + 1 ≤ Hd l ∧ PrimAsm.CallIndexR.capZR l + 1 ≤ Hd l := by
    unfold Hd; omega
  obtain ⟨dN, dP, d6, d3, dd, dT, dZ⟩ := hHd
  have hZD := Zx_le_Dl l
  have hZx : Zx l = 3 * Hd l + 1 := rfl
  -- the base
  obtain ⟨y, hy⟩ : ∃ y, y = u.length + 1 + c0T l F := ⟨_, rfl⟩
  rw [← hy]
  have hnu' : n ≤ u.length := hnu
  have hy0 : 100000 ≤ y := by omega
  have hy1 : 1 ≤ y := by omega
  have hny : n + 1 ≤ y := by omega
  have huy : u.length + 1 ≤ y := by omega
  have pH : y ^ 2 ≤ y ^ Hd l := Nat.pow_le_pow_right hy1 (by omega)
  have p27 : y ^ 27 ≤ y ^ Hd l := Nat.pow_le_pow_right hy1 (by omega)
  have p2 : 100000 * y ≤ y ^ 2 := by nlinarith
  have p26 : 100000 * y ^ 26 ≤ y ^ 27 := mul_pow_le hy0
  have p1 : 1 ≤ y ^ 26 := Nat.one_le_pow _ _ (by omega)
  have hn26 : (n + 1) ^ 26 ≤ y ^ 26 := Nat.pow_le_pow_left hny 26
  have pHs : 100000 * y ^ Hd l ≤ y ^ (Hd l + 1) := mul_pow_le hy0
  have pZ : y ^ (Hd l + 1) ≤ y ^ Zx l := Nat.pow_le_pow_right hy1 (by omega)
  have p3 : 1000 * (y ^ Hd l) ^ 3 ≤ y ^ Zx l := by
    rw [← pow_mul]
    have h := mul_pow_le (Z := y) (e := Hd l * 3) (c := 1000) (by omega)
    rw [show Hd l * 3 + 1 = Zx l by omega] at h
    exact h
  have pZs : 1 ≤ y ^ Hd l := Nat.one_le_pow _ _ (by omega)
  have pY2 : y ^ Hd l ≤ (y ^ Hd l) ^ 3 := Nat.le_self_pow (by norm_num) _
  have pY23 : (y ^ Hd l) ^ 2 ≤ (y ^ Hd l) ^ 3 := Nat.pow_le_pow_right pZs (by norm_num)
  have eY : y ^ Hd l * y ^ Hd l = (y ^ Hd l) ^ 2 := by ring
  have pD : y ^ Zx l ≤ y ^ Dl l := Nat.pow_le_pow_right hy1 hZD
  have pW : 100000 * y ^ Dl l ≤ y ^ (Dl l + 1) := mul_pow_le hy0
  -- the numbers
  have hv : ∀ i, (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers).get i ≤ y ^ Hd l := fun i =>
    (vals_le l F kclk coef A a ha hs ha' Cs carriers hcar hd i).trans (kn_le_pow (by omega) hny dT hy1)
  have vM : (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers)).M ≤ y ^ Hd l := hv 6
  have vB : (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers)).Bstar ≤ y ^ Hd l := hv 8
  have vJ : (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers)).J ≤ y ^ Hd l := hv 9
  have vt : (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers)).t ≤ y ^ Hd l := hv 10
  have vl : (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers)).ell0 ≤ y ^ Hd l := hv 12
  have vG : (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers).nG ≤ y ^ Hd l := hv 0
  have vD : (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers).dig ≤ y ^ Hd l := hv 5
  obtain ⟨sW, sO, sN, sS⟩ := mp_words_le (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs
    (PrimT.W6.litAlg l) 1 carriers)) (castS hmp (hbC l F kclk coef A a ha hs Cs carriers translation)) (y ^ Hd l)
    pZs vM vt vB vJ vl
  have hc2a : 2 * (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
      carriers)).t * (2 * (mpOf (vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs
      (PrimT.W6.litAlg l) 1 carriers)).ell0 + 2) ≤ 2 * y ^ Hd l * (2 * y ^ Hd l + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hc2b : 2 * y ^ Hd l * (2 * y ^ Hd l + 2) = 4 * (y ^ Hd l * y ^ Hd l) + 4 * y ^ Hd l := by ring
  have hcap : PrimT.TS4.capTL l F.cr n ≤ y ^ Hd l :=
    (PrimT.TS4.capTL_le1 l F.cr n).trans (kn_le_pow (by omega) hny dZ hy1)
  have hN : PrimT.TS4.needT l F.cr n ≤ y ^ Hd l :=
    (PrimT.TS4.needT_le l F.cr n).trans (kn_le_pow (by omega) hny dN hy1)
  have hcodes := natWord_le_reqW n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
    (RepairRepresentation.natListWord translation ++
      seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
  rw [← hfp] at hcodes
  have hlen : (preC l F kclk coef A a ha hs ha' Cs carriers translation ++
      frame (List.ofFn (castS hmp (hbC l F kclk coef A a ha hs Cs carriers translation)))).length = u.length := by
    rw [hofn, hsp]
  have hu' : PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .thr, a', ha', Cs, carriers, translation⟩) =
      preC l F kclk coef A a ha hs ha' Cs carriers translation ++
        frame (List.ofFn (castS hmp (hbC l F kclk coef A a ha hs Cs carriers translation))) := by
    rw [← hfp, hsp, hofn]
  have hcl : (PrimAsm.ReqBridge.thrCodes Cs).length = a' := by simp [PrimAsm.ReqBridge.thrCodes]
  have hA := PrimT.TS4.a2_le a' ha'
  have hA' := Nat.le_mul_of_pos_left (40 * 2 ^ natBitLength a' + 40) (show 0 < natBitLength a' + 2 by omega)
  have eA : 2 ^ (natBitLength a' + 1) = 2 ^ natBitLength a' * 2 := pow_succ _ _
  have hK := PrimT.TS4.a2_le carriers.length (by omega)
  have hK' := Nat.le_mul_of_pos_left (40 * 2 ^ natBitLength carriers.length + 40)
    (show 0 < natBitLength carriers.length + 2 by omega)
  have eK : 2 ^ (natBitLength carriers.length + 1) = 2 ^ natBitLength carriers.length * 2 := pow_succ _ _
  have hNn := PrimT.TS4.a1_le n y (by omega)
  have hNn' := Nat.le_mul_of_pos_left (40 * 2 ^ natBitLength n + 40) (show 0 < natBitLength n + 2 by omega)
  have eN : 2 ^ (natBitLength n + 1) = 2 ^ natBitLength n * 2 := pow_succ _ _
  have eN6 : 2 ^ (natBitLength n + 1) ≤ 6 * y ^ 2 := by omega
  have hnb := ThrSz.nbl_le n
  have hPn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  have h26P : (((callInputs l F kclk coef A a ha).starParams n hs).n + 1) ^ 26 ≤ y ^ 26 := hn26
  have hcapP : PrimT.TS4.capTL l F.cr ((callInputs l F kclk coef A a ha).starParams n hs).n ≤ y ^ Hd l := hcap
  have hNP : PrimT.TS4.needT l F.cr ((callInputs l F kclk coef A a ha).starParams n hs).n ≤ y ^ Hd l := hN
  have hnbP : natBitLength ((callInputs l F kclk coef A a ha).starParams n hs).n ≤ n + 1 := hnb
  have eNP : 2 ^ (natBitLength ((callInputs l F kclk coef A a ha).starParams n hs).n + 1) ≤ 6 * y ^ 2 := eN6
  have hcu := counts_le ha' Cs carriers hcar hd he
  have hclP : (@PrimAsm.ReqBridge.thrCodes ((callInputs l F kclk coef A a ha).starParams n hs).n a' Cs).length = a' :=
    hcl
  have hpcapN : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength (PrimAsm.ReqBridge.thrCodes Cs).length + 1) + 1 ≤
      2 * y ^ (Dl l + 1) + 2 := by
    rw [hcl]; omega
  have hLd : ∀ i, (Cs i).descriptionBits ≤ y ^ Hd l := fun i => by have := hd i; omega
  have hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ y ^ Hd l := fun X hX g hg => by
    have := (he X hX).2 g hg; omega
  have hKc : ∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ u.length := fun i =>
    (nbl_le_natWord _).trans (hcodes.1 _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hKX : ∀ X ∈ carriers, natBitLength X.code ≤ u.length := fun X hX =>
    (nbl_le_natWord _).trans (hcodes.2 _ (List.mem_map.mpr ⟨X, hX, rfl⟩))
  have htd := PrimAsm.ThrData.thrDataStage2.cost_le Cs carriers (y ^ Hd l) (y ^ (Hd l + 1)) u.length ha' hcar hLd
    hLX hKc hKX (by omega)
  have hok := tf2ok_of Cs (carriers.map Stars.Carrier.code) (y ^ Hd l) (u.length + 1) ha' (by simpa using hcar)
    (by omega) (fun x hx => (hcodes.1 x hx).trans (by omega)) (fun x hx => (hcodes.2 x hx).trans (by omega))
    (by omega)
  -- the stage
  obtain ⟨σE, c, hstep, hcle, hin, h0, hpay, h5, h6, h7, hxD, hreg⟩ :=
    stage_thr (Dl l) (PrimT.W6.litAlg l) 1 (2 * y ^ (Dl l + 1) + 2) l F.cr (Hd l - 1) (Hd l - 1) (Hd l)
      (by omega) (by omega) (by omega)
      (σ03 (nr := nrL) (Dl l) (fs2 (Dl l) (x6L l) (xtL l)) (c0T l F) u)
      ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
      (RepairRepresentation.natListWord translation ++
        seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
      (y ^ Hd l) (y ^ Hd l) (y ^ (Hd l + 1)) (preC l F kclk coef A a ha hs ha' Cs carriers translation)
      (castS hmp (hbC l F kclk coef A a ha hs Cs carriers translation))
      (hu := hu')
      (hIn := (σ03_in (Dl l) (x6L l) (xtL l) (c0T l F) u).trans (congrArg frame hfp))
      (hT := by rw [σ03_tm, hlen])
      (hx0 := by rw [σ03_xs (Dl l) (x6L l) (xtL l) (c0T l F) u (Hd l - 1) (by omega), ← hy,
        show Hd l - 1 + 1 = Hd l by omega])
      (hxL := by rw [σ03_xs (Dl l) (x6L l) (xtL l) (c0T l F) u (Hd l - 1) (by omega), ← hy,
        show Hd l - 1 + 1 = Hd l by omega])
      (hxW := by rw [σ03_xs (Dl l) (x6L l) (xtL l) (c0T l F) u (Hd l) (by omega), ← hy])
      (hbl := fun i hi => σ03_blank (Dl l) (x6L l) (xtL l) (c0T l F) u i (by omega) (by omega) (by omega) (by omega))
      (hsh := σ03_sh (Dl l) (x6L l) (xtL l) (c0T l F) u) (hz0 := σ03_val (Dl l) (x6L l) (xtL l) (c0T l F) u)
      (hpcap := hpcapN) (hacap := by omega)
      (hKb := fun x hx => (nbl_le_natWord x).trans ((hcodes.1 x hx).trans (by omega)))
      (ha := ha') (hnc := hcar) (hN := (show PrimT.TS4.needT l F.cr n ≤ 2 * y ^ Hd l + 2 by omega)) (hn := hn1)
      (hd := hd)
      (hcap1 := PrimT.TS4.capTL_pos l F.cr n) (hok := hok)
      (hneed := PrimT.TS4.needW_of l F.cr n (y ^ Hd l) (by omega))
      (hL := hLd) (hLX := hLX) (h2 := (show 2 ≤ n + y ^ Hd l by omega))
      (hcN := (show natBitLength n + 1 ≤ 2 * y ^ (Hd l + 1) + 2 by omega))
      (hcA := (show 2 ^ (natBitLength a' + 1) ≤ 2 * y ^ (Hd l + 1) + 2 by omega))
      (hcK := (show 2 ^ (natBitLength carriers.length + 1) ≤ 2 * y ^ (Hd l + 1) + 2 by omega))
      (hcx := fun x hx => (show 2 * (RepairRepresentation.natWord x).length + 2 + n + y ^ Hd l ≤
        2 * y ^ (Hd l + 1) + 2 by have := hcodes.1 x hx; omega))
      (hcy := fun x hx => (show 2 * (RepairRepresentation.natWord x).length + 2 + n + y ^ Hd l ≤
        2 * y ^ (Hd l + 1) + 2 by have := hcodes.2 x hx; omega))
      (hcu := (show 2 * (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length + 2 ≤
        2 * y ^ (Hd l + 1) + 2 by omega))
      (hcapn := (show n ≤ 2 * y ^ (Dl l + 1) + 2 by omega))
      (hc1 := by rw [hlen]; omega) (hc2 := by omega) (hc3 := by omega) (hc4 := by omega)
      (hcapS := by omega) (hcapO := by omega) (hM := by omega) (hJ := by omega) (hc5 := by omega)
  -- the cost
  have hZ : 30000 ≤ y ^ Zx l := by omega
  have hc' := hcle.trans (stageThr_le _ _ _ _ (y ^ Zx l) (Hd l) hZ (by omega)
    (parse_le _ _ _ _ (by omega) (by omega) (by omega))
    (chainA_le (PrimT.W6.litAlg l) 1 l F.cr _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (show (carriers.map Stars.Carrier.code).length ≤ 2 by simpa using hcar)
      (by omega) (by omega) (by omega) (by omega) (by omega) dP (by omega) d6)
    (chainB_le (PrimT.W6.litAlg l) Cs carriers _ _ _ u.length _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) d3 htd (by omega) (by omega) dd)
    (tail_le _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)))
  have eD : (y ^ Zx l) ^ (2 * Hd l + 3) = y ^ Dl l := by rw [← pow_mul]; rfl
  rw [eD] at hc'
  refine ⟨σE, c, hstep, by omega, ?_, hin.trans (congrArg frame hfp.symm), by rw [hxD, σ03_xsD, hy], hreg⟩
  intro m
  match m with
  | ⟨0, _⟩ => exact h0.trans w0.symm
  | ⟨1, _⟩ =>
    refine (hpay 0 (by omega)).trans (Eq.trans ?_ (wpay 1 (by omega) (by omega)).symm)
    simp [tf2OutPorts, alg_eq] <;> rfl
  | ⟨2, _⟩ =>
    refine (hpay 1 (by omega)).trans (Eq.trans ?_ (wpay 2 (by omega) (by omega)).symm)
    simp [tf2OutPorts, alg_eq] <;> rfl
  | ⟨3, _⟩ =>
    refine (hpay 2 (by omega)).trans (Eq.trans ?_ (wpay 3 (by omega) (by omega)).symm)
    simp [tf2OutPorts, alg_eq] <;> rfl
  | ⟨4, _⟩ =>
    refine (hpay 3 (by omega)).trans (Eq.trans ?_ (wpay 4 (by omega) (by omega)).symm)
    simp [tf2OutPorts, alg_eq] <;> rfl
  | ⟨5, _⟩ => exact h5.trans w5.symm
  | ⟨6, _⟩ => exact (h6.trans hlv).trans w6.symm
  | ⟨7, _⟩ => exact h7.trans w7.symm

end Run1

end NearCubicWires.WireExponent3_5.FinalPass.S5T

end
