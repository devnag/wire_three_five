import Proof.Wire_3_5.Primitive.Writers.ThrHc3S
import Proof.Wire_3_5.Primitive.Writers.ThrBud2
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfC
import Proof.Wire_3_5.Primitive.SeedFix.TS4W

/-! # c4 THR block, piece 9 part 1: the THR stage at one THR call (`thr_plain_run`)

The THR twin of `sym_plain_run` (C4SymLfB): at a THR call, from the contract's side conditions (`ThrEAt3`), its
load (`c3_le`) and strip (`ThrStripAt`), the numbers' fits at the capacity v2 (`ThrFitAt`), the v4 data stage `S4`
at the unary numbers `C_L(n+1)^D ≥ needW` and `C_d(n+1)^D` above the data word, and PA's C3 request writer, the THR
stage runs to the call's seed word within any budget above its steps (`thr_stage_of_big` with `thr_hd`,
`thr_hxe_at`, `thr_big_at`, `thr_hc3S`) (P3:3011-3016, 3034-3038, 3098-3100).
* **`thr_data_W`** (the data stage's premises at `W = C_d(n+1)^D` above the data word and the stage's need),
  **`thr_plain_run`**.

Paper quantity of the main type: the THR stage's output at the call (its seed word) within the budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrLf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

/-- **The data stage's premises at the unary numbers** above the data word's unary length and the stage's need. -/
theorem thr_data_W (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation)) (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)
    (Cnw Dnw : ℕ) (hnw : PrimT.C4GateSym.needW n ≤ Cnw * (n + 1) ^ Dnw) (Kn Dn : ℕ) (need : ℕ)
    (hneed : need ≤ Kn * (n + 1) ^ Dn) :
    PrimT.C4GateSym.needW n ≤ UnaryCalc.value (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + Dn + 16) (Cnw + 1) n ∧
      UnaryCalc.value (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + Dn + 16) (Cnw + 1) n ≤
        UnaryCalc.value (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + Dn + 16)
          (Cnw + 1 + 16 * (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F + 1) + Kn) n ∧
      2 * (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)).length +
          2 * UnaryCalc.value (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + Dn + 16) (Cnw + 1) n ≤
        2 * UnaryCalc.value (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + Dn + 16)
          (Cnw + 1 + 16 * (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F + 1) + Kn) n ∧
      need ≤ 2 * UnaryCalc.value (Dnw + HashLeaf.tnD (PrimT.W6.thrNumsPoly l) + Dn + 16)
          (Cnw + 1 + 16 * (HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F + 1) + Kn) n + 2 := by
  obtain ⟨hk2, hdesc, -⟩ := PrimT.C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  obtain ⟨tK, htK⟩ : ∃ x, x = HashLeaf.tnK (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F :=
    ⟨_, rfl⟩
  obtain ⟨tD, htD⟩ : ∃ x, x = HashLeaf.tnD (PrimT.W6.thrNumsPoly l) := ⟨_, rfl⟩
  have hv : ∀ v ∈ (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs), v + 1 ≤ tK * (n + 1) ^ tD + 1 := by
    intro v hv
    have h := HashLeaf.tn_spec (PrimT.W6.thrNumsPoly l) (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) F
      kclk coef A a0 ha0 n hs Cs carriers _ ha hk2 hdesc (HashFam.fam_capT l F kclk coef A a0 ha0 n) v hv
    rw [← htK, ← htD] at h
    omega
  have hl : (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).length = 16 := ThrData.hashNums_length _ _ _ _ _ _
  have hu : (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)).length ≤ 16 * (tK * (n + 1) ^ tD + 1) := by
    have h := ThrBud.unary_le _ _ hv
    rwa [hl] at h
  rw [← htK, ← htD]
  obtain ⟨D, hD⟩ : ∃ x, x = Dnw + tD + Dn + 16 := ⟨_, rfl⟩
  rw [← hD]
  have p1 : (n + 1) ^ Dnw ≤ (n + 1) ^ D := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : (n + 1) ^ tD ≤ (n + 1) ^ D := Nat.pow_le_pow_right (by omega) (by omega)
  have p3 : (n + 1) ^ Dn ≤ (n + 1) ^ D := Nat.pow_le_pow_right (by omega) (by omega)
  have p0 : 1 ≤ (n + 1) ^ D := Nat.one_le_pow _ _ (by omega)
  have q1 : Cnw * (n + 1) ^ Dnw ≤ Cnw * (n + 1) ^ D := Nat.mul_le_mul_left _ p1
  have q2 : tK * (n + 1) ^ tD ≤ tK * (n + 1) ^ D := Nat.mul_le_mul_left _ p2
  have q3 : Kn * (n + 1) ^ Dn ≤ Kn * (n + 1) ^ D := Nat.mul_le_mul_left _ p3
  unfold UnaryCalc.value
  have e1 : (Cnw + 1) * (n + 1) ^ D = Cnw * (n + 1) ^ D + (n + 1) ^ D := by ring
  have e2 : (Cnw + 1 + 16 * (tK + 1) + Kn) * (n + 1) ^ D = Cnw * (n + 1) ^ D + (n + 1) ^ D +
      16 * (tK * (n + 1) ^ D) + 16 * (n + 1) ^ D + Kn * (n + 1) ^ D := by ring
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The THR stage at a THR call** within any budget above the steps of every family whose cells fit the pad. -/
theorem thr_plain_run (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (EW : Envelope)
    (cW K3 D3 kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (C3 : C3ReqIface3.C3ReqAt3 l F EW cW K3 D3 kclk coef A a0 ha0)
    (L : Lay) (hL : L.S3 = ThrStrip.thrC3 C3.thr) (hDL : 16 ≤ L.D) (hT : (PrimT.C4SymW.famU wa).T + 1 + 1 + 1 ≤ L.T)
    (htS : 31 ≤ L.tS) (CL Cd Cc : ℕ) (Fp : FreeProg) (S4 : ThrData.ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D (fun n => ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap)) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation)) (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value L.D CL n)
    (hLW : UnaryCalc.value L.D CL n ≤ UnaryCalc.value L.D Cd n)
    (hcu : 2 * (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)).length + 2 * UnaryCalc.value L.D CL n ≤ 2 * UnaryCalc.value L.D Cd n)
    (hneed : S4.need n ≤ 2 * UnaryCalc.value L.D Cd n + 2)
    (dg K Kch : ℕ) (E3 : Envelope)
    (hE : ThrFam.ThrEAt3 (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg wa Cs carriers translation hs (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) dg K Kch E3)
    (hload : (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) + (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) + (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) + (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) ≤
      K3 * ((((gate0 l F).budget kclk coef A a0 ha0).psiOf n) + 1) * (n + 1) ^ D3)
    (hS : ThrFam.ThrStripAt (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) ha Cs carriers translation (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs))
    (hfit : ThrCap.ThrFitAt Fp F.cr F.filterErrDeg (2 ^ PrimT.C4Cap.capExp2 Cc n) (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg ha Cs carriers translation hs)
    (Bd : ℕ)
    (hBd : ∀ Fm : PrimT.C4Loop.ChildFam, Fm.cellCost + 1 ≤ 2 ^ (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6) → Fm.bound ≤ 8 * (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) →
      ∀ s : Fin (8 * (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs).ell) → Bool,
      wrapCost (ThrSet.setupT3Cost L ((thrReq n a ha Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs)) n CL Cd Cc (S4.cost3 a Cs carriers (UnaryCalc.value L.D CL n) (UnaryCalc.value L.D Cd n)) (2 ^ PrimT.C4Cap.capExp2 Cc n)
          (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length)
          (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) ++ ThrData.thrCounts Cs carriers))
          (ThrCap.thrBigCost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (PrimT.C4GateSym.needW n) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)))
          (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) (0 + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs) + PrimT.C4Geo.dRow ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6)
          (ThrStrip.thrB (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a0 ha0).kOf n) (((gate0 l F).budget kclk coef A a0 ha0).psiOf n)) (ThrHB.hbXCost n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length (ThrFam.kbT n) translation.length (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs).length (RepairRepresentation.natListWord translation).length + 60 * ((thrReq n a ha Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs)).length + 20) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) ((thrReq n a ha Cs carriers translation).word ++ (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs)).length (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4)))
        Fm (2 ^ (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 6)) (ThrFin.finCost (ThrFam.thrSP (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) s (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs)) + 1 ≤ Bd) :
    PrimT.SeedFixTypes.Stage3Run (ThrSet.thrStageU3 L CL Cd Cc S4.x3 S4.s3 S4.M3 Fp F.cr F.filterErrDeg wa hT) Bd
      (PrimT.SeedFixTypes.thrIn l F kclk coef A a0 ha0 n a ha Cs carriers translation hs)
      (thrTape (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation)
      (seedWord (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg (thrReq n a ha Cs carriers translation)) := by
  obtain ⟨hok, hpre, hQp, hcost, hrange, hR, hcf, h1⟩ := hE
  have hc3 := ThrSet.thr_hc3S l F EW cW K3 D3 kclk coef A a0 ha0 C3 L hL ha Cs carriers translation hcall hs
    (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) dg h1 hcf hload hS
  obtain ⟨hk2, hdesc, he⟩ := PrimT.C4GateSym.thr_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  obtain ⟨hL', hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu', -, -⟩ := PrimT.C4GateSym.thr_data_hyps Cs carriers ha hk2 hdesc he
    (UnaryCalc.value L.D CL n) hWL
  have hua : (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) ++ ThrData.thrCounts Cs carriers)).length = (Data.unaryList (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)).length +
      (Data.unaryList (ThrData.thrCounts Cs carriers)).length := by
    unfold Data.unaryList
    rw [List.flatMap_append, List.length_append]
  have hcu2 : 2 * (Data.unaryList ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) ++ ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by
    omega
  have hcN2 : natBitLength n + 1 ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by omega
  have hcA2 : 2 ^ (natBitLength a + 1) ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by omega
  have hcK2 : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * UnaryCalc.value L.D Cd n + 2 := by omega
  have hcx2 : ∀ x ∈ ReqBridge.thrCodes Cs,
      2 * (RepairRepresentation.natWord x).length + 2 + n + UnaryCalc.value L.D CL n ≤ 2 * UnaryCalc.value L.D Cd n + 2 :=
    fun x hx => by have := hcx x hx; omega
  have hcy2 : ∀ y ∈ carriers.map Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + UnaryCalc.value L.D CL n ≤ 2 * UnaryCalc.value L.D Cd n + 2 :=
    fun y hy => by have := hcy y hy; omega
  have hd := ThrSet.thr_hd S4 ((callInputs l F kclk coef A a0 ha0).starParams n hs) ha Cs carriers translation (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs) (UnaryCalc.value L.D CL n)
    (UnaryCalc.value L.D Cd n) hk2 hL' hLX h2 hcN2 hcA2 hcK2 hcx2 hcy2 hcu2 hdesc hneed
  obtain ⟨τh, hxe, hτh0, hZ⟩ := ThrCap.thr_hxe_at l F Fp kclk coef A a0 ha0 ha Cs carriers translation hcall hs hfit
  have hbig := ThrCap.thr_big_at l F Fp kclk coef A a0 ha0 ha Cs carriers translation hcall hs hfit
  have hkh1 := PrimT.C4SymLf.callKh_pos ((callInputs l F kclk coef A a0 ha0).starParams n hs)
  have hb : (ThrFam.thrFam (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation wa E3 (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 3) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 2) 0
      (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 4) dg (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 5) 0 (thrEnts (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers translation)
      (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 0) (Fp.val (ThrFam.thrX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs) 1) K Kch hok hpre hQp hcost).bound ≤ 8 * (max (SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) + SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) := by
    show 8 * max 1 (max (2 * SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs)) (Nat.clog 2 (SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs))) ≤ _
    omega
  exact ThrSet.thr_stage_of_big L (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg wa hDL CL Cd Cc S4.x3 S4.s3 _ S4.M3 Fp F.cr F.filterErrDeg
    hT htS ha Cs carriers translation hs (ThrCap.hbC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers translation hs) rfl _ hd τh _ hxe hτh0 hZ _ hbig hkh1 _ dg hc3 E3 K Kch hok hpre
    hQp hcost hrange hR Bd (hBd _ hR hb _)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrLf
