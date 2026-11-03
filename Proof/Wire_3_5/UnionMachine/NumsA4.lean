import Lean
import Proof.Wire_3_5.UnionMachine.NumsA3
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLk
import Proof.Wire_3_5.Primitive.SeedFix.C4BudD
import Proof.Wire_3_5.Primitive.Writers.ReqBridge
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.SymSz1
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsA4Base


noncomputable section
set_option maxRecDepth 4096


/-! # NW phase (a), part 4: the SYM numbers at a SYM request, at a polynomial capacity

P3:2929-2941, 2987-2988, 3011-3016, 3044-3048: at a SYM request `r` of the family, the SYM numbers program
(`C4Set.numsSW`, `numsS_spec`) runs from the cell's entry (the framed input `frame fpIn` on stream `0`, the counts
`unaryList (symCounts …)` on stream `113`) at the capacity `cap₀ ≥ K₀·(|fpIn|+1)^{D₀}`, `D₀ = K_F(fe) + 2`: its needs
from `sym_needsG` at `KQ = 2^{c_A+K_F}(n+2)^{K_F}2^k ≤ 2^{c_A+2K_F}(|fpIn|+1)^{K_F+2}` (`2^k = (2^{k_h})² ≤ Q²`,
`Q ≤ |fpIn|`, the printed sample). Its registers `G 21 = |E|`, `G 41 = |FlatSeed|`, `KB 52 = Q` multiply to `vOf r`.

* `numsP`, `countsOf`, `D0`, `K0`, `stV_one`, `q_le_fpIn`, **`numsAt`**.

Paper quantities of the main type: `|E|`, `|FlatSeed|`, `Q = symCount` at the request (`V = |E|·|FlatSeed|·Q`). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

section Gate
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM numbers program at the gate.** -/
noncomputable def numsP : WM (LNS 0) LNR :=
  PrimT.C4Set.numsSW F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)

/-- The numbers front's capacity degree (a function of `fe` alone). -/
noncomputable def D0 (fe : ℕ) : ℕ := KFa l fe + 2

/-- The numbers front's capacity coefficient. -/
noncomputable def K0 : ℕ := 100 * 2 ^ ((nwSB l F).cA + 2 * KFa l F.filterErrDeg) + 200002

/-- **`Q ≤ |fpIn|`** at a SYM request (the printed sample: `Q` pairs of `4k_h + 2` bits). -/
theorem q_le_fpIn {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤
      (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length := by
  show _ ≤ (PrimRequest.word ⟨n, .sym, a', ha', Cs, carriers, translation⟩ ++
    seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩).length
  simp only [seedWord, dif_pos hs]
  rw [List.length_append, S6Sizes.sampleWord_len, List.length_ofFn]
  have e : (SeedFix.symCallSample (callInputs l F kclk coef A a ha) hs Cs carriers translation).Q =
      SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers := rfl
  rw [e]
  have := Nat.le_mul_of_pos_right (SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers)
    (by omega : 0 < 4 * SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) + 2)
  omega

/-- `V` at a SYM request (on-star): `|E|·|FlatSeed|·Q`. -/
theorem vOf_sym {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    NumsPh2.vOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ =
      Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .sym n)) *
        Fintype.card (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).FlatSeed *
          SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers := by
  simp only [NumsPh2.vOf, NumsPh2.vOfReq, dif_pos hs]
  rfl

/-- **The SYM numbers at a SYM request**: `numsP` from the cell's entry at `cap₀ ≥ K₀·(|fpIn|+1)^{D₀}`, the three
registers multiplying to `vOf r`, the streams kept (the counts' head aside), within `3·10⁶·(cap₀+2)³` steps. -/
theorem numsAt (r : FReq l F kclk coef A a ha) (hm : r.1.mode = .sym) (cap₀ : ℕ)
    (hc : K0 l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ D0 l F.filterErrDeg ≤ cap₀) :
    ∃ (τ : WState (LNS 0) LNR) (c : ℕ), WExec cap₀ (numsP l F)
        (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha r) [] 0 (Data.unaryList (countsOf r.1))) τ c ∧
      τ.val (SymDec.G 21) * τ.val (SymDec.G 41) * τ.val (PrimT.C4Set.KB 52) = NumsPh2.vOf l F kclk coef A a ha r ∧
      τ.val (SymDec.G 21) * τ.val (SymDec.G 41) ≤ cap₀ ∧
      τ.val (PrimT.C4Set.KB 52) ≤ (fpIn l F kclk coef A a ha r).length ∧
      τ.st = (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha r) [] 0 (Data.unaryList (countsOf r.1))).st ∧
      (∀ s, s ≠ sk 0 113 →
        τ.sh s = (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha r) [] 0 (Data.unaryList (countsOf r.1))).sh s) ∧
      τ.cell = false ∧ c ≤ 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hm' : mode = .sym := hm
  subst hm'
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  obtain ⟨hk2, -, -⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a ha hs
  have hcl : (Data.symCodes a' Cs).length = a' := by unfold Data.symCodes; simp
  -- the input and its length
  obtain ⟨w, hwd⟩ : ∃ v, v = fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ :=
    ⟨_, rfl⟩
  rw [← hwd] at hc ⊢
  have hnw : n ≤ w.length := by
    have := FinalPass.FpInLen.n_le_fpIn (l := l) (F := F) (kclk := kclk) (coef := coef) (A := A) (a := a) (ha := ha)
      ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
    rw [hwd]; exact this
  have hQw : SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤ w.length := by
    rw [hwd]; exact q_le_fpIn l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := FinalPass.SymFr.kh_two l F kclk coef A a ha hs
  have hN : 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤
      SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers :=
    Sampler.N_le_sampleCount _ _ _ _ (by omega) (by omega)
  -- the envelope
  obtain ⟨X, hXd⟩ : ∃ v, v = w.length + 1 := ⟨_, rfl⟩
  rw [← hXd] at hc
  have eKF : (nwSB l F).KF = KFa l F.filterErrDeg := KF_eq l F
  obtain ⟨KF, hKFd⟩ : ∃ v, v = KFa l F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨cA, hcAd⟩ : ∃ v, v = (nwSB l F).cA := ⟨_, rfl⟩
  obtain ⟨k, hkd⟩ : ∃ v, v = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨kh, hkhd⟩ : ∃ v, v = SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  rw [← hkhd] at hN hkh
  rw [← hkd] at hkh
  have h2k : 2 ^ k ≤ X ^ 2 := by
    rw [← hkh, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by omega) 2
  have hn2 : n + 2 ≤ 2 * X := by omega
  have hp : (n + 2) ^ KF ≤ 2 ^ KF * X ^ KF := by rw [← mul_pow]; exact Nat.pow_le_pow_left hn2 _
  obtain ⟨KQ, hKQd⟩ : ∃ v, v = 2 ^ (cA + KF) * (n + 2) ^ KF * 2 ^ k := ⟨_, rfl⟩
  have hKQle : KQ ≤ 2 ^ (cA + 2 * KF) * X ^ (KF + 2) := by
    rw [hKQd]
    calc 2 ^ (cA + KF) * (n + 2) ^ KF * 2 ^ k ≤ 2 ^ (cA + KF) * (2 ^ KF * X ^ KF) * X ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) h2k
      _ = 2 ^ (cA + 2 * KF) * X ^ (KF + 2) := by rw [two_mul, pow_add, pow_add, pow_add]; ring
  have hP1 : 1 ≤ X ^ (KF + 2) := Nat.one_le_pow _ _ (by omega)
  have hPX : X ≤ X ^ (KF + 2) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (KF + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have eK0 : K0 l F * X ^ D0 l F.filterErrDeg =
      100 * (2 ^ (cA + 2 * KF) * X ^ (KF + 2)) + 200002 * X ^ (KF + 2) := by
    unfold K0 D0; rw [← hKFd, ← hcAd]; ring
  rw [eK0] at hc
  have hKQ : 100 * KQ + 200000 ≤ cap₀ := by omega
  have hwc : 2 * w.length + 2 ≤ cap₀ := by omega
  -- the needs
  obtain ⟨hN1, hKb, hC, hcS, hcP, hcC, hN2, hv, hag⟩ := sym_needsG l F kclk coef A a ha (nwSB l F) (nw_hwb l F)
    (nw_hnw l F) rfl rfl rfl rfl rfl rfl rfl rfl rfl ha' Cs carriers translation hcall hs cap₀ KQ
    (fun {X c d a'} hX hc hda => by
      rw [hKQd, hcAd, hKFd, ← eKF, hkd]
      exact kq_atom _ _ _ _ hX hc hda) hKQ
  -- `numsS_spec`'s premises
  have a_hw : w = Data.reqW ((callInputs l F kclk coef A a ha).starParams n hs).n false (Data.symCodes a' Cs)
      (carriers.map Stars.Carrier.code) (RepairRepresentation.natListWord translation ++
        seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩) := by
    rw [hwd]
    exact (ReqBridge.reqW_word ⟨n, .sym, a', ha', Cs, carriers, translation⟩ _).symm
  have a_ccs : (carriers.map Stars.Carrier.code).length = (carriers.map (·.length)).length := by
    rw [List.length_map, List.length_map]
  have a_cx : (carriers.map (·.length)).length ≤ 2 := by rw [List.length_map]; exact hk2
  have a_cy : (SymDec.cyOf Cs).length ≤ 4 := by rw [SymDec.cyOf_length]; exact ha'
  have a_N1 : P1Need cap₀ w ((callInputs l F kclk coef A a ha).starParams n hs).n (Data.symCodes a' Cs)
      (carriers.map Stars.Carrier.code) (carriers.map (·.length)) (SymDec.cyOf Cs)
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) :=
    ⟨hwc, hN1.cP, hN1.cX, hN1.cC⟩
  have hQl : (PrimT.C4Set.symInOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n) n
      (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) carriers.length a' (SymDec.cyOf Cs)).Q =
      SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers :=
    PrimT.C4SymL.symQ_link (callInputs l F kclk coef A a ha) Cs carriers hs ha' rfl rfl
  have a_Q : 2 * (PrimT.C4Set.symInOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
      ((callInputs l F kclk coef A a ha).starParams n hs).n
      (F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n)
      (Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
      (carriers.map (·.length)).length (Data.symCodes a' Cs).length (SymDec.cyOf Cs)).Q ≤ cap₀ := by
    rw [List.length_map, hcl]
    show 2 * (PrimT.C4Set.symInOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n) n
      (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) carriers.length a' (SymDec.cyOf Cs)).Q ≤ cap₀
    rw [hQl]
    omega
  have a_v : ∀ j : Fin 11, (![((gate0 l F).budget kclk coef A a ha).capOf .sym n,
      ((callInputs l F kclk coef A a ha).starParams n hs).n,
      F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n,
      Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n,
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs),
      (carriers.map (·.length)).length, (Data.symCodes a' Cs).length, (SymDec.cyOf Cs).getD 0 0,
      (SymDec.cyOf Cs).getD 1 0, (SymDec.cyOf Cs).getD 2 0, (SymDec.cyOf Cs).getD 3 0] : Fin 11 → ℕ) j ≤ cap₀ := by
    rw [List.length_map]; exact hv
  have a_N2 : SymDec.NumsNeed cap₀ ((callInputs l F kclk coef A a ha).starParams n hs).n
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
      (F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n) (SymDec.cyOf Cs).sum
      (carriers.map (·.length)).length (Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Data.symCodes a' Cs).length
      ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0)
      ((SymDec.cyOf Cs).getD 3 0) := by
    rw [List.length_map, hcl]; exact hN2
  obtain ⟨τ, c, e, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, hKB, -, hst, hsh, hcell, hcost⟩ :=
    PrimT.C4Set.numsS_spec cap₀ F.cr F.filterErrDeg (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)
      ((callInputs l F kclk coef A a ha).starParams n hs) rfl w (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (carriers.map (·.length)) (SymDec.cyOf Cs) (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26)
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n) (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) a_hw a_ccs a_cx a_cy hKb hC a_N1 rfl rfl
      rfl rfl hcS hcP hcC a_N2 (le_trans (by norm_num) hn8) a_Q a_v
  -- the values
  have e21 := hG 21
  rw [vec21] at e21
  change τ.val (SymDec.G 21) =
    2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a ha).capOf .sym n) (F.filterErrDeg * Ledger.Lq n)).seedBits
    at e21
  have e41 := hG 41
  rw [vec41, List.length_map] at e41
  change τ.val (SymDec.G 41) = 2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum
    (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a ha).capOf .sym n)) (Ledger.Lq n + 5) at e41
  have e52 : τ.val (PrimT.C4Set.KB 52) = SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers := by
    rw [hKB, List.length_map, hcl]; exact hQl
  have hg : 2 ^ (SymDec.gP n (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
      (F.filterErrDeg * Ledger.Lq n)).seedBits =
      Fintype.card (GapSeed ((callInputs l F kclk coef A a ha).filterParams .sym n)) :=
    SymDec.seed_eq_nGap (callInputs l F kclk coef A a ha) (n := n) _ rfl rfl
  have hf : 2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum
      (SymDec.bV carriers.length (((gate0 l F).budget kclk coef A a ha).capOf .sym n)) (Ledger.Lq n + 5) =
      Fintype.card (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).FlatSeed :=
    SymDec.fbv_eq_nFlat (callInputs l F kclk coef A a ha) Cs carriers _ rfl rfl
  have eu : countsOf ⟨n, .sym, a', ha', Cs, carriers, translation⟩ = carriers.map (·.length) ++ SymDec.cyOf Cs := rfl
  -- the steps
  have cP := hN1.cP
  have cC := hN1.cC
  have hsp := hcC.hs
  have hL := hcC.hL1
  have ht : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n ≤ cap₀ := by
    unfold SparseNum.sparseBound at hcP
    omega
  have h4 : 4 * (n + 3) ≤ (F.filterErrDeg + 4) * (n + 3) := Nat.mul_le_mul_right _ (by omega)
  have h5 : F.filterErrDeg ≤ (F.filterErrDeg + 4) * (n + 3) :=
    le_trans (Nat.le_add_right _ 4) (Nat.le_mul_of_pos_right _ (by omega))
  have v1 := Nat.one_le_two_pow (n := natBitLength n)
  have v2 := Nat.one_le_two_pow (n := natBitLength (Data.symCodes a' Cs).length)
  have v3 := Nat.one_le_two_pow (n := natBitLength (carriers.map Stars.Carrier.code).length)
  have hB : PrimT.C4SymN.symBigCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum 0 ≤
      3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) + 0 :=
    PrimT.C4Bud.symBig_le cap₀ n F.cr F.filterErrDeg _ _ (Ledger.Lq n) a' carriers.length _ ((n + 1) ^ 26) _
    0 (by omega) ha' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ht hsp hL
  have hcost' : c ≤ PrimT.C4Set.numsSCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum := by
    have := hcost
    rw [List.length_map, hcl] at this
    exact this
  have hsb : PrimT.C4Set.numsSCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum ≤
      PrimT.C4SymN.symBigCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum 0 := by
    unfold PrimT.C4SymN.symBigCost; omega
  -- the bound on `|E|·|FlatSeed|`
  have hst1 := stV_one ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0)
    ((SymDec.cyOf Cs).getD 3 0)
  have hGF : τ.val (SymDec.G 21) * τ.val (SymDec.G 41) ≤ KQ := by
    rw [e21, e41]
    exact le_trans (Nat.le_mul_of_pos_right _ (by omega)) hag
  rw [eu]
  refine ⟨τ, c, e, ?_, le_trans hGF (by omega), by rw [e52]; exact hQw, hst, hsh, hcell,
    le_trans hcost' (le_trans hsb (le_of_le_of_eq hB (Nat.add_zero _)))⟩
  rw [e21, e41, e52, hg, hf, vOf_sym l F kclk coef A a ha ha' Cs carriers translation hcall hs]

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
