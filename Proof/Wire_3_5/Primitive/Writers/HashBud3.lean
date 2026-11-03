import Lean
import Proof.Wire_3_5.Primitive.Writers.HashBud2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashS
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.HashFit1
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Proof.Wire_3_5.Primitive.SeedFix.TS4O
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 HASH budget (C), part 3: the cell and the writer at every THR call, at rate `7`

P3:3105-3115: the kept words writer's numbers `kwT ≤ 9q` at the call's unit `q = 2^{E·(B+1)²}` (**`kwT_le`**: the
majorant's `ℓ₀, pMod, B_*, t, J` are the call's THR numbers (`mp_eq`), `|𝒢|`, `nE`, `A` too, `N = 2^{k_h}`), and
**`hX_ex`**: one `c_X` (after `F`, the layout's degree `D`, `C_d`, `C_c` and the writer) with the HASH cell's and the
writer's steps at rate `7` at every THR call whose cell fits (`CellFit`, `B_m ≤ cap`, the writer's capacity
`fr 1 ≤ W`).

Paper quantity of the main type: the HASH setup's cell and writer steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Bud

/-- **The writer's numbers** at the call's unit. -/
theorem kwT_le (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (E : ℕ)
    (hE : HashFit.CallSz l F kclk coef A a0 ha0 ha Cs carriers translation hs E) :
    PrimT.C4KW.kwT (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) ≤
      9 * 2 ^ (E * PrimT.C4Cap.bsq n) := by
  obtain ⟨-, -, hhn, -, -, -, hkh, hnE, -, hG, -, -, -, -⟩ := hE
  have e7 : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).A ≤ 2 ^ (E * PrimT.C4Cap.bsq n) :=
    hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 7)
  have e8 : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).Bs ≤ 2 ^ (E * PrimT.C4Cap.bsq n) :=
    hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 8)
  have e9 : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).J ≤ 2 ^ (E * PrimT.C4Cap.bsq n) :=
    hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 9)
  have e10 : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).tt ≤ 2 ^ (E * PrimT.C4Cap.bsq n) :=
    hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 10)
  have e12 : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell0 ≤ 2 ^ (E * PrimT.C4Cap.bsq n) :=
    hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 12)
  have e13 : (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).pMod ≤ 2 ^ (E * PrimT.C4Cap.bsq n) :=
    hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 13)
  have hN : 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) ≤ 2 ^ (E * PrimT.C4Cap.bsq n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmp := HashCell.mp_eq (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers
  have f1 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.ell0 = (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).ell0 := by rw [hmp]; rfl
  have f2 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.refMod = (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).pMod := by rw [hmp]; rfl
  have f3 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.Bstar = (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).Bs := by rw [hmp]; rfl
  have f4 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.t = (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).tt := by rw [hmp]; rfl
  have f5 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).MP.J = (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).J := by rw [hmp]; rfl
  have f6 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).G = (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers).length := rfl
  have f7 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).N = 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) := rfl
  have f8 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).nE = WriterIface.nE (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers := rfl
  have f9 : (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).pops.length = (HashCell.cv (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).A := HashCell.pops_len (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers
  unfold PrimT.C4KW.kwT
  rw [f1, f2, f3, f4, f5, f6, f7, f8, f9]
  omega

/-- **The HASH cell and the kept words writer at rate `7`** at every THR call whose cell fits, with `B_m` within the
cell's capacity and the writer's capacity `fr 1 ≤ W`. -/
theorem hX_ex (l : Literals) (F : GateFree l) (Wk : PrimT.C4KW.KWW) (D Cd Cc : ℕ) :
    ∃ cX : ℕ, ∀ (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) (n a : ℕ) (ha : a ≤ 4)
      (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
      (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation) →
      ∀ (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (Bm Sm fr1 : ℕ),
      HashCell.CellFit (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation F.cr Bm Sm (2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2) →
      Bm ≤ 2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2 → fr1 ≤ 2 ^ PrimT.C4Cap.capExp2 Cc n →
      Ex n 7 cX (HashCell.callCost (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs ha Cs carriers translation (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg)
          (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D) F.cr (UnaryCalc.value D Cd n) (2 ^ PrimT.C4Cap.capExp2 Cc n) Bm Sm +
        Wk.cost (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) fr1) := by
  obtain ⟨E, hE⟩ := HashFit.call_sizes l F
  obtain ⟨cq, hcq⟩ := ex_s E
  obtain ⟨cT, hcT⟩ := ex_poly (D * (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc)
  obtain ⟨KT, hKT⟩ : ∃ x, x = Nat.clog 2 ((PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Cc * (Cd + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ x, x = CallIndexR.capZR l := ⟨_, rfl⟩
  obtain ⟨kC, hkC⟩ : ∃ x, x = CallIndexR.capK F.cr := ⟨_, rfl⟩
  obtain ⟨cN, hcN⟩ := ex_poly ((D + z) * (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc)
  obtain ⟨KN, hKN⟩ : ∃ x, x = Nat.clog 2 ((PrimT.W6.numsW6 (gate0 l F).alg 1).Cc * (Cd + kC * 2 ^ z + 2) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc) := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := PrimT.C4Cap.mul_sq_le_div16 (2 * F.cr + 2)
  obtain ⟨K3, hK3⟩ := FinalPass.HashFr.cube_absorb (FinalPass.HashFr.cHt l)
  obtain ⟨cg, hcg⟩ := ex_s (E * Wk.Dg)
  obtain ⟨Kg, hKg⟩ : ∃ x, x = Nat.clog 2 (10 ^ Wk.Dg) := ⟨_, rfl⟩
  obtain ⟨cU, hcU⟩ : ∃ x, x = Cc + 3 + cq + cT + KT + cN + KN + 2 * K0 + K3 + cg + Kg := ⟨_, rfl⟩
  refine ⟨Nat.clog 2 (1000000000 + 170 * Wk.K) + 4 * cU, ?_⟩
  intro kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs Bm Sm fr1 hfit hBm hfr
  have hE' := hE kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs
  have kw := kwT_le l F kclk coef A a0 ha0 ha Cs carriers translation hs E hE'
  obtain ⟨hw, hn3, hhn, hsx, htg, hcp, hkh, hnE, hM, hG, hcut, hpops, hpay, hcr⟩ := hE'
  obtain ⟨U, hU⟩ : ∃ x, x = 2 ^ (n / 8 + cU) := ⟨_, rfl⟩
  have hU1 : 1 ≤ U := by rw [hU]; exact Nat.one_le_two_pow
  have hs1 := PrimT.C4Cap.bsq_pos n
  -- the call's unit
  have hq : 2 ^ (E * PrimT.C4Cap.bsq n) ≤ U := by
    have h := hcq n
    unfold Ex at h
    rw [one_mul] at h
    have h' : 2 ^ (E * PrimT.C4Cap.bsq n) ≤ 2 ^ (n / 8 + cq) := h
    rw [hU]
    exact h'.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hW : 2 ^ PrimT.C4Cap.capExp2 Cc n ≤ U := by
    rw [hU]; unfold PrimT.C4Cap.capExp2; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlt : E * PrimT.C4Cap.bsq n < 2 ^ (E * PrimT.C4Cap.bsq n) := Nat.lt_two_pow_self
  have hEs : E ≤ E * PrimT.C4Cap.bsq n := Nat.le_mul_of_pos_right _ hs1
  have hn3' : n + 3 ≤ U := by omega
  have hcr' : F.cr ≤ U := by omega
  -- the front end's cost
  have hTc : (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).cost (UnaryCalc.value D Cd n) ≤ U := by
    have h1 : (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).cost (UnaryCalc.value D Cd n) ≤ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Cc * (UnaryCalc.value D Cd n + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc :=
      (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).cost_poly _
    have hp1 : 1 ≤ (n + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    have h2 : UnaryCalc.value D Cd n + 1 ≤ (Cd + 1) * (n + 1) ^ D := by
      unfold UnaryCalc.value
      have e : (Cd + 1) * (n + 1) ^ D = Cd * (n + 1) ^ D + (n + 1) ^ D := by ring
      omega
    have h3 : (UnaryCalc.value D Cd n + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc ≤ (Cd + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc * (n + 1) ^ (D * (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc) := by
      calc (UnaryCalc.value D Cd n + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc ≤ ((Cd + 1) * (n + 1) ^ D) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc := Nat.pow_le_pow_left h2 _
        _ = (Cd + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc * (n + 1) ^ (D * (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc) := by rw [mul_pow, ← pow_mul]
    have h4 : (n + 1) ^ (D * (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc) ≤ 2 ^ (n / 8 + cT) := by
      have := hcT n; unfold Ex at this; rw [one_mul] at this; exact this
    have h5 : (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Cc * (Cd + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc ≤ 2 ^ KT := by rw [hKT]; exact Nat.le_pow_clog (by norm_num) _
    calc (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).cost (UnaryCalc.value D Cd n) ≤ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Cc * ((Cd + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc * (n + 1) ^ (D * (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc)) :=
          h1.trans (Nat.mul_le_mul_left _ h3)
      _ = (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Cc * (Cd + 1) ^ (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc * (n + 1) ^ (D * (PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).Dc) := by ring
      _ ≤ 2 ^ KT * 2 ^ (n / 8 + cT) := Nat.mul_le_mul h5 h4
      _ = 2 ^ (KT + (n / 8 + cT)) := (pow_add 2 _ _).symm
      _ ≤ U := by rw [hU]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the numbers machine's cost
  have hNc : (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D).cost (n + UnaryCalc.value D Cd n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap) ≤ U := by
    have h1 : (PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D).cost (n + UnaryCalc.value D Cd n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap) ≤
        (PrimT.W6.numsW6 (gate0 l F).alg 1).Cc * (n + UnaryCalc.value D Cd n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap + 1) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc :=
      (PrimT.W6.numsW6 (gate0 l F).alg 1).cost_poly _
    have hz1 : 1 ≤ z := by rw [hz]; exact PrimT.TS4.capZR_pos l
    have hcap : ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ≤ kC * 2 ^ z * (n + 1) ^ z := by
      have c1 : ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ≤ kC * (n + 2) ^ z := by
        rw [hkC, hz]; exact PrimT.TS4.capTL_le l F.cr n
      have c2 := PrimT.TS4.two_pow_le n z
      calc ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap ≤ kC * (n + 2) ^ z := c1
        _ ≤ kC * (2 ^ z * (n + 1) ^ z) := Nat.mul_le_mul_left _ c2
        _ = kC * 2 ^ z * (n + 1) ^ z := by ring
    have p1 : n + 1 ≤ (n + 1) ^ (D + z) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    have p2 : (n + 1) ^ D ≤ (n + 1) ^ (D + z) := Nat.pow_le_pow_right (by omega) (by omega)
    have p3 : (n + 1) ^ z ≤ (n + 1) ^ (D + z) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : n + UnaryCalc.value D Cd n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap + 1 ≤ (Cd + kC * 2 ^ z + 2) * (n + 1) ^ (D + z) := by
      have a1 : Cd * (n + 1) ^ D ≤ Cd * (n + 1) ^ (D + z) := Nat.mul_le_mul_left _ p2
      have a2 : kC * 2 ^ z * (n + 1) ^ z ≤ kC * 2 ^ z * (n + 1) ^ (D + z) := Nat.mul_le_mul_left _ p3
      have e : (Cd + kC * 2 ^ z + 2) * (n + 1) ^ (D + z) = Cd * (n + 1) ^ (D + z) + kC * 2 ^ z * (n + 1) ^ (D + z) +
          2 * (n + 1) ^ (D + z) := by ring
      unfold UnaryCalc.value
      omega
    have h3 : (n + UnaryCalc.value D Cd n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap + 1) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc ≤
        (Cd + kC * 2 ^ z + 2) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc * (n + 1) ^ ((D + z) * (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc) := by
      calc _ ≤ ((Cd + kC * 2 ^ z + 2) * (n + 1) ^ (D + z)) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc := Nat.pow_le_pow_left h2 _
        _ = _ := by rw [mul_pow, ← pow_mul]
    have h4 : (n + 1) ^ ((D + z) * (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc) ≤ 2 ^ (n / 8 + cN) := by
      have := hcN n; unfold Ex at this; rw [one_mul] at this; exact this
    have h5 : (PrimT.W6.numsW6 (gate0 l F).alg 1).Cc * (Cd + kC * 2 ^ z + 2) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc ≤ 2 ^ KN := by rw [hKN]; exact Nat.le_pow_clog (by norm_num) _
    calc _ ≤ (PrimT.W6.numsW6 (gate0 l F).alg 1).Cc * ((Cd + kC * 2 ^ z + 2) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc * (n + 1) ^ ((D + z) * (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc)) :=
          h1.trans (Nat.mul_le_mul_left _ h3)
      _ = (PrimT.W6.numsW6 (gate0 l F).alg 1).Cc * (Cd + kC * 2 ^ z + 2) ^ (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc * (n + 1) ^ ((D + z) * (PrimT.W6.numsW6 (gate0 l F).alg 1).Dc) := by ring
      _ ≤ 2 ^ KN * 2 ^ (n / 8 + cN) := Nat.mul_le_mul h5 h4
      _ = 2 ^ (KN + (n / 8 + cN)) := (pow_add 2 _ _).symm
      _ ≤ U := by rw [hU]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the populations
  have hnG : HashPops.hNG (gate0 l F).alg Cs ≤ 2 ^ (E * PrimT.C4Cap.bsq n) := by
    rw [HashCell.hng_eq (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers]
    exact hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 0)
  have hdig : thrDigits ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs (gate0 l F).alg (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs) ≤ 2 ^ (E * PrimT.C4Cap.bsq n) :=
    hhn _ (HashFit.num_mem ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap 5)
  have hSm : Sm ≤ 2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2 := by have := hfit.cc; omega
  have hpc := pops_le (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs Bm Sm (2 ^ (E * PrimT.C4Cap.bsq n)) (2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2) hnG hcut hdig hBm hSm
  have hZ : 2 ^ (E * PrimT.C4Cap.bsq n) + (2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2) + 1 ≤ 6 * U := by omega
  have hZ4 : (2 ^ (E * PrimT.C4Cap.bsq n) + (2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2) + 1) * (2 ^ (E * PrimT.C4Cap.bsq n) + (2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2) + 1) * (2 ^ (E * PrimT.C4Cap.bsq n) + (2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2) + 1) *
      (2 ^ (E * PrimT.C4Cap.bsq n) + (2 * 2 ^ PrimT.C4Cap.capExp2 Cc n + 2) + 1) ≤ 1296 * (U * U * U * U) := by
    calc _ ≤ (6 * U) * (6 * U) * (6 * U) * (6 * U) := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hZ hZ) hZ) hZ
      _ = 1296 * (U * U * U * U) := by ring
  have hP : HashCell.popsCost (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs Bm Sm ≤ 400000 * (U * U * U * U) := by omega
  have hcall' := call_arith U (2 ^ PrimT.C4Cap.capExp2 Cc n) n F.cr (HashCell.cw ha Cs carriers translation).length
    ((PrimThrW.TF3Cost.topFront3 (gate0 l F).alg).cost (UnaryCalc.value D Cd n))
    ((PrimT.W6.numsW6 (gate0 l F).alg (callInputs l F kclk coef A a0 ha0).D).cost (n + UnaryCalc.value D Cd n + ((callInputs l F kclk coef A a0 ha0).filterParams .thr n).cap))
    (HashCell.popsCost (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs Bm Sm) hU1 hW hn3' hcr' hTc hNc hP
  -- the writer
  have hht : (PrimT.HbM.htWord (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).Fs).length ≤ U * U := by
    have h := FinalPass.HashFr.htW_le l F kclk coef A a0 ha0 ha Cs carriers translation hcall hs
    have hk : ((gate0 l F).budget kclk coef A a0 ha0).kOf n ≤ n / 16 + K0 :=
      le_trans (PrimT.C4SymN.kOf_le_bsq l F kclk coef A a0 ha0 n) (hK0 n)
    have h3 := hK3 n
    have e3 : FinalPass.HashFr.cHt l * ((Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1) * (Nat.clog 2 (n + 2) + 1)) =
        FinalPass.HashFr.cHt l * (Nat.clog 2 (n + 2) + 1) ^ 3 := by ring
    have hUU : U * U = 2 ^ (n / 8 + cU + (n / 8 + cU)) := by rw [hU, ← pow_add]
    rw [hUU]
    exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hkS : PrimT.C4KW.kwS (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) fr1 + 1 ≤ 13 * (U * U) := by
    have hpw : (PrimT.HbM.popsWord (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers).pops).length ≤ 2 ^ (E * PrimT.C4Cap.bsq n) := hpops
    have hUU : U ≤ U * U := Nat.le_mul_of_pos_left U hU1
    unfold PrimT.C4KW.kwS
    omega
  have hkT : (PrimT.C4KW.kwT (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1) ^ Wk.Dg ≤ U := by
    have h1 : PrimT.C4KW.kwT (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1 ≤ 10 * 2 ^ (E * PrimT.C4Cap.bsq n) := by have := Nat.one_le_two_pow (n := E * PrimT.C4Cap.bsq n); omega
    have h2 : (10 * 2 ^ (E * PrimT.C4Cap.bsq n)) ^ Wk.Dg = 10 ^ Wk.Dg * 2 ^ ((E * Wk.Dg) * PrimT.C4Cap.bsq n) := by
      rw [mul_pow, ← pow_mul]; ring_nf
    have h3 : 2 ^ ((E * Wk.Dg) * PrimT.C4Cap.bsq n) ≤ 2 ^ (n / 8 + cg) := by
      have := hcg n; unfold Ex at this; rw [one_mul] at this; exact this
    have h4 : 10 ^ Wk.Dg ≤ 2 ^ Kg := by rw [hKg]; exact Nat.le_pow_clog (by norm_num) _
    calc (PrimT.C4KW.kwT (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) + 1) ^ Wk.Dg ≤ (10 * 2 ^ (E * PrimT.C4Cap.bsq n)) ^ Wk.Dg := Nat.pow_le_pow_left h1 _
      _ = 10 ^ Wk.Dg * 2 ^ ((E * Wk.Dg) * PrimT.C4Cap.bsq n) := h2
      _ ≤ 2 ^ Kg * 2 ^ (n / 8 + cg) := Nat.mul_le_mul h4 h3
      _ = 2 ^ (Kg + (n / 8 + cg)) := (pow_add 2 _ _).symm
      _ ≤ U := by rw [hU]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwk := wk_arith Wk (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a0 ha0) hs Cs carriers) fr1 U hU1 hkS hkT
  -- rate 7
  apply ex_U n cU
  rw [← hU]
  have e : (1000000000 + 170 * Wk.K) * (U * U * U * U) = 1000000000 * (U * U * U * U) + 170 * Wk.K * (U * U * U * U) := by
    ring
  unfold HashCell.callCost
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.HashBud

end
