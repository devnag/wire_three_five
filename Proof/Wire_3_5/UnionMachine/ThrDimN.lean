import Lean
import Proof.Wire_3_5.UnionMachine.ThrDimMBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.NumsXT2Gate
import Proof.Wire_3_5.Primitive.Writers.SymNeed
import Proof.Wire_3_5.Primitive.Writers.ThrDimIface
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.UnionMachine.ThrDimNBase


noncomputable section
set_option maxRecDepth 4096


/-! # T-A2, part 2: the stage's fill need `needG` within `K_n·(n+1)^{D_n}`, `D_n` fixed by `l`

The fill need is a sum of the stage's capacity terms (`TNeed2`): the star numbers, the sparse count (`2^{O(L)}`),
`CapNum`'s bound `capNT`, the mass bound `Λ̄`, phase B's `(B_T·L + 2)²`, the phases' values `tNeedT2` and `2·m_T + 3`.
Every one is `c·N^e` with `N = n + 2`, `e` from the literals and `c` after `F`:

* `capMainG`, `capEncG`, **`bT_le`** (`B_T ≤ N^{capZR l}` at EVERY star parameter, `r ≤ n`);
* `ZY`, `cY`, **`YB`** (`Y = c_Y·N^{Z_Y}` dominating the stage's atoms), `yb_ge`, the atom bounds `yb_*`;
* `tT_shape` (`T ≤ 3Y⁶`), `tNeed_shape` (the phases' values `≤ 100Y⁶`);
* `sa`, `sb`, `ZE`, **`DnG`** (`l` only), `Kn0`, **`KnG`**, **`need_leG`** (T-A2's `need_le`).

Paper quantity of the main type: the THR dimension stage's fill need, polynomial in `n` (prim:runtime P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Transfer

/-! ## The THR cap at every star parameter -/

theorem capMainG (l : Literals) (m : Mode) (r n N : ℕ) (hNd : N = n + 2) (hr : r ≤ N) :
    Ledger.capMainNum (gateCap l) m r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n ≤
      N ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32) := by
  have hN : 2 ≤ N := by omega
  have hs0 := CallIndex.sp_le l n
  rw [← hNd] at hs0
  have hs : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ N ^ (gateCsp l + 3) := hs0
  have hβ := CallIndex.pw_const hN (gateBetaInv l)
  have hq : n ≤ N := by omega
  unfold Ledger.capMainNum
  rw [CallIndex.gateCoef l m, one_pow, mul_one]
  obtain ⟨E1, hE1⟩ : ∃ E, E = (gateCsp l + 3) * 32 := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E, E = gateBetaInv l * 32 := ⟨_, rfl⟩
  have hs32 : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 ≤ N ^ E1 :=
    hE1 ▸ CallIndex.pw_pow hs 32
  have hβ32 : gateBetaInv l ^ 32 ≤ N ^ E2 := hE2 ▸ CallIndex.pw_pow hβ 32
  have e80 : (2 : ℕ) ^ 80 ≤ N ^ 80 := Nat.pow_le_pow_left hN 80
  have hr48 : r ^ 48 ≤ N ^ 48 := Nat.pow_le_pow_left hr 48
  have hq64 : n ^ 64 ≤ N ^ 64 := Nat.pow_le_pow_left hq 64
  rw [← hE1, ← hE2]
  calc 2 ^ 80 * r ^ 48 * Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ^ 32 * n ^ 64 *
        gateBetaInv l ^ 32
      ≤ N ^ 80 * N ^ 48 * N ^ E1 * N ^ 64 * N ^ E2 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul e80 hr48) hs32) hq64) hβ32
    _ = N ^ (80 + 48 + E1 + 64 + E2) := by ring

theorem capEncG (l : Literals) (r n N : ℕ) (hNd : N = n + 2) (hr : r ≤ N) :
    Ledger.capEncPow (gateCap l) r n ≤ N ^ (5 + 3 + 2 + 1 + gateBetaInv l * 2) := by
  have hN : 2 ≤ N := by omega
  have hβ := CallIndex.pw_const hN (gateBetaInv l)
  have hq : n ≤ N := by omega
  have hr3 : r ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left hr 3
  have h32 : (32 : ℕ) ≤ N ^ 5 := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ N ^ 5 := Nat.pow_le_pow_left hN 5
  have h2 : (gateCap l).Cpar ^ 2 ≤ N ^ 2 := by
    show 2 ^ 2 ≤ N ^ 2; exact Nat.pow_le_pow_left hN 2
  obtain ⟨E3, hE3⟩ : ∃ E, E = gateBetaInv l * 2 := ⟨_, rfl⟩
  have hβ2 : gateBetaInv l ^ 2 ≤ N ^ E3 := hE3 ▸ CallIndex.pw_pow hβ 2
  unfold Ledger.capEncPow
  rw [← hE3]
  calc 32 * r ^ 3 * (gateCap l).Cpar ^ 2 * n * gateBetaInv l ^ 2 ≤ N ^ 5 * N ^ 3 * N ^ 2 * N ^ 1 * N ^ E3 := by
        rw [pow_one]
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h32 hr3) h2) hq) hβ2
    _ = N ^ (5 + 3 + 2 + 1 + E3) := by ring

/-- **`B_T ≤ N^{capZR l}`** at every star parameter (`r ≤ n/4`: no `c_r` in the bound). -/
theorem bT_le (l : Literals) (P : Shared.StarParams) : ThrDim.bT l P ≤ (P.n + 2) ^ CallIndexR.capZR l := by
  obtain ⟨N, hNd⟩ : ∃ N, N = P.n + 2 := ⟨_, rfl⟩
  rw [← hNd]
  have hN : 2 ≤ N := by omega
  have hr : P.r ≤ N := by have := P.four_r_le_n; omega
  have hnum := capMainG l .thr P.r P.n N hNd hr
  have henc := capEncG l P.r P.n N hNd hr
  have hD : Ledger.Lq P.n ^ Ledger.capExp32 .thr ≤ N ^ 174 :=
    le_trans (Nat.pow_le_pow_left (hNd ▸ CallIndex.Lq_le_N P.n) _)
      (Nat.pow_le_pow_right (by omega) (CallIndex.capExp32_le .thr))
  obtain ⟨Z, hZd⟩ : ∃ Z, Z = CallIndexR.capZR l := ⟨_, rfl⟩
  rw [← hZd]
  have hZ1 : 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32 ≤ Z - 2 := by
    rw [hZd]; unfold CallIndexR.capZR; omega
  have hZ2 : 174 ≤ Z - 2 := by rw [hZd]; unfold CallIndexR.capZR; omega
  have hZ3 : 5 + 3 + 2 + 1 + gateBetaInv l * 2 ≤ Z - 2 := by rw [hZd]; unfold CallIndexR.capZR; omega
  have hZ4 : Z = Z - 2 + 2 := by rw [hZd]; unfold CallIndexR.capZR; omega
  have hPow : ∀ {e : ℕ}, e ≤ Z - 2 → N ^ e ≤ N ^ (Z - 2) := fun h => Nat.pow_le_pow_right (by omega) h
  have hA := le_trans hnum (hPow hZ1)
  have hB := le_trans henc (hPow hZ3)
  have hC := le_trans hD (hPow hZ2)
  have hP : 1 ≤ N ^ (Z - 2) := Nat.one_le_pow _ _ (by omega)
  have h4 : 4 ≤ N ^ 2 := by nlinarith
  have hsum : 1 + (Ledger.capMainNum (gateCap l) .thr P.r
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) P.n) P.n +
      Ledger.Lq P.n ^ Ledger.capExp32 .thr) + Ledger.capEncPow (gateCap l) P.r P.n ≤ 4 * N ^ (Z - 2) := by
    omega
  show Ledger.rowBCap (gateCap l) .thr P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) P.n)
    P.n ≤ N ^ Z
  refine le_trans (CallIndex.rowBCap_le (gateCap l) .thr P.r _ P.n) (le_trans hsum ?_)
  calc 4 * N ^ (Z - 2) ≤ N ^ 2 * N ^ (Z - 2) := Nat.mul_le_mul_right _ h4
    _ = N ^ Z := by rw [← pow_add]; congr 1; omega

/-! ## The master bound `Y = c_Y·N^{Z_Y}` -/

/-- The master exponent (the literals only). -/
noncomputable def ZY (l : Literals) : ℕ := CallIndexR.capZR l + gateCsp l + 5

/-- The master coefficient (after `F`, `K_L`, `K_f`). -/
noncomputable def cY (l : Literals) (F : GateFree l) (KL Kf : ℕ) : ℕ :=
  16 + SymSizes.KLam l + 2 * SymSizes.schedJ l + F.CD + Kf + KL + F.cr

/-- **The master bound** at length `n`. -/
noncomputable def YB (l : Literals) (F : GateFree l) (KL Kf n : ℕ) : ℕ := cY l F KL Kf * (n + 2) ^ ZY l

section Atoms
variable (l : Literals) (F : GateFree l) (KL Kf : ℕ)

theorem pZ (n e : ℕ) (he : e ≤ ZY l) : (n + 2) ^ e ≤ (n + 2) ^ ZY l := Nat.pow_le_pow_right (by omega) he

theorem one_pZ (n : ℕ) : 1 ≤ (n + 2) ^ ZY l := Nat.one_le_pow _ _ (by omega)

theorem yb_ge {n a x : ℕ} (hx : x ≤ a * (n + 2) ^ ZY l) (ha : a ≤ cY l F KL Kf) : x ≤ YB l F KL Kf n :=
  hx.trans (Nat.mul_le_mul_right _ ha)

theorem yb_pos (n : ℕ) : 1 ≤ YB l F KL Kf n :=
  yb_ge l F KL Kf (a := 1) (by rw [one_mul]; exact one_pZ l n) (by unfold cY; omega)

theorem yb_n (n : ℕ) : n + 2 ≤ YB l F KL Kf n := by
  refine yb_ge l F KL Kf (a := 1) ?_ (by unfold cY; omega)
  rw [one_mul]
  calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
    _ ≤ _ := pZ l n 1 (by unfold ZY; omega)

theorem yb_B (P : Shared.StarParams) : ThrDim.bT l P ≤ YB l F KL Kf P.n := by
  refine yb_ge l F KL Kf (a := 1) ?_ (by unfold cY; omega)
  rw [one_mul]
  exact (bT_le l P).trans (pZ l P.n _ (by unfold ZY; omega))

theorem X_le (P : Shared.StarParams) :
    ThrDim.bT l P * Nat.clog 2 (P.n + 2) ≤ (P.n + 2) ^ ZY l := by
  have h1 := bT_le l P
  have h2 := clog_le P.n
  calc ThrDim.bT l P * Nat.clog 2 (P.n + 2) ≤ (P.n + 2) ^ CallIndexR.capZR l * (P.n + 2) ^ 1 := by
        rw [pow_one]; exact Nat.mul_le_mul h1 h2
    _ = (P.n + 2) ^ (CallIndexR.capZR l + 1) := by rw [← pow_add]
    _ ≤ _ := pZ l P.n _ (by unfold ZY; omega)

theorem yb_X (P : Shared.StarParams) : ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 2 ≤ YB l F KL Kf P.n := by
  refine yb_ge l F KL Kf (a := 3) ?_ (by unfold cY; omega)
  have h1 := X_le l P
  have h2 := one_pZ l P.n
  omega

theorem yb_D (P : Shared.StarParams) :
    (CanonicalFourfoldRowProgram.natCeilSqrt (ThrDim.bT l P * Nat.clog 2 (P.n + 2)) + 1) +
      Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2) ≤ YB l F KL Kf P.n := by
  refine yb_ge l F KL Kf (a := 4) ?_ (by unfold cY; omega)
  have h1 := X_le l P
  have h2 := one_pZ l P.n
  have hS := ncs_le_sqrt (ThrDim.bT l P * Nat.clog 2 (P.n + 2))
  have hS2 := Nat.sqrt_le_self (ThrDim.bT l P * Nat.clog 2 (P.n + 2))
  have hL := clog_le P.n
  have hLL : Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2) ≤ (P.n + 2) ^ ZY l :=
    calc Nat.clog 2 (P.n + 2) * Nat.clog 2 (P.n + 2) ≤ (P.n + 2) * (P.n + 2) := Nat.mul_le_mul hL hL
      _ = (P.n + 2) ^ 2 := (pow_two _).symm
      _ ≤ _ := pZ l P.n _ (by unfold ZY; omega)
  omega

theorem yb_kp (P : Shared.StarParams) :
    P.r * natBitLength (P.n / P.r + 1) + Nat.clog 2 (P.n + 2) ≤ YB l F KL Kf P.n := by
  refine yb_ge l F KL Kf (a := 3) ?_ (by unfold cY; omega)
  have h1 := kp_le_n P
  have h2 := clog_le P.n
  have h3 : P.n + 2 ≤ (P.n + 2) ^ ZY l := by
    calc P.n + 2 = (P.n + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := pZ l P.n 1 (by unfold ZY; omega)
  omega

theorem yb_sp (n : ℕ) : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ YB l F KL Kf n := by
  refine yb_ge l F KL Kf (a := 1) ?_ (by unfold cY; omega)
  rw [one_mul]
  exact (CallIndex.sp_le l n).trans (pZ l n _ (by unfold ZY; omega))

theorem yb_lam (n : ℕ) : Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 n ≤ YB l F KL Kf n := by
  refine yb_ge l F KL Kf (a := SymSizes.KLam l) ?_ (by unfold cY; omega)
  exact (SymSizes.lambda_le l n).trans (Nat.mul_le_mul_left _ (pZ l n _ (by unfold ZY; omega)))

theorem yb_t (n : ℕ) : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n + 5 ≤ YB l F KL Kf n := by
  refine yb_ge l F KL Kf (a := 2 * SymSizes.schedJ l + 6) ?_ (by unfold cY; omega)
  have h1 := SymSizes.rowBt_le l n
  have h2 := clog_le n
  have h3 : n + 2 ≤ (n + 2) ^ ZY l := by
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := pZ l n 1 (by unfold ZY; omega)
  have h4 : SymSizes.schedJ l * (Nat.clog 2 (n + 2) + 1) ≤ SymSizes.schedJ l * (2 * (n + 2) ^ ZY l) :=
    Nat.mul_le_mul_left _ (by omega)
  have h5 := one_pZ l n
  have e : (2 * SymSizes.schedJ l + 6) * (n + 2) ^ ZY l =
      SymSizes.schedJ l * (2 * (n + 2) ^ ZY l) + 6 * (n + 2) ^ ZY l := by ring
  rw [e]
  omega

theorem yb_CD (n : ℕ) : F.CD ≤ YB l F KL Kf n :=
  yb_ge l F KL Kf (a := F.CD) (Nat.le_mul_of_pos_right _ (one_pZ l n)) (by unfold cY; omega)

theorem yb_Kf (n : ℕ) : Kf ≤ YB l F KL Kf n :=
  yb_ge l F KL Kf (a := Kf) (Nat.le_mul_of_pos_right _ (one_pZ l n)) (by unfold cY; omega)

theorem yb_KL (n : ℕ) : KL ≤ YB l F KL Kf n :=
  yb_ge l F KL Kf (a := KL) (Nat.le_mul_of_pos_right _ (one_pZ l n)) (by unfold cY; omega)

theorem yb_cr (n : ℕ) : F.cr ≤ YB l F KL Kf n :=
  yb_ge l F KL Kf (a := F.cr) (Nat.le_mul_of_pos_right _ (one_pZ l n)) (by unfold cY; omega)

/-- `Y⁶ = c_Y⁶·N^{6Z_Y}`. -/
theorem yb_pow6 (n : ℕ) : YB l F KL Kf n ^ 6 = cY l F KL Kf ^ 6 * (n + 2) ^ (6 * ZY l) := by
  unfold YB; rw [mul_pow, ← pow_mul, Nat.mul_comm (ZY l) 6]

end Atoms

/-! ## The load term and the phases' values below `Y⁶` -/

/-! ## The fill need -/

/-- The sparse count's `L`-coefficient. -/
noncomputable def sa (l : Literals) : ℕ := 3 + 32 * SymSizes.cXg l * SymSizes.schedJ l

/-- The sparse count's constant exponent. -/
noncomputable def sb (l : Literals) : ℕ := 6 + 32 * SymSizes.cXg l * (SymSizes.schedJ l + 1)

/-- `capNT`'s exponent. -/
noncomputable def ZE (l : Literals) : ℕ := 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32

/-- **The fill need's exponent** (the literals only). -/
noncomputable def DnG (l : Literals) : ℕ := 6 * ZY l + sa l + ZE l + 3

/-- The fill need's coefficient at `N = n + 2`. -/
noncomputable def Kn0 (l : Literals) (F : GateFree l) (KL Kf : ℕ) : ℕ :=
  (F.cr + KL + 20) + 2 ^ (sa l + sb l) + (2 ^ 40 * CallIndexR.capK F.cr + CapNum.cMain (gateCap l) .thr) +
    SymSizes.KLam l + 12 * cY l F KL Kf ^ 6 + 100 * cY l F KL Kf ^ 6 + (9 + 2 * KL + 6 * cY l F KL Kf ^ 6)

/-- **The fill need's coefficient** (after `F`, `K_L`, `K_f`). -/
noncomputable def KnG (l : Literals) (F : GateFree l) (KL Kf : ℕ) : ℕ := Kn0 l F KL Kf * 2 ^ DnG l

section Need
variable (l : Literals) (F : GateFree l) (KL Kf : ℕ)

theorem need_N (P : Shared.StarParams) : ThrDim.needG l F KL Kf P ≤ Kn0 l F KL Kf * (P.n + 2) ^ DnG l := by
  obtain ⟨M, hM⟩ : ∃ M, M = (P.n + 2) ^ DnG l := ⟨_, rfl⟩
  rw [← hM]
  have pD : ∀ e, e ≤ DnG l → (P.n + 2) ^ e ≤ M := fun e he => hM ▸ Nat.pow_le_pow_right (by omega) he
  have hM1 : 1 ≤ M := hM ▸ Nat.one_le_pow _ _ (by omega)
  have hN1 : P.n + 2 ≤ M := by
    have := pD 1 (by unfold DnG; omega); rwa [pow_one] at this
  have hN2 : (P.n + 2) ^ 2 ≤ M := pD 2 (by unfold DnG ZY; omega)
  -- the pieces
  have t1 : 2 * P.n + F.cr + 16 + KL * (P.n + 2) ^ 2 ≤ F.cr * M + KL * M + 20 * M := by
    have a1 : F.cr ≤ F.cr * M := Nat.le_mul_of_pos_right _ hM1
    have a2 : KL * (P.n + 2) ^ 2 ≤ KL * M := Nat.mul_le_mul_left _ hN2
    omega
  have t2 : SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq P.n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n - 1) ≤ 2 ^ (sa l + sb l) * M := by
    have h := SymSizes.sparse_le_gate l P.n
    have h2L : 2 ^ Nat.clog 2 (P.n + 2) ≤ 2 * (P.n + 2) := CallIndexR.two_pow_clog_le_two_mul _ (by omega)
    have hsa : (P.n + 2) ^ sa l ≤ M := pD _ (by unfold DnG; omega)
    refine h.trans ?_
    calc 2 ^ ((3 + 32 * SymSizes.cXg l * SymSizes.schedJ l) * Nat.clog 2 (P.n + 2) +
          (6 + 32 * SymSizes.cXg l * (SymSizes.schedJ l + 1)))
        = (2 ^ Nat.clog 2 (P.n + 2)) ^ sa l * 2 ^ sb l := by
          unfold sa sb; rw [pow_add, Nat.mul_comm _ (Nat.clog 2 (P.n + 2)), pow_mul]
      _ ≤ (2 * (P.n + 2)) ^ sa l * 2 ^ sb l := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2L _)
      _ = 2 ^ sa l * (P.n + 2) ^ sa l * 2 ^ sb l := by rw [mul_pow]
      _ ≤ 2 ^ sa l * M * 2 ^ sb l := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hsa)
      _ = 2 ^ (sa l + sb l) * M := by rw [pow_add]; ring
  have t3 : ThrDim.capNT l F P.n ≤ 2 ^ 40 * CallIndexR.capK F.cr * M + CapNum.cMain (gateCap l) .thr * M := by
    unfold ThrDim.capNT
    have hE : (P.n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32) ≤ M :=
      pD _ (by unfold DnG ZE; omega)
    have a1 : 2 ^ 40 * (CallIndexR.capK F.cr * (P.n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 +
        gateBetaInv l * 32)) ≤ 2 ^ 40 * CallIndexR.capK F.cr * M := by
      rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hE
    have a2 : CapNum.cMain (gateCap l) .thr ≤ CapNum.cMain (gateCap l) .thr * M := Nat.le_mul_of_pos_right _ hM1
    omega
  have t4 : Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n ≤ SymSizes.KLam l * M :=
    (SymSizes.lambda_le l P.n).trans (Nat.mul_le_mul_left _ (pD 3 (by unfold DnG ZY; omega)))
  -- the master bound's sixth power
  have hY6 : YB l F KL Kf P.n ^ 6 ≤ cY l F KL Kf ^ 6 * M := by
    rw [yb_pow6]; exact Nat.mul_le_mul_left _ (pD _ (by unfold DnG; omega))
  have hY1 := yb_pos l F KL Kf P.n
  have q16 : YB l F KL Kf P.n ≤ YB l F KL Kf P.n ^ 6 := by
    calc YB l F KL Kf P.n = YB l F KL Kf P.n ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hY1 (by norm_num)
  have hX := yb_X l F KL Kf P
  have t5 : NumsXT2.xNeedT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) ≤
      12 * (cY l F KL Kf ^ 6 * M) := by
    show (ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 2) * (ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 2) +
      ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 10 ≤ _
    have a1 : (ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 2) * (ThrDim.bT l P * Nat.clog 2 (P.n + 2) + 2) ≤
        YB l F KL Kf P.n ^ 6 := by
      have q26 : YB l F KL Kf P.n ^ 2 ≤ YB l F KL Kf P.n ^ 6 := Nat.pow_le_pow_right hY1 (by norm_num)
      exact (Nat.mul_le_mul hX hX).trans ((pow_two _).symm.le.trans q26)
    omega
  have hD := yb_D l F KL Kf P
  have hkp := yb_kp l F KL Kf P
  have hCD := yb_CD l F KL Kf P.n
  have hKf := yb_Kf l F KL Kf P.n
  have t6 : NumsXT2.tNeedT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf ≤
      100 * (cY l F KL Kf ^ 6 * M) := by
    have hn := yb_n l F KL Kf P.n
    have hr : P.r ≤ P.n := by have := P.four_r_le_n; omega
    have hm : P.n % P.r ≤ P.n := Nat.mod_le _ _
    have hq : P.n / P.r ≤ P.n := Nat.div_le_self _ _
    have hnb : natBitLength (P.n / P.r + 1) ≤ P.n / P.r + 2 := by
      show Nat.log 2 (P.n / P.r + 1) + 1 ≤ _
      have := Nat.log_le_self 2 (P.n / P.r + 1); omega
    have hB := yb_B l F KL Kf P
    have hsp := yb_sp l F KL Kf P.n
    have hS := tNeed_shape P.n P.r (P.n % P.r) (P.n / P.r) (natBitLength (P.n / P.r + 1))
      (P.r * natBitLength (P.n / P.r + 1)) (ThrDim.bT l P) (Nat.clog 2 (P.n + 2))
      (ThrDim.bT l P * Nat.clog 2 (P.n + 2))
      (CanonicalFourfoldRowProgram.natCeilSqrt (ThrDim.bT l P * Nat.clog 2 (P.n + 2)))
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) P.n) F.CD Kf (YB l F KL Kf P.n)
      hY1 (by omega) (by omega) (by omega) (by omega) (by omega) hkp hB (by omega) hD hsp hCD hKf
    exact hS.trans (Nat.mul_le_mul_left _ hY6)
  have t7 : 2 * ThrDim.mTG l F KL Kf P + 3 ≤ 9 * M + 2 * (KL * M) + 6 * (cY l F KL Kf ^ 6 * M) := by
    have hT := tT_shape (P.r * natBitLength (P.n / P.r + 1)) (Nat.clog 2 (P.n + 2))
      (CanonicalFourfoldRowProgram.natCeilSqrt (ThrDim.bT l P * Nat.clog 2 (P.n + 2))) F.CD Kf
      (YB l F KL Kf P.n) hY1 hkp hD hCD hKf
    have hT' : NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf ≤
        3 * (cY l F KL Kf ^ 6 * M) := hT.trans (Nat.mul_le_mul_left _ hY6)
    have hk2 := NumsX.kh2_le P
    have hL := clog_le P.n
    have hLL : KL * Nat.clog 2 (P.n + 2) ^ 2 ≤ KL * M :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hL 2).trans hN2)
    show 2 * (2 * (P.s * (P.r / 2)) + Nat.clog 2 (P.n + 2) + KL * Nat.clog 2 (P.n + 2) ^ 2 +
      NumsXT2.tT2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) F.CD Kf) + 3 ≤ _
    omega
  unfold ThrDim.needG
  have e : Kn0 l F KL Kf * M = F.cr * M + KL * M + 20 * M + 2 ^ (sa l + sb l) * M +
      (2 ^ 40 * CallIndexR.capK F.cr * M + CapNum.cMain (gateCap l) .thr * M) + SymSizes.KLam l * M +
      12 * (cY l F KL Kf ^ 6 * M) + 100 * (cY l F KL Kf ^ 6 * M) +
      (9 * M + 2 * (KL * M) + 6 * (cY l F KL Kf ^ 6 * M)) := by
    unfold Kn0; ring
  rw [e]
  omega

/-- **T-A2 `need_le`**: the fill need within `K_n·(n+1)^{D_n}`, `D_n = DnG l`. -/
theorem need_leG (P : Shared.StarParams) (_hrP : P.r = Ledger.rowBr F.cr P.n) :
    ThrDim.needG l F KL Kf P ≤ KnG l F KL Kf * (P.n + 1) ^ DnG l := by
  refine (need_N l F KL Kf P).trans ?_
  have h : (P.n + 2) ^ DnG l ≤ 2 ^ DnG l * (P.n + 1) ^ DnG l := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc Kn0 l F KL Kf * (P.n + 2) ^ DnG l ≤ Kn0 l F KL Kf * (2 ^ DnG l * (P.n + 1) ^ DnG l) :=
        Nat.mul_le_mul_left _ h
    _ = KnG l F KL Kf * (P.n + 1) ^ DnG l := by unfold KnG; ring

end Need

end NearCubicWires.WireExponent3_5.UnionMachine.ThrDimB

end
