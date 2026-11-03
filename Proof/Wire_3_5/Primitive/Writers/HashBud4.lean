import Lean
import Proof.Wire_3_5.Primitive.Writers.HashBud3
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.HashFree
import Proof.Wire_3_5.FinalPass.HashFree2
import Proof.Wire_3_5.FinalPass.HashSz1
import Proof.Wire_3_5.FinalPass.HashSz2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrB7
import Proof.Wire_3_5.Primitive.Writers.ThrBud2
import Proof.Wire_3_5.Primitive.Writers.ThrLf2
import Proof.Wire_3_5.Primitive.Writers.ThrSide1
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrB
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Primitive.SeedFix.TS4L
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.HashBud2
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2Base


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 HASH budget (C), part 4: `hash_steps_gen` (the `HashStepsAt2` at the HASH leaf's instance)

P3:3098-3100, 3105-3115 (`E₄` before `F`, `c₄` after): at the HASH leaf's instance (the layout
`symLay wa S3 (hDl l Dnw)`, `C_L = C_nw + 1`, `C_d = hCd l F C_nw`, the `stage4At`, `topFront3`, `numsW6`, the kept
words writer `Wk`), with the THR and HASH free numbers' fits at `C_c` (`hash_fits`), one `c₄` bounds the HASH stage's
steps at every THR call whose cell fits (`CellFit`, `B_m ≤ cap`): every term at its rate (`hash_steps_core`), the
cell and the writer at rate `7` (`hX_ex`), the loop's bound `L_b = ℓ + 2tℓ₀` linear in `n`.
* `hc_le` (the HASH numbers machine at rate `3`), **`hash_steps_gen`**.

Paper quantity of the main type: the HASH stage's steps against the seed-fixing budget (`c₄·seedClasses E₄`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

/-- **The HASH numbers machine at rate `3`** (quadratic in the capacity, a free program quadratic too). -/
theorem hc_le (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) (hk2 : carriers.length ≤ 2) (Fp : PrimT.C4Set.FreeProg) (Kc : ℕ)
    (hKc : ∀ (cap : ℕ) (x : PrimT.C4Set.FreeIn), Fp.cost cap x ≤ Kc * (cap + 1) ^ 2) (Cc : ℕ)
    (hn : n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (hKb : PrimT.C4GateSym.needW n ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (ht : (ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).getD 12 0 ≤ 2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) :
    ThrNums.hashBigCost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length
        (PrimT.C4GateSym.needW n) ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).getD 12 0) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) ≤
      ((3000000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc)) * 2 ^ (3 * (n / 8)) := by
  have hcod : (ReqBridge.thrCodes Cs).length = a := List.length_ofFn
  have hcar : (carriers.map Carrier.code).length = carriers.length := List.length_map _
  have h1 := hashBig_le (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) n (ReqBridge.thrCodes Cs).length (carriers.map Carrier.code).length
    (PrimT.C4GateSym.needW n) ((ThrCap.hnC (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs).getD 12 0) (Fp.cost (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) hn (by rw [hcod]; exact ha)
    (by rw [hcar]; omega) hKb ht
  have h2 := hKc (2 * (2 ^ PrimT.C4Cap.capExp2 Cc n) + 2) (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)
  have hB := capB_le Cc n
  obtain ⟨Z, hZ⟩ : ∃ z, z = (2 ^ PrimT.C4Cap.capExp2 Cc n) := ⟨_, rfl⟩
  obtain ⟨Xv, hXv⟩ : ∃ z, z = 2 ^ (n / 8) := ⟨_, rfl⟩
  have hX3 : 2 ^ (3 * (n / 8)) = Xv * Xv * Xv := by rw [hXv]; ring
  rw [← hZ] at h1 h2 hB ⊢
  rw [← hXv] at hB
  rw [hX3]
  have hX1 : 1 ≤ Xv := hXv ▸ Nat.one_le_two_pow
  obtain ⟨G, hG⟩ : ∃ g, g = 6 * 2 ^ Cc * Xv := ⟨_, rfl⟩
  have g1 : (2 * Z + 2 + 2) * (2 * Z + 2 + 2) ≤ G * G := Nat.mul_le_mul (by omega) (by omega)
  have g2 : (2 * Z + 2 + 1) ^ 2 ≤ (2 * Z + 2 + 2) * (2 * Z + 2 + 2) := by nlinarith
  have g3 : Xv * Xv ≤ Xv * Xv * Xv := Nat.le_mul_of_pos_right _ (by omega)
  have g4 : Kc * (2 * Z + 2 + 1) ^ 2 ≤ Kc * (G * G) := Nat.mul_le_mul_left _ (g2.trans g1)
  have g5 : 3000000 * ((2 * Z + 2 + 2) * (2 * Z + 2 + 2)) ≤ 3000000 * (G * G) := Nat.mul_le_mul_left _ g1
  have g6 : (3000000 + Kc) * (G * G) ≤ (3000000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc) * (Xv * Xv * Xv) := by
    have e : (3000000 + Kc) * (G * G) = (3000000 + Kc) * (6 * 2 ^ Cc) * (6 * 2 ^ Cc) * (Xv * Xv) := by rw [hG]; ring
    rw [e]
    exact Nat.mul_le_mul_left _ g3
  have e2 : (3000000 + Kc) * (G * G) = 3000000 * (G * G) + Kc * (G * G) := by ring
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.HashBud

end
