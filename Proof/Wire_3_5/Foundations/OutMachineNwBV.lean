import Lean
import Proof.Wire_3_5.Primitive.SeedFix.NwBT
import Proof.Wire_3_5.UnionMachine.NumsW1
import Proof.Wire_3_5.Primitive.Writers.ThrCap1
import Proof.Wire_3_5.FinalPass.S5TNum3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.S5TChC
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Proof.Wire_3_5.Primitive.SeedFix.TS4O
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.Foundations.OutMachineNwBVBase


noncomputable section
set_option maxRecDepth 120000


/-! # NW phase (b)'s value link and capacity need (#257, the `PrimT.NwB` types): **`vLinkB`**, **`needB`**

Phase (b) computes, at a THR call on the star, `vB = 2^{⌊(5k_h+3)/4⌋}·B·2^{sb}·#primes` from W6's numbers. The paper's
value is `V = |PrimeIndex(cut)|·|E|·Q` (P3:3044-3048) with `Q = 2^e·B` (the THR sample count, the `thrQ_link`),
`|E| = 2^{sb}` (`card_gapSeed` at the THR filter `gP n cap_T (f_e·L)`) and `|PrimeIndex(cut)| = #primes`:

* **`vLinkB l : NwB.VLinkB l`** (`vB = vOf` at every THR call on the star).

Every number phase (b)'s register programs hold is polynomial in `X = |fpIn| + 1` (P3:3170-3181): the need
(`needT_le`), `cap_T` (`capTL_le1`), `(n+1)^{26}`, W6's power, W6's fourteen numbers (`S5T.vals_le`), the gap numbers
(`gapSeed_leR`, `lfw_le`), `V` (`vLinkB` and the `vOf_le`), `T_f = K_T·(n+2)^{Z_T}`, and `#primes ≥ 1`
(`cut ≥ 563`):

* `Kn`, `Dn`, `atom_le`, **`needB l : NwB.NeedB l`**.

Paper quantities of the main types: the final pass's unshifted denominator `V = |PrimeIndex(cut)|·|E|·Q` at a THR
request (P3:3044-3048) and the polynomial size of (b)'s numbers in the input (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.NwBV
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT.NwB

/-- **(b)'s value link** (P3:3044-3048): `vB = |PrimeIndex(cut)|·|E|·Q = vOf` at every THR call on the star. -/
theorem vLinkB (l : Literals) : VLinkB l := by
  intro F kclk coef A a ha n a' ha' Cs carriers translation hc hs
  simp only [UnionMachine.NumsPh2.vOf, UnionMachine.NumsPh2.vOfReq, dif_pos hs]
  show _ = _ * _ * SeedFix.thrCount (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs
  rw [PrimAsm.ThrCap.thrQ_link (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs hs rfl rfl,
    Filters.card_gapSeed, PrimAsm.ThrCap.filterParams_thr (callInputs l F kclk coef A a ha) rfl]
  simp only [SupplierPrime.PrimeIndex, Fintype.card_coe]
  unfold vB vVal valsB gapB khB
  simp only [PrimThrW.Joins.thrNumVals]
  have hPn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  have e1 : (gate0 l F).alg = PrimT.W6.litAlg l := rfl
  have e2 : (callInputs l F kclk coef A a ha).D = 1 := rfl
  have e3 : ((gate0 l F).budget kclk coef A a ha).capOf Mode.thr n = PrimT.TS4.capTL l F.cr n := rfl
  have e4 : (callInputs l F kclk coef A a ha).filterErrDeg = F.filterErrDeg := rfl
  simp only [Primitive.thrCallDen, hPn, SeedFix.callKh, e1, e2, e3, e4, pow_one]
  rw [Nat.div_div_eq_div_mul]
  ring

/-- **(b)'s atoms' coefficient** (on `F`): at least every atom's coefficient. -/
noncomputable def Kn (l : Literals) (F : GateFree l) : ℕ :=
  PrimT.TS4.NCoef l F.cr + PrimT.TS4.capKc l F.cr + 1 +
    (PrimT.TS4.capKc l F.cr + 1) ^ (PrimT.ThrDecF.NW l).Dn + S5T.KtT l F +
    4 * PrimAsm.CallIndexR.gapK F.cr * 2 ^ PrimAsm.CallIndexR.gapZR l F.filterErrDeg + UnionMachine.NumsA.KV l F +
    Sd.R.KT l F * 2 ^ Sd.R.ZT l F

/-- **(b)'s atoms' degree** (on `l` and `f_e`): at least every atom's degree. -/
noncomputable def Dn (l : Literals) (fe : ℕ) : ℕ :=
  PrimT.TS4.NDeg l + PrimAsm.CallIndexR.capZR l + 26 +
    (PrimAsm.CallIndexR.capZR l + 1) * (PrimT.ThrDecF.NW l).Dn + S5T.DtT l + PrimAsm.CallIndexR.gapZR l fe +
    UnionMachine.NumsA.DV l fe +
    (PrimAsm.CallIndexR.gapZR l fe + PrimAsm.CallIndexR.symZI l fe + PrimAsm.CallIndexR.thrZI l fe + Sd.R.ZV l + 4)

/-- **(b)'s capacity need** (P3:3170-3181): every atom at `K_n(F)·(|fpIn|+1)^{D_n(f_e)}`. -/
theorem needB (l : Literals) : NeedB l := by
  refine ⟨Kn l, Dn l, ?_⟩
  intro F kclk coef A a ha n a' ha' Cs carriers translation hc hs
  obtain ⟨hcar, hd, _, _⟩ := S5T.call_facts l F kclk coef A a ha ha' Cs carriers translation hc
  have hX : n + 1 ≤ (FinalPass.PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩).length + 1 :=
    Nat.succ_le_succ (FpInLen.n_le_fpIn ⟨_, hc⟩)
  have hV := UnionMachine.NumsA.vOf_le l F kclk coef A a ha ⟨_, hc⟩
  rw [← vLinkB l F kclk coef A a ha n a' ha' Cs carriers translation hc hs] at hV
  generalize (FinalPass.PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩).length + 1 = X at hX hV ⊢
  have hX1 : 1 ≤ X := by omega
  have pw : ∀ K d : ℕ, K * (n + 1) ^ d ≤ K * X ^ d := fun K d => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX d)
  have hP : (callInputs l F kclk coef A a ha).filterParams .thr n = gapB l F n :=
    PrimAsm.ThrCap.filterParams_thr (callInputs l F kclk coef A a ha) rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((PrimT.TS4.needT_le l F.cr n).trans (pw _ _)).trans
      (atom_le (by unfold Kn; omega) (by unfold Dn; omega) hX1)
  · exact ((PrimT.TS4.capTL_le1 l F.cr n).trans (pw _ _)).trans
      (atom_le (by unfold Kn; omega) (by unfold Dn; omega) hX1)
  · have h := Nat.pow_le_pow_left hX 26
    rw [← one_mul (X ^ 26)] at h
    exact h.trans (atom_le (by unfold Kn; omega) (by unfold Dn; omega) hX1)
  · exact (pow_atom_le hX (PrimT.TS4.capTL_le1 l F.cr n)).trans
      (atom_le (by unfold Kn; omega) (by unfold Dn; omega) hX1)
  · intro i
    exact ((S5T.vals_le l F kclk coef A a ha hs ha' Cs carriers hcar hd i).trans (pw _ _)).trans
      (atom_le (by unfold Kn; omega) (by unfold Dn; omega) hX1)
  · have hl := PrimT.ThrDecF.lfw_le l F kclk coef A a ha (n := n)
    have hg := PrimAsm.CallIndexR.gapSeed_leR l F kclk coef A a ha .thr n
    rw [Filters.card_gapSeed] at hg
    rw [hP] at hl hg
    have h := gap_arith (by omega : (gapB l F n).labelBits + (gapB l F n).fieldBits + (gapB l F n).walkLen ≤
      (gapB l F n).seedBits + 1) (hg.trans (pow2_le hX _ _))
    rw [← Nat.add_assoc, ← Nat.add_assoc] at h
    refine h.trans ?_
    rw [show 4 * (PrimAsm.CallIndexR.gapK F.cr * 2 ^ PrimAsm.CallIndexR.gapZR l F.filterErrDeg *
        X ^ PrimAsm.CallIndexR.gapZR l F.filterErrDeg) = 4 * PrimAsm.CallIndexR.gapK F.cr *
        2 ^ PrimAsm.CallIndexR.gapZR l F.filterErrDeg * X ^ PrimAsm.CallIndexR.gapZR l F.filterErrDeg by ring]
    exact atom_le (by unfold Kn; omega) (by unfold Dn; omega) hX1
  · exact hV.trans (atom_le (by unfold Kn; omega) (by unfold Dn; omega) hX1)
  · show Sd.R.KT l F * (n + 2) ^ Sd.R.ZT l F ≤ _
    exact (pow2_le hX _ _).trans (atom_le (by unfold Kn; omega) (by unfold Dn Sd.R.ZT; omega) hX1)
  · show 1 ≤ (SupplierPrime.primesUpTo (Primitive.thrCutoff _ _ _ _)).card
    unfold Primitive.thrCutoff
    exact Finset.card_pos.mpr ⟨2, SupplierPrime.mem_primesUpTo.mpr
      ⟨Nat.prime_two, le_trans (by norm_num) (SupplierPrime.canonicalPrimeCutoff_ge_563 _ _)⟩⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.NwBV

end
