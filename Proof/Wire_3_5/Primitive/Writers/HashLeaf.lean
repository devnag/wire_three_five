import Proof.Wire_3_5.FinalPass.SeamsUni
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Proof.Wire_3_5.Primitive.Writers.WritersJoin

/-! # (HASH (d4)): the HASH writer's leaf

**`hashLeaf : HashLeafOf l`**: from the v3 data stage family (`ThrStage3U l`, uniform constants in StageU's order),
the walk bank, the FILTER setup, `FiltPipeLe2` and `ThrNumsPoly l`, the HASH writer's leaf `WritersJoin.HashLeafJ2 l`.
After `fe`: the floor envelope `envMax E₀ E_H` (`E₀` the floor, `E_H` with `c_ψ = E_tot`, the budget's exponent in
`Q = 2^m + 1`, a function of the exponents only) and the floor `max CD₀ 1`; after `F`: the coefficient `c_W`
(`HashFam.HB.cW`, with `C₀`, W6's `K_t`, the cap's `capK c_r`, the dimension's `K_H`); at every clock and
source work, the machine `HashFam.hashM` (ShellH's shell at the data stage and PA's HASH unit) and its run
(`hash_fam_run`) within `c_W·classBound` (`hash_fam_cost`).

* `wbC`, `wbD`, `nwC`, `nwD` (the call word's and `needW` polynomial bounds), `fpK`, `fpD` (`FiltPipeLe2`),
  `tnD`, `tnK` (`ThrNumsPoly`), `hbE` (the exponents), `hbF` (all constants), `hbF_Etot`;
* **`hashLeaf`**.

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226) within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.HashFam
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline

/-! ## The producers' constants -/

noncomputable def wbC : ℕ := Classical.choose CallSize.wordBound_poly
noncomputable def wbD : ℕ := Classical.choose (Classical.choose_spec CallSize.wordBound_poly)
theorem wb_spec (n : ℕ) : CallSize.wordBound 26 26 2 n ≤ wbC * (n + 1) ^ wbD :=
  (Classical.choose_spec (Classical.choose_spec CallSize.wordBound_poly)).2 n

noncomputable def nwC : ℕ := Classical.choose PrimT.C4GateSym.needW_pb
noncomputable def nwD : ℕ := Classical.choose (Classical.choose_spec PrimT.C4GateSym.needW_pb)
theorem nw_spec (n : ℕ) : PrimT.C4GateSym.needW n ≤ nwC * (n + 1) ^ nwD :=
  (Classical.choose_spec (Classical.choose_spec PrimT.C4GateSym.needW_pb)).2 n

noncomputable def fpK (hfp : BudgetIface.FiltPipeLe2) : ℕ := Classical.choose hfp
noncomputable def fpD (hfp : BudgetIface.FiltPipeLe2) : ℕ := Classical.choose (Classical.choose_spec hfp)
theorem fp_spec (hfp : BudgetIface.FiltPipeLe2) : ∀ (P : Filters.GapParams) (e : Filters.GapSeed P) (L r4 G off : ℕ),
    1 ≤ P.cap → FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
      fpK hfp * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ fpD hfp * (L + 2) ^ (fpD hfp * (P.errExp + 1)) :=
  Classical.choose_spec (Classical.choose_spec hfp)

variable {l : Literals}

noncomputable def tnD (hT : BudgetIface.ThrNumsPoly l) : ℕ := Classical.choose (hT (CallIndexR.capZR l))
noncomputable def tnK (hT : BudgetIface.ThrNumsPoly l) (Cc : ℕ) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (hT (CallIndexR.capZR l)) Cc F)
theorem tn_spec (hT : BudgetIface.ThrNumsPoly l) (Cc : ℕ) (F : GateFree l) :
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
      (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (capT : ℕ),
      a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
      capT ≤ Cc * (n + 1) ^ CallIndexR.capZR l →
      ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D capT, v ≤ tnK hT Cc F * (n + 1) ^ tnD hT :=
  Classical.choose_spec (Classical.choose_spec (hT (CallIndexR.capZR l)) Cc F)

/-- **The exponents** (fixed with the floors). -/
def hbE (Dw Dnw Dt D0 Df Dn Db Z : ℕ) : HB := ⟨0, Dw, 0, Dnw, 0, Dt, 0, D0, 0, Df, 0, Dn, 0, Db, Z, 0, 0⟩

/-- **All the constants** (after `F`). -/
def hbF (Cw Dw Cnw Dnw Kt Dt C0 D0 Kf Df Cn Dn Cb Db Z Cc cr : ℕ) : HB :=
  ⟨Cw, Dw, Cnw, Dnw, Kt, Dt, C0, D0, Kf, Df, Cn, Dn, Cb, Db, Z, Cc, cr⟩

/-- The budget's exponent reads the exponents only. -/
theorem hbF_Etot (Cw Dw Cnw Dnw Kt Dt C0 D0 Kf Df Cn Dn Cb Db Z Cc cr : ℕ) :
    (hbF Cw Dw Cnw Dnw Kt Dt C0 D0 Kf Df Cn Dn Cb Db Z Cc cr).Etot = (hbE Dw Dnw Dt D0 Df Dn Db Z).Etot := rfl

/-! ## The leaf -/

end NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
