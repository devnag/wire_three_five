import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR2
import Proof.Wire_3_5.Primitive.SeedFix.TS4OBase
import Proof.Wire_3_5.Primitive.Writers.SymDecNums
import Proof.Wire_3_5.UnionMachine.NumsPh3Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.TS4N
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.Primitive.SeedFix.NwBTBase


noncomputable section
set_option maxRecDepth 4096


/-! # T3 NW phase (b), the types: the value (b) computes, its link, its capacity atoms, its dock cost

Phase (b) (the `NumsPh3.PhB`) computes, at a THR call on the star, from W6's numbers `|𝒢|`, `cut`, `Σp`,
`#primes` (ports 3, 5, 7, 6), the gap numbers' `2^{sb}` and the star numbers' `n`, `k_h = s·⌊r/2⌋`:

* **`vVal`**: `V = 2^e·B·2^{sb}·#primes` with `q = 2|𝒢|·cut + 1`, `B = (|𝒢|·Σp·2^{sb}·q² + 1)·8192·n²`,
  `e = ⌊(5k_h + 3)/4⌋` (the THR sample count `Q = 2^e·B`, `ThrCap.thrQ_link`);
* **`vB`**: `vVal` at the call's numbers (`valsB` = W6's `thrNumVals` at `cap_T = capTL`, `|carriers|`; `gapB` =
  the gap parameters at `(2(n+1)^{26}, cap_T, f_e·L)`; `khB`);
* **`VLinkB l`**: at every THR call on the star, `vB = vOf` (P3:3044-3048: `|PrimeIndex(cut)|·|E|·Q`);
* **`AtomsB c Tf`** and **`NeedB l`**: every number (b)'s register programs hold is at most
  `K_n(F)·(|fpIn|+1)^{D_n(f_e)}` (the v4 need, `cap_T`, `(n+1)^{26}`, W6's power, W6's 14 numbers, the gap numbers,
  `V`, `T_f`; and `#primes ≥ 1`);
* **`CostB l`**: the two docked machines' cost at `V_d = tV(|fpIn|, n, cap_T)` is at most
  `K_c(F)·(|fpIn|+1)^{D_c(f_e)}`.

The phase-(b) term takes `VLinkB l`, `NeedB l`, `CostB l` as arguments.

Paper quantity of the main types: the final pass's unshifted denominator `V = |PrimeIndex(cut)|·|E|·Q` at a THR request
(P3:3044-3048) and its polynomial size in the input (P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

section Call
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n : ℕ}
  (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
  (carriers : List (Stars.Carrier n))

/-- W6's numbers at the call (`D = 1`, `|carriers|`, `cap_T = capTL`). -/
noncomputable def valsB : PrimThrW.Joins.ThrNumVals :=
  PrimThrW.Joins.thrNumVals ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1
    carriers.length (PrimT.TS4.capTL l F.cr n)

/-- The gap parameters (b) computes: `(2(n+1)^{26}, cap_T, f_e·L)`. -/
noncomputable def gapB (n : ℕ) : Filters.GapParams :=
  PrimAsm.SymDec.gP n (PrimT.TS4.capTL l F.cr n) (F.filterErrDeg * Ledger.Lq n)

/-- `k_h = s·⌊r/2⌋` (the star numbers' `SGb 8`). -/
noncomputable def khB : ℕ :=
  ((callInputs l F kclk coef A a ha).starParams n hs).s * (((callInputs l F kclk coef A a ha).starParams n hs).r / 2)

/-- **The value (b) computes** at the call. -/
noncomputable def vB : ℕ :=
  vVal (valsB l F kclk coef A a ha hs Cs carriers).nG (valsB l F kclk coef A a ha hs Cs carriers).cut
    (valsB l F kclk coef A a ha hs Cs carriers).pSum (2 ^ (gapB l F n).seedBits)
    (valsB l F kclk coef A a ha hs Cs carriers).nPr n (khB l F kclk coef A a ha hs)

/-- **(b)'s capacity atoms** at one THR call: every number the register programs hold is at most `c`. -/
structure AtomsB (c Tf : ℕ) : Prop where
  need : PrimT.TS4.needT l F.cr n ≤ c
  capT : PrimT.TS4.capTL l F.cr n ≤ c
  n26 : (n + 1) ^ 26 ≤ c
  pow : (n + PrimT.TS4.capTL l F.cr n + 1) ^ (ThrDecF.NW l).Dn ≤ c
  vals : ∀ i : Fin 14, (valsB l F kclk coef A a ha hs Cs carriers).get i ≤ c
  gap : 2 ^ ((gapB l F n).seedBits + 1) + (gapB l F n).labelBits + (gapB l F n).fieldBits + (gapB l F n).walkLen ≤ c
  val : vB l F kclk coef A a ha hs Cs carriers ≤ c
  tf : Tf ≤ c
  np : 1 ≤ (valsB l F kclk coef A a ha hs Cs carriers).nPr

end Call

section Props
variable (l : Literals)

/-- **(b)'s value link** (P3:3044-3048): at every THR call on the star, the computed value is `vOf`. -/
def VLinkB : Prop :=
  ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n),
    vB l F kclk coef A a ha hs Cs carriers = UnionMachine.NumsPh2.vOf l F kclk coef A a ha ⟨_, hc⟩

/-- **(b)'s capacity need** (P3:3170-3181): the atoms at `K_n(F)·(|fpIn|+1)^{D_n(f_e)}`. -/
def NeedB : Prop :=
  ∃ (Kn : GateFree l → ℕ) (Dn : ℕ → ℕ), ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ)
    (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ) (hc : (callInputs l F kclk coef A a ha).Call ⟨n, .thr, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n),
    AtomsB l F kclk coef A a ha hs Cs carriers
      (Kn F * ((FinalPass.PlanFP.fpIn l F kclk coef A a ha ⟨_, hc⟩).length + 1) ^ Dn F.filterErrDeg)
      (FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨_, hc⟩)

end Props

end NearCubicWires.WireExponent3_5.PrimT.NwB

end
