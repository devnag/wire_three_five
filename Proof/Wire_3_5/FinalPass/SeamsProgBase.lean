import Proof.Wire_3_5.FinalPass.SeamsPtBase
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins
import Proof.Wire_3_5.FinalPass.FiltTabBlock
import Proof.Wire_3_5.Primitive.SeedFix.C4GeoV
import Proof.Wire_3_5.FinalPass.ListEvalBridge
import Proof.Wire_3_5.FinalPass.MaskRef
import Proof.Wire_3_5.Primitive.Writers.DataTabs

/-! # The final pass's program types: S2 (THR per point) and S4 (the seeds phase), with their words

Consumer backward from the seams (`PtEvalW`, `FrontOut`, `NumDenOut`, `FitsRes`): the front (S5) must leave
exactly the words the per-point evaluators and the seeds phase read. This module fixes them.

* **`PtEvalFix`**: a per-point evaluator with its call words and numbers FIXED in the type (`toW` forgets them).
* **S2**: `thrWords` (7 words: the tuple's gate table, as ThrData's `tabS`; the four payloads, as `DigsIn`'s `Pay`;
  the primes up to the cutoff, as W6's port 17; stage 4's table `levelWord` at `L = |occs|`), `thrNums` (`a`, `|𝒢|`,
  `τ₀`, `|occs|`), **`ThrPtProg`** `:= PtEvalFix ThrCall … rsumThr 7 4 thrWords thrNums`. `thrCallOf`: the THR call
  data at a request (`den = thrCallDen`, `D` the fixed hash's lists, so the reporter is `thrCallReportBits`).
* **S4's own words** (`s4Core`, 8 words): X3's offset word `frameP (ofFn offset) ++ [false]`; the sampled pairs
  (`sampWord`: per pair both indices framed in `s·(r/2)`-bit binary, then `false`: stage 0's input); the carriers'
  mask tables (as ThrData's `sCar k 3`); stage 6's `tauWord`, `modWord`; stage 7's threshold `1^{thr} 0`; the small
  numbers `1` (the star flag), `b, s, r/2, hL, n−rb−hL, n−rb, dRow, dR, |mask gates X₀|, |mask gates X₁|, seed
  width, |carriers|` as one unary list.
* **`frontWordsOf`**: per request, S4's 8 words, then the THR evaluator's 7 words and its numbers (unary list), then
  the SYM evaluator's words (`E3.words`) and its numbers; the other mode's slots and every slot off the star
  hypotheses are blank.
* **`SeedsProg`** (S4's type): one machine for the family; from every front exit meeting `FrontOut` at these words,
  `Num = 0`, `Den = denOf` in `W`-bit binary (`W` the front's choice with `ptCount·vmax < 2^W`), and S4's register tapes
  blank of length `Kc·(|fpIn|+1)^Dc + 1`, it reaches `NumDenOut` within `seedsShape`. `SeedsProg.phase` is
  `FpPhases.seeds`, `SeedsProg.numDen` its exit.

Paper quantities: the per-point sum `Σ_{g,p} R̂_{g,p}` (S2), the printed numerator and denominator (S4). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split
open NearCubicWires.SupplierWalk (majorityThreshold)

/-! ## A per-point evaluator with fixed words -/

/-! ## S2: the THR per-point evaluator's words -/

/-- **S2's call words** (THR): 0 the tuple's gate table (ThrData's `tabS`), 1–4 the payloads (`DigsIn`'s `Pay`),
5 the primes up to the cutoff (W6's port 17), 6 stage 4's table at `L = |occs|`. -/
def thrWords (k : ThrCall) : Fin 7 → List Bool := fun i =>
  if i.val = 0 then
    (if k.a = 0 then [] else Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG k.Cs)) (PrimT.ThrTab.tupleG k.Cs))
  else if h : i.val - 1 < k.a ∧ i.val ≤ 4 then PrimThrW.TopFront.payOf k.alg (k.Cs ⟨i.val - 1, h.1⟩)
  else if i.val ≤ 4 then []
  else if i.val = 5 then PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (thrCutoff k.P k.Cs k.alg k.den))
  else ListEval.levelWord k.D.M k.D.J k.D.W (ListEval.rowsOf k.D (thrOccs k.P k.Cs).length)

/-- **S2's numbers** (THR): `a`, `|𝒢|`, `τ₀`, `|occs|`. -/
def thrNums (k : ThrCall) : Fin 4 → ℕ :=
  ![k.a, Fintype.card (ThrEq k.P k.Cs k.alg), thrDigits k.P k.Cs k.alg k.den, (thrOccs k.P k.Cs).length]

section Req
variable {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm)

/-- **The THR call data at a request**: the fixed hash's lists at `thrCallDen`, `thrCallE/T/J`. -/
def thrCallOf {n : ℕ} (hs : I.StarAt n) {a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ) : ThrCall :=
  ⟨I.starParams n hs, a, ha, Cs, alg, thrCallDen alg I hs Cs,
    MajorantBits.dataBits
      (thrMajorant (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg (thrCallDen alg I hs Cs)
        (thrCallE alg I hs Cs carriers) (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers))
      (thrHashBits (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation) Cs carriers
        (I.filterParams .thr n) alg (thrCallDen alg I hs Cs) (thrCallE alg I hs Cs carriers)
        (thrCallT alg I hs Cs carriers) (thrCallJ alg I hs Cs carriers))⟩

/-- The SYM call data at a request. -/
def symCallOf {n : ℕ} (hs : I.StarAt n) {a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) : SymCall :=
  ⟨I.starParams n hs, a, ha, Cs, symListParams I n a Cs carriers⟩

end Req

/-! ## S4's own words -/

/-- **The sampled pairs as stage 0 reads them**: per pair, both indices framed in `s·(r/2)`-bit binary; then `false`. -/
def sampWord (P : StarParams) (smp : CallSample P) : List Bool :=
  (List.ofFn fun l : Fin smp.Q =>
    frame (binary (P.s * (P.r / 2)) (smp.S l).1) ++ frame (binary (P.s * (P.r / 2)) (smp.S l).2)).flatten ++ [false]

/-- **A carrier's mask table** (ThrData's `sCar k 3`): the doubled gates' table, blank past the carriers. -/
def carTab {n : ℕ} (carriers : List (Carrier n)) (k : ℕ) : List Bool :=
  if h : k < carriers.length then
    Corner.gatesW (PrimT.tabH (carriers.get ⟨k, h⟩)) (Corner.maskGates (carriers.get ⟨k, h⟩))
  else []

/-- The mask gates' count of carrier `k` (the filter's point length). -/
def carLen {n : ℕ} (carriers : List (Carrier n)) (k : ℕ) : ℕ :=
  if h : k < carriers.length then (Corner.maskGates (carriers.get ⟨k, h⟩)).length else 0

/-- The seed index width `160·(2⌊errExp/4⌋) + 2r`, `r = wOf·128` (X1's `seedIndex_cast`). -/
def seedWidth (FP : GapParams) : ℕ :=
  160 * (2 * (FP.errExp / 4)) + 2 * (Filt.wOf FP.fieldBits FP.labelBits * 128)

/-- **S4's small numbers**: the star flag `1` (off the star hypotheses the whole word is blank), `b, s, r/2, hL,
n−rb−hL, n−rb, dRow, dR, |mask gates X₀|, |mask gates X₁|, the seed width, |carriers|`. -/
def s4Small (P : StarParams) {n : ℕ} (carriers : List (Carrier n)) (FP : GapParams) : List ℕ :=
  [1, P.b, P.s, P.r / 2, PrimT.C4Geo.hL P, P.n - P.r * P.b - PrimT.C4Geo.hL P, P.n - P.r * P.b, PrimT.C4Geo.dRow P,
    PrimT.C4Geo.dR P, carLen carriers 0, carLen carriers 1, seedWidth FP, carriers.length]

/-- **S4's own words** at a star call: 0 X3's offset word, 1 the sampled pairs, 2–3 the carriers' mask tables,
4–5 stage 6's field words, 6 stage 7's threshold `1^{thr} 0`, 7 the small numbers (unary list). -/
def s4Core (P : StarParams) (σ : P.Translation) (smp : CallSample P) (carriers : List (Carrier P.n))
    (FP : GapParams) : Fin 8 → List Bool :=
  ![frameP (List.ofFn (PrimT.C4Geo.offset P σ)) ++ [false], sampWord P smp, carTab carriers 0, carTab carriers 1,
    Filt.tauWord FP, Filt.modWord FP, ListEval.unary (majorityThreshold FP.walkLen),
    PrimAsm.Data.unaryList (s4Small P carriers FP)]

section Req2
variable {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (E3 : SymPtEval)

/-- **The largest per-point value** at a request: `|𝒢|·|𝒫|` (THR), the list seeds (SYM). -/
def vmaxOf : PrimRequest → ℕ
  | ⟨n, .sym, a, _, Cs, carriers, _⟩ =>
      if _hs : I.StarAt n then Fintype.card (symListParams I n a Cs carriers).FlatSeed else 0
  | ⟨n, .thr, _, _, Cs, _, _⟩ =>
      if hs : I.StarAt n then
        Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
          Fintype.card (PrimeIndex (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)))
      else 0

end Req2

/-! ## S4's program type -/

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
