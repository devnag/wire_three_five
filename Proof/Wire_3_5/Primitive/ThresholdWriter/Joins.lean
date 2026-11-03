import Proof.Wire_3_5.Primitive.Writers.FiltSetupIface2
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface
import Proof.Wire_3_5.FinalPass.HashBuild
import Proof.Wire_3_5.Lists.ListMachineRowRadixClass

/-! # THR, joins (1), (3), (5): the THR numbers, the RADIX row's entry, the FILTER rows' dock

**(1) THR numbers (W6: one machine, two consumers, the THR writer's cells and the finalpass node's
stages 4/8).** P3:2543-2558 (row:threshold-rows: the equations `L_g`, `g ∈ 𝒢`, and Theorem 2.5's prime surrogate with
cutoff `(max 24 (6(e+1)(K+1)))²`, `K = 8(|𝒢|+1)n^D`), P3:2596-2599 (the radix `b₀ = 2`, `τ₀ = ⌈log₂ cutoff⌉`), P3:2604 and
P3:2220-2231 (the fixed count hash of `filt:soft` over the `A = |𝒢|·|primes|·τ₀·2` digit populations of `M = |occs|`
coordinates, `B_* = a·4096·cap_aux`, its `t`, `J`, `e`), P3:2150-2157 (the hash's field `GF(2^{ℓ₀})`, the machine's
modulus, the level windows `W_j`).
* `primesList c` (the primes `≤ c`, increasing: `Enum.primeEquiv`'s order), **`ThrNumVals`**, **`thrNumVals`** (the
  values), `winRecs` (the level records of finalpass stage 4's input `winWord`), the anchors `thrNumVals_den`
  (`= thrCallDen`), `thrNumVals_A` (`= thrCallA`), `thrNumVals_MP` (`= thrMajorant`'s parameters), `primesList_get`
  (`= primeEquiv`), `thrNumVals_nT` (`thrNT = 2^{seedBits}·|𝒢|·Σp`);
* **`ThrNumsSpec alg Dexp`**: a machine on the encoded banks of its own register layout; entry: the framed THR request on stream `0` (head `0`),
  `|carriers|` and the THR filter cap in two input registers, everything else blank/zero; exit: stream `0` kept (head
  `0`), the fourteen values in fourteen output registers, the primes on `sPr`, the level records on `sWin` (heads `0`),
  the modulus word `frame (binary ℓ₀ p)` on `sMod` (heads `0`), every other stream blank (head `0`), every other
  register `0`, the cell `false`; cost and capacity polynomial.

**(3) RADIX row (W7).** C2's entry for the `.rad` row is its contract `ListMachine.Row.radContract`: the input word
`RadReq.record r = radRowRecC D digs p b0 s` under `RadReq.Pre r`; `radRow_run` runs the row from the framed record on
its input cursor with EMPTY work tapes and appends `Rec.exprWord (radRefC …)`. No register-level RADIX setup exists
(the gap: a writer of `frame (RadReq.record r)` from the unit's registers, and a pipe docking C2's `radMachine`).
* **`RadReady x σ w out j u r`**: the RADIX pipe's entry on the cell layout (record on stream `3`, RADIX flag `150`).

**(5) FILTER rows (W3 on the THR side).** A THR entry's FILTER row `j` is `Records.filtRow (thrSlices …) FP e G row n j`
(`Records.thrGroups`); it docks `FiltSetupSpec2` at the eight values **`thrFiltVals`**:
`FP.len, FP.cap, FP.errExp`, the seed index `t / (|𝒢|·Σp)`, `r4 = 4·row`, `G = |thrPool|`, `off = sliceOff (thrSlices)
j`, `L = |thrSlices[j]|`. **`thrFilt_emit`**: the row's C2 reference is the one `filtPipe_ready` prints from those
values; **`thrFilt_labs`**: the labels' length precondition `|sliceLabs| = 4L`.

Paper quantities of the main types: `|𝒢|`, `K`, the cutoff, `Σ_p p`, `τ₀`, the fixed hash's `(M, A, B_*, t, J, e, ℓ₀,
p)` (`ThrNumsSpec`); the RADIX row's record (`RadReady`); the THR FILTER row's filter, seed and labels (`thrFiltVals`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline

/-! ## (1) The THR numbers -/

/-- **The primes up to `c`, increasing** (the prime rows' order). -/
def primesList (c : ℕ) : List ℕ := (List.range (c + 1)).filter Nat.Prime

/-- The fourteen THR numbers of a call. -/
structure ThrNumVals where
  /-- `|𝒢|` -/
  nG : ℕ
  /-- `K = 8(|𝒢|+1)n^D` -/
  den : ℕ
  /-- the prime cutoff -/
  cut : ℕ
  /-- the number of primes `≤ cut` -/
  nPr : ℕ
  /-- `Σ_{p ≤ cut} p` -/
  pSum : ℕ
  /-- `τ₀ = ⌈log₂ cut⌉` -/
  dig : ℕ
  /-- `M = |occs|` -/
  M : ℕ
  /-- `A = |𝒢|·|primes|·τ₀·2` -/
  A : ℕ
  /-- `B_* = a·4096·cap_aux` -/
  Bs : ℕ
  /-- the list depth `J` -/
  J : ℕ
  /-- the moment order `t` -/
  tt : ℕ
  /-- the aux filter's error exponent `e` -/
  ee : ℕ
  /-- the field dimension `ℓ₀` -/
  ell0 : ℕ
  /-- the machine's modulus of `GF(2^{ℓ₀})` -/
  pMod : ℕ

/-- The values in register order `0 … 13`. -/
def ThrNumVals.get (v : ThrNumVals) : Fin 14 → ℕ :=
  ![v.nG, v.den, v.cut, v.nPr, v.pSum, v.dig, v.M, v.A, v.Bs, v.J, v.tt, v.ee, v.ell0, v.pMod]

/-- The fixed hash's majorant parameters from `M, A, B_*, K`. -/
def thrMP (M A Bs den : ℕ) : MajorantParams :=
  ⟨M, A, Bs, Primitive.listT A Bs den, Primitive.listJ A Bs den⟩

/-- **The THR numbers of a call** (`Dexp` the target exponent `D`, `ncar = |carriers|`, `capT` the THR filter cap). -/
def thrNumVals (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp ncar capT : ℕ) : ThrNumVals :=
  let nG := Fintype.card (Primitive.ThrEq P Cs alg)
  let den := 8 * (nG + 1) * P.n ^ Dexp
  let cut := Primitive.thrCutoff P Cs alg den
  let dig := Primitive.thrDigits P Cs alg den
  let nPr := (SupplierPrime.primesUpTo cut).card
  let M := (Primitive.thrOccs P Cs).length
  let A := nG * (nPr * (dig * 2))
  let Bs := a' * (4096 * ((ncar + 1) * (4096 * capT)))
  ⟨nG, den, cut, nPr, ThrQ.primeSum cut, dig, M, A, Bs, (thrMP M A Bs den).J, (thrMP M A Bs den).t,
    Primitive.listE A Bs M den, (thrMP M A Bs den).ell0, (thrMP M A Bs den).refMod⟩

/-- **The level records** of finalpass stage 4's input (`winWord M L J W` is `unary M ++ unary L ++ unary J ++ winRecs
++ [false]`). -/
def winRecs (MP : MajorantParams) : List Bool :=
  (FinalPass.ListEval.levels MP.J).flatMap (FinalPass.Hash4.winRec MP.J MP.W)

section Anchors
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}

theorem thrNumVals_den (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (ncar capT : ℕ) :
    (thrNumVals (I.starParams n hs) Cs alg I.D ncar capT).den = Primitive.thrCallDen alg I hs Cs := rfl

theorem thrNumVals_A (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ}
    (hs : I.StarAt n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (ncar capT : ℕ) :
    (thrNumVals (I.starParams n hs) Cs alg I.D ncar capT).A = Primitive.thrCallA alg I hs Cs := by
  unfold Primitive.thrCallA thrNumVals
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, SupplierPrime.PrimeIndex, Fintype.card_coe]
  rfl

theorem thrNumVals_MP (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (FP : GapParams) (alg : RepairRepresentation.DecompositionAlgorithm)
    (Dexp e : ℕ) :
    Primitive.thrMajorant P Cs carriers FP alg (thrNumVals P Cs alg Dexp carriers.length FP.cap).den e
        (thrNumVals P Cs alg Dexp carriers.length FP.cap).tt (thrNumVals P Cs alg Dexp carriers.length FP.cap).J =
      thrMP (thrNumVals P Cs alg Dexp carriers.length FP.cap).M (thrNumVals P Cs alg Dexp carriers.length FP.cap).A
        (thrNumVals P Cs alg Dexp carriers.length FP.cap).Bs (thrNumVals P Cs alg Dexp carriers.length FP.cap).den := by
  unfold Primitive.thrMajorant thrMP thrNumVals Primitive.thrAux
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, SupplierPrime.PrimeIndex, Fintype.card_coe]
  rfl

theorem primesList_sorted (c : ℕ) : primesList c = (SupplierPrime.primesUpTo c).sort := by
  apply List.Perm.eq_of_pairwise' (r := fun a b : ℕ => a ≤ b)
  · exact (List.pairwise_lt_range.filter _).imp le_of_lt
  · exact Finset.pairwise_sort _ _
  · refine (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range) (Finset.sort_nodup _ _)).mpr ?_
    intro p
    simp [SupplierPrime.primesUpTo, Finset.mem_sort]

/-- **The prime of index `i`** is `primesList c`'s `i`-th entry (`Enum.primeEquiv`'s order). -/
theorem primesList_get (c : ℕ) (i : Fin (SupplierPrime.primesUpTo c).card) :
    ((Enum.primeEquiv c i) : ℕ) = (primesList c).getD i 0 := by
  have hl : (primesList c).length = (SupplierPrime.primesUpTo c).card := by
    rw [primesList_sorted, Finset.length_sort]
  show (((SupplierPrime.primesUpTo c).orderIsoOfFin rfl) i : ℕ) = _
  rw [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply,
    List.getD_eq_getElem _ _ (by rw [hl]; exact i.isLt)]
  simp only [primesList_sorted]
  rfl

end Anchors

/-! ## (3) The RADIX row's entry on the cell layout -/

/-! ## (5) The THR FILTER rows dock `FiltSetupSpec2` -/

section Filt
variable (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Stars.Carrier P.n))

/-- **The THR FILTER row's reference is what `filtPipe_ready` prints** from the eight values. -/
theorem thrFilt_emit (FP : GapParams) (e : GapSeed FP) (G row nw jr : ℕ) :
    WriterIface.refOf (Records.filtRow (Records.thrSlices P Cs carriers) FP e G row nw jr) =
      ListMachine.Row.filtRefC (FinalPass.Filt.filterTable FP e ((Records.thrSlices P Cs carriers).getD jr []).length)
        (SupplierWalk.majorityThreshold FP.walkLen) ((Records.thrSlices P Cs carriers).getD jr []).length true
        (Emit.sliceLabs (4 * row) G (Records.sliceOff (Records.thrSlices P Cs carriers) jr)
          ((Records.thrSlices P Cs carriers).getD jr []).length) := by
  rw [← Emit.labs_eq]
  rfl

/-- The labels' length precondition of `FiltSetupSpec2.run`. -/
theorem thrFilt_labs (r4 G off L : ℕ) : (Emit.sliceLabs r4 G off L).length = 4 * L := by
  unfold Emit.sliceLabs Emit.gateLabs
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate, List.length_range',
    smul_eq_mul]
  ring

end Filt

end NearCubicWires.WireExponent3_5.PrimThrW.Joins
