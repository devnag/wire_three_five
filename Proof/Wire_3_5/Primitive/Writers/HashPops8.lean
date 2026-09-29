import Proof.Wire_3_5.Primitive.Writers.HashPops7
import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.Primitive.SeedFix.W6L
import Proof.Wire_3_5.FinalPass.DigsFinal

/-! # HASH setup (C), P2a part 8: the HASH call's populations stream

At a THR call (`filt:soft`, P3:2253-2293; the populations of, `C4H.hashPopsOf`: one per
`(g, p, d, ±)` in the order `thrEqEquiv`, `primeEquiv`, digits, sign), the generic rows loop (`popsW`) with C1's
verified digit program `DigsBody.digsWImpl` as its row writes exactly the populations stream
`HbM.popsWord (hashPopsOf …)` (the KW writer's input `1`):

* `thrOff_hash` (`oOff = |carriers' mask gates|`), `hashGis_eq` (`hashGis` is PA's `thrDigGis`);
* `hNG`, `hPrimes`, `hF`; **`popsWord_eq`**: `popsWord (hashPopsOf …) = rowsAll hF |primes| |𝒢| ++ [false]`.

Paper quantity of the main type: the HASH call's populations stream `popsWord (hashPopsOf …)` (P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.HbM (elemW popRec popsWord)

theorem flatMap_finRange {α : Type} (N : ℕ) (F : Fin N → List α) (F' : ℕ → List α) (hF : ∀ i : Fin N, F i = F' i.val) :
    (List.finRange N).flatMap F = (List.range N).flatMap F' := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  exact List.flatMap_congr (fun i _ => hF i)

theorem thrOff_hash (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) : Records.thrOff P Cs carriers = PrimT.C4H.hashOOff carriers := by
  unfold Records.thrOff Records.sliceOff Records.thrSlices PrimT.C4H.hashOOff
  rw [List.take_left' (by simp), List.length_flatten]

section Call
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- The call's selection count `|𝒢|` (the size of `thrEqEquiv`'s range). -/
abbrev hNG : ℕ := ∏ i : Fin (List.ofFn Cs).length,
  (ThresholdRows.children alg ((List.ofFn Cs).get i)).length

/-- The call's primes, increasing. -/
abbrev hPrimes : List ℕ := PrimThrW.Joins.primesList (Primitive.thrCutoff (I.starParams n hs) Cs alg
  (Primitive.thrCallDen alg I hs Cs))

/-- Row `(gi, pi)`'s digit populations (empty off the call's range). -/
noncomputable def hF (gi pi : ℕ) : List (List ℕ) :=
  if hg : gi < hNG alg Cs then
    if hp : pi < (SupplierPrime.primesUpTo (Primitive.thrCutoff (I.starParams n hs) Cs alg
        (Primitive.thrCallDen alg I hs Cs))).card then
      digL (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs)
        ((PrimAsm.Enum.thrEqEquiv (I.starParams n hs) Cs alg).symm ⟨gi, hg⟩)
        (PrimAsm.Enum.primeEquiv _ ⟨pi, hp⟩)
    else []
  else []

theorem hashGis_eq (g : Primitive.ThrEq (I.starParams n hs) Cs alg)
    (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs)))
    (d : Fin (Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))) :
    PrimT.C4H.hashGis alg I hs Cs carriers g pr d =
      Records.thrDigGis (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) g pr d := by
  have e : Records.thrOff (I.starParams n hs) Cs carriers = PrimT.C4H.hashOOff carriers :=
    thrOff_hash (I.starParams n hs) Cs carriers
  unfold PrimT.C4H.hashGis Records.thrDigGis
  simp only [e]

theorem hPrimes_length : (hPrimes alg I hs Cs).length = (SupplierPrime.primesUpTo (Primitive.thrCutoff
    (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))).card := PrimT.W6.primesList_length _

/-- **The populations stream is the rows' records.** -/
theorem popsWord_eq : popsWord (PrimT.C4H.hashPopsOf alg I hs Cs carriers) =
    rowsAll (hF alg I hs Cs carriers) (hPrimes alg I hs Cs).length (hNG alg Cs) ++ [false] := by
  unfold popsWord PrimT.C4H.hashPopsOf rowsAll
  congr 1
  rw [List.flatMap_assoc]
  refine flatMap_finRange _ _ _ (fun gi => ?_)
  rw [List.flatMap_assoc, hPrimes_length]
  unfold rowsG
  refine flatMap_finRange _ _ _ (fun pi => ?_)
  rw [List.flatMap_assoc]
  unfold hF
  rw [dif_pos (show (gi : ℕ) < hNG alg Cs from gi.isLt), dif_pos pi.isLt]
  simp only [digL, List.ofFn_eq_map, List.flatMap_map]
  refine List.flatMap_congr (fun d _ => ?_)
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, recsOf,
    Function.comp_apply, hashGis_eq]

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
