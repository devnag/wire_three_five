import Proof.Supplier.SupplierWalk
import Proof.Supplier.SupplierToeplitzCore
import Proof.Wire_3_5.Foundations.GF

/-! # The regular sparsity filter of `filt:gap` (P3:2016-2104): definitions

Realizes the filter of `filt:gap` (P3:2016-2034): "Let `Z=(Z_1,…,Z_M)∈{0,1}^M`, let `w(Z)=Σ_i Z_i`, and let
`U ≥ 1` be an integer. Put `C=4096`. For every `0<ε<1/2`, there is an explicit distribution of Boolean polynomials
`F_e(Z)` over `𝔽₂` such that `w(Z) ≤ U ⟹ Pr_e[F_e(Z)=0] ≤ ε`, `w(Z) ≥ CU ⟹ Pr_e[F_e(Z)=1] ≤ ε`." It is the
filter `lem:primitive` applies to each named carrier's signed mixed-residual population: "For each name, use the
regular filter of filt:gap on its signed mixed-residual population, with cap `B` and an endpoint error chosen as a
sufficiently small fixed inverse power of `n`" (P3:3074-3077), with "one common seed `e` [...] for all coordinates"
(P3:3432-3434).

The construction follows the proof (P3:2036-2101) step by step:
* "Choose a dyadic `p` with `1/(64U) ≤ p ≤ 1/(32U)`. An affine map `Aα_i+B` [...] followed by a zero-prefix test,
  gives pairwise-independent inclusion bits `H_i` of mean `p`": `p = 2^{-a}` with `a = prefixBits` (so
  `1/(64U) < p ≤ 1/(32U)`), and `H_i = selected h i`, the zero-prefix test on the binary Toeplitz hash
  (`SupplierToeplitzCore.toeplitzHash`, an affine pairwise-independent family) of the label of coordinate `i`;
* "choose `u,v` uniformly in a binary field `𝕂` of order at least `16M`, and set `a_i = Tr(u v^i)`": the field is
  `GaloisField 2 m` with `m = fieldBits ≥ log₂(16M)`, the trace is `Algebra.trace` to `ZMod 2`;
* "the bit `P = Σ_i H_i a_i Z_i` in `𝔽₂`": `copyParity`;
* "Take 128 independent copies and accept when at most one quarter of the resulting bits are one": `baseFilter`;
* "Pad the base seed [...] and use the explicit powered Margulis walk [...] An odd walk of length `t` has a bad
  majority only if some `(t+1)/2` locations are all bad": the seed `e` is a walk sample of Theorem 2.5's powered
  Margulis walk (`SupplierWalk.MargulisWalkSample`) over the base seeds, `t = walkLen` is odd, and the filter is the
  majority vote `concreteMajorityFailure` (at least `(t+1)/2` of the visited base seeds accept).

Main quantities: `GapParams` (the paper's `M`, `U` and `ε = 2^{-errExp}`), the seed space `GapSeed P` (a finite
type), and the regular filter `gapFilter P e Z = F_e(Z)`, Boolean on every seed and every input by its type. The
walk vertex is a pair in `ZMod N × ZMod N` with `N` the number of base seeds; its first coordinate is decoded to a
base seed and its second coordinate is the padding. The construction is written once, generically in the field
operations (`gapFilterWith`), so that the executable twin (component module `Proof.Wire_3_5.Filters.FilterGap`) runs the same code
over a computable field; the guarantee (the two error bounds, the seed length and the `𝔽₂` degree) is proved there.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitzCore
open NearCubicWires.SupplierWalk

/-- The parameters of one `filt:gap` filter (P3:2019-2022): the vector length bound `M` (`len`), the cap `U`
(`cap`), and the endpoint error `ε = 2^{-errExp}`. -/
structure GapParams where
  /-- `M`: the filter is applied to vectors `Z` of at most `len` coordinates -/
  len : ℕ
  /-- `U`: the cap -/
  cap : ℕ
  /-- the endpoint error is `ε = 2^{-errExp}` -/
  errExp : ℕ

namespace GapParams
variable (P : GapParams)

/-- The zero-prefix length `a`, `p = 2^{-a}` (P3:2037): the least `a` with `32U ≤ 2^a`, so
`1/(64U) < p ≤ 1/(32U)` for `U ≥ 1`. -/
def prefixBits : ℕ := Nat.clog 2 (32 * P.cap)

/-- The rank of the Toeplitz hash: the prefix fits and the `len` coordinate labels are distinct
(P3:2039-2041, "The field contains distinct labels `α_i` and has enough coordinate bits for that prefix"). -/
def labelBits : ℕ := max P.prefixBits (Nat.clog 2 P.len)

/-- `m`, the field `𝕂 = GF(2^m)` has order `2^m ≥ 16M` (P3:2053-2054), and `m ≥ 4`. -/
def fieldBits : ℕ := Nat.clog 2 P.len + 4

theorem fieldBits_ne_zero : P.fieldBits ≠ 0 := by unfold fieldBits; omega

/-- The odd walk length `t` (P3:2096-2100): `2^{-(2t+4)} ≤ 2^{-errExp}`. -/
def walkLen : ℕ := 2 * (P.errExp / 4) + 1

/-- The number of seeds of one copy of the selected parity: a Toeplitz seed (`2·rank − 1` diagonal bits and a
`rank`-bit translation) and two field elements `u, v`. -/
def copySize : ℕ :=
  2 ^ P.labelBits * 2 ^ (P.labelBits - 1) * 2 ^ P.labelBits * (2 ^ P.fieldBits * 2 ^ P.fieldBits)

/-- The number of base seeds: `128` independent copies (P3:2076). -/
def baseSize : ℕ := P.copySize ^ 128

instance instNeZeroBaseSize : NeZero P.baseSize := ⟨by unfold baseSize copySize; positivity⟩

end GapParams

/-- The field operations the construction uses: multiplication, one, and the `𝔽₂`-valued trace (as a `Bool`).
The seed instantiates them with `GaloisField 2 m`; the executable twin with a computable field. -/
structure BiasOps (K : Type) where
  mul : K → K → K
  one : K
  tr : K → Bool

/-- `v^k` by repeated multiplication. -/
def BiasOps.pow {K : Type} (o : BiasOps K) (v : K) : ℕ → K
  | 0 => o.one
  | k + 1 => o.mul (o.pow v k) v

/-- The seed of one copy of the selected parity: the Toeplitz seed of the inclusion bits and `(u, v) ∈ 𝕂²`. -/
abbrev CopySeed (P : GapParams) (K : Type) : Type := ToeplitzSeed P.labelBits × K × K

/-- A base seed: `128` independent copies (P3:2076). -/
abbrev BaseSeed (P : GapParams) (K : Type) : Type := Fin 128 → CopySeed P K

/-- The label of coordinate `i` (its binary expansion), distinct for distinct `i < 2^rank`. -/
def coordLabel (rank i : ℕ) : SupplierToeplitzCore.BitVec rank := fun j => if i.testBit j.val then 1 else 0

/-- The inclusion bit `H_i` (P3:2036-2039): the Toeplitz hash of coordinate `i`'s label has a zero prefix of
length `a`. -/
def selected (P : GapParams) (h : ToeplitzSeed P.labelBits) (i : ℕ) : Bool :=
  decide (∀ j : Fin P.labelBits, j.val < P.prefixBits → toeplitzHash (coordLabel P.labelBits i) h j = 0)

/-- The selected active coordinates: `Z_i = 1` and `H_i = 1`. -/
def selectedActive (P : GapParams) (h : ToeplitzSeed P.labelBits) (Z : List Bool) : Finset ℕ :=
  (Finset.range Z.length).filter fun i => Z.getD i false = true ∧ selected P h i = true

/-- The small-bias bit `a_i = Tr(u v^i)` of coordinate `i` (P3:2053-2055); list position `i` is the paper's
coordinate `i + 1`. -/
def biasBit {K : Type} (o : BiasOps K) (u v : K) (i : ℕ) : Bool := o.tr (o.mul u (o.pow v (i + 1)))

/-- **The selected parity** `P = Σ_i H_i a_i Z_i ∈ 𝔽₂` of one copy (P3:2063). -/
def copyParity (P : GapParams) {K : Type} (o : BiasOps K) (c : CopySeed P K) (Z : List Bool) : Bool :=
  decide (Odd ((selectedActive P c.1 Z).filter fun i => biasBit o c.2.1 c.2.2 i = true).card)

/-- **The base filter** (P3:2076-2081): accept when at most one quarter of the `128` parity bits are one. -/
def baseFilter (P : GapParams) {K : Type} (o : BiasOps K) (s : BaseSeed P K) (Z : List Bool) : Bool :=
  decide ((Finset.univ.filter fun j : Fin 128 => copyParity P o (s j) Z = true).card ≤ 32)

/-- The seeds of one copy, enumerated: `Fin copySize ≃ CopySeed`, from a coordinate map of the field. -/
def copyEquiv (P : GapParams) {K : Type} (kEq : Fin (2 ^ P.fieldBits) ≃ K) :
    Fin P.copySize ≃ CopySeed P K :=
  finProdFinEquiv.symm.trans <|
    Equiv.prodCongr
      (finProdFinEquiv.symm.trans <|
        Equiv.prodCongr
          (finProdFinEquiv.symm.trans <|
            Equiv.prodCongr (finFunctionFinEquiv.symm : Fin (2 ^ P.labelBits) ≃ (Fin P.labelBits → Fin 2))
              (finFunctionFinEquiv.symm : Fin (2 ^ (P.labelBits - 1)) ≃ (Fin (P.labelBits - 1) → Fin 2)))
          (finFunctionFinEquiv.symm : Fin (2 ^ P.labelBits) ≃ (Fin P.labelBits → Fin 2)))
      (finProdFinEquiv.symm.trans (Equiv.prodCongr kEq kEq))

/-- The base seeds, enumerated: `Fin baseSize ≃ BaseSeed`. -/
def baseEquiv (P : GapParams) {K : Type} (kEq : Fin (2 ^ P.fieldBits) ≃ K) :
    Fin P.baseSize ≃ BaseSeed P K :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin 128)) (copyEquiv P kEq))

/-- The base seed at a walk vertex: its first coordinate, decoded (the second coordinate is padding). -/
def vertexSeed (P : GapParams) {K : Type} (kEq : Fin (2 ^ P.fieldBits) ≃ K)
    (v : MargulisVertex P.baseSize) : BaseSeed P K :=
  baseEquiv P kEq ((ZMod.finEquiv P.baseSize).symm v.1)

/-- **The regular filter, generically in the field operations** (P3:2083-2101): the majority vote of the base
filter over the `t` base seeds visited by the powered Margulis walk `e`: `true` iff at least `(t+1)/2` of them
accept. -/
def gapFilterWith (P : GapParams) {K : Type} (o : BiasOps K) (kEq : Fin (2 ^ P.fieldBits) ≃ K)
    (e : MargulisWalkSample P.baseSize P.walkLen) (Z : List Bool) : Bool :=
  concreteMajorityFailure (fun v => baseFilter P o (vertexSeed P kEq v) Z) e

/-! ## The seed's instance: `𝕂 = GF(2^m)` -/

/-- The field operations of `GF(2^m)`, with the absolute trace to `𝔽₂` (P3:2054-2055). -/
noncomputable def galoisOps (m : ℕ) : BiasOps (GaloisField 2 m) where
  mul := (· * ·)
  one := 1
  tr := fun x => decide (Algebra.trace (ZMod 2) (GaloisField 2 m) x = 1)

/-- **The coordinate map of `GF(2^m)`, anchored to bits**: the `m`-bit vectors of the certified field
`𝔽₂[X]/(p)` at the searched modulus `p = GF.firstPrimitive m` (`GF.encEquiv`), followed by an algebra isomorphism onto
`GaloisField 2 m` (`GF.refAlgEquivGalois`). The filter does not depend on which isomorphism (the absolute trace is
invariant under algebra isomorphisms), so `gapFilter` is the bit-level filter a machine computes with the shift-and-xor
product and the masked-parity trace bit (`Checks/GapFilterBits`). The certificate is decided; the second branch is never
taken (`GF.firstPrimitive_cert`, component module `Proof.Wire_3_5.Filters.GFExists`). -/
noncomputable def galoisEquiv (m : ℕ) (hm : m ≠ 0) : Fin (2 ^ m) ≃ GaloisField 2 m :=
  if hc : GF.PrimitiveCert (GF.firstPrimitive m) m then
    (GF.encEquiv (GF.firstPrimitive m) m hc.2.1).trans (GF.refAlgEquivGalois (GF.firstPrimitive m) m hc).toEquiv
  else (Finite.equivFinOfCardEq (GaloisField.card 2 m hm)).symm

/-- **The seed space** `e` of the regular filter: a powered Margulis walk sample over the base seeds. -/
abbrev GapSeed (P : GapParams) : Type := MargulisWalkSample P.baseSize P.walkLen

instance (P : GapParams) : Fintype (GapSeed P) := inferInstanceAs (Fintype (MargulisWalkSample _ _))

instance (P : GapParams) : Nonempty (GapSeed P) := ⟨⟨(0, 0), fun _ _ => 0⟩⟩

/-- **The regular filter of `filt:gap`** `F_e(Z)` (P3:2016-2034), Boolean on every seed and every input. -/
noncomputable def gapFilter (P : GapParams) (e : GapSeed P) (Z : List Bool) : Bool :=
  gapFilterWith P (galoisOps P.fieldBits) (galoisEquiv P.fieldBits P.fieldBits_ne_zero) e Z

end NearCubicWires.WireExponent3_5.Filters
