import Proof.Wire_3_5.Transfer.TransferTests
import Proof.Wire_3_5.Foundations.Skeleton

/-! # The tests' masks are the seed's `filt:gap` filters of the named carriers (P3:3432-3449)

Realizes the masks of `tr:masks` at the seed's types: "Use the regular Boolean sparsity filter from
Lemma lem:primitive on each coordinate's entire carrier union. Denote its value by `G_X(e,x) ∈ {0,1}`, where one
common seed `e` is used for all coordinates" (P3:3432-3434), and "For clause `i`, use
`M_i(e,x) = G_{X(i,1)}(e,x) G_{X(i,2)}(e,x)`" (P3:3444-3445); "Every occurrence of one variable uses the same filter,
and the same filter multiplies every term, including the constant term, of a given verification expression"
(P3:3450-3452).

`carrierFilter I m pcpp carrier translation` is `G_X` in class mode `m`: the seed's mask (`PrimitiveInputs.mask`,
the product of the `filt:gap` regular filters of the named carriers' signed mixed-residual populations at the call's
translation, with the mode's cap `B.capOf m`) of a request naming the one carrier of `X`. A branch of
the union machine works in its guessed class mode `m` (P3:3669-3671), so every primitive call it makes is in mode
`m`: each call for a `V` or `Q` term of `X` (one named carrier) sees exactly `G_X` (`mask_single`), and each call for
a `μ` term of clause `i` (the two named carriers of `X(i,1)`, `X(i,2)`, with any circuits) sees exactly `M_i`
(`mask_pair`, `clauseMask_carrierFilter`). So the tests of `Proof.Wire_3_5.Transfer.TransferTests` at these filters are the
quantities the primitive's calls estimate. The seed space is the seed's `I.Seed m q` (finite, nonempty), and
`tr:soundness` holds there (`seedMaskedVerifierTrace_empty`).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost

section SeedMasks
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)

/-- A request in mode `m` at length `q` naming the given carriers at the given translation, with no circuits (the
mask of a request depends only on its mode, length, carriers and translation). -/
def maskRequest (m : Mode) (q : ℕ) (carriers : List (Stars.Carrier q)) (translation : List ℕ) : PrimRequest :=
  ⟨q, m, 0, Nat.zero_le 4, Fin.elim0, carriers, translation⟩

/-- `G_X(e,x)` in mode `m`: the seed's regular filter of the carrier of `X` at the common translation and seed. -/
noncomputable def carrierFilter (m : Mode) {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)
    (carrier : PcppVar pcpp → Stars.Carrier q) (translation : List ℕ) :
    PcppVar pcpp → I.Seed m q → BitInput q → Bool :=
  fun X e x => I.mask (maskRequest m q [carrier X] translation) e x

/-- A call in mode `m` naming two carriers has the product of their masks (P3:3444-3445). -/
theorem mask_pair {q : ℕ} (m : Mode) (a : ℕ) (ha : a ≤ 4) (circuits : Fin a → m.Circuit q)
    (c c' : Stars.Carrier q) (translation : List ℕ) (e : I.Seed m q) (x : BitInput q) :
    I.mask ⟨q, m, a, ha, circuits, [c, c'], translation⟩ e x =
      (I.mask (maskRequest m q [c] translation) e x && I.mask (maskRequest m q [c'] translation) e x) := by
  unfold PrimitiveInputs.mask maskRequest
  by_cases h : I.StarAt q
  · simp only [dif_pos h, List.all_cons, List.all_nil, Bool.and_true]
  · simp only [dif_neg h, Bool.and_self]

/-- The clause mask of the tests at the seed's filters is the mask of the clause's two-carrier call. -/
theorem clauseMask_carrierFilter (m : Mode) {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)
    (carrier : PcppVar pcpp → Stars.Carrier q) (translation : List ℕ) (i : Fin (2 ^ pcpp.clauseBits))
    (e : I.Seed m q) (x : BitInput q) (a : ℕ) (ha : a ≤ 4) (circuits : Fin a → m.Circuit q) :
    clauseMask pcpp (carrierFilter I m pcpp carrier translation) i e x =
      I.mask ⟨q, m, a, ha, circuits, [carrier (posVar pcpp i 0), carrier (posVar pcpp i 1)], translation⟩ e x := by
  rw [mask_pair]
  rfl

end SeedMasks

end NearCubicWires.WireExponent3_5.Transfer
