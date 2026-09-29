import Mathlib
import Proof.Wire_3_5.Foundations.MaskedExpectation

/-!
# S3: k-wise independence and moments (statements)

Consumers: `list:base` (pairwise, P3:1392-1402), `filt:gap` (pairwise inclusion + trace parity,
P3:2036-2062), `filt:majorant` (`2t`-wise labels, scalar moment, P3:2150-2177), `samp:seed`
(`2h`-wise positions, P3:2932-2948).  Finite uniform spaces, counting form: no measure theory.
Statements are `Prop` definitions (no proofs yet); the few cheap facts are proved.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Shared

/-- `t`-wise independent uniform labels, counting form: every set of at most `t` labels sees the
uniform product law (P3:2152-2154 "their field values … are 2t-wise independent"; P3:2935-2937). -/
def KWiseUniform {S L V : Type} [Fintype S] [Fintype V] [DecidableEq V] (t : ℕ) (f : S → L → V) : Prop :=
  ∀ ls : Finset L, ls.card ≤ t → ∀ val : L → V,
    (Finset.univ.filter fun s => ∀ l ∈ ls, f s l = val l).card * Fintype.card V ^ ls.card = Fintype.card S

/-- A function of the labels that reads only the labels in `ls` (P3:2176-2177 "Expanding a 2t-th power
uses at most 2t distinct labels"; P3:2945-2948). -/
def ReadsOnly {L V : Type} (ls : Finset L) (g : (L → V) → ℝ) : Prop :=
  ∀ w w' : L → V, (∀ l ∈ ls, w l = w' l) → g w = g w'

/-- S3.2, polynomial evaluation (Carter–Wegman tradition, "verified here", P3:2929-2937): over a finite
field, a uniformly random polynomial of degree `< t` evaluated at distinct labels is `t`-wise uniform. -/
def PolyEvalKWise : Prop :=
  ∀ {K L : Type} [Field K] [Fintype K] [DecidableEq K] (t : ℕ) (label : L → K),
    Function.Injective label →
    KWiseUniform t (fun (c : Fin t → K) (l : L) => ∑ i : Fin t, c i * label l ^ (i : ℕ))

/-- S3.3, projection (P3:2935-2937 "project each value to k binary coordinates"; P3:2155-2156): composing
with a surjective additive map preserves `t`-wise uniformity. -/
def ProjectKWise : Prop :=
  ∀ {S L V W : Type} [Fintype S] [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    [AddCommGroup V] [AddCommGroup W] (t : ℕ) (f : S → L → V) (π : V →+ W),
    Function.Surjective π → KWiseUniform t f → KWiseUniform t (fun s l => π (f s l))

/-- The trivial SAT witness for `KWiseUniform`: independent labels (`P9`). Statement only. -/
def IdentityKWise : Prop :=
  ∀ {L V : Type} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V] (t : ℕ),
    KWiseUniform t (fun (w : L → V) (l : L) => w l)

end NearCubicWires.WireExponent3_5.Shared
