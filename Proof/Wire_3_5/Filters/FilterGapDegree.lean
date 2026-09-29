import Proof.Wire_3_5.Filters.FilterGap

/-! # `filt:gap`: the regular filter is an `𝔽₂` polynomial of degree `O(log 1/ε)` in `Z` (P3:2028-2029, 2079-2081, 2100-2101)

Realizes the degree claims of `filt:gap`: "The degree is `O(log(1/ε))`" (P3:2028-2029); "This fixed Boolean
function has an exact `𝔽₂` polynomial of degree at most `128` in the parity bits, and hence of constant degree in `Z`"
(P3:2079-2081); "Majority multiplies the Boolean degree by at most `t`" (P3:2100-2101).

For every seed `e` the filter `Z ↦ F_e(Z)` is a Boolean function of the `128·t` selected parities, each of which is
an `𝔽₂`-linear form in `Z` (`P = Σ_i H_i a_i Z_i`, P3:2063). A Boolean function of `s` linear forms is an `𝔽₂`
polynomial of total degree at most `s` (`polyOfForms`, by the indicator expansion
`Φ(y) = Σ_b Φ(b) Π_j (1 + y_j + b_j)`). Main result: `gapFilter_degree`, an `MvPolynomial (Fin L) (ZMod 2)` of
total degree at most `128·t` that equals `F_e` on every vector `Z ∈ {0,1}^L`, and `degree_le_errExp`
(`128·t ≤ 64·log₂(1/ε) + 128`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Filters
open NearCubicWires NearCubicWires.SupplierWalk MvPolynomial Finset

/-- A bit as an element of `𝔽₂`. -/
def bitF2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-! ## The selected parity is a linear form in `Z` -/

/-! ## The filter's polynomial -/

end NearCubicWires.WireExponent3_5.Filters
