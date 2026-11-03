import W3.Aliases
import W3.Proof.Assembly.SelectedRecoveryIntegration
import W3.Joins.Cases
import Proof.CaseAnalysis.Language

/-! # The single canonical language (`languageC`)

The near-cubic-wires paper (three cases) and C.12 (schedule). `language` keeps its name and argument list and is
now three-way `languageC` at this proof's sources (`toCase`), the short PCP `shortPCP` and 𝒱_G (`sv`);
`widthAt` reads `width` (q(N)) instead of the projection PCP's native width. The untainted helpers of the base module
(`paddedUnsigned`, `clauseWidth`, `coreWidth`, `selectedIndex` and its two lemmas) are re-exported unchanged; the old
two-way `core` over the projection PCP is not part of the new proof. -/

set_option autoImplicit false

namespace W3

namespace NearCubicWires.RepairSource.CloseoutLanguage

export _root_.NearCubicWires.RepairSource.CloseoutLanguage (paddedUnsigned clauseWidth coreWidth selectedIndex
  selectedIndex_le selectedIndex_fits)

noncomputable section

end
end NearCubicWires.RepairSource.CloseoutLanguage

end W3
