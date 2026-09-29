import Proof.Wire_3_5.Recovery.HybridProgTwoPorts
import Proof.Wire_3_5.Recovery.HybridProgRecoveryInput

/-! # The hybrid `E^NP` program: TwoAliases (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramTwoAliases`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: The actual Case2 input aliases are the same retained hierarchy word, canonical description, final address, and original raw R/B recovery fields.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
noncomputable section

theorem recovery_inputs (p : Parameters) (j : Fin 3) :
    recoverySlot p (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree j)=
      prefixSlot p (prefixRecoveryFields p j):=by
  exact (congrArg (lift1 p) (CloseoutCommonPortBank.shared_slot _ _
    (RecoveryBoundedCold.sharedLocal_injective (source p) p.k p.degree) j)).trans
      (recovery_shared_prefix p j)

theorem two_hierarchy_alias (p : Parameters) :
    twoSlot p (twoLocal p 0)=
      recoverySlot p (RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0):=by
  exact (two_inputs p 0).trans (recovery_inputs p 0).symm

theorem two_description_alias (p : Parameters) :
    twoSlot p (twoLocal p 1)=lift1 p (descriptionBank p):=two_inputs p 1
theorem two_address_alias (p : Parameters) :
    twoSlot p (twoLocal p 2)=lift0 p (address0 p):=two_inputs p 2
theorem two_r_alias (p : Parameters) :
    twoSlot p (twoLocal p 3)=lift1 p (scalarBank p 0):=two_inputs p 3
theorem two_b_alias (p : Parameters) :
    twoSlot p (twoLocal p 4)=lift1 p (scalarBank p 2):=two_inputs p 4

end
end NearCubicWires.RepairSource.HybridProgram
