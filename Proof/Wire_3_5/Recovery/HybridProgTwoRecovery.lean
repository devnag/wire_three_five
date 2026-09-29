import Proof.Wire_3_5.Recovery.HybridProgTwoInput

/-! # The hybrid `E^NP` program: TwoRecovery (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramTwoRecovery`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: Four Case2 fields come directly from the same recovery result. The remaining address and initially empty output are retained ambient words.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
noncomputable section

def twoRecoveryLocal (p : Parameters) : Fin 4→Fin (rn p):=
  ![RecoveryBoundedCold.sharedLocal (source p) p.k p.degree 0,
    (787 : Fin 790).natAdd (RecoveryBoundedCold.oldTapes (source p) p.k p.degree),
    (RecoveryBoundedColdSourceGraph.graphSlots (source p) p.k p.degree ((0 : Fin 5).natAdd 1659)).castAdd 790,
    (RecoveryBoundedColdSourceGraph.graphSlots (source p) p.k p.degree ((2 : Fin 5).natAdd 1659)).castAdd 790]
def twoRecoveryIndices : Fin 4→Fin 6:=![0,1,3,4]
def twoRecoveryWords (word description : List Bool) (R B : ℕ) : Fin 4→List Bool:=
  ![word,description,List.replicate R true,List.replicate B true]

theorem two_recovery_alias (p : Parameters) (j : Fin 4) :
    twoSlot p (twoLocal p (twoRecoveryIndices j))=recoverySlot p (twoRecoveryLocal p j):=by
  fin_cases j
  · exact two_hierarchy_alias p
  · exact two_description_alias p
  · exact two_r_alias p
  · exact two_b_alias p

theorem two_recovery_not_query (p : Parameters) (j : Fin 4) :
    twoRecoveryLocal p j≠RecoveryBoundedCold.queryPort (source p) p.k p.degree:=by
  have hG:=recovery_old_large p
  intro he
  fin_cases j
  · exact (by decide : (0 : Fin 3)≠2)
      (RecoveryBoundedCold.sharedLocal_injective (source p) p.k p.degree he)
  · have hv:=congrArg Fin.val he
    change RecoveryBoundedCold.oldTapes (source p) p.k p.degree+787=
      RecoveryBoundedCold.oldTapes (source p) p.k p.degree+356 at hv
    omega
  · have hv:=congrArg Fin.val he
    change 1659=RecoveryBoundedCold.oldTapes (source p) p.k p.degree+356 at hv
    omega
  · have hv:=congrArg Fin.val he
    change 1661=RecoveryBoundedCold.oldTapes (source p) p.k p.degree+356 at hv
    omega

theorem two_recovery_input (p : Parameters) (word description address : List Bool) (R B : ℕ) (j : Fin 4) :
    twoInput p word description address R B (twoLocal p (twoRecoveryIndices j))=
      twoRecoveryWords word description R B j:=by
  fin_cases j
  · exact two_input_fields p word description address R B 0
  · exact two_input_fields p word description address R B 1
  · exact two_input_fields p word description address R B 3
  · exact two_input_fields p word description address R B 4

end
end NearCubicWires.RepairSource.HybridProgram
