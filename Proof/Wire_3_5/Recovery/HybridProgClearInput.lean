import Proof.Wire_3_5.Recovery.HybridProgClearPorts

/-! # The hybrid `E^NP` program: ClearInput (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramClearInput`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: Literal two-field input and fresh work of the paid common query clear.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
noncomputable section

theorem clear_inputs (p : Parameters) (j : Fin 2) :
    clearSlot p (clearLocal j)=lift2 p ((clearShared p j).castAdd 28):=
  congrArg (lift2 p) (CloseoutCommonPortBank.shared_slot _ _ clear_local_injective j)

theorem clear_input_fields (bits query : List Bool) (j : Fin 2) :
    CloseoutCommonQueryClear.input bits query (clearLocal j)=(![frame bits,query] : Fin 2→List Bool) j:=by
  fin_cases j <;>rfl

theorem clear_input_empty (bits query : List Bool) (i : Fin 28) (hi : ∀ j,clearLocal j≠i) :
    CloseoutCommonQueryClear.input bits query i=[]:=by
  fin_cases i
  all_goals first | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl) | rfl

theorem clear_entry (p : Parameters) (bits query : List Bool)
    (A : Fin (tapes p)→List Bool)
    (fields : ∀ j,A (lift2 p ((clearShared p j).castAdd 28))=
      CloseoutCommonQueryClear.input bits query (clearLocal j))
    (fresh : ∀ i : Fin 28,A (lift2 p (i.natAdd (n1 p)))=[]) (i : Fin 28) :
    A (clearSlot p i)=CloseoutCommonQueryClear.input bits query i:=
  CloseoutCommonPortBank.input_at clearLocal (clearShared p) (fun z=>A (lift2 p z))
    (CloseoutCommonQueryClear.input bits query) fields fresh (clear_input_empty bits query) i

theorem clear_entry_heads (p : Parameters) (H : Fin (tapes p)→ℕ)
    (fields : ∀ j,H (lift2 p ((clearShared p j).castAdd 28))=0)
    (fresh : ∀ i : Fin 28,H (lift2 p (i.natAdd (n1 p)))=0) (i : Fin 28) : H (clearSlot p i)=0:=by
  cases hp : RecoveryFocus.pick clearLocal i with
  | none =>simp only [clearSlot,clearBank,CloseoutCommonPortBank.slot,hp,fresh]
  | some j =>simpa only [clearSlot,clearBank,CloseoutCommonPortBank.slot,hp] using fields j

end
end NearCubicWires.RepairSource.HybridProgram
