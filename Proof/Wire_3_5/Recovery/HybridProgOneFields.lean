import Proof.Wire_3_5.Recovery.HybridProgOneInput

/-! # The hybrid `E^NP` program: OneFields (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramOneFields`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: The four shared Case1 words are the original hierarchy input, final address, physically cleared query and initially empty common output.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
noncomputable section

theorem one_cold_fields (p : Parameters) (word bits : List Bool) (j : Fin 4) :
    oneColdInput p word bits (oneLocal p j)=(![word,frame bits,[],[]] : Fin 4→List Bool) j:=by
  fin_cases j
  · rw [oneColdInput,RecoveryCaseOnePaddedBit.input_lookup]
    rfl
  · rw [oneColdInput,RecoveryCaseOnePaddedBit.input_lookup]
    change (if RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+16=0 then word else
      if RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+16=
        RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+16 then frame bits else [])=frame bits
    rw [if_neg (by omega),if_pos rfl]
  · exact one_query_empty p word bits
  · rw [oneColdInput,RecoveryCaseOnePaddedBit.input_lookup]
    change (if RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+43=0 then word else
      if RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+43=
        RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k+16 then frame bits else [])=[]
    rw [if_neg (by omega),if_neg (by omega)]

theorem one_nonquery (p : Parameters) (j : Fin 4) (hj : j≠2) : oneLocal p j≠(one p).queryTape:=
  fun he=>hj (one_local_injective p he)

theorem one_input_fields (p : Parameters) (word bits : List Bool) (capacity : ℕ) (j : Fin 4) :
    oneInput p word bits capacity (oneLocal p j)=
      (![word,frame bits,List.replicate capacity false,[]] : Fin 4→List Bool) j:=by
  fin_cases j
  · exact (Function.update_of_ne (one_nonquery p 0 (by decide)) _ _).trans (one_cold_fields p word bits 0)
  · exact (Function.update_of_ne (one_nonquery p 1 (by decide)) _ _).trans (one_cold_fields p word bits 1)
  · exact Function.update_self _ _ _
  · exact (Function.update_of_ne (one_nonquery p 3 (by decide)) _ _).trans (one_cold_fields p word bits 3)

theorem one_entry (p : Parameters) (word bits : List Bool) (capacity : ℕ)
    (A : Fin (tapes p)→List Bool)
    (fields : ∀ j,A (lift3 p ((oneShared p j).castAdd (on p)))=
      oneInput p word bits capacity (oneLocal p j))
    (fresh : ∀ i : Fin (on p),A (lift3 p (i.natAdd (n2 p)))=[]) (i : Fin (on p)) :
    A (oneSlot p i)=oneInput p word bits capacity i:=by
  exact CloseoutCommonPortBank.input_at (oneLocal p) (oneShared p)
    (fun z=>A (lift3 p z)) (oneInput p word bits capacity) fields fresh
    (one_input_empty p word bits capacity) i

theorem one_entry_heads (p : Parameters) (H : Fin (tapes p)→ℕ)
    (fields : ∀ j,H (lift3 p ((oneShared p j).castAdd (on p)))=0)
    (fresh : ∀ i : Fin (on p),H (lift3 p (i.natAdd (n2 p)))=0) (i : Fin (on p)) :
    H (oneSlot p i)=0:=by
  cases hp : RecoveryFocus.pick (oneLocal p) i with
  | none =>simp only [oneSlot,oneBank,CloseoutCommonPortBank.slot,hp,fresh]
  | some j =>simpa only [oneSlot,oneBank,CloseoutCommonPortBank.slot,hp] using fields j

end
end NearCubicWires.RepairSource.HybridProgram
