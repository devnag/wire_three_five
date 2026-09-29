import Proof.Wire_3_5.Recovery.HybridProgPorts

/-! # The hybrid `E^NP` program: OnePorts (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramOnePorts`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: The existing Case1 input, address, query and Boolean output are four distinct physical ports. The common layout shares exactly those four.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
noncomputable section

private theorem four_injective {n : ℕ} (f : Fin 4→Fin n) (B Q : ℕ)
    (hq : 0<Q) (hb : Q<B)
    (hf : ∀ i,(f i).val=(![0,B+16,Q,B+43] : Fin 4→ℕ) i) : Function.Injective f:=by
  intro i j he
  have hv : (![0,B+16,Q,B+43] : Fin 4→ℕ) i=(![0,B+16,Q,B+43] : Fin 4→ℕ) j:=
    (hf i).symm.trans ((congrArg Fin.val he).trans (hf j))
  fin_cases i <;>fin_cases j <;>simp at hv ⊢ <;>omega

theorem one_local_injective (p : Parameters) : Function.Injective (oneLocal p):=by
  let B:=RecoveryCaseOnePaddedBit.base (source p) (amp p) p.k
  have hq:0<(one p).queryTape.val:=by
    have h:=(one p).queryFresh
    omega
  have hb:(one p).queryTape.val<B:=
    (RecoveryCaseOneHierarchy.ports (source p) (amp p) p.k).queryTape.isLt
  exact four_injective (oneLocal p) B (one p).queryTape.val hq hb
    (by intro i;fin_cases i <;>rfl)

theorem one_query (p : Parameters) : oneSlot p (one p).queryTape=(ports p).queryTape:=by
  change lift3 p (oneBank p (oneLocal p 2))=_
  rw [oneBank,CloseoutCommonPortBank.shared_slot _ _ (one_local_injective p)]
  rfl

theorem one_output (p : Parameters) : oneSlot p (one p).base.outputTape=(ports p).outputTape:=by
  change lift3 p (oneBank p (oneLocal p 3))=_
  rw [oneBank,CloseoutCommonPortBank.shared_slot _ _ (one_local_injective p)]
  rfl

theorem one_word (p : Parameters) : oneSlot p (oneLocal p 0)=lift0 p (word0 p):=by
  rw [oneSlot,oneBank,CloseoutCommonPortBank.shared_slot _ _ (one_local_injective p)]
  rfl

theorem one_address (p : Parameters) : oneSlot p (oneLocal p 1)=lift0 p (address0 p):=by
  rw [oneSlot,oneBank,CloseoutCommonPortBank.shared_slot _ _ (one_local_injective p)]
  rfl

end
end NearCubicWires.RepairSource.HybridProgram
