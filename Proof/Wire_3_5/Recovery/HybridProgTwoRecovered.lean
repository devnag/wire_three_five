import Proof.Wire_3_5.Recovery.HybridProgTwoRecovery
import Proof.Wire_3_5.Recovery.HybridProgRecoveryFresh

/-! # The hybrid `E^NP` program: TwoRecovered (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice, "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on
the source length `N_{a(n)}`" (P3:3758-3759): base's `CloseoutCommonProgram` step `CommonProgramTwoRecovered`, restated over
the hybrid program's `Parameters` (the scan prefix and hybrid Case-2 machine). Base's description: The selected Case2 cold entry is supplied by the actual recovery result, retained final address, and the untouched fresh worker bank.

Paper quantity: the hybrid slice's one ordinary `E^NP` program. -/

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary OrdinaryOracleCompose
set_option autoImplicit false
noncomputable section

private theorem six_heads (f : Fin 6→ℕ) (h : ∀ j,f (twoRecoveryIndices j)=0)
    (h2 : f 2=0) (h5 : f 5=0) : ∀ j,f j=0:=by
  intro j
  fin_cases j
  · exact h 0
  · exact h 1
  · exact h2
  · exact h 2
  · exact h 3
  · exact h5

theorem two_recovered_got (p : Parameters) (bits word description : List Bool)
    (R B padding : ℕ) (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (final : (recovery p).Config)
    (fields : ∀ j,final.tapes (twoRecoveryLocal p j)=twoRecoveryWords word description R B j)
    (heads : ∀ j,final.heads (twoRecoveryLocal p j)=0) (j : Fin 4) :
    (recovered p bits out padding final).tapes (twoSlot p (twoLocal p (twoRecoveryIndices j)))=
        twoRecoveryWords word description R B j ∧
      (recovered p bits out padding final).heads (twoSlot p (twoLocal p (twoRecoveryIndices j)))=0:=by
  refine ⟨?_,?_⟩
  · exact (congrArg (recovered p bits out padding final).tapes (two_recovery_alias p j)).trans
      ((recovered_word p bits out padding final _ (two_recovery_not_query p j)).trans (fields j))
  · exact (congrArg (recovered p bits out padding final).heads (two_recovery_alias p j)).trans
      ((recovered_heads p bits out padding final _).trans (heads j))

theorem two_recovered_words (p : Parameters) (bits word description : List Bool)
    (R B padding : ℕ) (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (final : (recovery p).Config)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits)
    (fields : ∀ j,final.tapes (twoRecoveryLocal p j)=twoRecoveryWords word description R B j)
    (heads : ∀ j,final.heads (twoRecoveryLocal p j)=0) (j : Fin 6) :
    (recovered p bits out padding final).tapes (twoSlot p (twoLocal p j))=
      twoInput p word description (frame bits) R B (twoLocal p j):=by
  have got:=two_recovered_got p bits word description R B padding out final fields heads
  have addr:=recovered_address p bits out padding final ha
  have result:=recovered_output p bits out padding final
  fin_cases j
  · exact (got 0).1.trans (two_recovery_input p word description (frame bits) R B 0).symm
  · exact (got 1).1.trans (two_recovery_input p word description (frame bits) R B 1).symm
  · exact ((congrArg (recovered p bits out padding final).tapes (two_address_alias p)).trans addr.2).trans
      (two_input_fields p word description (frame bits) R B 2).symm
  · exact (got 2).1.trans (two_recovery_input p word description (frame bits) R B 2).symm
  · exact (got 3).1.trans (two_recovery_input p word description (frame bits) R B 3).symm
  · exact ((congrArg (recovered p bits out padding final).tapes (two_output p)).trans result.2).trans
      (two_input_output p word description (frame bits) R B).symm

theorem two_recovered_heads (p : Parameters) (bits word description : List Bool)
    (R B padding : ℕ) (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (final : (recovery p).Config)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits)
    (fields : ∀ j,final.tapes (twoRecoveryLocal p j)=twoRecoveryWords word description R B j)
    (heads : ∀ j,final.heads (twoRecoveryLocal p j)=0) :
    ∀ j,(recovered p bits out padding final).heads (twoSlot p (twoLocal p j))=0:=by
  have got:=two_recovered_got p bits word description R B padding out final fields heads
  have addr:=recovered_address p bits out padding final ha
  have result:=recovered_output p bits out padding final
  exact six_heads (fun j=>(recovered p bits out padding final).heads (twoSlot p (twoLocal p j))) (fun j=>(got j).2)
    ((congrArg (recovered p bits out padding final).heads (two_address_alias p)).trans addr.1)
    ((congrArg (recovered p bits out padding final).heads (two_output p)).trans result.1)

theorem two_recovered_entry (p : Parameters) (bits word description : List Bool)
    (R B padding : ℕ) (out : Fin (prefixProgram p).base.tapeCount→List Bool)
    (final : (recovery p).Config)
    (ha : out ⟨0,(prefixProgram p).base.twoTapes.trans_lt' (by decide)⟩=frame bits)
    (fields : ∀ j,final.tapes (twoRecoveryLocal p j)=twoRecoveryWords word description R B j)
    (heads : ∀ j,final.heads (twoRecoveryLocal p j)=0) :
    let c:=recovered p bits out padding final
    (∀ i,c.tapes (twoSlot p i)=twoInput p word description (frame bits) R B i) ∧
      (∀ i,c.heads (twoSlot p i)=0):=by
  let c:=recovered p bits out padding final
  have local_words:=two_recovered_words p bits word description R B padding out final ha fields heads
  have local_heads:=two_recovered_heads p bits word description R B padding out final ha fields heads
  have boundary (i : Fin (tn p)) : n1 p ≤ ((i.natAdd (n3 p)).castAdd 2).val:=
    (Nat.le_add_right (n1 p) 28).trans
      ((Nat.le_add_right (n2 p) (on p)).trans (Nat.le_add_right (n3 p) i.val))
  refine ⟨two_entry p word description (frame bits) R B c.tapes ?_ ?_,
    two_entry_heads p c.heads ?_ ?_⟩
  · intro j
    exact (congrArg c.tapes (two_inputs p j).symm).trans (local_words j)
  · intro i
    exact (recovered_fresh p bits out padding final _ (boundary i)).2
  · intro j
    exact (congrArg c.heads (two_inputs p j).symm).trans (local_heads j)
  · intro i
    exact (recovered_fresh p bits out padding final _ (boundary i)).1
end
end NearCubicWires.RepairSource.HybridProgram
