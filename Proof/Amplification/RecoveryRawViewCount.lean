import Proof.Amplification.RecoveryRawViewCountTapes

/-! The enclosing raw-view body reads its literal count at the actual
retained witness cursor and produces the very padded driver used by the
verified clause controller. Counter erasure is a separate paid predecessor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem count_output (x : State) (word : List Bool) (k n : Nat)
    (hs : x.inner.stream.source=frame word) (hp : x.inner.stream.pos=2*k) :
    RecoveryFocus.config countSlots (x.cfg (0 : Fin 5)).heads (x.cfg (0 : Fin 5)).tapes
      (RecoveryCertificateCount.paddedCfg x.capacity 3 (frame word) (2*k+2*n+2) n x.limit 1)=
        (counted x n).cfg 3 := by
  apply focus_configuration countSlots countSlots_injective
  · rfl
  · intro j; fin_cases j
    · change 2*k+2*n+2=x.inner.stream.pos+2*n+2
      rw [hp]
    · rfl
    · rfl
  · intro j; fin_cases j
    · change ZeroPadding.pad 0 (frame word)=x.inner.stream.source
      rw [ZeroPadding.pad_zero]
      exact hs.symm
    · rfl
    · exact ZeroPadding.pad_zero _
  · intro i hi
    rw [counted_heads]
    exact (Function.update_of_ne (Ne.symm (hi 0)) _ _).symm
  · intro i hi
    rw [counted_tapes]
    exact (Function.update_of_ne (Ne.symm (hi 1)) _ _).symm

theorem counted_valid (x : State) (n : Nat) (hx : x.Valid) (hn : n ≤ x.limit) :
    (counted x n).Valid := ⟨hx.1,hx.2.1,hx.2.2.1,hn,hx.2.2.2.2⟩

end NearCubicWires.RepairOrdinary.RecoveryRawView
