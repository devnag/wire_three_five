import Proof.Circuits.DecompositionSourceFields

/-! Skip native signed fields at the retained source cursor. The existing
natural-field parser reads their actual widths; skipped fields are not copied. -/
namespace NearCubicWires.RepairOrdinary.RowNativeFieldSkip
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming PCPPQueryField
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sign : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,![.right,.stay,.stay]⟩
def machine := Composition.machine sign (PCPPQueryField.machine false)
def cost (z : ℤ) := 2*natBitLength z.natAbs+5
def saved := DecompositionSource.Fields.saved

theorem sign_run (source backing out : List Bool) (pos : ℕ) :
    ∃ r,runFrom sign 1 (store 0 source pos backing out)=some r ∧
      r.final=store 1 source (pos+1) backing out ∧ r.steps=1 := by
  have hs : step sign (store 0 source pos backing out)=some (store 1 source (pos+1) backing out) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

theorem int_run (pre tail backing out : List Bool) (z : ℤ) :
    ∃ r,runFrom machine (cost z)
      (store 0 (pre++intWord z++tail) pre.length backing out)=some r ∧
      r.final=store 5 (pre++intWord z++tail) (pre.length+(intWord z).length)
        (saved z backing) out ∧ r.steps=cost z := by
  let b := decide (z<0)
  let source := pre++intWord z++tail
  obtain ⟨first,hfirst,hff,hfs⟩ := sign_run source backing out pre.length
  obtain ⟨last,hl,hlf,hls⟩ := nat_run false (pre++[b]) tail backing out z.natAbs
  have hsource : (pre++[b])++natWord z.natAbs++tail=source := by
    simp [source,intWord,b,List.append_assoc]
  rw [hsource] at hl hlf
  have hi : PCPPQueryField.cfg 0 source (pre++[b]).length backing 0 out=
      Composition.restart first.final (PCPPQueryField.machine false).start := by
    rw [hff]
    simp [PCPPQueryField.cfg,store,Composition.restart,PCPPQueryField.machine]
  rw [hi] at hl
  have hj := Composition.run_join sign (PCPPQueryField.machine false) 1
    (2*natBitLength z.natAbs+3) _ first last hfirst hl
  have ht : 1+1+(2*natBitLength z.natAbs+3)=cost z := by unfold cost; omega
  rw [ht] at hj
  change runFrom machine (cost z) (store 0 source pre.length backing out)=_ at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig 2 last.final=_
    rw [hlf]
    simp only [selected,Bool.false_eq_true,↓reduceIte,List.append_nil,List.length_append,List.length_singleton]
    have hp : pre.length+1+2*natBitLength z.natAbs+1=pre.length+(intWord z).length := by
      rw [intWord,List.length_cons,DecompositionSource.natWord_length]
      omega
    rw [hp]
    rfl
  · change first.steps+1+last.steps=_
    rw [hfs,hls]
    exact ht

noncomputable def loop := RepeatMachine.machine machine (fun _ _ => true)

end NearCubicWires.RepairOrdinary.RowNativeFieldSkip
