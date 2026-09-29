import Proof.Amplification.RecoveryValuationStreamSemantics
import Proof.PCP.VerifierDecodingRejectingRepeat

/-! The actual bounded valuation-table scan. Every serialized row is read
and compared on the same eight physical tapes; the retained repeat driver
charges all loop transitions and rejects the first truncated row. -/
namespace NearCubicWires.RepairOrdinary.RecoveryValuationTable
open LocalBitMultitape RecoveryValuationStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Cursor where
  data : Data
  rest : List Bool

def Inv (width : Nat) (x : Cursor) : Prop :=
  x.data.width=width ∧ x.data.index.length=width ∧
  x.data.row.length≤2*(width+1)+1 ∧
  ∃ pre,x.data.source=pre++frame x.rest ∧ x.data.pos=pre.length

def advance (x : Cursor) : Cursor :=
  ⟨x.data.done (readKey x.data x.rest) (readValue x.data x.rest),x.rest.drop (x.data.width+1)⟩
def next (x : Cursor) : Bool×Cursor :=
  ((readEntry x.data.width x.rest).isSome,advance x)
noncomputable def source (x : Cursor) := x.data.cfg RecoveryValuationStream.machine.start
def accepted (_ : Fin (Fintype.card (RecoveryCalls.Control sizes))) (scanned : Fin 8→Bool) := scanned 7
noncomputable abbrev machine := RepeatMachine.machine RecoveryValuationStream.machine accepted

theorem next_inv (width : Nat) (x : Cursor) (hx : Inv width x) (ha : (next x).1=true) :
    Inv width (next x).2 := by
  rcases hx with ⟨hw,hi,hb,pre,hs,hp⟩
  have hlong : x.data.width+1≤x.rest.length := by
    simpa only [next,readEntry_isSome,decide_eq_true_eq] using ha
  have hkey : (readKey x.data x.rest).length=x.data.width := by
    simp [readKey,List.length_take,show x.data.width≤x.rest.length by omega]
  refine ⟨hw,hi,?_,pre++Streaming.marks (x.rest.take (x.data.width+1)),?_,?_⟩
  · change (frame (readKey x.data x.rest++[readValue x.data x.rest])).length≤_
    simp [frame_length,hkey,hw]
  · change x.data.source=(pre++Streaming.marks (x.rest.take (x.data.width+1)))++frame (x.rest.drop (x.data.width+1))
    rw [List.append_assoc,←Streaming.frame_append,List.take_append_drop]
    exact hs
  · change x.data.pos+2*(readKey x.data x.rest++[readValue x.data x.rest]).length=_
    simp [hp,hkey,Streaming.marks_length,List.length_take,Nat.min_eq_left hlong]

end NearCubicWires.RepairOrdinary.RecoveryValuationTable
