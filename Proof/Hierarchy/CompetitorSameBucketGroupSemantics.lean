import Proof.Hierarchy.CompetitorSameBucketKeys

/-! Literal signed-key grouping domain. Natural positive and negative totals
remain separate until the existing modular table consumer. A cell is keyed
by BOTH occurrence IDs; zero records provide dense row-major coverage. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSameBucketGroup
open MatrixScoreBatch SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Entry where
  coefficient : ℤ
  row : ℕ
  rightTaggedID : ℕ
  deriving DecidableEq

def Entry.record (p m : ℕ) (e : Entry) : StablePartition.Record :=
  CompetitorSameBucketKeys.key p m e.coefficient e.row e.rightTaggedID
def Entry.ids (m : ℕ) (e : Entry) : List Bool :=
  binary m e.rightTaggedID++binary m e.row
def records (p m : ℕ) (es : List Entry) := es.map (Entry.record p m)
def stream (p m : ℕ) (es : List Entry) := StablePartition.stream (records p m es)
def positive (es : List Entry) : ℕ := (es.map (fun e => e.coefficient.toNat)).sum
def negative (es : List Entry) : ℕ := (es.map (fun e => (-e.coefficient).toNat)).sum
def atCell (row rightTaggedID : ℕ) (es : List Entry) : List Entry :=
  es.filter (fun e => decide (e.row=row ∧ e.rightTaggedID=rightTaggedID))
def cell (row rightTaggedID : ℕ) (es : List Entry) : CompetitorPlaneStream.Cell :=
  ⟨0,positive (atCell row rightTaggedID es),negative (atCell row rightTaggedID es)⟩
def cells (u : ℕ) (es : List Entry) : List CompetitorPlaneStream.Cell :=
  (List.finRange u).flatMap (fun row => (List.finRange u).map (fun col => cell row.val (u+col.val) es))
def dense (w u : ℕ) (es : List Entry) : List Bool := CompetitorPlaneStream.oldWords w (cells u es)

@[simp] theorem ids_length (m : ℕ) (e : Entry) : (e.ids m).length=2*m := by
  simp [Entry.ids,two_mul]

theorem ids_eq_iff (m : ℕ) (a b : Entry)
    (ha : a.row<2^m) (har : a.rightTaggedID<2^m)
    (hb : b.row<2^m) (hbr : b.rightTaggedID<2^m) :
    a.ids m=b.ids m ↔ a.row=b.row ∧ a.rightTaggedID=b.rightTaggedID := by
  constructor
  · intro h
    obtain ⟨hr,hl⟩ := List.append_inj h (by simp : (binary m a.rightTaggedID).length=(binary m b.rightTaggedID).length)
    have hvrow := congrArg value hl
    have hvright := congrArg value hr
    rw [binary_value _ _ ha,binary_value _ _ hb] at hvrow
    rw [binary_value _ _ har,binary_value _ _ hbr] at hvright
    exact ⟨hvrow,hvright⟩
  · rintro ⟨hr,hc⟩
    simp only [Entry.ids,hr,hc]

theorem cell_order (p m : ℕ) (a b : Entry)
    (ha : a.row<2^m) (har : a.rightTaggedID<2^m)
    (hb : b.row<2^m) (hbr : b.rightTaggedID<2^m)
    (h : value (word (a.record p m))≤value (word (b.record p m))) :
    a.row<b.row ∨ a.row=b.row ∧ a.rightTaggedID≤b.rightTaggedID :=
  CompetitorSameBucketKeys.key_order p m a.coefficient b.coefficient a.row a.rightTaggedID
    b.row b.rightTaggedID ha har hb hbr h

@[simp] theorem positive_nil : positive []=0 := rfl
@[simp] theorem negative_nil : negative []=0 := rfl
@[simp] theorem positive_cons (e : Entry) (es : List Entry) :
    positive (e::es)=e.coefficient.toNat+positive es := by simp [positive]
@[simp] theorem negative_cons (e : Entry) (es : List Entry) :
    negative (e::es)=(-e.coefficient).toNat+negative es := by simp [negative]
theorem positive_append (xs ys : List Entry) : positive (xs++ys)=positive xs+positive ys := by
  simp [positive]
theorem negative_append (xs ys : List Entry) : negative (xs++ys)=negative xs+negative ys := by
  simp [negative]


end NearCubicWires.RepairOrdinary.CompetitorSameBucketGroup
