import Proof.Supplier.RowBinLiftWidth

/-! A safe power radix gives the same occurrence conjunctions as canonical
stacking. Its numeric coefficients are deliberately not identified with the
canonical radix coefficients. This is the semantic target of binary blocks. -/
namespace NearCubicWires.RepairOrdinary.RowPowerBinLift
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def stack {α : Type} (w : ℕ) (es : List (LabelledEquation α)) :=
  stackEquations ((2 : ℤ)^w) es

theorem stack_width {α : Type} [Fintype α] (w : ℕ)
    (es : List (LabelledEquation α))
    (hw : ∀ e ∈ es,equationMagnitudeBound e<2^w) :
    equationMagnitudeBound (stack w es)<2^(w*es.length) := by
  have h := equationMagnitudeBound_stackEquations_le ((2 : ℤ)^w) es
  have hb : ((2 : ℤ)^w).natAbs=2^w := by simp
  rw [hb] at h
  have horner := RowBinLift.horner_lt_pow (2^w) (by positivity)
    (es.map equationMagnitudeBound) (by
      intro x hx
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
      exact hw e he)
  simpa only [stack,List.length_map,←pow_mul] using h.trans_lt horner

theorem term_members {α : Type} (Q : ℕ) (ms : List (List α))
    (t : ℤ × List α) (ht : t ∈ terms Q ms) (e : α) (he : e ∈ t.2) :
    e ∈ ms.flatten := by
  obtain ⟨j,_,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨selected,hs,rfl⟩ := List.mem_map.mp ht
  obtain ⟨m,hm,he⟩ := List.mem_flatten.mp he
  exact List.mem_flatten.mpr ⟨m,(List.mem_sublistsLen.mp hs).1.subset hm,he⟩

def cuts {l r : ℕ} (w Q : ℕ) (ms : List (List (Equation l r))) : List Cut :=
  (terms Q ms).map fun t => split t.1 (stack w t.2)

theorem cuts_length {l r : ℕ} (w Q : ℕ) (ms : List (List (Equation l r))) :
    (cuts w Q ms).length=(RowBinLift.cuts Q ms).length := by
  simp [cuts,RowBinLift.cuts]

def batch {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r)))) :=
  rows.flatMap (cuts w Q)

theorem batch_length {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r)))) :
    (batch w Q rows).length=(RowBinLift.batch Q rows).length := by
  simp only [batch,RowBinLift.batch,List.length_flatMap,cuts_length]

end NearCubicWires.RepairOrdinary.RowPowerBinLift
