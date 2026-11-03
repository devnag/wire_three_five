import Proof.Assembly.FixedCore
import Proof.CaseAnalysis.FinalPrinterMonomials

/-! Boolean squarefree normalization used by the fixed packet compiler.
All evaluation statements hold on every Boolean assignment. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 120000
set_option linter.unusedVariables false

open NearCubicWires.SupplierPrinter
open scoped BigOperators
namespace PCJ9eff70d512234a4c_Fixed.Ring

variable {α : Type}

@[simp] theorem canon_mem [LinearOrder α] {m : List α} {x : α} :
    x ∈ canon m ↔ x ∈ m := by
  simp [canon]

theorem canon_pairwise [LinearOrder α] (m : List α) : (canon m).Pairwise (· < ·) := by
  have hn : (canon m).Nodup := List.nodup_dedup _
  have hs : (canon m).Pairwise (· ≤ ·) :=
    (List.pairwise_insertionSort (· ≤ ·) m).sublist (List.dedup_sublist _)
  exact (hs.and hn).imp (fun h => lt_of_le_of_ne h.1 h.2)

theorem mem_toggle [DecidableEq α] {m n : List α} {P : Poly α}
    (h : n ∈ toggle m P) : n = m ∨ n ∈ P := by
  unfold toggle at h
  split at h
  · exact Or.inr (List.mem_of_mem_erase h)
  · simpa only [List.mem_cons] using h

theorem fold_toggle_property [DecidableEq α] (T : List α → Prop)
    (f : List α → List α) (Q P : Poly α)
    (hP : ∀ m ∈ P, T m) (hQ : ∀ m ∈ Q, T (f m)) :
    ∀ m ∈ Q.foldl (fun acc n => toggle (f n) acc) P, T m := by
  induction Q generalizing P with
  | nil => exact hP
  | cons n Q ih =>
    apply ih
    · intro m hm
      rcases mem_toggle hm with rfl | hm
      · exact hQ n (by simp)
      · exact hP m hm
    · intro m hm
      exact hQ m (by simp [hm])

theorem normal_toggle [LinearOrder α] {m : List α} {P : Poly α}
    (hm : m.Pairwise (· < ·)) (hP : Normal P) : Normal (toggle m P) := by
  unfold toggle
  split
  · refine ⟨hP.1.erase _, fun n hn => hP.2 n (List.mem_of_mem_erase hn)⟩
  · refine ⟨List.nodup_cons.mpr ⟨by assumption, hP.1⟩, ?_⟩
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hm
    · exact hP.2 n hn

theorem normal_fold [LinearOrder α] (f : List α → List α) (P Q : Poly α)
    (hP : Normal P) (hQ : ∀ m ∈ Q, (f m).Pairwise (· < ·)) :
    Normal (Q.foldl (fun acc m => toggle (f m) acc) P) := by
  induction Q generalizing P with
  | nil => exact hP
  | cons m Q ih =>
    apply ih _ (normal_toggle (hQ m (by simp)) hP)
    intro n hn
    exact hQ n (by simp [hn])

theorem normal_norm [LinearOrder α] (P : Poly α) : Normal (norm P) := by
  apply normal_fold canon [] P
  · simp [Normal]
  · intro m hm
    exact canon_pairwise m

theorem normal_add [LinearOrder α] {P Q : Poly α}
    (hP : Normal P) (hQ : Normal Q) : Normal (add P Q) :=
  normal_fold id P Q hP hQ.2

theorem support_norm [LinearOrder α] (S : Finset α) (P : Poly α)
    (hP : ∀ m ∈ P, ∀ x ∈ m, x ∈ S) :
    ∀ m ∈ norm P, ∀ x ∈ m, x ∈ S := by
  apply fold_toggle_property (fun m => ∀ x ∈ m, x ∈ S) canon P []
  · simp
  · intro m hm x hx
    exact hP m hm x (canon_mem.mp hx)

end PCJ9eff70d512234a4c_Fixed.Ring
