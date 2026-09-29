import Proof.CaseAnalysis.RowsSourceLoad

/-! The actual canonical support becomes the existing native incidence ABI.
Only repeated variables inside one conjunction are collapsed; distinct
monomial occurrences, including equal resulting masks, remain separate. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSourceMeaning
open SupplierPrinter CloseoutRowsSourceDigits CloseoutRowsCacheInput RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem positions_mem (bits : List Bool) (j i : ℕ) :
    i∈RowMaskMeaning.positions j bits ↔
      ∃ k : Fin bits.length,i=j+k.val ∧ bits.get k=true := by
  induction bits generalizing j with
  | nil => simp [RowMaskMeaning.positions]
  | cons b bs ih =>
    have ha (k : ℕ) : j+1+k=j+(k+1) := by omega
    cases b <;> simp [RowMaskMeaning.positions,ih,Fin.exists_fin_succ,ha]

theorem mask_one_mem {B : ℕ} (f : Fin B→Bool) (i : Fin B) :
    i∈RowTupleCommonEquation.one B (List.ofFn f) ↔ f i=true := by
  have hlen : (List.ofFn f).length ≤ B := by simp
  rw [RowTupleCommonEquation.one,dif_pos hlen]
  have hv:=RowMaskMeaning.typed_values B 0 (List.ofFn f) (by simp)
  have he : i∈RowMaskMeaning.typed B 0 (List.ofFn f) (by simp) ↔
      i.val∈RowMaskMeaning.positions 0 (List.ofFn f) := by
    rw [←hv]
    constructor
    · intro hi; exact List.mem_map.mpr ⟨i,hi,rfl⟩
    · intro hi
      obtain ⟨k,hk,hki⟩ := List.mem_map.mp hi
      exact (Fin.ext hki) ▸ hk
  rw [he,positions_mem]
  constructor
  · rintro ⟨k,hk,hf⟩
    have hik : k.val=i.val := by omega
    have he : (⟨k.val,by simpa using k.isLt⟩ : Fin B)=i := Fin.ext hik
    simpa only [List.get_eq_getElem,List.getElem_ofFn,he] using hf
  · intro hf
    refine ⟨⟨i.val,by simp⟩,by simp,?_⟩
    simpa using hf

end NearCubicWires.RepairOrdinary.CloseoutRowsSourceMeaning
