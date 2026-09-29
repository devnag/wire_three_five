import Proof.MachineModel.OrdinaryWitnessCounterAdvance

/-! One streamed witness bit followed by the paid small-counter check.
Only local scalar tapes rewind; source and output advance by two positions. -/
namespace NearCubicWires.RepairOrdinary.WitnessPrefixBody
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def config {s : ℕ} (state : Fin s) (w counter bound cap : ℕ) (flag : Bool)
    (source out : List Bool) (cursor : ℕ) : Configuration 6 s :=
  TapeEmbedding.config (![cursor,out.length] : Fin 2 → ℕ) (![source,out] : Fin 2 → List Bool)
    (WitnessCounterCheck.config state w counter bound cap flag)
def check : Machine 6 12 := TapeEmbedding.machine 2 WitnessCounterAdvance.machine

theorem check_run (w counter bound cap : ℕ) (source out : List Bool) (cursor : ℕ)
    (hn : counter+1<2^w) (hb : bound<2^w) (hcap : 2*w+1≤cap) :
    ∃ r : ExecutionReceipt 6 12,
      runFrom check (8*w+7) (config check.start w counter bound cap false source out cursor) = some r ∧
      r.final = config 11 w (counter+1) bound cap (decide (counter+1≤bound)) source out cursor := by
  obtain ⟨base,hr,hf⟩ := WitnessCounterAdvance.check_run w counter bound cap hn hb hcap
  have he := TapeEmbedding.run_embed WitnessCounterAdvance.machine (![cursor,out.length] : Fin 2 → ℕ)
    (![source,out] : Fin 2 → List Bool) _ _ base hr
  refine ⟨TapeEmbedding.receipt (![cursor,out.length] : Fin 2 → ℕ)
    (![source,out] : Fin 2 → List Bool) base,he,?_⟩
  simp only [TapeEmbedding.receipt,hf]
  rfl

end NearCubicWires.RepairOrdinary.WitnessPrefixBody
