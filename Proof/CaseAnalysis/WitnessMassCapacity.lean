import Proof.CaseAnalysis.WitnessSumFinish

/-! The reusable Store itself bounds every native tape. No per-iteration
workspace promise is needed after choosing the shared actual capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCapacity
open LocalBitMultitape CompetitorSumFold CompetitorReusableDecision SignedSortKey
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem store_length (B : ℕ) (a : Estimate) (ambient : Fin 94→List Bool)
    (h : Store B a [] ambient) (i : Fin 94) : (ambient i).length≤capacity B+1:=by
  refine Fin.addCases (m:=88) (n:=6) ?_ ?_ i
  · intro j;exact (h.support j).trans (Nat.le_succ _)
  · intro j;fin_cases j
    · change (ambient 88).length≤capacity B+1;rw [h.source];simp
    · change (ambient 89).length≤capacity B+1;rw [h.loaderReset,List.length_replicate];omega
    · change (ambient 90).length≤capacity B+1;rw [h.eraseDriver,List.length_replicate];omega
    · change (ambient 91).length≤capacity B+1;rw [h.eraseReset,List.length_replicate]
    · change (ambient 92).length≤capacity B+1;rw [h.copyCounter,List.length_replicate];omega
    · change (ambient 93).length≤capacity B+1;rw [h.copyReset,List.length_replicate];omega

theorem prepare_length (P B b n d : ℕ) (a : Estimate) (ambient : Fin 94→List Bool)
    (h : Store B a [] ambient) (hcap : capacity B+1≤P) (hb : 2*b+1≤P)
    (i : Fin 103) : (MassPrepare.input ambient (binary b n) (binary b d) i).length≤P:=by
  refine Fin.addCases (m:=94) (n:=9) ?_ ?_ i
  · intro j
    rw [MassPrepare.input,Fin.addCases_left]
    exact (store_length B a ambient h j).trans hcap
  · intro j;fin_cases j
    all_goals first
      | (change (frame (binary b n)).length≤P;simpa only [frame_length,binary_length] using hb)
      | (change (frame (binary b d)).length≤P;simpa only [frame_length,binary_length] using hb)
      | (change 0≤P;omega)

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCapacity
