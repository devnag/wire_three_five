import Proof.Packets.BudgetRestFree

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## 1. `backCost` at `Rc = 0`, by owner -/

section back
variable {a : DecompositionAlgorithm} {vE vP : Request → Nat}
  (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP) (rq : Request)
  (w q L Mb Ms : Nat)

/-- **`backCost|_{Rc=0}` exactly**: the two unary stages (PM/PG), the two binary counts, the denominator engine, a polynomial rest. -/
theorem backFree_eq :
    Rest.backCost se sp rq 0 w q L Mb Ms =
      (se.cost rq + sp.cost rq) + (CloseoutRowsCountBinary.budget (vE rq) + CloseoutRowsCountBinary.budget (vP rq)) +
        (CompetitorDenominator.budget (natBitLength (vE rq)) w q + 4*(rq.input a).length + 6*w + 2*q +
          2*(if 3 < L then Mb else Ms) + 84) := by
  simp only [Rest.backCost, Rest.stagesCost, Prologue.f6FullCost, Prologue.f6Cost, Rest.slopeCost]
  omega

/-- **`backCost|_{Rc=0}` in the classes** from the stages' and counts' class facts (`BudgetRestParts`, `BudgetCountsAt`) and one
polynomial bound. -/
theorem backFree_inClasses {dP hT hS m L' n qn c2P c2T c2S c3P c3T c3S xC : Nat}
    (hst : InClasses dP hT hS m L' n qn c2P c2T c2S (se.cost rq + sp.cost rq))
    (hcb : InClasses dP hT hS m L' n qn c3P c3T c3S
      (CloseoutRowsCountBinary.budget (vE rq) + CloseoutRowsCountBinary.budget (vP rq)))
    (hpoly : CompetitorDenominator.budget (natBitLength (vE rq)) w q + 4*(rq.input a).length + 6*w + 2*q +
      2*(if 3 < L then Mb else Ms) + 84 ≤ xC*(n+1)^dP) :
    InClasses dP hT hS m L' n qn (c2P + c3P + xC) (c2T + c3T + 0) (c2S + c3S + 0)
      (Rest.backCost se sp rq 0 w q L Mb Ms) := by
  rw [backFree_eq]
  exact (hst.add hcb).add (InClasses.poly hpoly le_rfl)

end back

/-! ## 2. The first seam's fuel -/

section seam

end seam

/-! ## 3. The family entry heads -/

theorem addCases_le {m n c : ℕ} (f : Fin m → ℕ) (g : Fin n → ℕ) (hf : ∀ j, f j ≤ c) (hg : ∀ j, g j ≤ c)
    (i : Fin (m+n)) : Fin.addCases (motive := fun _ => ℕ) f g i ≤ c := by
  induction i using Fin.addCases with
  | left j => rw [Fin.addCases_left]; exact hf j
  | right j => rw [Fin.addCases_right]; exact hg j

/-- **The native family's entry heads are `0` or `1`** (the loader's heads at position `0` with empty output, the repeat counter's
head `1`, the eleven extra tapes' `0`): S's `hfamH` head term is a constant, no class needed. -/
theorem r_inputH_le_one (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B N : ℕ)
    (i : Fin (r_tapes a)) : r_inputH a ds S R B N i ≤ 1 := by
  unfold r_inputH f_entry
  refine addCases_le _ _ (fun j => ?_) (fun _ => Nat.zero_le 1) i
  simp only [RepairSource.VerifierDecoding.RepeatMachine.cfg, controlConfig, TapeEmbedding.config]
  refine addCases_le _ _ (fun j => ?_) (fun _ => le_rfl) j
  simp only [P1TopDownPaidReusable.source, P1TopDownPaidReusable.heads, P1TopDownPaidReusableBody.heads,
    List.take_zero, List.flatMap_nil, List.length_nil]
  refine addCases_le _ _ (fun j => ?_) (fun j => ?_) j
  · simp only [RawRowJoin.heads, List.length_nil]
    refine addCases_le _ _ (fun j => ?_) (fun j => ?_) j
    · exact addCases_le _ _ (fun _ => Nat.zero_le 1) (fun _ => Nat.zero_le 1) j
    · fin_cases j <;> simp
  · fin_cases j <;> simp

/-- **`hfamH` past an onset** (S's `hfamH0`/`hfamH`): the family fuel's class fact alone gives `r_inputH … i + fuel + 1 ≤ Rc`
for every `Rc = Cr·tableClass L hR q` with `Cr ≥ 1`, `hR ≥ c.hT + 2`. -/
theorem hfamH_at (sources : EightSources) (k : ℕ) (c : CostCls) (m L : ℕ) (hm : 2 ≤ m) (hk : c.dP + 1 ≤ k + 2) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ fuel : ℕ, c.In m L n (C10PartsSchedule.widthAt sources k n) fuel →
      ∀ Cr hR : ℕ, 1 ≤ Cr → c.hT + 2 ≤ hR →
        ∀ (a : WilliamsAlgorithm) (ds : List P1TopDownPaidReusable.Datum) (S R B N : ℕ) (i : Fin (r_tapes a)),
          r_inputH a ds S R B N i + fuel + 1 ≤ Cr * tableClass L hR (C10PartsSchedule.widthAt sources k n) := by
  obtain ⟨n0, h0⟩ := hfamH_sat sources k c m L 0 1 hm hk
  refine ⟨n0, fun n hn fuel hf Cr hR hC hTR a ds S R B N i => h0 n hn _ fuel hf ?_ Cr hR hC hTR (by omega)⟩
  have h1 := SourceConstruction.one_le_tableClass L 0 (C10PartsSchedule.widthAt sources k n)
  have h2 := r_inputH_le_one a ds S R B N i
  omega

end
end NearCubicWires.SourceBudget
end

