import Proof.Wire_3_5.Selection.ScanW

/-! # C1.3: the `<`-join in the word layer, assembled (P3:1345-1356)

Paper: "For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities [...] constant-
dimensional dominance counting [...] Coordinate-compress all values, sweep the first coordinate in order [...] At ties
order updates before or after queries according to the chosen weak inequality" (P3:1345-1355). **`joinW`** sorts the
key stream of the tagged keys (`sortW`) and sweeps it once (`scanW`); **`joinW_spec : JoinSpec …`** (from the
interface's `joinSpec_of`, the sweep's math `scanJoin`, `sortW_spec` and `scanW_spec`): from any arrangement `l` of
`A.map tagA ++ B.map tagB` on `S`, the total `TOT` gains `joinLt A B`. Paper quantity: the dominance count
`joinLt A B`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- A sort spec holds for any larger list of zero registers. -/
theorem SortSpec.widen {cap W : ℕ} {P : WM ns nr} {S S' : Fin (ns + 1)} {regs regs' : List (Fin nr)}
    {cost : ℕ → ℕ → ℕ} (h : SortSpec cap W P S S' regs cost) (hsub : ∀ r ∈ regs, r ∈ regs') :
    SortSpec cap W P S S' regs' cost := by
  intro σ l hW hl hS hSh hS' hS'h hr hcap
  exact h σ l hW hl hS hSh hS' hS'h (fun r hr' => hr r (hsub r hr')) hcap

/-- A sweep spec holds for any larger list of zero registers. -/
theorem ScanSpec.widen {cap W : ℕ} {P : WM ns nr} {S CNT TOT : Fin (ns + 1)} {regs regs' : List (Fin nr)}
    {cost : ℕ → ℕ → ℕ} (h : ScanSpec cap W P S CNT TOT regs cost) (hsub : ∀ r ∈ regs, r ∈ regs') :
    ScanSpec cap W P S CNT TOT regs' cost := by
  intro σ l t0 hW hl hS hSh hC hT hc ht hr hcap
  exact h σ l t0 hW hl hS hSh hC hT hc ht (fun r hr' => hr r (hsub r hr')) hcap

/-- **The join-accumulate**: sort, then sweep. -/
def joinW (S S' CNT TOT : Fin (ns + 1)) (CA CB K C F R G : Fin nr) : WM ns nr :=
  .seq (sortW S S' CA CB K) (scanW S CNT TOT C F R G)

/-- The join's cost. -/
def joinCost (W m : ℕ) : ℕ := sortCost W m + 1 + scanCost W m

/-- **`joinW` meets `JoinSpec`.** -/
theorem joinW_spec (cap W : ℕ) {S S' CNT TOT : Fin (ns + 1)} {CA CB K C F R G : Fin nr}
    (hSS' : S ≠ S') (hSC : S ≠ CNT) (hST : S ≠ TOT) (hS'C : S' ≠ CNT) (hS'T : S' ≠ TOT) (hCT : CNT ≠ TOT)
    (hAB : CA ≠ CB) (hKA : K ≠ CA) (hKB : K ≠ CB)
    (hCF : C ≠ F) (hCR : C ≠ R) (hCG : C ≠ G) (hFR : F ≠ R) (hFG : F ≠ G) (hRG : R ≠ G) :
    JoinSpec cap W (joinW S S' CNT TOT CA CB K C F R G) S S' CNT TOT [CA, CB, K, C, F, R, G] joinCost :=
  joinSpec_of scanJoin
    ((sortW_spec cap W hSS' hAB hKA hKB).widen (fun r hr => by simp at hr ⊢; tauto))
    ((scanW_spec cap W hSC hST hCT hCF hCR hCG hFR hFG hRG).widen (fun r hr => by simp at hr ⊢; tauto))
    hSS' hSC hST hS'C hS'T

end NearCubicWires.WireExponent3_5.SelectionMachine.Sort
