import Lean
import Proof.Wire_3_5.FinalPass.SdW2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SdI1Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4 (the seeds phase), part 50: the internal entry at a star call, read (P3:3044-3048, 3170-3178)

From S4's internal entry `SdEntry2` on the layout `gLay E tw`: the blank streams (`ent_lo`, `ent_hi`, `ent_W`), the
words at a SYM star call (`sym_w8`, `sym_w13`, `sym_ws`, `sym_ns`) and at a THR star call (`thr_w8`, `thr_ws`,
`thr_ns`); the sampled halves decoded (`dl_call`, `dr_call`: `callEqv`'s codes); the numerators within the index
counts (`symNum_le`, `thrNum_le`) and, at every request of the family, **`fpNum_le`**: `fpNum ≤ ptCount·vmax`.

Paper quantity of the main type: the printed numerator (P3:3044-3048) against the number of point evaluations. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 SdEntry2 frontWordsOfW2 s4Core2 symCallOf thrCallOf
  thrWords thrNums)
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decWord digitsOf)

/-! ## The blank streams at the entry -/

section Ent
variable {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} (E : SymPtEval2) {tw : ℕ}
  {r : FReq l F kclk coef A a ha} {W : ℕ} {σ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs)}

theorem ent_lo (h : SdEntry2 l F kclk coef A a ha (gLay E tw) r W σ) (i : Fin (bns E.nw E.nsc + 1))
    (h30 : i.val < 30) (h0 : i.val ≠ 0) : σ.st (fsB i) = [] :=
  h.blank (fsB i)
    (fun k hk => by
      have e := congrArg Fin.val hk
      simp only [gLay, fsB, tW] at e
      omega)
    (fun hk => by
      have e := congrArg Fin.val hk
      simp only [gLay, fsB, tN, bst] at e
      omega)
    (fsB_ne_gD i)

theorem ent_hi (h : SdEntry2 l F kclk coef A a ha (gLay E tw) r W σ) (i : Fin (bns E.nw E.nsc + 1))
    (h47 : 47 + E.nw ≤ i.val) : σ.st (fsB i) = [] :=
  h.blank (fsB i)
    (fun k hk => by
      have e := congrArg Fin.val hk
      simp only [gLay, fsB, tW] at e
      have := k.isLt
      omega)
    (fun hk => by
      have e := congrArg Fin.val hk
      simp only [gLay, fsB, tN, bst] at e
      omega)
    (fsB_ne_gD i)

theorem ent_W (h : SdEntry2 l F kclk coef A a ha (gLay E tw) r W σ) (win wout x : Fin tw) (h1 : x ≠ win)
    (h2 : x ≠ wout) : σ.st (tmW win wout x) = [] :=
  h.blank (tmW win wout x) (fun k => tmW_off win wout x h1 h2 (tW k)) (tmW_off win wout x h1 h2 tN)
    (tmW_ne_gD win wout x)

theorem ent_w (h : SdEntry2 l F kclk coef A a ha (gLay E tw) r W σ) (k : Fin (17 + E.nw)) :
    σ.st (fsB (tW k)) = frontWordsOfW2 (callInputs l F kclk coef A a ha) (gate0 l F).alg E.toWords r.1 k :=
  h.words k

end Ent

/-! ## The words at a star call -/

section Words

end Words

/-! ## The sampled halves, decoded -/

/-! ## The numerators within the index counts -/

/-! ## At a request of the family -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The numerator is at most the number of point evaluations times the largest per-point value.** -/
theorem fpNum_le (r : FReq l F kclk coef A a ha) :
    Seams.fpNum l F kclk coef A a ha r ≤ Seams.ptCount l F kclk coef A a ha r * Seams.vmax l F kclk coef A a ha r := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  cases mode with
  | sym =>
    simp only [Seams.fpNum, Seams.ptCount, Seams.vmax, NumDen.numOf, Seams.ptCountOf, Seams.vmaxOf, dif_pos hs]
    refine (symNum_le _ _ _ _ _ _ _ _).trans (le_of_eq ?_)
    ring
  | thr =>
    simp only [Seams.fpNum, Seams.ptCount, Seams.vmax, NumDen.numOf, Seams.ptCountOf, Seams.vmaxOf, dif_pos hs]
    refine (thrNum_le _ _ _ _ _ _ _ _ _ _).trans (le_of_eq ?_)
    ring

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

end
