import Proof.Wire_3_5.UnionMachine.SampLoop

/-! # C6 tail, item 2 (part 5): the sample expansion's word program

From the entry streams (`σE`: the framed seed bits, `1^{kh}`, `1^Q`, `1^ℓ`, the modulus word; every other stream blank,
every head and register `0`), the word program `mainW` writes the zero words (`X`, `ACC`, `NEW`, `ST`), the seed's
coefficient records (`SampSeed.seed_spec`), and then per label `j < Q` the generator's value and its pair words
(`SampLoop.loop_spec`). **`main_spec`**: the output stream ends as the final pass's sample word of the seed's positions,
`sampleWord kh (seedPairs P s)` (`SampMath.sampleWord_eq`).

Paper quantity of the main type: the sample positions `posC P (bitsNum s) j`, `j < Q`, printed (P3:2932-2937,
3044-3053). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SampRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.SampSeed
open NearCubicWires.WireExponent3_5.UnionMachine.SampLoop

variable (cap : ℕ)

/-- The expansion's entry state. -/
def σE (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) : WState 10 16 :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame (List.ofFn s) else if i.val = 1 then List.replicate P.kh true
    else if i.val = 2 then List.replicate P.Q true else if i.val = 3 then List.replicate P.ell true
    else if i.val = 4 then frame (binary P.ell P.modulus) else [], fun _ => 0, false⟩

section Entry
variable (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool)

theorem σE_st3 : (σE P s).st 3 = List.replicate P.ell true := rfl
theorem σE_blank (i : Fin 11) (hi : 5 ≤ i.val) : (σE P s).st i = [] := by
  simp only [σE]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem σE_sh (i : Fin 11) : (σE P s).sh i = 0 := rfl
theorem σE_val (r : Fin 16) : (σE P s).val r = 0 := rfl

end Entry

/-- The zero words of `X`, `ACC`, `NEW`, `ST`. -/
def initW : WM 10 16 := .seq (zwW 7) (.seq (zwW 8) (.seq (zwW 9) (zwW 10)))

/-- The expansion's word program. -/
def mainW : WM 10 16 := .seq initW (.seq seedW loopW)

def mainCost (P : Sampler.SeedParams) : ℕ :=
  zwCost P.ell + 1 + (zwCost P.ell + 1 + (zwCost P.ell + 1 + zwCost P.ell)) + 1 +
    (seedCost P.ell + 1 + (P.Q * (stepCost P.ell P.kh + 4) + 1))

theorem keep {S : Fin 11 → Prop} {G : Fin 16 → Prop} {σ τ : WState 10 16} (h : WFrame S G σ τ) (i : Fin 11)
    (hi : ¬ S i) : τ.st i = σ.st i ∧ τ.sh i = σ.sh i := h.1 i hi

/-- **The expansion's word program**: the output stream ends as `sampleWord kh (seedPairs P s)`. -/
theorem main_spec (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hcap : 18 * P.ell + 20 ≤ cap) :
    ∃ τ, WExec cap mainW (σE P s) τ (mainCost P) ∧
      τ.st 5 = FinalPass.Sample.sampleWord P.kh (PrimT.C4Iface.seedPairs P s) := by
  have hl : P.ell ≤ cap := by omega
  obtain ⟨τ1, s1, x1, hx1, f1⟩ := zw_spec cap 7 (by decide) (by decide) P.ell hl (σE P s)
    (σE_blank P s 7 (by decide)) (σE_sh P s 7) (σE_st3 P s) (σE_sh P s 3) (σE_val P s 0)
  obtain ⟨τ2, s2, x2, hx2, f2⟩ := zw_spec cap 8 (by decide) (by decide) P.ell hl τ1
    (by rw [(keep f1 8 (by decide)).1]; exact σE_blank P s 8 (by decide)) (by rw [(keep f1 8 (by decide)).2]; rfl)
    (by rw [(keep f1 3 (by decide)).1]; rfl) (by rw [(keep f1 3 (by decide)).2]; rfl)
    (by rw [f1.2.1 0 (fun h => h)]; rfl)
  obtain ⟨τ3, s3, x3, hx3, f3⟩ := zw_spec cap 9 (by decide) (by decide) P.ell hl τ2
    (by rw [(keep f2 9 (by decide)).1, (keep f1 9 (by decide)).1]; exact σE_blank P s 9 (by decide))
    (by rw [(keep f2 9 (by decide)).2, (keep f1 9 (by decide)).2]; rfl)
    (by rw [(keep f2 3 (by decide)).1, (keep f1 3 (by decide)).1]; rfl)
    (by rw [(keep f2 3 (by decide)).2, (keep f1 3 (by decide)).2]; rfl)
    (by rw [f2.2.1 0 (fun h => h), f1.2.1 0 (fun h => h)]; rfl)
  obtain ⟨τ4, s4, x4, hx4, f4⟩ := zw_spec cap 10 (by decide) (by decide) P.ell hl τ3
    (by rw [(keep f3 10 (by decide)).1, (keep f2 10 (by decide)).1, (keep f1 10 (by decide)).1]
        exact σE_blank P s 10 (by decide))
    (by rw [(keep f3 10 (by decide)).2, (keep f2 10 (by decide)).2, (keep f1 10 (by decide)).2]; rfl)
    (by rw [(keep f3 3 (by decide)).1, (keep f2 3 (by decide)).1, (keep f1 3 (by decide)).1]; rfl)
    (by rw [(keep f3 3 (by decide)).2, (keep f2 3 (by decide)).2, (keep f1 3 (by decide)).2]; rfl)
    (by rw [f3.2.1 0 (fun h => h), f2.2.1 0 (fun h => h), f1.2.1 0 (fun h => h)]; rfl)
  have fI : WFrame (fun i => i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10) (fun _ => False) (σE P s) τ4 :=
    (f1.mono (fun i h => Or.inl h) (fun _ h => h)).trans ((f2.mono (fun i h => Or.inr (Or.inl h)) (fun _ h => h)).trans
      ((f3.mono (fun i h => Or.inr (Or.inr (Or.inl h))) (fun _ h => h)).trans
        (f4.mono (fun i h => Or.inr (Or.inr (Or.inr h))) (fun _ h => h))))
  obtain ⟨τ5, s5, e56, eh56, f5⟩ := seed_spec cap P s hl τ4
    (by rw [(keep fI 0 (by decide)).1]; rfl) (by rw [(keep fI 0 (by decide)).2]; rfl)
    (by rw [(keep fI 6 (by decide)).1]; exact σE_blank P s 6 (by decide)) (by rw [(keep fI 6 (by decide)).2]; rfl)
    (by rw [(keep fI 3 (by decide)).1]; rfl) (by rw [(keep fI 3 (by decide)).2]; rfl)
    (by rw [fI.2.1 0 (fun h => h)]; rfl)
  have k7 := keep f4 7 (by decide)
  have k7' := keep f3 7 (by decide)
  have k7'' := keep f2 7 (by decide)
  have k8 := keep f4 8 (by decide)
  have k8' := keep f3 8 (by decide)
  have k9 := keep f4 9 (by decide)
  have hL : LInv P s 0 τ5 := by
    refine ⟨?_, ?_, ?_, ?_, e56, eh56, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(keep f5 2 (by decide)).1, (keep fI 2 (by decide)).1]; rfl
    · rw [(keep f5 2 (by decide)).2, (keep fI 2 (by decide)).2]; rfl
    · rw [(keep f5 5 (by decide)).1, (keep fI 5 (by decide)).1]; exact σE_blank P s 5 (by decide)
    · rw [(keep f5 5 (by decide)).1, (keep f5 5 (by decide)).2, (keep fI 5 (by decide)).1,
        (keep fI 5 (by decide)).2, σE_blank P s 5 (by decide)]; rfl
    · rw [(keep f5 8 (by decide)).1, k8.1, k8'.1]; exact ⟨0, x2⟩
    · rw [(keep f5 8 (by decide)).2, k8.2, k8'.2]; exact hx2
    · rw [(keep f5 9 (by decide)).1, k9.1]; exact ⟨0, x3⟩
    · rw [(keep f5 9 (by decide)).2, k9.2]; exact hx3
    · rw [(keep f5 10 (by decide)).1]; exact ⟨0, x4⟩
    · rw [(keep f5 10 (by decide)).2]; exact hx4
    · rw [(keep f5 7 (by decide)).1, k7.1, k7'.1, k7''.1]; exact x1
    · rw [(keep f5 7 (by decide)).2, k7.2, k7'.2, k7''.2]; exact hx1
    · rw [(keep f5 4 (by decide)).1, (keep fI 4 (by decide)).1]; rfl
    · rw [(keep f5 4 (by decide)).2, (keep fI 4 (by decide)).2]; rfl
    · rw [(keep f5 1 (by decide)).1, (keep fI 1 (by decide)).1]; rfl
    · rw [(keep f5 1 (by decide)).2, (keep fI 1 (by decide)).2]; rfl
    · intro r; rw [f5.2.1 r (fun h => h), fI.2.1 r (fun h => h)]; rfl
  obtain ⟨τ, s6, hτ⟩ := loop_spec cap P s hcap P.Q 0 τ5 (by omega) hL
  refine ⟨τ, WExec.seq (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (WExec.seq s5 s6), ?_⟩
  rw [hτ.out, SampMath.sampleWord_eq]

end NearCubicWires.WireExponent3_5.UnionMachine.SampRun
