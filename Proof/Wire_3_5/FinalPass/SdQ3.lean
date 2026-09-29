import Proof.Wire_3_5.FinalPass.SdQ2

/-! # S4 (the seeds phase), part 37: the seed loop's invariant at the loops' entry (P3:3170-3178)

From `PreSet` (part 36), the loops' entry state `ωQ` meets the seed loop's invariant at accumulator `0`
(**`sdinv_of`**: the numerator's zero, the point's three streams, the two tables' lengths, every carrier's gate
table and formatted accumulators, blank scratch, both center counters at `0`) and **`entry_misc`** (the tables' and
seeds' registers `0`, the tables word in place, every register off the setup's and the numbers' `0`).

Paper quantity of the main type: the seeds phase's loop-entry state (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)

section Body
variable {nw nn nsc nrs : ℕ}
variable {P : StarParams} {σT : P.Translation} {smp : CallSample P} {carriers : List (Stars.Carrier P.n)}
  {FP : GapParams} {W : ℕ} {σ0 : BS nw nn nsc nrs} {e0 : GapSeed FP}

section
variable (H : PreSet P σT smp carriers FP W σ0) (ωQ : BS nw nn nsc nrs)
  (hst : ωQ.st = (omS P carriers FP σ0 e0).st) (hsh : ωQ.sh = (omS P carriers FP σ0 e0).sh)
  (hv : ∀ q, q ∉ (thrRegs : List (Fin (bnr nn nrs))) → q ∉ (symRegs : List (Fin (bnr nn nrs))) →
    ωQ.val q = (omS P carriers FP σ0 e0).val q)
include H hst hsh hv

theorem omQ_zero (q : Fin (bnr nn nrs)) (h1 : q.val = 0 ∨ 5 ≤ q.val) (h2 : q.val < 220)
    (h3 : q.val < 120 ∨ (121 < q.val ∧ q.val < 156) ∨ (159 < q.val ∧ q.val < 168) ∨ 172 < q.val) : ωQ.val q = 0 := by
  rw [hv q (notThr q h1) (notSym q h2)]; exact omS_zero H.R q h3

theorem omQ_st (j : ℕ) (hj : j < 47) (h : j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3 ∧ (j < 8 ∨ 17 < j) ∧ j ≠ 25 ∧ j ≠ 26) (h4 : j ≠ 4) :
    ωQ.st (bst j hj) = σ0.st (bst j hj) := by
  rw [hst]; exact omS_st_other (bst j hj) h h4

theorem omQ_frame (o : Fin (bns nw nsc + 1)) (k : Fin 30)
    (hj : (⟨o, sRp k, [true, false], false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈ sJobs) :
    ωQ.st o = frame (List.replicate (σ0.val (sRp k)) false) := by
  rw [hst]; exact setRS_frame σ0 _ _ _ _ o k hj

theorem sdinv_of : SdInv FP P carriers W 0 ωQ ωQ := by
  have f : ∀ k : Fin 16, σ0.val (sRp ⟨k.val, by omega⟩) = (Seams.s4Small2 P carriers FP).getD k.val 0 := H.Rp
  have fr : ∀ (o : Fin (bns nw nsc + 1)),
      (⟨o, sRp 17, [true, false], false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈ sJobs →
      ∃ Y : List Bool, ωQ.st o = frameP Y ++ [false] ∧ Y.length = P.n := fun o hj =>
    ⟨List.replicate P.n false, by rw [omQ_frame H ωQ hst hsh hv o 17 hj, H.Rn, frame_eq_frameP], by simp⟩
  have cnt0 : ∀ q : Fin (bnr nn nrs), 193 < q.val → q.val < 200 → ωQ.val q = 0 := fun q h1 h2 =>
    omQ_zero H ωQ hst hsh hv q (Or.inr (by omega)) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))
  refine
    { st := fun _ _ _ _ => rfl, sh := rfl, val := fun _ _ _ => rfl, cell := rfl, Nw := ?_,
      U := fr tU (by simp [sJobs]), V := fr tV (by simp [sJobs]), C := fr tC (by simp [sJobs]), T := ?_,
      car := ?_, sc := ?_, cc := ?_, cr := ?_ }
  · exact (omQ_st H ωQ hst hsh hv 0 (by omega) (by omega) (by omega)).trans H.N
  · intro k
    rw [hst, omS, setRS_tT, List.length_append, flat_len, List.length_singleton]
    have hT0 := tab_len FP e0 (Seams.carLen carriers 0)
    have hT1 := tab_len FP e0 (Seams.carLen carriers 1)
    fin_cases k
    · show ((tb FP e0 (Seams.carLen carriers 0)).length - 1) * 1 + 1 =
        FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) + 1
      unfold tb
      rw [hT0]
      omega
    · show ((tb FP e0 (Seams.carLen carriers 1)).length - 1) * 1 + 1 =
        FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) + 1
      unfold tb
      rw [hT1]
      omega
  · intro k hk
    have hG : ωQ.st (tG k) = gatesW (PrimT.tabH (carriers.get ⟨k.val, hk⟩)) (maskGates (carriers.get ⟨k.val, hk⟩)) := by
      have e1 := omQ_st H ωQ hst hsh hv (32 + k.val) (by omega) (by omega) (by omega)
      have e2 := H.W8 ⟨2 + k.val, by omega⟩
      have e3 : Seams.s4Core2 P σT smp carriers FP ⟨2 + k.val, by omega⟩ = Seams.carTab carriers k.val := by
        fin_cases k <;> rfl
      rw [show (tG k : Fin (bns nw nsc + 1)) = bst (32 + k.val) (by omega) from rfl, e1,
        show (bst (32 + k.val) (by omega) : Fin (bns nw nsc + 1)) = bst (30 + (⟨2 + k.val, by omega⟩ : Fin 8).val)
          (by omega) from Fin.ext (by simp [bst]; omega), e2, e3]
      unfold Seams.carTab
      rw [dif_pos hk]
    have hHk : ![Hof carriers 0, Hof carriers 1] k = PrimT.tabH (carriers.get ⟨k.val, hk⟩) := by
      fin_cases k <;> simp [Hof, hk]
    have hL : σ0.val (sRp ⟨9 + k.val, by omega⟩) = (maskGates (carriers.get ⟨k.val, hk⟩)).length := by
      have := f ⟨9 + k.val, by omega⟩
      rw [this]
      fin_cases k <;> simp [Seams.s4Small2, Seams.s4Small, Seams.carLen, hk]
    obtain ⟨hPos, hNeg⟩ := setRS_tPos σ0 (Hof carriers 0) (Hof carriers 1) (tb FP e0 (Seams.carLen carriers 0)).length
      (tb FP e0 (Seams.carLen carriers 1)).length k
    obtain ⟨hX, hZ⟩ := setRS_tX σ0 (Hof carriers 0) (Hof carriers 1) (tb FP e0 (Seams.carLen carriers 0)).length
      (tb FP e0 (Seams.carLen carriers 1)).length k
    refine ⟨hG, ⟨0, 0, (List.replicate (σ0.val (sRp ⟨9 + k.val, by omega⟩)) (List.replicate 8 false)).flatten,
      ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hst]; unfold omS; rw [hPos, hHk, binary_zero_rep, frame_eq_frameP]
    · rw [hst]; unfold omS; rw [hNeg, hHk, binary_zero_rep, frame_eq_frameP]
    · rw [hst]; unfold omS; exact hX
    · rw [flat_len, hL, List.length_replicate, Nat.mul_comm]
    · rw [hst]; unfold omS; rw [hZ, hL, flat_ff]
  · intro i hi b hb
    have hnj : i.val ≠ 1 ∧ i.val ≠ 2 ∧ i.val ≠ 3 ∧ (i.val < 8 ∨ 17 < i.val) ∧ i.val ≠ 25 ∧ i.val ≠ 26 := by
      unfold IsSc at hi; omega
    have h4 : i.val ≠ 4 := by unfold IsSc at hi; omega
    rw [hst, omS_st_other i hnj h4, H.Sc i hi] at hb
    simp at hb
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have f8 : σ0.val (sRp 8) = (Seams.s4Small2 P carriers FP).getD 8 0 := f 8
      rw [show (cT false : Fin (bns nw nsc + 1)) = tCol from rfl, omQ_frame H ωQ hst hsh hv tCol 8 (by simp [sJobs]),
        f8, binary_zero_rep]
      rfl
    · rw [hsh, omS, setRS_sh]; exact H.sh _
    · exact cnt0 _ (by simp [cC, brg]) (by simp [cC, brg])
    · exact cnt0 _ (by simp [cF, brg]) (by simp [cF, brg])
    · exact cnt0 _ (by simp [cK, brg]) (by simp [cK, brg])
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have f7 : σ0.val (sRp 7) = (Seams.s4Small2 P carriers FP).getD 7 0 := f 7
      rw [show (cT true : Fin (bns nw nsc + 1)) = tRow from rfl, omQ_frame H ωQ hst hsh hv tRow 7 (by simp [sJobs]),
        f7, binary_zero_rep]
      rfl
    · rw [hsh, omS, setRS_sh]; exact H.sh _
    · exact cnt0 _ (by simp [cC, brg]) (by simp [cC, brg])
    · exact cnt0 _ (by simp [cF, brg]) (by simp [cF, brg])
    · exact cnt0 _ (by simp [cK, brg]) (by simp [cK, brg])

theorem entry_misc :
    ωQ.val rgP = 0 ∧ ωQ.val fS = 0 ∧ ωQ.val rgT = 0 ∧ ωQ.val rgB = 0 ∧
      ωQ.st tTW = twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1) ∧
      (∀ q, q ∉ (tdFix : List (Fin (bnr nn nrs))) → q ∉ (thrRegs : List (Fin (bnr nn nrs))) →
        q ∉ (symRegs : List (Fin (bnr nn nrs))) → ωQ.val q = 0) := by
  refine ⟨omQ_zero H ωQ hst hsh hv _ (Or.inr (show 5 ≤ 203 by omega)) (show 203 < 220 by omega)
      (Or.inr (Or.inr (Or.inr (show 172 < 203 by omega)))),
    omQ_zero H ωQ hst hsh hv _ (Or.inr (show 5 ≤ 202 by omega)) (show 202 < 220 by omega)
      (Or.inr (Or.inr (Or.inr (show 172 < 202 by omega)))),
    omQ_zero H ωQ hst hsh hv _ (Or.inr (show 5 ≤ 200 by omega)) (show 200 < 220 by omega)
      (Or.inr (Or.inr (Or.inr (show 172 < 200 by omega)))),
    omQ_zero H ωQ hst hsh hv _ (Or.inr (show 5 ≤ 201 by omega)) (show 201 < 220 by omega)
      (Or.inr (Or.inr (Or.inr (show 172 < 201 by omega)))),
    (omQ_st H ωQ hst hsh hv 27 (by omega) (by omega) (by omega)).trans H.TW, ?_⟩
  intro q h1 h2 h3
  rw [hv q h2 h3]
  apply setRS_val_zero σ0 _ _ _ _ H.R q
  intro hm
  apply h1
  simp only [seedFix, List.mem_cons, List.not_mem_nil, or_false] at hm
  simp only [tdFix, List.mem_cons, List.not_mem_nil, or_false]
  tauto

end

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
