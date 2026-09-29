import Proof.Wire_3_5.Selection.CosGate

/-! # C1.5: one gate occurrence of a population (P3:1356-1362)

Paper: "Sum its exact count with the rational population weights, over gates and rows" (P3:1356-1357); "Repeated
labelled occurrences are charged with their weights; they need not be deduplicated" (P3:1361-1362). One index of a
population: `IX := i` from the population table (C6's `copyAtB`); if `i < #gates` (C6's `ltB` against the gate count):
count `i` into `GI` (`toU`), fetch gate `i`'s record into `GA`, clear `GI`, and call the gate routine, so `TX` gains
the gate's row count at the coset; otherwise nothing (an index outside the gate list reads the default gate, whose
row counts vanish: `popRows`). Main declarations: `rowsAt`, `gcall`, `idxB`, `idxCost`, **`idxB_spec`**. Paper
quantity: a population's row count, one occurrence at a time. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-- One occurrence's row count at the coset `N` (`0` outside the gate list; `popRows` summand). -/
def rowsAt (R : SelectionReq) (h : ParamsOk R) (N i : ℕ) : ℕ :=
  if hi : i < R.gates.length then gateRows (starParamsOf R h)
    ((starParamsOf R h).translationOfCodes (codesOfIdx R.s R.r N)) (gateOf R.gates[i]) else 0

/-- The call of gate `GI`: count, fetch, clear, call. -/
def gcall (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) : WM ns nr :=
  .seq (.dec (Q 50)) (.seq (toU S Q) (.seq (fetch S Q) (.seq (WM.clear (Q 54)) (gateW (gG S) (gR Q)))))

/-- **One index** of a population. -/
def idxB (S : Fin 50 → Fin (ns + 1)) (Q : Fin 64 → Fin nr) : WM ns nr :=
  .seq (copyAtB (S 44) (S 31) (Q 61) (Q 62)) (.seq (ltB (S 44) (S 32) (Q 50) (Q 62)) (.ifr (Q 50) (gcall S Q) .skip))

/-- One index's cost (at most, over `i < g`). -/
def idxCost (P : StarParams) (n W V g : ℕ) : ℕ :=
  46 * W + 7 + 1 + (41 * W + 3 + 1 + (1 + 1 + (toUCost W g + 1 + (fetchCost n W g + 1 +
    (3 * g + 1 + 1 + gateCost P W V))) + 1))

theorem toUCost_mono (W i g : ℕ) (hig : i ≤ g) : toUCost W i ≤ toUCost W g := by
  unfold toUCost
  have := Nat.mul_le_mul_right (uRound W + 2) hig
  omega

theorem fetchCost_mono (n W i g : ℕ) (hig : i ≤ g) : fetchCost n W i ≤ fetchCost n W g := by
  unfold fetchCost
  gcongr

/-- **One index**: `TX += rowsAt i`; the table's head moves past the index word; `Base` holds. -/
theorem idxB_spec (S : Fin 50 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 64 → Fin nr)
    (hQ : Function.Injective Q) (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (W V N : ℕ) (σ : WState ns nr)
    (b : Base S Q R h W V N σ) (i tx x0 j0 : ℕ) (pre rest : List Bool)
    (hPT : σ.st (S 31) = pre ++ frame (binary W i) ++ rest) (hPTh : σ.sh (S 31) = pre.length)
    (hTX : NumOn σ (S 3) W tx) (hIX : NumOn σ (S 44) W x0) (hJ : NumOn σ (S 46) W j0)
    (hi : i < 2 ^ W) (hng : R.gates.length < 2 ^ W) (hN : N < 2 ^ (R.r * R.s))
    (hKB : ∀ g ∈ R.gates, KeyBound (gateOf g) V) (hW : 2 * V + 3 ≤ W) (hnk : R.n + (starParamsOf R h).k + 4 ≤ W)
    (hfit : tx + rowsAt R h N i < 2 ^ W) (hcap : gateNeed (starParamsOf R h) W V ≤ cap) (hcap2 : 2 * W + 1 ≤ cap)
    (hcapG : R.gates.length * (R.n + 1) * (2 * W + 2) + 2 < cap) :
    ∃ τ : WState ns nr, WExec cap (idxB S Q) σ τ (idxCost (starParamsOf R h) R.n W V R.gates.length) ∧
      Base S Q R h W V N τ ∧ NumOn τ (S 3) W (tx + rowsAt R h N i) ∧
      τ.sh (S 31) = pre.length + 2 * W + 1 ∧ NumOn τ (S 44) W i ∧ (∃ j, NumOn τ (S 46) W j) ∧
      (∀ k : Fin 50, 28 ≤ k.val → k.val ≠ 44 → k.val ≠ 46 → τ.st (S k) = σ.st (S k)) ∧
      (∀ k : Fin 50, k ≠ 31 → τ.sh (S k) = σ.sh (S k)) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have q48 : σ.val (Q 48) = 0 := b.tmp 48 (by decide)
  have q49 : σ.val (Q 49) = 0 := b.tmp 49 (by decide)
  have q50 : σ.val (Q 50) = 0 := b.tmp 50 (by decide)
  have q54 : σ.val (Q 54) = 0 := b.tmp 54 (by decide)
  have q55 : σ.val (Q 55) = 0 := b.tmp 55 (by decide)
  have q56 : σ.val (Q 56) = 0 := b.tmp 56 (by decide)
  have q61 : σ.val (Q 61) = 0 := b.tmp 61 (by decide)
  have q62 : σ.val (Q 62) = 0 := b.tmp 62 (by decide)
  have sne : ∀ a c : Fin 50, a ≠ c → S a ≠ S c := fun a c h => hS.ne h
  have qne : ∀ a c : Fin 64, a ≠ c → Q a ≠ Q c := fun a c h => hQ.ne h
  have c1 := copyAtB_spec cap W (A := S 44) (I := S 31) (F := Q 61) (R := Q 62) (sne 44 31 (by decide))
    (qne 61 62 (by decide)) σ x0 i pre rest hIX hPT hPTh q61 q62 hcap2
  set σ1 := (σ.sets (S 44) (frame (binary W i))).seth (S 31) (pre.length + 2 * W + 1) with hσ1
  have b1 : Base S Q R h W V N σ1 := (b.sets hS hQ 44 (by decide) _).seth31 hS hQ _
  have ix1 : NumOn σ1 (S 44) W i := ⟨by simp [hσ1], by simp [hσ1, sne 44 31 (by decide), hIX.2]⟩
  have c2 := ltB_spec cap W (A := S 44) (B := S 32) (F := Q 50) (R := Q 62) (sne 44 32 (by decide))
    (qne 50 62 (by decide)) σ1 i R.gates.length ix1 b1.ng (by simp [hσ1, q50]) (by simp [hσ1, q62]) hi hng hcap2
  set σ2 := σ1.setv (Q 50) (decide (i < R.gates.length)).toNat with hσ2
  have tx1 : NumOn σ1 (S 3) W tx :=
    ⟨by simp [hσ1, sne 3 44 (by decide), hTX.1], by simp [hσ1, sne 3 31 (by decide), hTX.2]⟩
  have v1 : σ1.val = σ.val := rfl
  have hcg : R.gates.length ≤ cap := by
    have : R.gates.length ≤ R.gates.length * (R.n + 1) * (2 * W + 2) := by
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  by_cases hig : i < R.gates.length
  · have hF : σ2.val (Q 50) = 1 := by simp [hσ2, hig]
    have d := WExec.dec (cap := cap) (Q 50) σ2 (by rw [hF]; omega)
    have e3 : σ2.setv (Q 50) (σ2.val (Q 50) - 1) = σ1 := by
      rw [hF, hσ2, wsetv_setv]; exact Gate.wsetv_zero _ _ (by simp [hσ1, q50])
    rw [e3] at d
    have u := toU_spec S hS Q hQ cap W σ1 j0 i
      ⟨by simp [hσ1, sne 46 44 (by decide), hJ.1], by simp [hσ1, sne 46 31 (by decide), hJ.2]⟩ ix1 hi
      (by simp [hσ1, q50]) (by simp [hσ1, q54]) (by simp [hσ1, q61]) (by simp [hσ1, q62]) (by omega) hcap2
    set σ4 := (σ1.sets (S 46) (frame (binary W i))).setv (Q 54) i with hσ4
    have f := fetch_spec S hS Q hQ cap W R σ4 i hig
      (by simp [hσ4, hσ1, sne 30 46 (by decide), sne 30 44 (by decide), b.gt])
      (by simp [hσ4, hσ1, sne 30 31 (by decide), b.gth]) (by simp [hσ4, hσ1, sne 1 31 (by decide), b.gah])
      (by simp [hσ4, hσ1, sne 1 46 (by decide), sne 1 44 (by decide)]; exact b.ga)
      (by simp [hσ4, hσ1, qne 48 54 (by decide), q48]) (by simp [hσ4, hσ1, qne 49 54 (by decide), q49])
      (by simp [hσ4]) (by simp [hσ4, hσ1, qne 55 54 (by decide), q55]) (by simp [hσ4, hσ1, qne 56 54 (by decide), q56])
      (by simp [hσ4, hσ1, qne 60 54 (by decide), b.nr1]) hcapG
    set σ5 := σ4.sets (S 1) (gateRec W (gateOf R.gates[i])) with hσ5
    have cl := wclear_spec cap (Q 54) i σ5 (by simp [hσ5, hσ4]) (by simp [hσ5, hσ4]; omega)
    set σ6 := σ5.setv (Q 54) 0 with hσ6
    have v6 : σ6.val = σ.val := by
      funext r
      by_cases hr : r = Q 54
      · subst hr; simp [hσ6, q54]
      · simp [hσ6, hσ5, hσ4, hσ1, Function.update_apply, hr]
    have glen : (gateRec W (gateOf R.gates[i])).length = (R.n + 1) * (2 * W + 2) := by
      rw [← tbl_gRecs, tbl_length, gRecs_length]
    have b6 : Base S Q R h W V N σ6 := by
      refine Base.of_agree b (fun k hk => ?_) (by simp [hσ6, hσ5, hσ4, glen]) (fun k hk => ?_) (fun j _ => by rw [v6])
      · have k1 : S k ≠ S 1 := sne k 1 (fun e => by subst e; simp at hk)
        have k44 : S k ≠ S 44 := sne k 44 (fun e => by subst e; simp at hk)
        have k46 : S k ≠ S 46 := sne k 46 (fun e => by subst e; simp at hk)
        simp [hσ6, hσ5, hσ4, hσ1, k1, k44, k46]
      · have k31 : S k ≠ S 31 := sne k 31 hk
        simp [hσ6, hσ5, hσ4, hσ1, k31]
    have tx6 : NumOn σ6 (S 3) W tx :=
      ⟨by simp [hσ6, hσ5, hσ4, hσ1, sne 3 1 (by decide), sne 3 46 (by decide), sne 3 44 (by decide), hTX.1],
        by simp [hσ6, hσ5, hσ4, hσ1, sne 3 31 (by decide), hTX.2]⟩
    have hrows : rowsAt R h N i = gateRows (starParamsOf R h)
        ((starParamsOf R h).translationOfCodes (codesOfIdx R.s R.r N)) (gateOf R.gates[i]) := by
      simp [rowsAt, hig]
    obtain ⟨τ, hx, bτ, hTXτ, hk28, hk1, hsh, hval, hcell⟩ := gate_call S hS Q hQ cap R h W V N σ6 b6 i tx hig
      (by simp [hσ6, hσ5]) tx6 hN (hKB _ (List.getElem_mem hig)) hW hnk (by rw [← hrows]; exact hfit) hcap
    refine ⟨τ, ?_, bτ, by rw [hrows]; exact hTXτ, ?_, ?_, ⟨i, ?_⟩, ?_, ?_, by rw [hval, v6], by rw [hcell]; rfl⟩
    · have gc := WExec.ifrT (P := gcall S Q) (Q := .skip) (by rw [hF]; omega)
        (WExec.seq d (WExec.seq u (WExec.seq f (WExec.seq cl hx))))
      unfold idxB
      refine WExec.cast cap (WExec.seq c1 (WExec.seq c2 gc)) rfl ?_
      unfold idxCost
      have m1 := toUCost_mono W i R.gates.length hig.le
      have m2 := fetchCost_mono R.n W i R.gates.length hig.le
      omega
    · rw [hsh]; simp [hσ6, hσ5, hσ4, hσ1]
    · refine ⟨by rw [hk28 44 (by decide)]; simp [hσ6, hσ5, hσ4, hσ1, sne 44 1 (by decide), sne 44 46 (by decide)],
        by rw [hsh]; simp [hσ6, hσ5, hσ4, hσ1, sne 44 31 (by decide), hIX.2]⟩
    · refine ⟨by rw [hk28 46 (by decide)]; simp [hσ6, hσ5, hσ4, hσ1, sne 46 1 (by decide)],
        by rw [hsh]; simp [hσ6, hσ5, hσ4, hσ1, sne 46 31 (by decide), hJ.2]⟩
    · intro k hk h44 h46
      rw [hk28 k hk]
      have k1 : S k ≠ S 1 := sne k 1 (fun e => by subst e; simp at hk)
      have k44 : S k ≠ S 44 := sne k 44 (fun e => by subst e; simp at h44)
      have k46 : S k ≠ S 46 := sne k 46 (fun e => by subst e; simp at h46)
      simp [hσ6, hσ5, hσ4, hσ1, k1, k44, k46]
    · intro k hk
      rw [hsh]
      simp [hσ6, hσ5, hσ4, hσ1, sne k 31 hk]
  · have hF : σ2.val (Q 50) = 0 := by simp [hσ2, hig]
    have e2 : σ2 = σ1 := by rw [hσ2, show (decide (i < R.gates.length)).toNat = 0 by simp [hig]];
                            exact Gate.wsetv_zero _ _ (by simp [hσ1, q50])
    have gc := WExec.ifrF (cap := cap) (P := gcall S Q) (Q := .skip) hF (WExec.skip (cap := cap) σ2)
    have hrows : rowsAt R h N i = 0 := by simp [rowsAt, hig]
    refine ⟨σ1, ?_, b1, by rw [hrows, Nat.add_zero]; exact tx1, by simp [hσ1], ix1,
      ⟨j0, by simp [hσ1, sne 46 44 (by decide), hJ.1], by simp [hσ1, sne 46 31 (by decide), hJ.2]⟩, ?_, ?_, v1, rfl⟩
    · unfold idxB
      refine WExec.cast cap (WExec.seq c1 (WExec.seq c2 gc)) e2 ?_
      unfold idxCost
      omega
    · intro k hk h44 h46
      have k44 : S k ≠ S 44 := sne k 44 (fun e => by subst e; simp at h44)
      simp [hσ1, k44]
    · intro k hk
      simp [hσ1, sne k 31 hk]

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
