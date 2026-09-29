import Proof.Wire_3_5.Primitive.SeedFix.NwB10

/-! # NW phase (b), part 11: the docks with every head kept at `0`

`docksT_run2` with one more conjunct: the docked streams' heads end at `0` and the other streams' heads are
kept, so a bank with every head at `0` leaves the docks with every head at `0` (**`docksT_run3`**; phase (b)'s exit
`AfterV.heads`).

Paper quantity of the main type: the THR call's numbers (`thrNumVals`, P3:2543-2558) on the docks' ports. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.SupplierPipeline

section Dock2
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
variable (cap : ℕ)

/-- **The docks, run, with W6's fourteen numbers exposed and the heads at `0`.** -/
theorem docksT_run3 (x : ℕ) (hx : dX T N ≤ x) (σ : WState (LNS x) LNR) (P : Shared.StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ) (tl : List Bool) (V ncar capT : ℕ)
    (hin : DockInT T N x σ (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V ncar capT)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : ncar ≤ 2)
    (hcap : 1 ≤ capT) (hok : PrimThrW.TopFront2.TF2Ok Cs codes V) (hneed : N.need (P.n + capT) ≤ V) :
    ∃ τ : WState (LNS x) LNR,
      Step (docksMT T N x hx) (T.cost V + 1 + N.cost (P.n + V + capT)) (wenc cap σ).H (wenc cap σ).A
        (wenc cap τ).H (wenc cap τ).A ∧
      DockOutT x σ τ (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) (thrNumVals P Cs alg Dexp ncar capT)
        (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []) ∧
      (∀ k : Fin 14, τ.st (w6M T N x hx (Fin.castAdd N.x ⟨k.val + 3, by omega⟩)) =
        List.replicate ((thrNumVals P Cs alg Dexp ncar capT).get k) true) ∧
      ((∀ i, σ.sh i = 0) → ∀ i, τ.sh i = 0) := by
  obtain ⟨J1, -, r1⟩ := T.run Cs codes tl V hn ha hd hok
  obtain ⟨eH1, eA1⟩ := tf_inT T N x hx σ _ V ncar capT hin
  have s1 := DockW.dockS cap (tfM T N x hx) (tfM_inj T N x hx) σ (HashCell.step_in r1 eH1.symm eA1.symm)
  obtain ⟨eH2, eA2⟩ := w6_inT T N x hx σ _ V ncar capT hin Cs J1
  obtain ⟨J2, -, r2⟩ := N.run P Cs codes tl ncar capT V hn ha hd hnc hcap hok hneed
  have s2 := DockW.dockS cap (w6M T N x hx) (w6M_inj T N x hx) _ (HashCell.step_in r2 eH2.symm eA2.symm)
  refine ⟨_, Step.seq s1 s2, ?_⟩
  set σ1 := updS (tfM T N x hx) σ (fun _ => 0) (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
    (PrimThrW.TopFront2.tf2OutPorts alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V Cs) J1) with hσ1
  have rdW : ∀ (k : Fin 161) (i : Fin 21), w6V T N i.val = k.val →
      (updS (w6M T N x hx) σ1 (fun _ => 0) (Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool)
        (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
          (thrNumVals P Cs alg Dexp ncar capT)) J2)).st (sk x k) =
      PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
        (thrNumVals P Cs alg Dexp ncar capT) i ∧
      (updS (w6M T N x hx) σ1 (fun _ => 0) (Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool)
        (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
          (thrNumVals P Cs alg Dexp ncar capT)) J2)).sh (sk x k) = 0 := by
    intro k i hk
    have e : sk x k = w6M T N x hx (Fin.castAdd N.x i) := Fin.ext (by rw [sk_val, w6M_val]; simp [hk])
    refine ⟨?_, ?_⟩
    · show install (w6M T N x hx) _ _ (sk x k) = _
      rw [e, install_slot _ (w6M_inj T N x hx), Fin.addCases_left]
    · show dockH (w6M T N x hx) _ _ (sk x k) = _
      rw [e, dockH_slot _ (w6M_inj T N x hx)]
  have w6ne : ∀ (k : Fin 161), k.val ≠ 0 → (k.val < 130 ∨ 132 < k.val) → ∀ j, w6M T N x hx j ≠ sk x k := by
    intro k h0 hk j h
    have e : w6V T N j.val = k.val := by have := congrArg Fin.val h; rwa [w6M_val, sk_val] at this
    have hj := j.isLt
    have hk' := k.isLt
    unfold w6V at e; unfold bT at e
    split_ifs at e <;> omega
  have tfne : ∀ (k : Fin 161), k.val ≠ 0 → (k.val < 133 ∨ 136 < k.val) → ∀ j, tfM T N x hx j ≠ sk x k := by
    intro k h0 hk j h
    have e : tfV T N j.val = k.val := by have := congrArg Fin.val h; rwa [tfM_val, sk_val] at this
    have hj := j.isLt
    have hk' := k.isLt
    unfold tfV at e; unfold bT at e
    split_ifs at e <;> omega
  refine ⟨⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [(rdW 0 0 (by simp [w6V])).1]; rfl
  · rw [(rdW 130 17 (by simp [w6V])).1]; rfl
  · rw [(rdW 131 18 (by simp [w6V])).1]; rfl
  · rw [(rdW 132 19 (by simp [w6V])).1]; rfl
  · intro i
    have hi := i.isLt
    show install (w6M T N x hx) (install (tfM T N x hx) σ.st _) _ (sk x ⟨133 + i.val, _⟩) = _
    rw [install_other _ _ _ _ (w6ne ⟨133 + i.val, by omega⟩ (by simp) (by simp; omega))]
    have e : sk x ⟨133 + i.val, by omega⟩ = tfM T N x hx (Fin.castAdd T.x ⟨i.val + 2, by omega⟩) :=
      Fin.ext (by rw [sk_val, tfM_val]; simp [tfV]; split_ifs <;> omega)
    rw [e, install_slot _ (tfM_inj T N x hx), Fin.addCases_left]
    have a6 : i.val + 2 < 6 := by omega
    by_cases hh : i.val < a'
    · simp [PrimThrW.TopFront2.tf2OutPorts, hh, a6]
    · simp [PrimThrW.TopFront2.tf2OutPorts, hh, a6]
  · intro k hk
    rcases hk with h0 | h
    · exact (rdW k 0 (by simp [w6V, h0])).2
    · by_cases hm : k.val ≤ 132
      · have hv : w6V T N (k.val - 113) = k.val := by
          unfold w6V
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          omega
        exact (rdW k ⟨k.val - 113, by omega⟩ hv).2
      · show dockH (w6M T N x hx) (dockH (tfM T N x hx) σ.sh (fun _ => 0)) (fun _ => 0) (sk x k) = 0
        rw [dockH_other _ _ _ _ (w6ne k (by omega) (by omega))]
        have e : sk x k = tfM T N x hx (Fin.castAdd T.x ⟨k.val - 131, by omega⟩) :=
          Fin.ext (by rw [sk_val, tfM_val]; simp only [Fin.val_castAdd, tfV]; split_ifs <;> omega)
        rw [e, dockH_slot _ (tfM_inj T N x hx)]
  · intro k h0 hk
    refine ⟨?_, ?_⟩
    · show install (w6M T N x hx) (install (tfM T N x hx) σ.st _) _ (sk x k) = _
      rw [install_other _ _ _ _ (w6ne k h0 (by omega)), install_other _ _ _ _ (tfne k h0 (by omega))]
    · show dockH (w6M T N x hx) (dockH (tfM T N x hx) σ.sh _) _ (sk x k) = _
      rw [dockH_other _ _ _ _ (w6ne k h0 (by omega)), dockH_other _ _ _ _ (tfne k h0 (by omega))]
  · intro k
    show install (w6M T N x hx) _ _ (w6M T N x hx (Fin.castAdd N.x ⟨k.val + 3, _⟩)) = _
    rw [install_slot _ (w6M_inj T N x hx), Fin.addCases_left]
    have hk := k.isLt
    have h20 : (⟨k.val + 3, by omega⟩ : Fin 21).val < 20 := by simp; omega
    show PrimThrW.Nums3.nums3OutPorts _ _ _ _ _ ⟨k.val + 3, _⟩ = _
    unfold PrimThrW.Nums3.nums3OutPorts
    rw [dif_pos h20]
    unfold PrimThrW.NumsP.numsOutPorts
    have a0 : (k.val + 3) ≠ 0 := by omega
    have a1 : (k.val + 3) ≠ 1 := by omega
    have a2 : (k.val + 3) ≠ 2 := by omega
    have a3 : k.val + 3 < 17 := by omega
    simp only [a0, a1, a2, a3, if_false, dif_pos]
    have e : (⟨k.val + 3 - 3, by omega⟩ : Fin 14) = k := Fin.ext (by simp)
    rw [e]
  · intro hz i
    show dockH (w6M T N x hx) (dockH (tfM T N x hx) σ.sh (fun _ => 0)) (fun _ => 0) i = 0
    unfold dockH
    split
    · rfl
    · split
      · rfl
      · exact hz i

end Dock2

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
