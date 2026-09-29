import Proof.Wire_3_5.FinalPass.S5TLay2

/-! # S5-THR, part 23: the THR numbers on W6's block (P3:2543-2558, 2596-2599, 2150-2157)

The THR path's first docks on the THR half's layout: the fill count `1^{W_p}` copied from the power `xs j₀`
(`plainCopy`), the prep (`p0_dock`: `1^{|carriers|}`, `1^{cap_T}`, `1^V`, `V = W_p + (n+1)^{26}`), then W6
(`w6_dock`: the THR numbers in unary on its ports `3 … 16`, the primes on slot `13`, the level records on port `18`,
the modulus word on port `19`).

* `updS_st_in`, `updS_st_out`, `updS_sh0` (a docked run's exit state, read off);
* `chainAM`, `chainACost`, **`chainA_spec`**.

Paper quantities of the main type: the THR call's numbers `thrNumVals` (`|𝒢|`, `K`, the cutoff, `τ₀`, the fixed
hash's `M, A, B_*, J, t, e, ℓ₀, p`), THR slot `13` (the primes up to the cutoff). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS sTape_val)
open NearCubicWires.WireExponent3_5.PrimThrW.Nums3 (nums3InPorts nums3OutPorts)
open NearCubicWires.SupplierPipeline

section Upd
variable {ns nr t : ℕ}

theorem updS_st_in (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (hout : Fin t → ℕ) (tout : Fin t → List Bool) (j : Fin t) : (updS tmap σ hout tout).st (tmap j) = tout j :=
  install_slot _ hinj _ _ j

theorem updS_st_out (tmap : Fin t → Fin (ns + 1)) (σ : WState ns nr) (hout : Fin t → ℕ) (tout : Fin t → List Bool)
    (i : Fin (ns + 1)) (hi : ∀ j, tmap j ≠ i) : (updS tmap σ hout tout).st i = σ.st i :=
  install_other _ _ _ _ hi

theorem updS_sh0 (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (tout : Fin t → List Bool) (hsh : ∀ i, σ.sh i = 0) : ∀ i, (updS tmap σ (fun _ => 0) tout).sh i = 0 := by
  intro i
  show dockH tmap σ.sh (fun _ => 0) i = 0
  by_cases hi : ∃ j, tmap j = i
  · obtain ⟨j, rfl⟩ := hi; rw [dockH_slot _ hinj]
  · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩), hsh]

end Upd

section ChainA
variable (D xt : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (cap : ℕ)

/-- The first docks' machine: the fill count, the prep, W6. -/
noncomputable def chainAM (l : Literals) (cr j0 : ℕ) :=
  Composition.machine (Composition.machine
    (plainCopy (xsN D (PrimT.W6.numsW6 alg Dexp).x xt j0) (sMisc D (PrimT.W6.numsW6 alg Dexp).x xt 0)
      : WM (nsL D (PrimT.W6.numsW6 alg Dexp).x xt) nrL).toProg.compile
    (RecoveryFocus.machine (fun j => sTape (nr := nrL) (p0Map D (PrimT.W6.numsW6 alg Dexp).x xt j))
      (PrimT.TS4.p0M cr (gateCParams1 l).ζ (gateCδ1 l) (gateCap l))))
    (RecoveryFocus.machine (fun j => sTape (nr := nrL) (w6Map D (PrimT.W6.numsW6 alg Dexp).x xt j))
      (PrimT.W6.numsW6 alg Dexp).M)

/-- The first docks' cost. -/
noncomputable def chainACost (l : Literals) (cr n a nc Wp : ℕ) : ℕ :=
  12 * Wp + 7 + 1 + (2 * PrimT.TS4.p0StageCost n cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) a nc
    Wp Wp + 2) + 1 + (PrimT.W6.numsW6 alg Dexp).cost (n + (Wp + (n + 1) ^ 26) + PrimT.TS4.capTL l cr n)

theorem chainA_spec (l : Literals) (cr : ℕ) (σ : WState (nsL D (PrimT.W6.numsW6 alg Dexp).x xt) nrL)
    (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (cc : List ℕ)
    (tl : List Bool) (j0 Wp : ℕ) (hj0 : j0 ≤ D)
    (hIn : σ.st (sIn D _ xt) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) cc tl))
    (hx : σ.st (xsN D _ xt j0) = sent Wp)
    (hbl : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x xt + 1),
      (1 ≤ i.val ∧ i.val ≤ 8) ∨ (13 + D ≤ i.val ∧ i.val ≠ 21 + D) → σ.st i = [])
    (hsh : ∀ i, σ.sh i = 0)
    (hKb : ∀ c ∈ PrimAsm.ReqBridge.thrCodes Cs, natBitLength c ≤ Wp) (ha : a' ≤ 4) (hnc : cc.length ≤ 2)
    (hN : PrimT.TS4.needT l cr P.n ≤ 2 * Wp + 2) (hn : 1 ≤ P.n) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (hcap1 : 1 ≤ PrimT.TS4.capTL l cr P.n) (hok : PrimThrW.TopFront2.TF2Ok Cs cc (Wp + (P.n + 1) ^ 26))
    (hneed : (PrimT.W6.numsW6 alg Dexp).need (P.n + PrimT.TS4.capTL l cr P.n) ≤ Wp + (P.n + 1) ^ 26) :
    ∃ σ3, Step (chainAM D xt alg Dexp l cr j0)
        (chainACost alg Dexp l cr P.n (PrimAsm.ReqBridge.thrCodes Cs).length cc.length Wp)
        (wenc cap σ).H (wenc cap σ).A (wenc cap σ3).H (wenc cap σ3).A ∧
      σ3.st (sIn D _ xt) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) cc tl) ∧
      (∀ (j : ℕ) (hj : j < 21), σ3.st (w6Map D _ xt ⟨j, by omega⟩) =
        nums3OutPorts (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) cc tl) cc.length
          (PrimT.TS4.capTL l cr P.n) (Wp + (P.n + 1) ^ 26)
          (PrimThrW.Joins.thrNumVals P Cs alg Dexp cc.length (PrimT.TS4.capTL l cr P.n)) ⟨j, hj⟩) ∧
      (∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x xt + 1), ((1 ≤ i.val ∧ i.val ≤ 5) ∨
        (7 ≤ i.val ∧ i.val < 13 + D) ∨ (13 + D < i.val ∧ i.val < 45 + D) ∨
        (w6B D + (21 + (PrimT.W6.numsW6 alg Dexp).x) ≤ i.val)) → σ3.st i = σ.st i) ∧
      (∀ i, σ3.sh i = 0) ∧ σ3.val = σ.val := by
  have hge := nsL_ge D (PrimT.W6.numsW6 alg Dexp).x xt
  have hS0 : (sIn D (PrimT.W6.numsW6 alg Dexp).x xt).val = 0 := rfl
  have hM0 : (sMisc D (PrimT.W6.numsW6 alg Dexp).x xt 0).val = 13 + D := rfl
  have hxv := xsN_val D (PrimT.W6.numsW6 alg Dexp).x xt j0 hj0
  -- 1: the fill count
  have e1 := plainCopy_spec cap (xsN D (PrimT.W6.numsW6 alg Dexp).x xt j0) (sMisc D (PrimT.W6.numsW6 alg Dexp).x xt 0)
    (fun h => by have := congrArg Fin.val h; rw [hxv, hM0] at this; omega) Wp σ hx (hsh _)
    (hbl _ (Or.inr ⟨by rw [hM0], by rw [hM0]; omega⟩)) (hsh _)
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.sets (sMisc D (PrimT.W6.numsW6 alg Dexp).x xt 0) (List.replicate Wp true) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have st1 : ∀ i, i.val ≠ 13 + D → σ1.st i = σ.st i := fun i hi => by
    rw [hσ1]; simp only [WState.sets_st]; rw [Function.update_of_ne (fun h => hi (by rw [h, hM0]))]
  have sh1 : ∀ i, σ1.sh i = 0 := fun i => by rw [hσ1]; exact hsh i
  -- 2: the prep
  obtain ⟨tout, m, s2, f0, _, f3, f4, f5⟩ := p0_dock D (PrimT.W6.numsW6 alg Dexp).x xt cap l cr σ1 P.n (PrimAsm.ReqBridge.thrCodes Cs) cc tl Wp
    (by rw [st1 _ (by rw [hS0]; omega), hIn]) (by rw [hσ1]; simp)
    (fun j h0 h2 => by
      have hv : (p0Map D (PrimT.W6.numsW6 alg Dexp).x xt j).val = p0B D + j.val := by rw [p0Map_val]; simp [h0, h2]
      rw [st1 _ (by rw [hv]; unfold p0B; omega)]
      exact hbl _ (Or.inr ⟨by rw [hv]; unfold p0B; omega, by rw [hv]; unfold p0B; omega⟩))
    sh1 hKb (by simpa [PrimAsm.ReqBridge.thrCodes] using ha) hnc hN
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = updS (p0Map D (PrimT.W6.numsW6 alg Dexp).x xt) σ1 (fun _ => 0) (Fin.addCases (m := LNS 0 + 2 + LNR) (n := 1)
      (motive := fun _ => List Bool) tout (fun _ : Fin 1 => List.replicate m false)) := ⟨_, rfl⟩
  rw [← hσ2] at s2
  have hlt : ∀ k, k < LNS 0 + 2 + LNR → p0B D + k < nsL D (PrimT.W6.numsW6 alg Dexp).x xt + 1 := fun k hk => by
    unfold LNS LNR at hk; unfold p0B; omega
  have p0v : ∀ (k : ℕ) (hk : k < LNS 0 + 2 + LNR) (h0 : k ≠ 0) (h2 : k ≠ 2),
      σ2.st ⟨p0B D + k, hlt k hk⟩ = tout ⟨k, hk⟩ := by
    intro k hk h0 h2
    have e : (⟨p0B D + k, hlt k hk⟩ : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x xt + 1)) =
        p0Map D (PrimT.W6.numsW6 alg Dexp).x xt (Fin.castAdd 1 ⟨k, hk⟩) := by
      apply Fin.ext; rw [p0Map_val]; simp [h0, h2]
    rw [e, hσ2, updS_st_in _ (p0Map_inj D (PrimT.W6.numsW6 alg Dexp).x xt), Fin.addCases_left]
  have p0o : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x xt + 1), i.val ≠ 0 → i.val ≠ 13 + D → (i.val < 45 + D ∨ 720 + D ≤ i.val) →
      σ2.st i = σ1.st i := fun i h0 h1 h2 => by
    rw [hσ2]
    refine updS_st_out _ _ _ _ i (fun j h => ?_)
    have hv := congrArg Fin.val h; rw [p0Map_val] at hv; unfold p0B at hv
    have hj : j.val < 675 := j.isLt; split_ifs at hv <;> omega
  have hsIn2 : σ2.st (sIn D (PrimT.W6.numsW6 alg Dexp).x xt) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) cc tl) := by
    have e : sIn D (PrimT.W6.numsW6 alg Dexp).x xt = p0Map D (PrimT.W6.numsW6 alg Dexp).x xt (Fin.castAdd 1 ⟨0, by decide⟩) := by
      apply Fin.ext; rw [p0Map_val]; simp [hS0]
    rw [e, hσ2, updS_st_in _ (p0Map_inj D (PrimT.W6.numsW6 alg Dexp).x xt), Fin.addCases_left]; exact f0
  have sh2 : ∀ i, σ2.sh i = 0 := by rw [hσ2]; exact updS_sh0 _ (p0Map_inj D (PrimT.W6.numsW6 alg Dexp).x xt) σ1 _ sh1
  -- 3: W6
  have w6v : ∀ (j : ℕ) (hj : j < 21 + (PrimT.W6.numsW6 alg Dexp).x), (w6Map D (PrimT.W6.numsW6 alg Dexp).x xt ⟨j, hj⟩).val = if j = 0 then 0 else if j = 1 then p0B D + 4
      else if j = 2 then p0B D + 5 else if j = 20 then p0B D + 6 else if j = 17 then 6 else w6B D + j :=
    fun j hj => w6Map_val D (PrimT.W6.numsW6 alg Dexp).x xt ⟨j, hj⟩
  obtain ⟨J, _, s3⟩ := w6_dock D xt cap alg Dexp σ2 P Cs cc tl cc.length (PrimT.TS4.capTL l cr P.n)
    (Wp + (P.n + 1) ^ 26)
    (by rw [show w6Map D (PrimT.W6.numsW6 alg Dexp).x xt ⟨0, by omega⟩ = sIn D (PrimT.W6.numsW6 alg Dexp).x xt from Fin.ext (by rw [w6v]; rfl)]; exact hsIn2)
    (by rw [show w6Map D (PrimT.W6.numsW6 alg Dexp).x xt ⟨1, by omega⟩ = ⟨p0B D + 4, hlt 4 (by unfold LNS LNR; omega)⟩
          from Fin.ext (by rw [w6v]; rfl), p0v 4 (by unfold LNS LNR; omega) (by omega) (by omega)]; exact f3)
    (by rw [show w6Map D (PrimT.W6.numsW6 alg Dexp).x xt ⟨2, by omega⟩ = ⟨p0B D + 5, hlt 5 (by unfold LNS LNR; omega)⟩
          from Fin.ext (by rw [w6v]; rfl), p0v 5 (by unfold LNS LNR; omega) (by omega) (by omega)]; exact f4)
    (by rw [show w6Map D (PrimT.W6.numsW6 alg Dexp).x xt ⟨20, by omega⟩ = ⟨p0B D + 6, hlt 6 (by unfold LNS LNR; omega)⟩
          from Fin.ext (by rw [w6v]; rfl), p0v 6 (by unfold LNS LNR; omega) (by omega) (by omega)]; exact f5)
    (fun j h0 h1 h2 h20 => by
      have hv := w6Map_val D (PrimT.W6.numsW6 alg Dexp).x xt j
      rw [if_neg h0, if_neg h1, if_neg h2, if_neg h20] at hv
      rw [p0o _ (by rw [hv]; split_ifs <;> omega) (by rw [hv]; unfold w6B p0B; split_ifs <;> omega)
        (by rw [hv]; unfold w6B p0B; split_ifs <;> omega), st1 _ (by rw [hv]; unfold w6B p0B; split_ifs <;> omega)]
      refine hbl _ ?_
      rw [hv]; unfold w6B p0B; have := j.isLt; split_ifs <;> omega)
    sh2 hn ha hd hnc hcap1 hok hneed
  refine ⟨_, Step.seq (Step.seq (Exec.step (WExec.exec cap e1)) s2) s3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show sIn D (PrimT.W6.numsW6 alg Dexp).x xt = w6Map D (PrimT.W6.numsW6 alg Dexp).x xt (Fin.castAdd (PrimT.W6.numsW6 alg Dexp).x ⟨0, by decide⟩) from Fin.ext (by rw [w6Map_val]; rfl),
      updS_st_in _ (w6Map_inj D (PrimT.W6.numsW6 alg Dexp).x xt), Fin.addCases_left, PrimThrW.Nums3.nums3Out_low _ _ _ _ _ ⟨0, by decide⟩]
    rfl
  · intro j hj
    rw [show (⟨j, by omega⟩ : Fin (21 + (PrimT.W6.numsW6 alg Dexp).x)) = Fin.castAdd (PrimT.W6.numsW6 alg Dexp).x ⟨j, hj⟩ from rfl, updS_st_in _ (w6Map_inj D (PrimT.W6.numsW6 alg Dexp).x xt),
      Fin.addCases_left]
  · intro i hi
    rw [updS_st_out _ _ _ _ i (fun j h => by
        have hv := congrArg Fin.val h; rw [w6Map_val] at hv; unfold w6B p0B at hv hi
        have hj := j.isLt; split_ifs at hv <;> omega),
      p0o i (by unfold w6B p0B at hi; omega) (by unfold w6B p0B at hi; omega) (by unfold w6B p0B at hi; omega),
      st1 i (by unfold w6B p0B at hi; omega)]
  · exact updS_sh0 _ (w6Map_inj D (PrimT.W6.numsW6 alg Dexp).x xt) σ2 _ sh2
  · show σ2.val = σ.val
    rw [hσ2, hσ1]; rfl

end ChainA

end NearCubicWires.WireExponent3_5.FinalPass.S5T
