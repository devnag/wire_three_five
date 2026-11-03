import W3.Front.Layout

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP

namespace W3.NearCubicWires.RepairSource.Outer3.Front

/-- `L_ν = ν^{G+2}`, the evaluator's guards and phase K's register capacity and cost. -/
def lenF (G ν : ℕ) : ℕ := ν ^ (G + 2)
def lbF (G ν : ℕ) : ℕ := (lenF G ν + 4).size
def lpF (ν : ℕ) : ℕ := ν.size

def capKF (G ν : ℕ) : ℕ :=
  4 * 2 ^ ν + 4 * lenF G ν * lenF G ν + 10 * lenF G ν + 8 * (lbF G ν + lpF ν) + 16 * 2 ^ (lbF G ν + lpF ν + 1) +
    10 * ν + 300

def costKF (G ν dl : ℕ) : ℕ :=
  18 * 2 ^ ν + 3 + 60 * (ν + 1) ^ 2 + 100 * (G + 3) * (lenF G ν + ν + 1) ^ 2 + 16 +
    (lbF G ν * (12 * (lenF G ν + 4) + 30) + 1) + Succinct.checkCost dl (lbF G ν) (lpF ν) (2 ^ ν) + 10

theorem phKF_exec (ta th G ν : ℕ) (z : BitInput (2 ^ ν)) {m : ℕ} (Bs : BooleanCircuit m) (cap : ℕ)
    (hν1 : 1 ≤ ν) (hfit : Outer.SrcFits G ν Bs) (hcap : capKF G ν ≤ cap) (σ : WState (nsF ta th) nrW)
    (hS : σ.st (sS ta th) = PCPPNative.descriptor Bs) (hSh : σ.sh (sS ta th) = 0)
    (hZ : σ.st (sZ ta th) = RepairOrdinary.frame (List.ofFn z)) (hZh : σ.sh (sZ ta th) = 0)
    (hPT : σ.st (sPT ta th) = []) (hPTh : σ.sh (sPT ta th) = 0) (hVV : σ.st (sVV ta th) = [])
    (hVVh : σ.sh (sVV ta th) = 0) (hTT : σ.st (sTT ta th) = []) (hTTh : σ.sh (sTT ta th) = 0)
    (hFL : σ.st (sFL ta th) = [true]) (hFLh : σ.sh (sFL ta th) = 0)
    (hN : σ.val rN = 2 ^ ν) (hnu : σ.val rNu = ν)
    (hz : ∀ r : Fin nrW, 19 ≤ r.val → r ≠ rN → r ≠ rNu → σ.val r = 0) :
    ∃ τ, WXExec cap (phKF ta th G) σ τ (costKF G ν (PCPPNative.descriptor Bs).length) ∧
      τ.st (sFL ta th) = [decide (Outer.Check ν z Bs)] ∧
      ∀ i, i ≠ sPT ta th → i ≠ sVV ta th → i ≠ sTT ta th → i ≠ sFL ta th → τ.st i = σ.st i := by
  classical
  have hcap' := hcap
  unfold capKF lbF lpF at hcap'
  set L := lenF G ν with hLdef
  have hLL : 4 * L * L = 4 * (L * L) := by ring
  have hLL2 : L ≤ L * L := Nat.le_mul_self L
  have hνN : ν < 2 ^ ν := Nat.lt_two_pow_self
  have hval : ∀ r : Fin nrW, 19 ≤ r.val → r ≠ rN → r ≠ rNu → σ.val r = 0 := hz
  have hEK0 : ∀ v, σ.val (EK v) = 0 := fun v =>
    hval _ (by have := (EK_val v).1; omega) (EK_ne v _ (by left; decide)) (EK_ne v _ (by right; decide))
  -- 1. `nN := N`
  have e1 := Codec.dupR_spec cap rN (EK .nN) dS (EK_ne _ _ (by left; decide)).symm (by decide)
    (EK_ne _ _ (by left; decide)) σ (hval _ (by decide) (by decide) (by decide)) (by rw [hN, hEK0]; omega)
  rw [hEK0, hN, Nat.zero_add] at e1
  set σ1 := σ.setv (EK .nN) (2 ^ ν) with hσ1
  -- 2. `lp := size ν`
  have hlp_ne : ∀ r ∈ ([rNu, pT1, pH, pB, dS] : List (Fin nrW)), EK (.e .lp) ≠ r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact EK_ne _ _ (by first | (left; decide) | (right; decide))
  have e2 := sizeNuW_exec (cap := cap) (EK (.e .lp)) hlp_ne ν σ1
    (by rw [hσ1, upd_ne _ _ (EK_ne _ _ (by right; decide)).symm]; exact hnu)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          (rw [hσ1, upd_ne _ _ (EK_ne _ _ (by first | (left; decide) | (right; decide))).symm]
           exact hval _ (by decide) (by decide) (by decide)))
    (by rw [hσ1, upd_ne _ _ (EK_inj.ne (by decide)), hEK0]) (by omega)
  set σ2 := σ1.setv (EK (.e .lp)) ν.size with hσ2
  have c2 : ∀ r : Fin nrW, (r.val < 60 ∨ 105 ≤ r.val) → σ2.val r = σ.val r := fun r hr => by
    rw [hσ2, upd_ne _ _ (EK_ne _ _ hr).symm, hσ1, upd_ne _ _ (EK_ne _ _ hr).symm]
  -- 3. `pX2 := L`, 4. `+ 4`
  have hY : ∀ r ∈ ([rNu, pX1, pX3, pH, pB, dS] : List (Fin nrW)), pX2 ≠ r := by decide
  have e3 := powNuW_exec (cap := cap) (G + 2) pX2 hY ν hν1 σ2 (by rw [c2 _ (by right; decide)]; exact hnu)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
          (rw [c2 _ (by first | (left; decide) | (right; decide))]; exact hval _ (by decide) (by decide) (by decide)))
    (by rw [c2 _ (by right; decide)]; exact hval _ (by decide) (by decide) (by decide)) (by
      show 2 * L + L * L + ν + 2 ≤ cap; omega)
  set σ3 := σ2.setv pX2 L with hσ3
  have e4 := NodeEmit.incN_spec (cap := cap) pX2 4 σ3 (by simp [hσ3]; omega)
  rw [show σ3.setv pX2 (σ3.val pX2 + 4) = σ2.setv pX2 (L + 4) by simp [hσ3, LitDecode.setv_setv]] at e4
  set σ4 := σ2.setv pX2 (L + 4) with hσ4
  -- 5. `lb := size (L + 4)`
  have hnd : ([pX2, pH, pB, EK (.e .lb)] : List (Fin nrW)).Nodup := by
    have h1 : pX2 ≠ EK (.e .lb) := (EK_ne _ _ (by right; decide)).symm
    have h2 : pH ≠ EK (.e .lb) := (EK_ne _ _ (by right; decide)).symm
    have h3 : pB ≠ EK (.e .lb) := (EK_ne _ _ (by right; decide)).symm
    have d1 : pX2 ≠ pH := by decide
    have d2 : pX2 ≠ pB := by decide
    have d3 : pH ≠ pB := by decide
    simp [List.nodup_cons, h1, h2, h3, d1, d2, d3]
  have e5 := Recovery.HTParts.sizeW_exec (cap := cap) (X := pX2) (H := pH) (B := pB) (C := EK (.e .lb))
    hnd (L + 4) (by omega) (L + 4) σ4 le_rfl (by simp [hσ4])
    (by rw [hσ4, upd_ne _ _ (by decide), c2 _ (by right; decide)]; exact hval _ (by decide) (by decide) (by decide))
    (by rw [hσ4, upd_ne _ _ (by decide), c2 _ (by right; decide)]; exact hval _ (by decide) (by decide) (by decide))
    (by
      rw [hσ4, upd_ne _ _ (EK_ne _ _ (by right; decide)), hσ2, upd_ne _ _ (EK_inj.ne (by decide)), hσ1,
        upd_ne _ _ (EK_inj.ne (by decide)), hEK0, Nat.zero_add]
      have := size_le_self (L + 4); omega)
  have hlb0 : σ4.val (EK (.e .lb)) = 0 := by
    rw [hσ4, upd_ne _ _ (EK_ne _ _ (by right; decide)), hσ2, upd_ne _ _ (EK_inj.ne (by decide)), hσ1,
      upd_ne _ _ (EK_inj.ne (by decide)), hEK0]
  rw [hlb0, Nat.zero_add] at e5
  set σ5 := (σ4.setv pX2 0).setv (EK (.e .lb)) (L + 4).size with hσ5
  -- the state before CHECK
  have st5 : σ5.st = σ.st := by simp only [hσ5, hσ4, hσ2, hσ1, WState.setv_st]
  have sh5 : σ5.sh = σ.sh := by simp only [hσ5, hσ4, hσ2, hσ1, WState.setv_sh]
  have nX : ∀ v, EK v ≠ pX2 := fun v => EK_ne v _ (by right; decide)
  have z5 : ∀ v, v ≠ .nN → v ≠ .e .lb → v ≠ .e .lp → σ5.val (EK v) = 0 := fun v h1 h2 h3 => by
    rw [hσ5, upd_ne _ _ (EK_inj.ne h2), upd_ne _ _ (nX v), hσ4, upd_ne _ _ (nX v), hσ2,
      upd_ne _ _ (EK_inj.ne h3), hσ1, upd_ne _ _ (EK_inj.ne h1), hEK0]
  have vN : σ5.val (EK .nN) = 2 ^ ν := by
    rw [hσ5, upd_ne _ _ (EK_inj.ne (by decide)), upd_ne _ _ (nX _), hσ4, upd_ne _ _ (nX _),
      hσ2, upd_ne _ _ (EK_inj.ne (by decide)), hσ1]; simp
  have vlp : σ5.val (EK (.e .lp)) = ν.size := by
    rw [hσ5, upd_ne _ _ (EK_inj.ne (by decide)), upd_ne _ _ (nX _), hσ4, upd_ne _ _ (nX _), hσ2]; simp
  have vlb : σ5.val (EK (.e .lb)) = (L + 4).size := by rw [hσ5]; simp
  -- 6. CHECK
  have hrd : Succinct.EvalReady (sS ta th) (sPT ta th) (sVV ta th) EK (PCPPNative.descriptor Bs ++ [])
      (L + 4).size ν.size σ5 :=
    { st := by rw [st5, hS, List.append_nil]
      sh := by rw [sh5]; exact hSh
      vv := ⟨0, by rw [st5, hVV]; rfl⟩
      vvh := by rw [sh5]; exact hVVh
      ph := by rw [sh5]; exact hPTh
      lb := vlb
      lp := vlp
      z := fun r hr => z5 _ (by simp) (by intro h; injection h with h; subst h; simp [Succinct.scratchE] at hr)
        (by intro h; injection h with h; subst h; simp [Succinct.scratchE] at hr)
      s := z5 _ (by simp) (by simp) (by simp)
      j := z5 _ (by simp) (by simp) (by simp)
      cd := z5 _ (by simp) (by simp) (by simp) }
  have hnd5 : ([sS ta th, sPT ta th, sVV ta th, sTT ta th, sZ ta th] : List (Fin (nsF ta th + 1))).Nodup := by
    simp [List.nodup_cons, Fin.ext_iff]
  have hdl : (PCPPNative.descriptor Bs).length ≤ L := hfit
  have hs : Bs.nodes.length + 5 ≤ 2 ^ (L + 4).size := by
    have := Nat.lt_size_self (L + 4); have := nodes_le_descriptor Bs; omega
  obtain ⟨τ6, e6, hf1, hf2, _, hse6, _, _⟩ := Succinct.checkW_check cap (sS ta th) (sPT ta th) (sVV ta th) (sTT ta th)
    (sZ ta th) hnd5 EK EK_inj σ5 Bs [] ν (L + 4).size ν.size z hrd (by rw [st5]; exact hPT) (by rw [st5]; exact hTT)
    (by rw [sh5]; exact hTTh) vN
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact z5 _ (by simp) (by simp) (by simp))
    (by rw [st5]; exact hZ) (by rw [sh5]; exact hZh) le_rfl hs (Nat.lt_size_self ν) (by
      simp only [List.append_nil]
      have := size_le_self (L + 4)
      have h2 : 2 ^ ((L + 4).size + ν.size + 1) = 2 ^ (lbF G ν + lpF ν + 1) := rfl
      omega)
  have nPT : ∀ i, i ∉ [sPT ta th, sVV ta th, sTT ta th] → τ6.st i = σ.st i ∧ τ6.sh i = σ.sh i := fun i hi => by
    rw [(hse6.1 i hi).1, (hse6.1 i hi).2, st5, sh5]; exact ⟨rfl, rfl⟩
  have memFL : sFL ta th ∉ [sPT ta th, sVV ta th, sTT ta th] := by simp [Fin.ext_iff]
  have FL6 : τ6.st (sFL ta th) = [true] := by rw [(nPT _ memFL).1]; exact hFL
  have FLh6 : τ6.sh (sFL ta th) = 0 := by rw [(nPT _ memFL).2]; exact hFLh
  -- 7. the flag
  set fv := τ6.val (EK .f) with hfv
  have e7 : WXExec cap (.ifr (EK .f) WMX.skip (WMX.wr (sFL ta th) false)) τ6
      (τ6.sets (sFL ta th) [decide (Outer.Check ν z Bs)]) 2 := by
    by_cases hc : Outer.Check ν z Bs
    · have h1 : fv = 1 := hf2.2 ((Outer.check_iff_checkAt ν z Bs).mp hc)
      refine WXExec.cast cap (WXExec.ifrT (by rw [← hfv, h1]; omega) (WXExec.skip cap τ6)) ?_ (by omega)
      apply WState.eq <;> try rfl
      funext i; by_cases hi : i = sFL ta th
      · subst hi; simp [FL6, hc]
      · simp [Function.update_of_ne hi]
    · have h0 : fv = 0 := by have := mt hf2.1 (fun h => hc ((Outer.check_iff_checkAt ν z Bs).mpr h)); omega
      refine WXExec.cast cap (WXExec.ifrF (by rw [← hfv, h0]) (WXExec.wr (cap := cap) (sFL ta th) false τ6)) ?_
        (by omega)
      rw [FL6, FLh6]; simp [hc]; rfl
  have hpL : ν ^ (G + 2) = L := rfl
  rw [hpL] at e3
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
      (WXExec.seq e5 (WXExec.seq (WXExec.wm e6) e7)))))) ?_, by simp, ?_⟩
  · unfold costKF lbF lpF
    simp only [List.append_nil, ← hLdef]
    rw [show G + 2 + 1 = G + 3 from rfl]
    omega
  · intro i h1 h2 h3 h4
    rw [WState.sets_st, Function.update_of_ne h4]
    exact (nPT i (by simp [h1, h2, h3])).1

end W3.NearCubicWires.RepairSource.Outer3.Front
