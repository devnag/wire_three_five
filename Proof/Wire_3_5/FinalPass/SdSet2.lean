import Proof.Wire_3_5.FinalPass.SdSet1

/-! # S4 (the seeds phase), part 29: the setup's register half, on the body (P3:3170-3178)

The body's setup registers: the prep's `sRp k = 10 + k` and the temporaries `sK, sT, sOP, sC, sH k, sTT k, sX`
(`40 … 48`), all in the THR evaluator's scratch (cleared by the stream half). **`setR`**: the star parameters into
the center counters `ctrR 0 … 4` and the decoder's digits `frD 0 … 3` (`cpJobs cps`), the carriers' presence flags
`rP k` (`flagW` of the carrier count), each carrier's weight width `H k` (`mH` on its mask table `tG k`), the two
tables' lengths less one (`mT` on the tables word `tTW`, then two decrements). **`setR_spec`**: the state
`setROut σ H₀ H₁ T₀ T₁`.

Paper quantity of the main type: the seeds phase's static numbers (star parameters, digits, presence flags, weight
widths, tables' lengths). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.PrimAsm

section Gen
variable {ns nr : ℕ} (cap : ℕ)

theorem mH_to (s : Fin (ns + 1)) (K C : Fin nr) (hKC : K ≠ C) (σ : WState ns nr) (H : ℕ)
    (hG : (∃ w rest, σ.st s = true :: (frameP w ++ false :: rest) ∧ w.length = H) ∨
      (readTapeBit (σ.st s) 0 = false ∧ H = 0))
    (hsh : σ.sh s = 0) (hC : σ.val C = 0) (hK : σ.val K = 0) (hc : 3 * H + 2 ≤ cap) :
    ∃ m, WExec cap (mH s K C) σ (σ.setv K H) m ∧ m ≤ 30 * H + 20 := by
  rcases hG with ⟨w, rest, hst, hw⟩ | ⟨hb, hH⟩
  · have e := mH_true cap s K C hKC w rest σ hst hsh hC (by rw [hK]; omega)
    rw [hK, Nat.zero_add, hw] at e
    exact ⟨_, e, by omega⟩
  · have e := mH_false cap s K C σ hb hsh hC
    refine ⟨3, ?_, by omega⟩
    rw [hH, ← hK, wsetv_same]
    exact e

end Gen

section Body
variable {nw nn nsc nrs : ℕ}

theorem brg_iff {a b : ℕ} (ha : a < 220) (hb : b < 220) :
    (brg a ha : Fin (bnr nn nrs)) = brg b hb ↔ a = b := by
  simp [brg, Fin.ext_iff]

/-- The prep's registers on the body: `10 + k`. -/
def sRp : Fin 30 ↪ Fin (bnr nn nrs) :=
  ⟨fun k => brg (10 + k.val) (by omega), fun a b h => Fin.ext (by
    have := congrArg Fin.val h
    simp [brg] at this
    omega)⟩

def sK : Fin (bnr nn nrs) := brg 40 (by omega)
def sT : Fin (bnr nn nrs) := brg 41 (by omega)
def sOP : Fin (bnr nn nrs) := brg 42 (by omega)
def sC : Fin (bnr nn nrs) := brg 43 (by omega)
def sH (k : Fin 2) : Fin (bnr nn nrs) := brg (44 + k.val) (by omega)
def sTT (k : Fin 2) : Fin (bnr nn nrs) := brg (46 + k.val) (by omega)
def sX : Fin (bnr nn nrs) := brg 48 (by omega)

theorem sRp_b (k : Fin 30) : (sRp k : Fin (bnr nn nrs)) = brg (10 + k.val) (by omega) := rfl
theorem ctrR_b (i : Fin 26) : (ctrR i : Fin (bnr nn nrs)) = brg (168 + i.val) (by omega) := rfl
theorem frD_b (q : Fin 12) : (frD q : Fin (bnr nn nrs)) = brg (156 + q.val) (by omega) := rfl
theorem rP_b (k : Fin 2) : (rP k : Fin (bnr nn nrs)) = brg (120 + k.val) (by omega) := rfl

/-- The copies: `ctrR 0 … 4 := b, s, r/2, hL, n − rb − hL`; `frD 0 … 3 := s, b, r/2, n − rb`. -/
def cps : List (Fin (bnr nn nrs) × Fin (bnr nn nrs)) :=
  [(sRp 1, ctrR 0), (sRp 2, ctrR 1), (sRp 3, ctrR 2), (sRp 4, ctrR 3), (sRp 5, ctrR 4), (sRp 2, frD 0),
    (sRp 1, frD 1), (sRp 3, frD 2), (sRp 6, frD 3)]

/-- The registers the register half needs at `0`. -/
def setZ : List (Fin (bnr nn nrs)) :=
  [ctrR 0, ctrR 1, ctrR 2, ctrR 3, ctrR 4, frD 0, frD 1, frD 2, frD 3, rP 0, rP 1, sK, sT, sOP, sC, sH 0, sH 1,
    sTT 0, sTT 1, sX]

theorem cps_nodup : (cps.map Prod.snd : List (Fin (bnr nn nrs))).Nodup := by
  simp [cps, ctrR_b, frD_b, brg_iff]

theorem cps_sd : ∀ p ∈ (cps : List (Fin (bnr nn nrs) × Fin (bnr nn nrs))), ∀ p' ∈ cps, p.1 ≠ p'.2 := by
  simp [cps, sRp_b, ctrR_b, frD_b, brg_iff]

theorem notin_cps (q : Fin (bnr nn nrs)) (hq : q.val < 156 ∨ (159 < q.val ∧ q.val < 168) ∨ 172 < q.val) :
    q ∉ (cps.map Prod.snd : List (Fin (bnr nn nrs))) := by
  intro h
  simp only [cps, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h <;> (rw [h] at hq; simp [ctrR_b, frD_b, brg] at hq)

/-- The register half. -/
def setR : BP nw nn nsc nrs :=
  .seq (cpJobs sT cps) (.seq (flagW (sRp 12) sX sT (rP 0) (rP 1)) (.seq (mH (tG 0) (sH 0) sC)
    (.seq (mH (tG 1) (sH 1) sC) (.seq (mT tTW (sTT 0) sC (sTT 1)) (.seq (.dec (sTT 0)) (.dec (sTT 1)))))))

/-- The register half's exit. -/
def setROut (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) : BS nw nn nsc nrs :=
  ((((((((cpApply σ cps).setv (rP 0) (if 1 ≤ σ.val (sRp 12) then 1 else 0)).setv (rP 1)
    (if 2 ≤ σ.val (sRp 12) then 1 else 0)).setv (sH 0) H0).setv (sH 1) H1).setv (sTT 0) T0).setv (sTT 1) T1).setv
    (sTT 0) (T0 - 1)).setv (sTT 1) (T1 - 1)

/-- The register half's step bound. -/
def setRCost (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) : ℕ :=
  cpjCost σ cps + 21 * σ.val (sRp 12) + 30 + (30 * H0 + 20) + (30 * H1 + 20) + (30 * (T0 + T1) + 20) + 20

theorem setR_spec (cap : ℕ) (σ : BS nw nn nsc nrs) (H0 H1 : ℕ) (w0 w1 rest : List Bool)
    (hz : ∀ q ∈ (setZ : List (Fin (bnr nn nrs))), σ.val q = 0) (hv : ∀ k : Fin 30, σ.val (sRp k) ≤ cap)
    (hG0 : (∃ w rest, σ.st (tG 0) = true :: (frameP w ++ false :: rest) ∧ w.length = H0) ∨
      (readTapeBit (σ.st (tG 0)) 0 = false ∧ H0 = 0))
    (hG1 : (∃ w rest, σ.st (tG 1) = true :: (frameP w ++ false :: rest) ∧ w.length = H1) ∨
      (readTapeBit (σ.st (tG 1)) 0 = false ∧ H1 = 0))
    (hsG : ∀ k : Fin 2, σ.sh (tG k) = 0)
    (hTW : σ.st tTW = frameP w0 ++ false :: (frameP w1 ++ false :: rest)) (hsTW : σ.sh tTW = 0)
    (hc : 3 * H0 + 3 * H1 + 3 * w0.length + 3 * w1.length + 10 ≤ cap) :
    ∃ m, WExec cap setR σ (setROut σ H0 H1 w0.length w1.length) m ∧ m ≤ setRCost σ H0 H1 w0.length w1.length := by
  have z : ∀ q, q ∈ (setZ : List (Fin (bnr nn nrs))) → σ.val q = 0 := hz
  -- the copies
  have e1 := cpJobs_spec cap sT cps σ cps_nodup cps_sd (fun p hp => by
    simp only [cps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp [sRp_b, sT, brg_iff], by simp [ctrR_b, frD_b, sT, brg_iff], z _ (by simp [setZ]), hv _⟩)
    (z _ (by simp [setZ]))
  obtain ⟨σ1, g1⟩ : ∃ y : BS nw nn nsc nrs, y = cpApply σ cps := ⟨_, rfl⟩
  rw [← g1] at e1
  have v1 : ∀ q, q.val < 156 ∨ (159 < q.val ∧ q.val < 168) ∨ 172 < q.val → σ1.val q = σ.val q := fun q hq => by
    rw [g1]; exact cpApply_notin σ cps q (notin_cps q hq)
  have s1 : σ1.st = σ.st := by rw [g1]; exact cpApply_st σ cps
  have h1 : σ1.sh = σ.sh := by rw [g1]; exact cpApply_sh σ cps
  -- the flags
  obtain ⟨m2, e2, hm2⟩ := flagW_spec cap (sRp 12) sX sT (rP 0) (rP 1) (by simp [sRp_b, sX, brg_iff])
    (by simp [sRp_b, sT, brg_iff]) (by simp [sX, sT, brg_iff]) (by simp [rP_b, sX, brg_iff])
    (by simp [rP_b, sX, brg_iff]) (by simp [rP_b, brg_iff]) (by simp [rP_b, sRp_b, brg_iff])
    (by simp [rP_b, sRp_b, brg_iff]) σ1
    (by rw [v1 _ (by simp [sX, brg])]; exact z _ (by simp [setZ]))
    (by rw [v1 _ (by simp [sT, brg])]; exact z _ (by simp [setZ]))
    (by rw [v1 _ (by simp [rP_b, brg])]; exact z _ (by simp [setZ]))
    (by rw [v1 _ (by simp [rP_b, brg])]; exact z _ (by simp [setZ]))
    (by rw [v1 _ (by simp [sRp_b, brg])]; exact hv _) (by omega)
  rw [v1 (sRp 12) (by simp [sRp_b, brg])] at e2 hm2
  obtain ⟨σ2, g2⟩ : ∃ y : BS nw nn nsc nrs, y = (σ1.setv (rP 0) (if 1 ≤ σ.val (sRp 12) then 1 else 0)).setv (rP 1)
      (if 2 ≤ σ.val (sRp 12) then 1 else 0) := ⟨_, rfl⟩
  rw [← g2] at e2
  have v2 : ∀ q, q.val < 120 ∨ (121 < q.val ∧ q.val < 156) ∨ (159 < q.val ∧ q.val < 168) ∨ 172 < q.val →
      σ2.val q = σ.val q := fun q hq => by
    have n0 : q ≠ rP 0 := fun h => by rw [h] at hq; simp [rP_b, brg] at hq
    have n1 : q ≠ rP 1 := fun h => by rw [h] at hq; simp [rP_b, brg] at hq
    rw [g2, WState.setv_val, Function.update_of_ne n1, WState.setv_val, Function.update_of_ne n0, v1 q (by omega)]
  have s2 : σ2.st = σ.st := by rw [g2, ← s1]; rfl
  have h2 : σ2.sh = σ.sh := by rw [g2, ← h1]; rfl
  -- the weight widths
  obtain ⟨m3, e3, hm3⟩ := mH_to cap (tG 0) (sH 0) sC (by simp [sH, sC, brg_iff]) σ2 H0 (by rw [s2]; exact hG0)
    (by rw [h2]; exact hsG 0) (by rw [v2 _ (by simp [sC, brg])]; exact z _ (by simp [setZ]))
    (by rw [v2 _ (by simp [sH, brg])]; exact z _ (by simp [setZ])) (by omega)
  obtain ⟨m4, e4, hm4⟩ := mH_to cap (tG 1) (sH 1) sC (by simp [sH, sC, brg_iff]) (σ2.setv (sH 0) H0) H1
    (by simpa [s2] using hG1) (by simpa [h2] using hsG 1)
    (by rw [WState.setv_val, Function.update_of_ne (by simp [sH, sC, brg_iff]), v2 _ (by simp [sC, brg])]
        exact z _ (by simp [setZ]))
    (by rw [WState.setv_val, Function.update_of_ne (by simp [sH, brg_iff]), v2 _ (by simp [sH, brg])]
        exact z _ (by simp [setZ])) (by omega)
  -- the tables' lengths
  obtain ⟨σ4, g4⟩ : ∃ y : BS nw nn nsc nrs, y = (σ2.setv (sH 0) H0).setv (sH 1) H1 := ⟨_, rfl⟩
  rw [← g4] at e4
  have v4 : ∀ q, q ≠ sH 0 → q ≠ sH 1 → q.val < 120 ∨ (121 < q.val ∧ q.val < 156) ∨ (159 < q.val ∧ q.val < 168) ∨
      172 < q.val → σ4.val q = σ.val q := fun q n0 n1 hq => by
    rw [g4, WState.setv_val, Function.update_of_ne n1, WState.setv_val, Function.update_of_ne n0, v2 q hq]
  have e5 := mT_spec cap tTW (sTT 0) sC (sTT 1) (by simp [sTT, sC, brg_iff]) (by simp [sTT, sC, brg_iff])
    (by simp [sTT, brg_iff]) w0 w1 rest σ4 (by rw [g4]; simpa [s2] using hTW) (by rw [g4]; simpa [h2] using hsTW)
    (by rw [v4 _ (by simp [sC, sH, brg_iff]) (by simp [sC, sH, brg_iff]) (by simp [sC, brg])]
        exact z _ (by simp [setZ]))
    (by rw [v4 _ (by simp [sTT, sH, brg_iff]) (by simp [sTT, sH, brg_iff]) (by simp [sTT, brg]),
          v4 _ (by simp [sTT, sH, brg_iff]) (by simp [sTT, sH, brg_iff]) (by simp [sTT, brg]),
          z (sTT 0) (by simp [setZ]), z (sTT 1) (by simp [setZ])]; omega)
  rw [v4 _ (by simp [sTT, sH, brg_iff]) (by simp [sTT, sH, brg_iff]) (by simp [sTT, brg]),
    v4 _ (by simp [sTT, sH, brg_iff]) (by simp [sTT, sH, brg_iff]) (by simp [sTT, brg]),
    z (sTT 0) (by simp [setZ]), z (sTT 1) (by simp [setZ]), Nat.zero_add, Nat.zero_add] at e5
  obtain ⟨σ5, g5⟩ : ∃ y : BS nw nn nsc nrs, y = (σ4.setv (sTT 0) w0.length).setv (sTT 1) w1.length := ⟨_, rfl⟩
  rw [← g5] at e5
  have t50 : σ5.val (sTT 0) = w0.length := by
    rw [g5, WState.setv_val, Function.update_of_ne (by simp [sTT, brg_iff]), WState.setv_val, Function.update_self]
  have e6 := WExec.dec (cap := cap) (sTT 0) σ5 (by rw [t50]; omega)
  rw [t50] at e6
  have t61 : (σ5.setv (sTT 0) (w0.length - 1)).val (sTT 1) = w1.length := by
    rw [WState.setv_val, Function.update_of_ne (by simp [sTT, brg_iff]), g5, WState.setv_val, Function.update_self]
  have e7 := WExec.dec (cap := cap) (sTT 1) (σ5.setv (sTT 0) (w0.length - 1)) (by rw [t61]; omega)
  rw [t61] at e7
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_ le_rfl, ?_⟩
  · rw [g5, g4, g2, g1]
    rfl
  · unfold setRCost
    omega

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
