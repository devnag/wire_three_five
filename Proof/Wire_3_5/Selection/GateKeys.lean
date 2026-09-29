import Proof.Wire_3_5.Selection.GateEmit

/-! # C1.4: a join's key stream (P3:1345-1356)

Paper: "For each of the sixteen corner patterns, count pairs satisfying its four weak inequalities" (P3:1345-1346).
A join's key stream: the right half's points (inner keys) then the left half's points (queries), then the stream's
end mark. This module states the gate routine's ready state (`WReady`: the words, the weight tables, the counts, the
constants), the join phase's moving parts (`jst`: the key streams `KY`, `KY'`, `KL`, `KL'`, the words `JT`, `ACC`, `EW`,
the level `ℓ` and `PW = 2^(ℓ+1)`), the writer `kw` and **`kw_spec`**: from `jst`, the target stream `G k` becomes
`overlay (Rkeys ++ Lkeys ++ [false])` over its old contents. Paper quantity: a join's key stream. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-- The registers the ready state holds at `0`. -/
def zeroReg (i : Fin 48) : Bool :=
  decide (6 ≤ i.val ∧ i.val ≤ 14) || decide (i.val = 16) || decide (i.val = 17) || decide (i.val = 20) ||
    decide (i.val = 22) || decide (27 ≤ i.val ∧ i.val ≤ 30) || decide (i.val = 33) || decide (i.val = 34) ||
    decide (i.val = 36) || decide (37 ≤ i.val ∧ i.val ≤ 45) || decide (i.val = 47)

/-- **The gate routine's ready state** (before the joins). -/
structure WReady (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (P : StarParams) (N W V : ℕ)
    (g : NormalizedThresholdGate P.n) (σ : WState ns nr) : Prop where
  x0 : σ.st (G 4) = frame (binary (lw P + 1) 0)
  u0 : σ.st (G 5) = frame (binary (P.s * hh P + 1) 0)
  ci0 : σ.st (G 8) = frame (binary P.s 0)
  sy0 : σ.st (G 9) = frame (binary P.s 0)
  ac0 : σ.st (G 10) = frame (binary W 0)
  ac0' : σ.st (G 11) = frame (binary W 0)
  wv0 : σ.st (G 12) = frame (binary W 0)
  xp : ∃ v, σ.st (G 14) = frame (binary (lw P + 1) v)
  up : ∃ v, σ.st (G 15) = frame (binary (P.s * hh P + 1) v)
  ns : σ.st (G 0) = frame (binary (P.r * P.s) N)
  wtl : σ.st (G 6) = tbl W (recsL P g)
  wtr : σ.st (G 7) = tbl W (recsR P g)
  tk : σ.st (G 13) = frame (binary W (keyOf V g.threshold))
  ofs : σ.st (G 2) = frame (binary W (2 ^ V))
  ht : σ.st (G 16) = frame (binary W 0)
  cnt : σ.st (G 22) = frame (binary W 0)
  heads : ∀ i : Fin 28, σ.sh (G i) = 0
  rh : σ.val (R 0) = hh P
  rb : σ.val (R 1) = P.b
  rs : σ.val (R 2) = P.s
  rfL : σ.val (R 3) = fL P
  rfR : σ.val (R 4) = fR P
  rv : σ.val (R 5) = V + 1
  ro : σ.val (R 15) = hh P
  rq : σ.val (R 21) = W - V - 2
  rW : σ.val (R 23) = W
  rW1 : σ.val (R 24) = W - 1
  rs1 : σ.val (R 25) = 2 * V + 3
  rs0 : σ.val (R 26) = W - (2 * V + 3)
  pxl : σ.val (R 31) = 2 ^ lw P
  pu : σ.val (R 32) = 2 ^ (P.s * hh P)
  pxr : σ.val (R 35) = 2 ^ rw P
  zr : ∀ i : Fin 48, zeroReg i = true → σ.val (R i) = 0

/-- **The join phase's moving parts** over a ready base. -/
def jst (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (W : ℕ) (σ0 : WState ns nr) (ky ky' kl kl' : List Bool)
    (jt acc ew ℓ : ℕ) : WState ns nr :=
  (((((((((σ0.sets (G 18) ky).sets (G 19) ky').sets (G 20) kl).sets (G 21) kl').sets (G 23) (frame (binary W jt))).sets
    (G 24) (frame (binary W acc))).sets (G 25) (frame (binary W ew))).setv (R 19) ℓ).sets (G 17)
    (frame (binary W (2 ^ (ℓ + 1)))))

/-- The point maps. -/
def SLm (G : Fin 28 → Fin (ns + 1)) : Fin 12 → Fin (ns + 1) := fun i => G (iSL i)
def SRm (G : Fin 28 → Fin (ns + 1)) : Fin 12 → Fin (ns + 1) := fun i => G (iSR i)
def QLm (R : Fin 48 → Fin nr) : Fin 20 → Fin nr := fun i => R (iQL i)
def QRm (R : Fin 48 → Fin nr) : Fin 20 → Fin nr := fun i => R (iQR i)

/-- **A join's key-stream writer** into `G k`: the right half with `EMR`, the left half with `EML`, the end mark. -/
def kw (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr)
    (EMR EML : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (k : Fin 28) : WM ns nr :=
  .seq (enumP (SRm G) (QRm R) (ptBody (SRm G) (QRm R) EMR (R 28) (R 29)))
    (.seq (enumP (SLm G) (QLm R) (ptBody (SLm G) (QLm R) EML (R 28) (R 29)))
      (.seq (emitB (G k) (R 27) false) (WM.rewind (G k) (R 27))))

theorem iSL_lt (i : Fin 12) : (iSL i).val < 16 := by revert i; decide
theorem iSR_lt (i : Fin 12) : (iSR i).val < 16 := by revert i; decide
theorem iQL_ne (a : Fin 48) (ha : a.val = 27 ∨ a.val = 28 ∨ a.val = 29 ∨ a.val = 19 ∨ a.val = 20 ∨ (21 ≤ a.val ∧ a.val ≤ 26)
    ∨ a.val = 30 ∨ a.val = 5 ∨ (37 ≤ a.val)) (i : Fin 20) : iQL i ≠ a := by
  revert i; rcases a with ⟨a, ha'⟩; simp only at ha; revert ha; revert a; decide
theorem iQR_ne (a : Fin 48) (ha : a.val = 27 ∨ a.val = 28 ∨ a.val = 29 ∨ a.val = 19 ∨ a.val = 20 ∨ (21 ≤ a.val ∧ a.val ≤ 26)
    ∨ a.val = 30 ∨ a.val = 5 ∨ (37 ≤ a.val)) (i : Fin 20) : iQR i ≠ a := by
  revert i; rcases a with ⟨a, ha'⟩; simp only at ha; revert ha; revert a; decide

section Jst
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (W : ℕ) (σ0 : WState ns nr) (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ)
include hG hR

theorem jst_sh : (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sh = σ0.sh := rfl

theorem jst_val (i : Fin 48) : (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).val (R i) = if i = 19 then ℓ else σ0.val (R i) := by
  simp only [jst, WState.sets_val, WState.setv_val, Function.update_apply, hR.eq_iff]

theorem jst_st (i : Fin 28) (hi : i.val ≠ 17 ∧ i.val ≠ 18 ∧ i.val ≠ 19 ∧ i.val ≠ 20 ∧ i.val ≠ 21 ∧ i.val ≠ 23 ∧
    i.val ≠ 24 ∧ i.val ≠ 25) : (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G i) = σ0.st (G i) := by
  obtain ⟨h17, h18, h19, h20, h21, h23, h24, h25⟩ := hi
  simp only [jst, WState.sets_st, WState.setv_st, Function.update_apply, hG.eq_iff]
  rw [if_neg (by intro h; rw [h] at h17; exact h17 rfl), if_neg (by intro h; rw [h] at h25; exact h25 rfl),
    if_neg (by intro h; rw [h] at h24; exact h24 rfl), if_neg (by intro h; rw [h] at h23; exact h23 rfl),
    if_neg (by intro h; rw [h] at h21; exact h21 rfl), if_neg (by intro h; rw [h] at h20; exact h20 rfl),
    if_neg (by intro h; rw [h] at h19; exact h19 rfl), if_neg (by intro h; rw [h] at h18; exact h18 rfl)]

theorem jst_st17 : (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G 17) = frame (binary W (2 ^ (ℓ + 1))) := by
  simp [jst, Function.update_apply]

end Jst

/-! ## Frame facts -/

theorem mkP_val_of {S : Fin 12 → Fin (ns + 1)} {Q : Fin 20 → Fin nr} (s W : ℕ) (σ : WState ns nr) (r : Fin nr)
    (hr : ∀ i : Fin 20, 2 ≤ i.val → i.val < 9 → r ≠ Q i) (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    (mkP S Q s W σ pX pW pU pN ci sy a a' ok fl sg wv).val r = σ.val r := by
  simp only [mkP]
  rw [if_neg (hr 5 (by decide) (by decide)), if_neg (hr 6 (by decide) (by decide)), if_neg (hr 7 (by decide) (by decide)),
    if_neg (hr 8 (by decide) (by decide)), if_neg (hr 2 (by decide) (by decide)), if_neg (hr 3 (by decide) (by decide)),
    if_neg (hr 4 (by decide) (by decide))]

theorem mkP_st_of {S : Fin 12 → Fin (ns + 1)} {Q : Fin 20 → Fin nr} (s W : ℕ) (σ : WState ns nr) (j : Fin (ns + 1))
    (hj : ∀ k : Fin 12, 4 ≤ k.val → k.val < 9 → j ≠ S k) (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    (mkP S Q s W σ pX pW pU pN ci sy a a' ok fl sg wv).st j = σ.st j := by
  simp only [mkP]
  rw [if_neg (hj 4 (by decide) (by decide)), if_neg (hj 5 (by decide) (by decide)), if_neg (hj 6 (by decide) (by decide)),
    if_neg (hj 7 (by decide) (by decide)), if_neg (hj 8 (by decide) (by decide))]

theorem mkP_sh_of {S : Fin 12 → Fin (ns + 1)} {Q : Fin 20 → Fin nr} (s W : ℕ) (σ : WState ns nr) (j : Fin (ns + 1))
    (hj : ∀ k : Fin 12, k.val < 4 → j ≠ S k) (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    (mkP S Q s W σ pX pW pU pN ci sy a a' ok fl sg wv).sh j = σ.sh j := by
  simp only [mkP]
  rw [if_neg (hj 0 (by decide) ), if_neg (hj 3 (by decide)), if_neg (hj 1 (by decide)), if_neg (hj 2 (by decide))]

theorem EmEnv_congr (G : Fin 28 → Fin (ns + 1)) (R : Fin 48 → Fin nr) (W V ℓ : ℕ) (σ σ' : WState ns nr)
    (hv : ∀ i : Fin 48, (i.val = 19 ∨ i.val = 20 ∨ i.val = 5 ∨ (21 ≤ i.val ∧ i.val ≤ 26) ∨ i.val = 6 ∨ i.val = 7 ∨
      i.val = 30) → σ'.val (R i) = σ.val (R i))
    (hs : σ'.st (G 16) = σ.st (G 16) ∧ σ'.sh (G 16) = σ.sh (G 16) ∧ σ'.st (G 17) = σ.st (G 17) ∧
      σ'.sh (G 17) = σ.sh (G 17)) (h : EmEnv G R W V ℓ σ) : EmEnv G R W V ℓ σ' := by
  obtain ⟨e19, e20, e5, e21, e22, e23, e24, e25, e26, e6, e7, e30, ⟨h16, h16'⟩, ⟨h17, h17'⟩⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hv 19 (by decide)]; exact e19
  · rw [hv 20 (by decide)]; exact e20
  · rw [hv 5 (by decide)]; exact e5
  · rw [hv 21 (by decide)]; exact e21
  · rw [hv 22 (by decide)]; exact e22
  · rw [hv 23 (by decide)]; exact e23
  · rw [hv 24 (by decide)]; exact e24
  · rw [hv 25 (by decide)]; exact e25
  · rw [hv 26 (by decide)]; exact e26
  · rw [hv 6 (by decide)]; exact e6
  · rw [hv 7 (by decide)]; exact e7
  · rw [hv 30 (by decide)]; exact e30
  · rw [hs.1]; exact h16
  · rw [hs.2.1]; exact h16'
  · rw [hs.2.2.1]; exact h17
  · rw [hs.2.2.2]; exact h17'

theorem kst_nil (σ : WState ns nr) (K : Fin (ns + 1)) (CK : Fin nr) (hK : σ.sh K = 0) (hCK : σ.val CK = 0) :
    kst σ K CK (σ.st K) [] = σ := by
  apply WState.eq
  · funext j; simp only [kst, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs with h
    · subst h; simp [hK]
    · rfl
  · funext j; simp only [kst, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs with h
    · subst h; simp [overlay]
    · rfl
  · funext j; simp only [kst, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs with h
    · subst h; simp [hCK]
    · rfl
  · rfl

/-- **The end of a key stream**: the end mark, then the head back to `0`. -/
theorem kst_end (cap : ℕ) (σ : WState ns nr) {A K : Fin (ns + 1)} {CA CK : Fin nr} (hAK : A ≠ K) (hC : CA ≠ CK)
    (hA : σ.sh A = 0) (hCA : σ.val CA = 0) (hK : σ.sh K = 0) (hCK : σ.val CK = 0) (L out : List Bool)
    (hcap : out.length + 1 ≤ cap) :
    WExec cap (.seq (emitB K CK false) (WM.rewind K CK)) (kst σ K CK L out) (σ.sets K (overlay (out ++ [false]) L))
      (5 * out.length + 14) := by
  have e1 := emitB_rst cap σ L hAK hC 0 out false (by omega)
  rw [rst_kst σ L hAK hC hA hCA, rst_kst σ L hAK hC hA hCA] at e1
  have r := wrewind_spec cap K CK (out ++ [false]).length (kst σ K CK L (out ++ [false])) (by simp [kst])
    (by simp [kst]; omega)
  refine WExec.cast cap (WExec.seq e1 r) ?_ (by simp; omega)
  apply WState.eq
  · funext j; simp only [kst, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs with h
    · subst h; simp [hK]
    · rfl
  · rfl
  · funext j; simp only [kst, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs with h
    · subst h; simp [hCK]
    · rfl
  · rfl

/-! ## Sizes -/

theorem size_facts (P : StarParams) : lw P ≤ P.n ∧ rw P ≤ lw P ∧ P.b ≤ P.n ∧ hh P ≤ P.r ∧ P.r ≤ P.n ∧
    hh P * P.b + fL P = lw P ∧ hh P * P.b + fR P = rw P ∧ 2 * hh P = P.r := by
  have h1 := hb_le_rb P
  have h2 := fL_le P
  have h3 := rb_le P
  have h4 := hh_two P
  have h5 := P.four_r_le_n
  have h6 : P.b ≤ P.r * P.b := Nat.le_mul_of_pos_left _ P.r_pos
  have h7 : fR P ≤ fL P := by unfold fR fL; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, h4⟩
  · unfold lw; omega
  · unfold rw lw; omega
  · omega
  · omega
  · omega

/-- The key-stream writer's room on the tapes. -/
def capKW (P : StarParams) (W : ℕ) : ℕ :=
  2 ^ (P.s * hh P) * (2 ^ lw P + 2 ^ rw P) * (4 * W + 2) + (P.n + P.r * P.s + P.s + 4) * (2 * W + 8) +
    2 ^ (P.s * hh P + 1) + 2 ^ (lw P + 1)

theorem keyOf_cast (V : ℕ) (z : ℤ) (hz : z.natAbs < 2 ^ V) : ((keyOf V z : ℕ) : ℤ) = z + 2 ^ V := by
  unfold keyOf RepairOrdinary.SignedSortKey.shifted
  have : (0 : ℤ) ≤ z + ((2 ^ V : ℕ) : ℤ) := by
    have h : (z.natAbs : ℤ) < ((2 ^ V : ℕ) : ℤ) := by exact_mod_cast hz
    rw [Int.natCast_natAbs] at h
    have := neg_abs_le z
    linarith
  rw [Int.toNat_of_nonneg this]; push_cast; ring

theorem iQR_rng (i : Fin 20) (h1 : 2 ≤ i.val) (h2 : i.val < 9) : 8 ≤ (iQR i).val ∧ (iQR i).val ≤ 14 := by
  revert i; decide
theorem iQL_rng (i : Fin 20) (h1 : 2 ≤ i.val) (h2 : i.val < 9) : 8 ≤ (iQL i).val ∧ (iQL i).val ≤ 14 := by
  revert i; decide
theorem iQR_zero (i : Fin 20) (h : i.val < 9) : zeroReg (iQR i) = true ∧ iQR i ≠ 19 := by revert i; decide
theorem iQL_zero (i : Fin 20) (h : i.val < 9) : zeroReg (iQL i) = true ∧ iQL i ≠ 19 := by revert i; decide

theorem capKW_facts (P : StarParams) (W cap : ℕ) (h : capKW P W ≤ cap) :
    2 * P.s + 1 ≤ cap ∧ 2 * W + 1 ≤ cap ∧ P.n * (2 * W + 2) ≤ cap ∧ 2 * P.n ≤ cap ∧
      2 * (P.s * P.r) ≤ cap ∧ 2 ^ (P.s * hh P) ≤ cap ∧ 2 ^ lw P ≤ cap ∧ 2 * (lw P + 1) + 1 ≤ cap ∧
      2 * (P.s * hh P + 1) + 1 ≤ cap ∧ 2 ^ (P.s * hh P) * (2 ^ lw P + 2 ^ rw P) * (4 * W + 2) + 4 * W + 8 ≤ cap := by
  obtain ⟨h1, -, -, h4, h5, -, -, h8⟩ := size_facts P
  unfold capKW at h
  set T1 := 2 ^ (P.s * hh P) * (2 ^ lw P + 2 ^ rw P) * (4 * W + 2) with hT1
  set M := P.n + P.r * P.s + P.s + 4 with hM
  set T2 := M * (2 * W + 8) with hT2
  set T3 := 2 ^ (P.s * hh P + 1) with hT3
  set T4 := 2 ^ (lw P + 1) with hT4
  have hM8 : M * 8 ≤ T2 := Nat.mul_le_mul_left _ (by omega)
  have hMW : M * (2 * W + 2) ≤ T2 := Nat.mul_le_mul_left _ (by omega)
  have hnW : P.n * (2 * W + 2) ≤ M * (2 * W + 2) := Nat.mul_le_mul_right _ (by omega)
  have hW8 : 1 * (2 * W + 8) ≤ T2 := Nat.mul_le_mul_right _ (by omega)
  have hsr : P.s * P.r ≤ M := by rw [Nat.mul_comm]; omega
  have hsh : P.s * hh P ≤ P.s * P.r := Nat.mul_le_mul_left _ h4
  have hp1 : 2 ^ (P.s * hh P) ≤ T3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ lw P ≤ T4 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsm : P.s ≤ M := by omega
  have hnM : P.n + 4 ≤ M := by omega
  have h4W : 4 * (2 * W + 8) ≤ T2 := Nat.mul_le_mul_right _ (by omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

section SideR
variable (G : Fin 28 → Fin (ns + 1)) (hG : Function.Injective G) (R : Fin 48 → Fin nr) (hR : Function.Injective R)
variable (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (cap : ℕ) (σ0 : WState ns nr)
  (hw : WReady G R P N W V g σ0) (ky ky' kl kl' : List Bool) (jt acc ew ℓ : ℕ) (k : Fin 28)
  (hk : 18 ≤ k.val ∧ k.val ≤ 21) (hW : 2 * V + 3 ≤ W) (hKB : KeyBound g V) (hcapB : capKW P W ≤ cap)
include hG hR hw hk hW hKB hcapB

theorem jst_emenv (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr)
    (hS : ∀ i : Fin 12, (∃ j : Fin 28, S i = G j ∧ j.val < 16))
    (hQ : ∀ i : Fin 20, 2 ≤ i.val → i.val < 9 → ∃ j : Fin 48, Q i = R j ∧ 8 ≤ j.val ∧ j.val ≤ 14)
    (v1 w1 v2 w2 u x a a' wv wx wu : ℕ) :
    EmEnv G R W V ℓ (mkP S Q P.s W (((((((jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).setv (R 32) v1).setv (R 34) w1).setv
      (R 35) v2).setv (R 33) w2).sets (S 1) (frame (binary wu u))).sets (S 0) (frame (binary wx x)))
      0 0 0 0 0 0 a a' 0 0 0 wv) ∧
    EmEnv G R W V ℓ (mkP S Q P.s W (((((((jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).setv (R 32) v1).setv (R 34) w1).setv
      (R 31) v2).setv (R 33) w2).sets (S 1) (frame (binary wu u))).sets (S 0) (frame (binary wx x)))
      0 0 0 0 0 0 a a' 0 0 0 wv) := by
  have base : EmEnv G R W V ℓ (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) := by
    have hv := jst_val G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hv]; simp
    · rw [hv]; simp; exact hw.zr 20 (by decide)
    · rw [hv]; simp; exact hw.rv
    · rw [hv]; simp; exact hw.rq
    · rw [hv]; simp; exact hw.zr 22 (by decide)
    · rw [hv]; simp; exact hw.rW
    · rw [hv]; simp; exact hw.rW1
    · rw [hv]; simp; exact hw.rs1
    · rw [hv]; simp; exact hw.rs0
    · rw [hv]; simp; exact hw.zr 6 (by decide)
    · rw [hv]; simp; exact hw.zr 7 (by decide)
    · rw [hv]; simp; exact hw.zr 30 (by decide)
    · rw [jst_st G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ 16 (by decide)]; exact hw.ht
    · rw [jst_sh G hG R hR]; exact hw.heads 16
    · exact jst_st17 G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ
    · rw [jst_sh G hG R hR]; exact hw.heads 17
  have hvS : ∀ i : Fin 12, S i ≠ G 16 ∧ S i ≠ G 17 := by
    intro i; obtain ⟨j, hj, hj'⟩ := hS i
    rw [hj]; exact ⟨hG.ne (by intro h; rw [h] at hj'; simp at hj'), hG.ne (by intro h; rw [h] at hj'; simp at hj')⟩
  have hvQ : ∀ (r : Fin 48), (r.val = 19 ∨ r.val = 20 ∨ r.val = 5 ∨ (21 ≤ r.val ∧ r.val ≤ 26) ∨ r.val = 6 ∨ r.val = 7 ∨
      r.val = 30) → ∀ i : Fin 20, 2 ≤ i.val → i.val < 9 → R r ≠ Q i := by
    intro r hr i hi1 hi2
    obtain ⟨j, hj, hj1, hj2⟩ := hQ i hi1 hi2
    rw [hj]; exact hR.ne (by intro h; subst h; omega)
  constructor
  · refine EmEnv_congr G R W V ℓ _ _ ?_ ?_ base
    · intro r hr
      rw [mkP_val_of P.s W _ (R r) (hvQ r hr)]
      simp only [WState.sets_val, WState.setv_val, Function.update_apply, hR.eq_iff]
      rw [if_neg (by intro h; subst h; simp at hr), if_neg (by intro h; subst h; simp at hr),
        if_neg (by intro h; subst h; simp at hr), if_neg (by intro h; subst h; simp at hr)]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mkP_st_of P.s W _ _ (fun k _ _ => Ne.symm (hvS k).1)]
        simp only [WState.sets_st, WState.setv_st, Function.update_apply]
        rw [if_neg (Ne.symm (hvS 0).1), if_neg (Ne.symm (hvS 1).1)]
      · rw [mkP_sh_of P.s W _ _ (fun k _ => Ne.symm (hvS k).1)]; rfl
      · rw [mkP_st_of P.s W _ _ (fun k _ _ => Ne.symm (hvS k).2)]
        simp only [WState.sets_st, WState.setv_st, Function.update_apply]
        rw [if_neg (Ne.symm (hvS 0).2), if_neg (Ne.symm (hvS 1).2)]
      · rw [mkP_sh_of P.s W _ _ (fun k _ => Ne.symm (hvS k).2)]; rfl
  · refine EmEnv_congr G R W V ℓ _ _ ?_ ?_ base
    · intro r hr
      rw [mkP_val_of P.s W _ (R r) (hvQ r hr)]
      simp only [WState.sets_val, WState.setv_val, Function.update_apply, hR.eq_iff]
      rw [if_neg (by intro h; subst h; simp at hr), if_neg (by intro h; subst h; simp at hr),
        if_neg (by intro h; subst h; simp at hr), if_neg (by intro h; subst h; simp at hr)]
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [mkP_st_of P.s W _ _ (fun k _ _ => Ne.symm (hvS k).1)]
        simp only [WState.sets_st, WState.setv_st, Function.update_apply]
        rw [if_neg (Ne.symm (hvS 0).1), if_neg (Ne.symm (hvS 1).1)]
      · rw [mkP_sh_of P.s W _ _ (fun k _ => Ne.symm (hvS k).1)]; rfl
      · rw [mkP_st_of P.s W _ _ (fun k _ _ => Ne.symm (hvS k).2)]
        simp only [WState.sets_st, WState.setv_st, Function.update_apply]
        rw [if_neg (Ne.symm (hvS 0).2), if_neg (Ne.symm (hvS 1).2)]
      · rw [mkP_sh_of P.s W _ _ (fun k _ => Ne.symm (hvS k).2)]; rfl

/-- **The right half's keys** into the key stream `G k`. -/
theorem sideR_spec (EM : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (f : ℕ → ℕ → List Bool)
    (cE : ℕ) (hEm : EmitHyp cap W V (SRm G) (G k) (R 27) (R 28) (R 29) EM (EmEnv G R W V ℓ) f cE)
    (hf : ∀ a b, (f a b).length ≤ 4 * W + 2) (L out : List Bool)
    (hcapK : out.length + 2 ^ (P.s * hh P) * 2 ^ rw P * (4 * W + 2) + 4 * W + 8 ≤ cap) :
    WExec cap (enumP (SRm G) (QRm R) (ptBody (SRm G) (QRm R) EM (R 28) (R 29)))
      (kst (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G k) (R 27) L out)
      (kst (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G k) (R 27) L (out ++ (List.range (2 ^ (P.s * hh P))).flatMap
        (fun u => (List.range (2 ^ rw P)).flatMap (fun x =>
          f (min (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x))
            (max (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x))))))
      (enumCost (2 ^ (P.s * hh P)) (2 ^ rw P) (pointCost (hh P) P.b (fR P) 0 P.s W + cE + 200 * W + 30) (lw P + 1)
        (P.s * hh P + 1)) := by
  set σ := jst G R W σ0 ky ky' kl kl' jt acc ew ℓ with hσ
  have hv := jst_val G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ
  have hst := jst_st G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ
  have hsh : σ.sh = σ0.sh := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := size_facts P
  have hSR : Function.Injective (SRm G) := hG.comp iSR_inj
  have hQR : Function.Injective (QRm R) := hR.comp iQR_inj
  have hKn : ∀ k' : Fin 12, G k ≠ SRm G k' := fun k' => hG.ne (by
    intro h; have := iSR_lt k'; rw [← h] at this; omega)
  have hrne : ∀ (a : Fin 48), (a.val = 27 ∨ a.val = 28 ∨ a.val = 29 ∨ a.val = 19 ∨ a.val = 20 ∨
      (21 ≤ a.val ∧ a.val ≤ 26) ∨ a.val = 30 ∨ a.val = 5 ∨ (37 ≤ a.val)) → ∀ i : Fin 20, R a ≠ QRm R i :=
    fun a ha i => hR.ne (Ne.symm (iQR_ne a ha i))
  obtain ⟨xp, hxp⟩ := hw.xp
  obtain ⟨up, hup⟩ := hw.up
  have hs := hw.heads
  have hVW : (2 : ℤ) ^ (V + 1) ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) (by omega)
  have hVWn : 2 ^ (V + 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hVV : 2 ^ V < 2 ^ (V + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hcast : ((2 ^ V : ℕ) : ℤ) = 2 ^ V := by push_cast; ring
  have hrng : ∀ (c : ℕ → Bool) (Pp : ℕ), Pp ≤ hh P * P.b + fR P →
      0 ≤ accC ((2 ^ V : ℕ) : ℤ) (zAt (recsR P g)) c Pp ∧ accC ((2 ^ V : ℕ) : ℤ) (zAt (recsR P g)) c Pp < 2 ^ (V + 1) := by
    intro c Pp hP; rw [hcast]; exact acc_rangeR P g V hKB c Pp (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := capKW_facts P W cap hcapB
  have hlwn : (hh P * P.b + fR P) * (2 * W + 2) ≤ P.n * (2 * W + 2) := Nat.mul_le_mul_right _ (by omega)
  have hshr : P.s * hh P ≤ P.s * P.r := Nat.mul_le_mul_left _ h4
  have hD : 2 ^ rw P ≤ 2 ^ lw P := Nat.pow_le_pow_right (by norm_num) h2
  exact side_spec P hSR hQR cap W V σ L hKn (fun i => hrne 27 (by decide) i) (fun i => hrne 28 (by decide) i)
    (fun i => hrne 29 (by decide) i) EM (EmEnv G R W V ℓ) f cE hEm hf (recsR P g) (2 ^ V) 0 (fR P) N (lw P + 1)
    (P.s * hh P + 1) (P.r * P.s) xp up (2 ^ rw P) (2 ^ (P.s * hh P)) out
    (by show σ.st (G 4) = _; rw [hst 4 (by decide)]; exact hw.x0)
    (by show σ.st (G 5) = _; rw [hst 5 (by decide)]; exact hw.u0)
    (fun k' _ => by rw [hsh]; exact hs _)
    (by show σ.st (G 8) = _; rw [hst 8 (by decide)]; exact hw.ci0)
    (by show σ.st (G 9) = _; rw [hst 9 (by decide)]; exact hw.sy0)
    (by show σ.st (G 10) = _; rw [hst 10 (by decide)]; exact hw.ac0)
    (by show σ.st (G 11) = _; rw [hst 11 (by decide)]; exact hw.ac0')
    (by show σ.st (G 12) = _; rw [hst 12 (by decide)]; exact hw.wv0)
    (fun i hi => by
      show σ.val (R (iQR i)) = 0
      rw [hv, if_neg (iQR_zero i hi).2]; exact hw.zr _ (iQR_zero i hi).1)
    (by show σ.st (G 0) = _; rw [hst 0 (by decide)]; exact hw.ns)
    (by show σ.st (G 7) = _; rw [hst 7 (by decide)]; exact hw.wtr)
    ⟨by show σ.st (G 2) = _; rw [hst 2 (by decide)]; exact hw.ofs, by rw [hsh]; exact hs 2⟩
    (by show σ.val (R 1) = _; rw [hv]; simp; exact hw.rb)
    (by show σ.val (R 0) = _; rw [hv]; simp; exact hw.rh)
    (by show σ.val (R 2) = _; rw [hv]; simp; exact hw.rs)
    (by show σ.val (R 4) = _; rw [hv]; simp; exact hw.rfR)
    (by show σ.val (R 36) = _; rw [hv]; simp; exact hw.zr 36 (by decide))
    (by show σ.val (R 16) = _; rw [hv]; simp; exact hw.zr 16 (by decide))
    (by show σ.val (R 17) = _; rw [hv]; simp; exact hw.zr 17 (by decide))
    (by show σ.val (R 35) = _; rw [hv]; simp; exact hw.pxr)
    (by show σ.val (R 33) = _; rw [hv]; simp; exact hw.zr 33 (by decide))
    (by show σ.val (R 32) = _; rw [hv]; simp; exact hw.pu)
    (by show σ.val (R 34) = _; rw [hv]; simp; exact hw.zr 34 (by decide))
    (by show σ.st (G 14) = _; rw [hst 14 (by decide)]; exact hxp)
    (by show σ.st (G 15) = _; rw [hst 15 (by decide)]; exact hup)
    (by rw [hv]; simp; exact hw.zr 28 (by decide)) (by rw [hv]; simp; exact hw.zr 29 (by decide))
    (fun v1 w1 v2 w2 u x a a' wv => (jst_emenv G hG R hR P N W V g cap σ0 hw ky ky' kl kl' jt acc ew ℓ k hk hW hKB
      hcapB (SRm G) (QRm R) (fun i => ⟨iSR i, rfl, iSR_lt i⟩)
      (fun i hi1 hi2 => ⟨iQR i, rfl, iQR_rng i hi1 hi2⟩) v1 w1 v2 w2 u x a a' wv (lw P + 1) (P.s * hh P + 1)).1)
    (by rw [recsR_length]; exact le_of_eq h7) (by omega) (by omega)
    (by rw [Nat.zero_add, Nat.mul_comm P.r P.s]; exact hshr)
    (Nat.pow_lt_pow_right (by norm_num) (by omega)) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    (fun c Pp hP => ⟨(hrng c Pp hP).1, lt_of_lt_of_le (hrng c Pp hP).2 hVW⟩)
    (fun u x => by
      constructor
      · unfold aW; split_ifs
        · exact toNat_lt_pow _ (V + 1) (hrng _ _ (by omega)).1 (hrng _ _ (by omega)).2
        · exact hVV
      · unfold aW'; split_ifs
        · exact toNat_lt_pow _ (V + 1) (hrng _ _ (by omega)).1 (hrng _ _ (by omega)).2
        · exact hVV)
    (lt_of_lt_of_le hVV hVWn)
    c1 c2 (le_trans hlwn c3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [Nat.zero_add]; omega) (by omega) (by omega) c8 c9 hcapK

/-- **The left half's keys** into the key stream `G k`. -/
theorem sideL_spec (EM : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (f : ℕ → ℕ → List Bool)
    (cE : ℕ) (hEm : EmitHyp cap W V (SLm G) (G k) (R 27) (R 28) (R 29) EM (EmEnv G R W V ℓ) f cE)
    (hf : ∀ a b, (f a b).length ≤ 4 * W + 2) (L out : List Bool)
    (hcapK : out.length + 2 ^ (P.s * hh P) * 2 ^ lw P * (4 * W + 2) + 4 * W + 8 ≤ cap) :
    WExec cap (enumP (SLm G) (QLm R) (ptBody (SLm G) (QLm R) EM (R 28) (R 29)))
      (kst (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G k) (R 27) L out)
      (kst (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ) (G k) (R 27) L (out ++ (List.range (2 ^ (P.s * hh P))).flatMap
        (fun u => (List.range (2 ^ lw P)).flatMap (fun x =>
          f (min (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
              (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x))
            (max (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
              (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x))))))
      (enumCost (2 ^ (P.s * hh P)) (2 ^ lw P) (pointCost (hh P) P.b (fL P) (hh P) P.s W + cE + 200 * W + 30) (lw P + 1)
        (P.s * hh P + 1)) := by
  set σ := jst G R W σ0 ky ky' kl kl' jt acc ew ℓ with hσ
  have hv := jst_val G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ
  have hst := jst_st G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ
  have hsh : σ.sh = σ0.sh := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := size_facts P
  have hSL : Function.Injective (SLm G) := hG.comp iSL_inj
  have hQL : Function.Injective (QLm R) := hR.comp iQL_inj
  have hKn : ∀ k' : Fin 12, G k ≠ SLm G k' := fun k' => hG.ne (by
    intro h; have := iSL_lt k'; rw [← h] at this; omega)
  have hrne : ∀ (a : Fin 48), (a.val = 27 ∨ a.val = 28 ∨ a.val = 29 ∨ a.val = 19 ∨ a.val = 20 ∨
      (21 ≤ a.val ∧ a.val ≤ 26) ∨ a.val = 30 ∨ a.val = 5 ∨ (37 ≤ a.val)) → ∀ i : Fin 20, R a ≠ QLm R i :=
    fun a ha i => hR.ne (Ne.symm (iQL_ne a ha i))
  obtain ⟨xp, hxp⟩ := hw.xp
  obtain ⟨up, hup⟩ := hw.up
  have hs := hw.heads
  have hVW : (2 : ℤ) ^ (V + 1) ≤ 2 ^ W := pow_le_pow_right₀ (by norm_num) (by omega)
  have hVWn : 2 ^ (V + 1) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hθ : g.threshold.natAbs < 2 ^ V := by
    have := keyBound_int P g V hKB
    have h0 : (0 : ℤ) ≤ ∑ i, |g.weight i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have : (g.threshold.natAbs : ℤ) < ((2 ^ V : ℕ) : ℤ) := by rw [Int.natCast_natAbs]; push_cast; linarith
    exact_mod_cast this
  have hcast := keyOf_cast V g.threshold hθ
  have hini2 : keyOf V g.threshold < 2 ^ (V + 1) := by
    have : ((keyOf V g.threshold : ℕ) : ℤ) < ((2 ^ (V + 1) : ℕ) : ℤ) := by
      rw [hcast]
      have hl := le_abs_self g.threshold
      have hθ' : (g.threshold.natAbs : ℤ) < ((2 ^ V : ℕ) : ℤ) := by exact_mod_cast hθ
      rw [Int.natCast_natAbs] at hθ'
      push_cast at hθ' ⊢; rw [pow_succ]; linarith
    exact_mod_cast this
  have hrng : ∀ (c : ℕ → Bool) (Pp : ℕ), Pp ≤ hh P * P.b + fL P →
      0 ≤ accC ((keyOf V g.threshold : ℕ) : ℤ) (zAt (recsL P g)) c Pp ∧
        accC ((keyOf V g.threshold : ℕ) : ℤ) (zAt (recsL P g)) c Pp < 2 ^ (V + 1) := by
    intro c Pp hP; rw [hcast]; exact acc_rangeL P g V hKB c Pp (by omega)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := capKW_facts P W cap hcapB
  have hlwn : (hh P * P.b + fL P) * (2 * W + 2) ≤ P.n * (2 * W + 2) := Nat.mul_le_mul_right _ (by omega)
  have hshr : P.s * hh P ≤ P.s * P.r := Nat.mul_le_mul_left _ h4
  have hhh : P.s * (hh P + hh P) = P.s * P.r := by rw [← two_mul, h8]
  exact side_spec P hSL hQL cap W V σ L hKn (fun i => hrne 27 (by decide) i) (fun i => hrne 28 (by decide) i)
    (fun i => hrne 29 (by decide) i) EM (EmEnv G R W V ℓ) f cE hEm hf (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N
    (lw P + 1) (P.s * hh P + 1) (P.r * P.s) xp up (2 ^ lw P) (2 ^ (P.s * hh P)) out
    (by show σ.st (G 4) = _; rw [hst 4 (by decide)]; exact hw.x0)
    (by show σ.st (G 5) = _; rw [hst 5 (by decide)]; exact hw.u0)
    (fun k' _ => by rw [hsh]; exact hs _)
    (by show σ.st (G 8) = _; rw [hst 8 (by decide)]; exact hw.ci0)
    (by show σ.st (G 9) = _; rw [hst 9 (by decide)]; exact hw.sy0)
    (by show σ.st (G 10) = _; rw [hst 10 (by decide)]; exact hw.ac0)
    (by show σ.st (G 11) = _; rw [hst 11 (by decide)]; exact hw.ac0')
    (by show σ.st (G 12) = _; rw [hst 12 (by decide)]; exact hw.wv0)
    (fun i hi => by
      show σ.val (R (iQL i)) = 0
      rw [hv, if_neg (iQL_zero i hi).2]; exact hw.zr _ (iQL_zero i hi).1)
    (by show σ.st (G 0) = _; rw [hst 0 (by decide)]; exact hw.ns)
    (by show σ.st (G 6) = _; rw [hst 6 (by decide)]; exact hw.wtl)
    ⟨by show σ.st (G 13) = _; rw [hst 13 (by decide)]; exact hw.tk, by rw [hsh]; exact hs 13⟩
    (by show σ.val (R 1) = _; rw [hv]; simp; exact hw.rb)
    (by show σ.val (R 0) = _; rw [hv]; simp; exact hw.rh)
    (by show σ.val (R 2) = _; rw [hv]; simp; exact hw.rs)
    (by show σ.val (R 3) = _; rw [hv]; simp; exact hw.rfL)
    (by show σ.val (R 15) = _; rw [hv]; simp; exact hw.ro)
    (by show σ.val (R 16) = _; rw [hv]; simp; exact hw.zr 16 (by decide))
    (by show σ.val (R 17) = _; rw [hv]; simp; exact hw.zr 17 (by decide))
    (by show σ.val (R 31) = _; rw [hv]; simp; exact hw.pxl)
    (by show σ.val (R 33) = _; rw [hv]; simp; exact hw.zr 33 (by decide))
    (by show σ.val (R 32) = _; rw [hv]; simp; exact hw.pu)
    (by show σ.val (R 34) = _; rw [hv]; simp; exact hw.zr 34 (by decide))
    (by show σ.st (G 14) = _; rw [hst 14 (by decide)]; exact hxp)
    (by show σ.st (G 15) = _; rw [hst 15 (by decide)]; exact hup)
    (by rw [hv]; simp; exact hw.zr 28 (by decide)) (by rw [hv]; simp; exact hw.zr 29 (by decide))
    (fun v1 w1 v2 w2 u x a a' wv => (jst_emenv G hG R hR P N W V g cap σ0 hw ky ky' kl kl' jt acc ew ℓ k hk hW hKB
      hcapB (SLm G) (QLm R) (fun i => ⟨iSL i, rfl, iSL_lt i⟩)
      (fun i hi1 hi2 => ⟨iQL i, rfl, iQL_rng i hi1 hi2⟩) v1 w1 v2 w2 u x a a' wv (lw P + 1) (P.s * hh P + 1)).2)
    (by rw [recsL_length]; exact le_of_eq h6) (by omega) (by omega)
    (by rw [hhh, Nat.mul_comm P.r P.s])
    (Nat.pow_lt_pow_right (by norm_num) (by omega)) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    (fun c Pp hP => ⟨(hrng c Pp hP).1, lt_of_lt_of_le (hrng c Pp hP).2 hVW⟩)
    (fun u x => by
      constructor
      · unfold aW; split_ifs
        · exact toNat_lt_pow _ (V + 1) (hrng _ _ (by omega)).1 (hrng _ _ (by omega)).2
        · exact hini2
      · unfold aW'; split_ifs
        · exact toNat_lt_pow _ (V + 1) (hrng _ _ (by omega)).1 (hrng _ _ (by omega)).2
        · exact hini2)
    (lt_of_lt_of_le hini2 hVWn)
    c1 c2 (le_trans hlwn c3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hhh]; omega) (by omega) (by omega) c8 c9 hcapK

/-- **A join's key stream**: the target stream `G k` becomes the right half's keys, then the left half's, then the
end mark, over its old contents; every other part of the state comes back. -/
theorem kw_spec (EMR EML : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (fr' fl' : ℕ → ℕ → List Bool)
    (cR cL : ℕ) (hEmR : EmitHyp cap W V (SRm G) (G k) (R 27) (R 28) (R 29) EMR (EmEnv G R W V ℓ) fr' cR)
    (hEmL : EmitHyp cap W V (SLm G) (G k) (R 27) (R 28) (R 29) EML (EmEnv G R W V ℓ) fl' cL)
    (hfr : ∀ a b, (fr' a b).length ≤ 4 * W + 2) (hfl : ∀ a b, (fl' a b).length ≤ 4 * W + 2) :
    WExec cap (kw G R EMR EML k) (jst G R W σ0 ky ky' kl kl' jt acc ew ℓ)
      ((jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).sets (G k) (overlay
        ((List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ rw P)).flatMap (fun x =>
          fr' (min (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x))
            (max (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x)))) ++
        (List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ lw P)).flatMap (fun x =>
          fl' (min (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
              (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x))
            (max (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
              (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x)))) ++ [false])
        ((jst G R W σ0 ky ky' kl kl' jt acc ew ℓ).st (G k))))
      (enumCost (2 ^ (P.s * hh P)) (2 ^ rw P) (pointCost (hh P) P.b (fR P) 0 P.s W + cR + 200 * W + 30) (lw P + 1)
        (P.s * hh P + 1) + 1 + (enumCost (2 ^ (P.s * hh P)) (2 ^ lw P)
          (pointCost (hh P) P.b (fL P) (hh P) P.s W + cL + 200 * W + 30) (lw P + 1) (P.s * hh P + 1) + 1 +
            (5 * (2 ^ (P.s * hh P) * ((2 ^ lw P + 2 ^ rw P) * (4 * W + 2))) + 14))) := by
  set σ := jst G R W σ0 ky ky' kl kl' jt acc ew ℓ with hσ
  set Lk := σ.st (G k) with hLk
  set Rks := (List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ rw P)).flatMap (fun x =>
    fr' (min (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x))
      (max (aW P (recsR P g) (2 ^ V) 0 (fR P) N x) (aW' P (recsR P g) (2 ^ V) 0 (fR P) N u x)))) with hRks
  set Lks := (List.range (2 ^ (P.s * hh P))).flatMap (fun u => (List.range (2 ^ lw P)).flatMap (fun x =>
    fl' (min (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
        (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x))
      (max (aW P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N x)
        (aW' P (recsL P g) (keyOf V g.threshold) (hh P) (fL P) N u x)))) with hLks
  have hv := jst_val G hG R hR W σ0 ky ky' kl kl' jt acc ew ℓ
  have hshk : σ.sh (G k) = 0 := by rw [jst_sh G hG R hR]; exact hw.heads k
  have hck : σ.val (R 27) = 0 := by rw [hv]; simp; exact hw.zr 27 (by decide)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := capKW_facts P W cap hcapB
  have lR : Rks.length ≤ 2 ^ (P.s * hh P) * (2 ^ rw P * (4 * W + 2)) :=
    flatMap_len_le _ _ (fun u => flatMap_len_le _ _ (fun x => hfr _ _) _) _
  have lL : Lks.length ≤ 2 ^ (P.s * hh P) * (2 ^ lw P * (4 * W + 2)) :=
    flatMap_len_le _ _ (fun u => flatMap_len_le _ _ (fun x => hfl _ _) _) _
  have e1 : 2 ^ (P.s * hh P) * (2 ^ rw P * (4 * W + 2)) + 2 ^ (P.s * hh P) * (2 ^ lw P * (4 * W + 2)) =
      2 ^ (P.s * hh P) * ((2 ^ lw P + 2 ^ rw P) * (4 * W + 2)) := by ring
  have e2 : 2 ^ (P.s * hh P) * (2 ^ lw P + 2 ^ rw P) * (4 * W + 2) =
      2 ^ (P.s * hh P) * ((2 ^ lw P + 2 ^ rw P) * (4 * W + 2)) := by ring
  have e3 : 2 ^ (P.s * hh P) * 2 ^ rw P * (4 * W + 2) = 2 ^ (P.s * hh P) * (2 ^ rw P * (4 * W + 2)) := by ring
  have e4 : 2 ^ (P.s * hh P) * 2 ^ lw P * (4 * W + 2) = 2 ^ (P.s * hh P) * (2 ^ lw P * (4 * W + 2)) := by ring
  have xR := sideR_spec G hG R hR P N W V g cap σ0 hw ky ky' kl kl' jt acc ew ℓ k hk hW hKB hcapB EMR fr' cR hEmR hfr Lk []
    (by rw [List.length_nil, e3]; omega)
  have xL := sideL_spec G hG R hR P N W V g cap σ0 hw ky ky' kl kl' jt acc ew ℓ k hk hW hKB hcapB EML fl' cL hEmL hfl Lk
    ([] ++ Rks) (by rw [List.nil_append, e4]; omega)
  have xE := kst_end cap σ (A := G 13) (K := G k) (CA := R 28) (CK := R 27) (hG.ne (by omega)) (hR.ne (by decide))
    (by rw [jst_sh G hG R hR]; exact hw.heads 13) (by rw [hv]; simp; exact hw.zr 28 (by decide)) hshk hck Lk
    ([] ++ Rks ++ Lks) (by simp; omega)
  rw [kst_nil σ (G k) (R 27) hshk hck] at xR
  have hall := WExec.seq xR (WExec.seq xL xE)
  unfold kw
  refine WExec.cast cap hall ?_ ?_
  · simp only [List.nil_append, List.append_assoc]
  · simp only [List.nil_append, List.length_append]; omega

end SideR

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
