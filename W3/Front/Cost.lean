import W3.Front.Run
import Setup.Core

set_option autoImplicit false

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicGates.Close NearCubicGates.Close.Setup
open NearCubicGates.Close.CheckedPCPP

namespace W3.NearCubicWires.RepairSource.Outer3.Front

theorem pow_mono_X {X : ℕ} (hX : 1 ≤ X) {a b : ℕ} (h : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right hX h

/-- Phase K's cost: `C (N+1)^2 X^{3G+9}` whenever `ν < X` and `|⟨B_src⟩| ≤ X`. -/
theorem costKF_le (G : ℕ) : ∃ Ck : ℕ, ∀ ν ds X : ℕ, ν + 1 ≤ X → ds ≤ X →
    costKF G ν ds ≤ Ck * ((2 ^ ν + 1) ^ 2 * X ^ (3 * G + 9)) := by
  refine ⟨13000000000000 + 1000 * (G + 3), fun ν ds X hν hds => ?_⟩
  have hX1 : 1 ≤ X := by omega
  set M := 2 ^ ν + 1 with hM
  set E := 3 * G + 9 with hE
  set L := lenF G ν with hL
  have hM1 : 1 ≤ M := Nat.le_add_left 1 _
  have hνX : ν ≤ X := by omega
  -- the powers of X
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ (G + 2) := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hXY : X ≤ Y := by rw [hY]; exact Nat.le_self_pow (by omega) _
  have hLY : L ≤ Y := by rw [hL, hY]; exact Nat.pow_le_pow_left hνX _
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = X ^ E := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_pow _ _ (by omega)
  have hXYZ : X * Y ≤ Z := by
    rw [hY, hZ, ← pow_succ']; exact pow_mono_X hX1 (by omega)
  have hYYZ : Y * Y ≤ Z := by
    rw [hY, hZ, ← pow_add]; exact pow_mono_X hX1 (by omega)
  have hX3 : (X * Y) ^ 3 ≤ Z := by
    rw [hY, hZ, ← pow_succ', ← pow_mul]; exact pow_mono_X hX1 (by omega)
  have hYZ : Y ≤ Z := (Nat.le_mul_of_pos_left Y (by omega : 0 < X)).trans hXYZ
  -- the guards
  have hlb : lbF G ν ≤ L + 4 := size_le_self _
  have hlp : lpF ν ≤ ν := size_le_self _
  have h2lb : 2 ^ lbF G ν ≤ 2 * (L + 4) + 1 := two_pow_size _
  have h2lp : 2 ^ lpF ν ≤ 2 * ν + 1 := two_pow_size _
  have h2 : 2 ^ (lbF G ν + lpF ν) ≤ 33 * (X * Y) := by
    rw [pow_add]
    calc 2 ^ lbF G ν * 2 ^ lpF ν ≤ (2 * (L + 4) + 1) * (2 * ν + 1) := Nat.mul_le_mul h2lb h2lp
      _ ≤ (11 * Y) * (3 * X) := Nat.mul_le_mul (by omega) (by omega)
      _ = 33 * (X * Y) := by ring
  have hXXY : X ≤ X * Y := Nat.le_mul_of_pos_right _ (by omega)
  have hYXY : Y ≤ X * Y := Nat.le_mul_of_pos_left _ (by omega)
  have hev := evalCost_le ds (lbF G ν) (lpF ν)
  have hsum : ds + 2 ^ (lbF G ν + lpF ν) + lbF G ν + lpF ν + 2 ≤ 50 * (X * Y) := by omega
  have hev' : Succinct.evalCost ds (lbF G ν) (lpF ν) ≤ 12500000000000 * Z := by
    have h3 : (ds + 2 ^ (lbF G ν + lpF ν) + lbF G ν + lpF ν + 2) ^ 3 ≤ (50 * (X * Y)) ^ 3 :=
      Nat.pow_le_pow_left hsum 3
    have h4 : (50 * (X * Y)) ^ 3 = 125000 * (X * Y) ^ 3 := by ring
    nlinarith
  -- the cost
  have hP : (2 ^ ν + 1) ^ 2 * X ^ (3 * G + 9) = M * M * Z := by rw [hZ, hM]; ring
  rw [hP]
  have hZP : Z ≤ M * M * Z := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have hMZP : M * Z ≤ M * M * Z := by
    have : M * Z ≤ M * (M * Z) := Nat.le_mul_of_pos_left _ (by omega)
    rw [← Nat.mul_assoc] at this; exact this
  have hMMP : M * M ≤ M * M * Z := Nat.le_mul_of_pos_right _ (by omega)
  have hMP : M ≤ M * M := Nat.le_mul_of_pos_left _ (by omega)
  have t1 : (ν + 1) ^ 2 ≤ Z := by
    calc (ν + 1) ^ 2 ≤ X * X := by rw [sq]; exact Nat.mul_le_mul hν hν
      _ ≤ X * Y := Nat.mul_le_mul_left _ hXY
      _ ≤ Z := hXYZ
  have t2 : (L + ν + 1) ^ 2 ≤ 4 * Z := by
    calc (L + ν + 1) ^ 2 ≤ (2 * Y) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * (Y * Y) := by ring
      _ ≤ 4 * Z := Nat.mul_le_mul_left _ hYYZ
  have t3 : lbF G ν * (12 * (L + 4) + 30) ≤ 450 * Z := by
    calc lbF G ν * (12 * (L + 4) + 30) ≤ (5 * Y) * (90 * Y) := Nat.mul_le_mul (by omega) (by omega)
      _ = 450 * (Y * Y) := by ring
      _ ≤ 450 * Z := Nat.mul_le_mul_left _ hYYZ
  have t4 : M * (Succinct.evalCost ds (lbF G ν) (lpF ν) + 14 * 2 ^ ν + 40 + 10) ≤
      12500000000000 * (M * Z) + 64 * (M * M) := by
    have hNM : 2 ^ ν + 1 = M := hM.symm
    nlinarith
  unfold costKF Succinct.checkCost Succinct.pointCost
  rw [← hL]
  have t2' : 100 * (G + 3) * (L + ν + 1) ^ 2 ≤ 400 * (G + 3) * Z := by
    calc 100 * (G + 3) * (L + ν + 1) ^ 2 ≤ 100 * (G + 3) * (4 * Z) := Nat.mul_le_mul_left _ t2
      _ = 400 * (G + 3) * Z := by ring
  have t5 : 400 * (G + 3) * Z ≤ 400 * (G + 3) * (M * M * Z) := Nat.mul_le_mul_left _ hZP
  have t6 : 1000 * (G + 3) * (M * M * Z) = 1000 * ((G + 3) * (M * M * Z)) := by ring
  have t7 : 400 * (G + 3) * (M * M * Z) = 400 * ((G + 3) * (M * M * Z)) := by ring
  have t8 : (13000000000000 + 1000 * (G + 3)) * (M * M * Z) =
      13000000000000 * (M * M * Z) + 1000 * ((G + 3) * (M * M * Z)) := by ring
  rw [t8]
  rw [t7] at t5
  rw [← hM]
  omega

section CostF
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G) (A : OuterM.ARun mw SV) (h : H2D)

theorem costF_le : ∃ K e : ℕ, ∀ ν ds dp dw dc q m : ℕ, ν < q → dw ≤ ds + ν + A.K * (ν + 1) ^ A.e →
    2 * dc + 1 ≤ dw + dp + h.K * (dw + dp + q + 1) ^ h.e → m ≤ dc →
    2 * costF mw SV A h ν ds dp dw dc q m + 2 ≤ K * (2 ^ ν + 1) ^ 2 * (ds + dp + q + 1) ^ e := by
  obtain ⟨Ck, hCk⟩ := costKF_le G
  set a := A.e with ha
  set b := h.e with hb
  set aK := A.K with haK
  set hK := h.K with hhK
  set ed := (a + 1) * (b + 1) with hed
  set Cd := (hK + 1) * (aK + 3) ^ (b + 1) with hCd
  set c1 := hK * (aK + 3) ^ b with hc1
  set c2 := 160 * (Cd + 3) ^ 2 with hc2
  refine ⟨2 * (23 + 1000 + 50 + aK + c1 + c2 + 34 * Cd + 7 + 41 + Ck + 20) + 2, 2 * ed + 3 * G + 9,
    fun ν ds dp dw dc q m hνq hdw hdc hm => ?_⟩
  set X := ds + dp + q + 1 with hX
  set M := 2 ^ ν + 1 with hM
  set E := 2 * ed + 3 * G + 9 with hE
  have hX1 : 1 ≤ X := by omega
  have hνX : ν + 1 ≤ X := by omega
  have hM1 : 1 ≤ M := Nat.le_add_left 1 _
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = X ^ E := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_pow _ _ (by omega)
  have pz : ∀ c, c ≤ E → X ^ c ≤ Z := fun c hc => by rw [hZ]; exact pow_mono_X hX1 hc
  have hXZ : X ≤ Z := by have := pz 1 (by omega); simpa using this
  set P := M * M * Z with hP
  have hZP : Z ≤ P := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have hMMP : M * M ≤ P := Nat.le_mul_of_pos_right _ (by omega)
  have hMP : M ≤ P := (Nat.le_mul_of_pos_left M (by omega : 0 < M)).trans hMMP

  have hXa : (ν + 1) ^ a ≤ X ^ a := Nat.pow_le_pow_left hνX a
  have hXa1 : X ^ a ≤ X ^ (a + 1) := pow_mono_X hX1 (by omega)
  have hX_a1 : X ≤ X ^ (a + 1) := by have := pow_mono_X hX1 (show 1 ≤ a + 1 by omega); simpa using this
  have hdw' : dw ≤ (aK + 2) * X ^ (a + 1) := by
    have : aK * (ν + 1) ^ a ≤ aK * X ^ (a + 1) := Nat.mul_le_mul_left _ (hXa.trans hXa1)
    have e : (aK + 2) * X ^ (a + 1) = aK * X ^ (a + 1) + 2 * X ^ (a + 1) := by ring
    rw [e]; omega
  have hW : dw + dp + q + 1 ≤ (aK + 3) * X ^ (a + 1) := by
    have e : (aK + 3) * X ^ (a + 1) = (aK + 2) * X ^ (a + 1) + X ^ (a + 1) := by ring
    rw [e]; omega
  have hWb : (dw + dp + q + 1) ^ b ≤ (aK + 3) ^ b * X ^ ((a + 1) * b) := by
    calc (dw + dp + q + 1) ^ b ≤ ((aK + 3) * X ^ (a + 1)) ^ b := Nat.pow_le_pow_left hW b
      _ = (aK + 3) ^ b * X ^ ((a + 1) * b) := by rw [mul_pow, ← pow_mul]
  have hW1 : 1 ≤ dw + dp + q + 1 := by omega
  have hdcC : dc ≤ Cd * X ^ ed := by
    have e1 : dw + dp + q + 1 ≤ (dw + dp + q + 1) ^ (b + 1) := Nat.le_self_pow (by omega) _
    have e2 : (dw + dp + q + 1) ^ b ≤ (dw + dp + q + 1) ^ (b + 1) := pow_mono_X hW1 (by omega)
    have e3 : (dw + dp + q + 1) ^ (b + 1) ≤ (aK + 3) ^ (b + 1) * X ^ ed := by
      calc (dw + dp + q + 1) ^ (b + 1) ≤ ((aK + 3) * X ^ (a + 1)) ^ (b + 1) := Nat.pow_le_pow_left hW _
        _ = (aK + 3) ^ (b + 1) * X ^ ed := by rw [mul_pow, ← pow_mul]
    have e4 : hK * (dw + dp + q + 1) ^ b ≤ hK * (dw + dp + q + 1) ^ (b + 1) := Nat.mul_le_mul_left _ e2
    have e5 : dc ≤ (hK + 1) * (dw + dp + q + 1) ^ (b + 1) := by
      have e : (hK + 1) * (dw + dp + q + 1) ^ (b + 1) =
          hK * (dw + dp + q + 1) ^ (b + 1) + (dw + dp + q + 1) ^ (b + 1) := by ring
      rw [e]; omega
    have e6 : (hK + 1) * (dw + dp + q + 1) ^ (b + 1) ≤ Cd * X ^ ed := by
      rw [hCd, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ e3
    exact e5.trans e6
  have hdc' : dc + 3 ≤ (Cd + 3) * X ^ ed := by
    have e7 : 1 ≤ X ^ ed := Nat.one_le_pow _ _ (by omega)
    have e : (Cd + 3) * X ^ ed = Cd * X ^ ed + 3 * X ^ ed := by ring
    rw [e]; omega
  have ha_ed : a + 1 ≤ ed := Nat.le_mul_of_pos_right _ (by omega)
  have hab_ed : (a + 1) * b ≤ ed := Nat.mul_le_mul_left _ (by omega)
  -- the terms
  have T3 : aK * (ν + 1) ^ a ≤ aK * P :=
    Nat.mul_le_mul_left _ ((hXa.trans (pz a (by omega))).trans hZP)
  have T4 : hK * (dw + dp + q + 1) ^ b ≤ c1 * P := by
    rw [hc1, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (hWb.trans (Nat.mul_le_mul_left _ ((pz _ (by omega)).trans hZP)))
  have T5 : 2 * DescW.readCost dc ≤ c2 * P := by
    unfold DescW.readCost
    have r1 : (dc + 3) * (80 * dc + 120) ≤ 80 * ((dc + 3) * (dc + 3)) := by nlinarith
    have r2 : (dc + 3) * (dc + 3) ≤ ((Cd + 3) * X ^ ed) * ((Cd + 3) * X ^ ed) := Nat.mul_le_mul hdc' hdc'
    have r3 : ((Cd + 3) * X ^ ed) * ((Cd + 3) * X ^ ed) = (Cd + 3) ^ 2 * X ^ (2 * ed) := by ring
    have r4 : X ^ (2 * ed) ≤ P := (pz _ (by omega)).trans hZP
    have r5 : (Cd + 3) ^ 2 * X ^ (2 * ed) ≤ (Cd + 3) ^ 2 * P := Nat.mul_le_mul_left _ r4
    have e : c2 * P = 160 * ((Cd + 3) ^ 2 * P) := by rw [hc2]; ring
    rw [e]; omega
  have T6 : 34 * m + 7 ≤ 34 * Cd * P + 7 * P := by
    have r1 : X ^ ed ≤ P := (pz _ (by omega)).trans hZP
    have r2 : Cd * X ^ ed ≤ Cd * P := Nat.mul_le_mul_left _ r1
    have e : 34 * Cd * P = 34 * (Cd * P) := by ring
    have hP1 : 1 ≤ P := hZ1.trans hZP
    rw [e]; omega
  have T7 : costKF G ν ds ≤ Ck * P := by
    have r1 := hCk ν ds X hνX (by omega)
    have r2 : (2 ^ ν + 1) ^ 2 * X ^ (3 * G + 9) ≤ P := by
      rw [hP, ← hM, sq]; exact Nat.mul_le_mul_left _ (pz _ (by omega))
    exact r1.trans (Nat.mul_le_mul_left _ r2)
  have T8 : 1000 * (2 ^ ν + 1) ^ 2 ≤ 1000 * P := by rw [← hM, sq]; exact Nat.mul_le_mul_left _ hMMP
  have T9 : q ≤ P := by omega
  have T10 : ν ≤ P := by omega
  have hgoal : (2 * (23 + 1000 + 50 + aK + c1 + c2 + 34 * Cd + 7 + 41 + Ck + 20) + 2) * (2 ^ ν + 1) ^ 2 * X ^ E =
      2 * (23 * P + 1000 * P + 50 * P + aK * P + c1 * P + c2 * P + 34 * Cd * P + 7 * P + 41 * P + Ck * P +
        20 * P) + 2 * P := by
    rw [hP, hZ, ← hM]; ring
  rw [hgoal]
  unfold costF powCostP
  rw [← ha, ← hb, ← haK, ← hhK]
  omega

end CostF

end W3.NearCubicWires.RepairSource.Outer3.Front
