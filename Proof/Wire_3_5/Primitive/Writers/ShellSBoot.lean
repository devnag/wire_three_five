import Proof.Wire_3_5.Primitive.Writers.ShellTRun

/-! # The SYM writer shell v2, part 1: ShellX's boot over any dimension stage

ShellX (`ShellXBoot`/`ShellXRun`) dimensions the SYM writer's scrub and loop by `n' = 2^(mOf P)`, `mOf P = 2·kh + L`.
The SYM tape's FILTER and POP units need `2^{Θ(L²)}` and `2^{Θ(√B·L)}`, so the SYM shell v2 takes its dimension
stage as a parameter, exactly as the THR shell does (`ShellT.DimOK`, build once): ShellX's boot with the stage
`M2` of `DimOK` in place of `NumsX.numsM`.

* `bootXMS` (ShellX's boot with any dimension stage), **`bootX_stepS`** (the loop's entry data on the real layout, the
  data tape `Data.dataWord (Data.symCounts a' Cs carriers)`, the counter `word b`, `b = CL(2^m+1)^DL`).

Paper quantity of the main type: the SYM call's counts on the writer's data tape (lem:primitive P3:3068-3084) and the
loop's dimension `2^m` (prim:runtime P3:3089-3108: the preprocessing term `2^{O(Ψ)}`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellS
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline

section Boot
variable {x D D2 Dv DL : ℕ}

/-- **The SYM boot with any dimension stage** (`ShellX.bootXM` at `M2 = NumsX.numsM cr`). -/
noncomputable def bootXMS (x D D2 Dv DL C2 Cv CL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine (MX0 x D D2 Dv DL C2) (MX1 x D D2 Dv DL Cv))
      (RecoveryFocus.machine (q2 x D D2 Dv DL) M2)) (MX3 x D D2 Dv DL)) (MX4 x D D2 Dv DL CL)) (MX5 x D D2 Dv DL))
    (act6 x D D2 Dv DL).compile

/-- **ShellX's boot with any dimension stage**: from the writer's entry bank on the SYM call's request word, the loop's
entry data on the real layout, the workspace `Scrub.calcIn D 2^m` and the counter `word b`, `b = CL(2^m+1)^DL`. -/
theorem bootX_stepS {s2 : ℕ} (M2 : Machine NUn s2) (c2 m : ℕ) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (C2 Cv CL : ℕ)
    (hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : DataOK Cs carriers (UnaryCalc.value D2 C2 n))
    (hx2 : ShellT.DimOK x D D2 Dv DL M2 c2 m w (UnaryCalc.value Dv Cv n)) :
    ∃ Bf : Fin (STx x D D2 Dv DL) → List Bool,
      Step (bootXMS x D D2 Dv DL C2 Cv CL M2) (ShellT.bootXCostG w n D2 C2
          (Data.coreCost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv c2 m DL CL)
        (fun _ => 0) (A0 w) (HF x D D2 Dv DL) Bf ∧
      Bf (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0)) = frame w ∧
      Bf (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)) = [false] ∧
      Bf (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 2)) = [] ∧
      (∀ c, kept x c = false → (Bf (lo (cT (D := D) (D1 := 0) (D2 := D2) c))).length ≤ bootCost w n 0 0) ∧
      (∀ j, Bf (lo (wT (x := x) (D1 := 0) (D2 := D2) j)) = Scrub.calcIn D (2 ^ m) j) ∧
      Bf (lo (lgT (x := x) (D := D) (D1 := 0) (D2 := D2))) = [] ∧
      Bf (lo (drT (x := x) (D := D) (D1 := 0) (D2 := D2))) = [] ∧
      Bf (TK x D D2 Dv DL) = RepairSource.VerifierDecoding.CompareMachine.word
        (UnaryCalc.value DL CL (2 ^ m)) ∧
      Bf (lo (dT (x := x) (D := D) (D1 := 0) (D2 := D2))) = Data.dataWord (Data.symCounts a' Cs carriers) := by
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hT := TT_lt_SD (x := x) (D := D) (D2 := D2)
  have hTT : 674 ≤ TT x := by unfold TT LNS LNR; omega
  have hN : NUn = 38 := rfl
  have hwk1 : 1 ≤ Scrub.wk D := by rw [Scrub.wk_eq]; omega
  obtain ⟨W, hWd⟩ : ∃ W, UnaryCalc.value Dv Cv n = W := ⟨_, rfl⟩
  rw [hWd] at hx2
  obtain ⟨b, hb⟩ : ∃ b, UnaryCalc.value DL CL (2 ^ m) = b := ⟨_, rfl⟩
  rw [hb]
  -- 0
  obtain ⟨B8, s0, e0, e1, e2, ewk, edt, escr⟩ := x0_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    Cs carriers tl w C2 hw hD
  obtain ⟨Bx0, hBx0⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) (A0 w) B8 :=
    ⟨_, rfl⟩
  rw [← hBx0] at s0
  have b0lo : ∀ i : Fin (SD x D D2), i.val < TT x + 1 → Bx0 (lo i) = B8 i := by
    intro i hi
    rw [hBx0, ← pX_lo (Dv := Dv) (DL := DL) i hi]
    exact install_slot _ pX_inj _ _ i
  have b0hi : ∀ i : Fin (STx x D D2 Dv DL), SD x D D2 + SD x D D2 ≤ i.val → Bx0 i = [] := by
    intro i hi
    rw [hBx0, inst_keep _ _ _ _ (fun j => by
      unfold pX; split_ifs
      · have := lo_lt (Dv := Dv) (DL := DL) j; omega
      · have := im_lt (Dv := Dv) (DL := DL) j; omega)]
    have hne : i ≠ lo (cs 0) := by
      intro e; have := lo_lt (Dv := Dv) (DL := DL) (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0); rw [← e] at this; omega
    simp [A0, hne]
  have b0lo_ge : ∀ i : Fin (SD x D D2), TT x + 1 ≤ i.val → Bx0 (lo i) = [] := by
    intro i hi
    rw [hBx0, inst_keep _ _ _ _ (fun j => by
      unfold pX; split_ifs with hj
      · simp only [lo_val, lo_val]; omega
      · have := im_ge (Dv := Dv) (DL := DL) j; have := i.isLt; simp only [lo_val]; omega)]
    have hne : lo (Dv := Dv) (DL := DL) i ≠ lo (cs 0) := by
      intro e; have := congrArg Fin.val e; rw [lo_val, lo_val] at this
      have h0 : (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0).val = 0 := rfl
      omega
    simp [A0, hne]
  have b0im : ∀ i : Fin (SD x D D2), TT x + 1 ≤ i.val → Bx0 (im i) = B8 i := by
    intro i hi
    rw [hBx0, ← pX_im (Dv := Dv) (DL := DL) i hi]
    exact install_slot _ pX_inj _ _ i
  -- 1
  obtain ⟨out1, s1, o1⟩ := x1_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) Cv n Bx0
    (by
      show Bx0 (im (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)))) = _
      rw [b0im (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D))) (by rw [wT_val]; exact Nat.le_add_right _ _), ewk]
      simp only [Scrub.calcIn, Fin.addCases_left]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape])
    (fun k => b0hi _ (by simp only [e5_val]; omega))
  rw [hWd] at o1
  obtain ⟨Bx1, hBx1⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (q1 x D D2 Dv DL) Bx0 out1 := ⟨_, rfl⟩
  rw [← hBx1] at s1
  have k1 : ∀ i : Fin (STx x D D2 Dv DL), i.val < SD x D D2 → Bx1 i = Bx0 i := by
    intro i hi
    rw [hBx1, inst_keep _ _ _ _ (fun j => by have := q1_val_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j; omega)]
  have k1' : ∀ i : Fin (STx x D D2 Dv DL), SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv ≤ i.val → Bx1 i = Bx0 i := by
    intro i hi
    rw [hBx1, inst_keep _ _ _ _ (fun j => by
      unfold q1; split_ifs
      · simp only [TI_val]; omega
      · rw [e5_val]; have := j.isLt; omega)]
  have o1' : Bx1 (TW x D D2 Dv DL) = List.replicate W true := by
    have hq : q1 x D D2 Dv DL (UnaryCalc.outputTape Dv) = TW x D D2 Dv DL := by
      unfold q1; rw [if_neg]; rfl
      intro e; have := congrArg Fin.val e; rw [outTape_val, inTape_val] at this; omega
    rw [hBx1, ← hq, install_slot _ q1_inj]
    exact o1
  -- 2
  obtain ⟨tout2, s2, o2, i2⟩ := hx2 Bx1
    (by rw [k1 (T0 x D D2 Dv DL) (by simp only [T0_val]; omega)]; show Bx0 (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0)) = _; rw [b0lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0) cs0_lt, e0]) o1'
    (fun k => by
      rw [k1' (nu (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [nu_val]; omega)]
      exact b0hi _ (by simp only [nu_val]; omega))
  obtain ⟨Bx2, hBx2⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (q2 x D D2 Dv DL) Bx1 tout2 := ⟨_, rfl⟩
  rw [← hBx2] at s2
  have k2 : ∀ i : Fin (STx x D D2 Dv DL), i.val ≠ 0 → i.val < SD x D D2 + SD x D D2 → Bx2 i = Bx1 i := by
    intro i h0 hi
    rw [hBx2, inst_keep _ _ _ _ (fun j => by
      rcases q2_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with e | e <;> omega)]
  have k2' : ∀ i : Fin (STx x D D2 Dv DL), SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv + NUn ≤ i.val →
      Bx2 i = Bx1 i := by
    intro i hi
    rw [hBx2, inst_keep _ _ _ _ (fun j => by
      rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;>
        rw [e]
      · simp only [T0_val]; omega
      · rw [TW_val]; have := outTape_lt Dv; omega
      · rw [nu_val]; have := j.isLt; omega)]
  have o2' : Bx2 (TS x D D2 Dv DL) = NumsX.srcWord m := by
    have hq : q2 x D D2 Dv DL oN = TS x D D2 Dv DL := by
      unfold q2; rw [if_neg (by decide), if_neg (by decide)]; rfl
    rw [hBx2, ← hq, install_slot _ q2_inj]
    exact o2
  have i2' : Bx2 (T0 x D D2 Dv DL) = frame w := by
    have hq : q2 x D D2 Dv DL iN = T0 x D D2 Dv DL := by unfold q2; rw [if_pos rfl]
    rw [hBx2, ← hq, install_slot _ q2_inj]
    exact i2
  -- 3
  obtain ⟨out3, s3, o8, o9⟩ := x3_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) m Bx2 o2'
    (by
      have tc1 : (TC x D D2 Dv DL).val ≠ 0 := by rw [TC_val]; omega
      have tc2 : (TC x D D2 Dv DL).val < SD x D D2 + SD x D D2 := lt_of_lt_of_le hT (Nat.le_add_right _ _)
      have tc3 : (TC x D D2 Dv DL).val < SD x D D2 := hT
      rw [k2 (TC x D D2 Dv DL) tc1 tc2, k1 (TC x D D2 Dv DL) tc3]
      show Bx0 (lo (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)))) = []
      exact b0lo_ge _ (by rw [wT_val]; exact Nat.le_add_right _ _))
    (by
      rw [k2' (TE x D D2 Dv DL) (by simp only [TE_val]; omega), k1' (TE x D D2 Dv DL) (by simp only [TE_val]; omega)]
      exact b0hi _ (by simp only [TE_val]; omega))
    (fun k => by
      rw [k2' (ca (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [ca_val]; omega), k1' (ca (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [ca_val]; omega)]
      exact b0hi _ (by simp only [ca_val]; omega))
  obtain ⟨Bx3, hBx3⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (q3 x D D2 Dv DL) Bx2 out3 := ⟨_, rfl⟩
  rw [← hBx3] at s3
  have k3 : ∀ i : Fin (STx x D D2 Dv DL), i.val ≠ TT x + 1 → i.val < SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv →
      Bx3 i = Bx2 i := by
    intro i h1 hi
    rw [hBx3, inst_keep _ _ _ _ (fun j => by
      rcases q3_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with e | e <;> omega)]
  have o8' : Bx3 (TC x D D2 Dv DL) = List.replicate (2 ^ m) true := by
    have hq : q3 x D D2 Dv DL 8 = TC x D D2 Dv DL := by unfold q3; rw [if_neg (by decide), if_pos rfl]
    rw [hBx3, ← hq, install_slot _ q3_inj]
    exact o8
  have o9' : Bx3 (TE x D D2 Dv DL) = List.replicate (2 ^ m) true := by
    have hq : q3 x D D2 Dv DL 9 = TE x D D2 Dv DL := by
      unfold q3; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    rw [hBx3, ← hq, install_slot _ q3_inj]
    exact o9
  -- 4
  obtain ⟨out4, s4, o4⟩ := x4_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) CL (2 ^ m) Bx3 o9'
    (fun k hk => by
      have hk0 : k.val ≠ 0 := fun e => hk (Fin.ext e)
      rw [hBx3, inst_keep _ _ _ _ (fun j => by
        rcases q3_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with
            ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, e⟩ <;> rw [e]
        · simp only [TS_val, e6_val]; omega
        · simp only [TC_val, e6_val]; omega
        · simp only [TE_val, e6_val]; omega
        · rw [ca_val, e6_val]; have := j.isLt; omega)]
      rw [k2' (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [e6_val]; omega), k1' (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [e6_val]; omega)]
      exact b0hi _ (by simp only [e6_val]; omega))
  rw [hb] at o4
  obtain ⟨Bx4, hBx4⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) Bx3 out4 :=
    ⟨_, rfl⟩
  rw [← hBx4] at s4
  have k4 : ∀ i : Fin (STx x D D2 Dv DL), i.val < SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv + NUn + 12 →
      Bx4 i = Bx3 i := by
    intro i hi
    rw [hBx4, inst_keep _ _ _ _ (fun j => by
      simp only [e6_val]; omega)]
  have o4' : Bx4 (TO x D D2 Dv DL) = List.replicate b true := by
    rw [hBx4, show TO x D D2 Dv DL = e6 (UnaryCalc.outputTape DL) from rfl, install_slot _ e6_inj]
    exact o4
  -- 5
  have hK4 : Bx4 (TK x D D2 Dv DL) = [] := by
    have vK := TK_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    rw [k4 (TK x D D2 Dv DL) (lt_of_lt_of_le TK_lt sd_le3), k3 (TK x D D2 Dv DL) (by rw [TK_val]; omega) (lt_of_lt_of_le TK_lt sd_le2),
      k2 (TK x D D2 Dv DL) (by rw [TK_val]; omega) (lt_of_lt_of_le TK_lt (Nat.le_add_right _ _)), k1 (TK x D D2 Dv DL) TK_lt]
    exact b0lo_ge _ (by simp only [kT_val]; omega)
  have s5 := x5_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) b Bx4 o4' hK4
  obtain ⟨Bx5, hBx5⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install ![TO x D D2 Dv DL, TK x D D2 Dv DL] Bx4
      (fun i => if i.val = 0 then List.replicate b true else RepairSource.VerifierDecoding.CompareMachine.word b) :=
    ⟨_, rfl⟩
  rw [← hBx5] at s5
  have k5 : ∀ i : Fin (STx x D D2 Dv DL), i.val ≠ (TK x D D2 Dv DL).val → i.val < SD x D D2 → Bx5 i = Bx4 i := by
    intro i hk hi
    rw [hBx5, inst_keep _ _ _ _ (fun j => by
      rcases q5_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with e | e <;> rw [e]
      · simp only [TO_val]; omega
      · exact fun e' => hk e'.symm)]
  -- the low region through stages 1–5
  have keep : ∀ i : Fin (SD x D D2), i.val ≠ 0 → i.val ≠ TT x + 1 →
      i.val ≠ TT x + 1 + Scrub.wk D + 2 → Bx5 (lo i) = Bx0 (lo i) := by
    intro i h0 h1 hk
    have hl := lo_lt (Dv := Dv) (DL := DL) i
    rw [k5 (lo (Dv := Dv) (DL := DL) i) (by rw [TK_val, lo_val]; exact hk) hl, k4 (lo (Dv := Dv) (DL := DL) i) (lt_of_lt_of_le hl sd_le3), k3 (lo (Dv := Dv) (DL := DL) i) (by rw [lo_val]; exact h1) (lt_of_lt_of_le hl sd_le2),
      k2 (lo (Dv := Dv) (DL := DL) i) (by rw [lo_val]; exact h0) (lt_of_lt_of_le hl (Nat.le_add_right _ _)), k1 (lo (Dv := Dv) (DL := DL) i) hl]
  -- 6
  have hcs1 : Bx5 (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)) = [false] := by
    rw [keep (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1) (by rw [cs1_val]; omega) (by rw [cs1_val]; omega) (by rw [cs1_val]; omega), b0lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1) (by
      have := cs_lt (x := x) (D := D) (D1 := 0) (D2 := D2) 1; omega), e1]
  have s6 := x6_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) Bx5 hcs1
  refine ⟨Bx5, (((((s0.seq s1).seq s2).seq s3).seq s4).seq s5).seq s6 |>.enlarge (by unfold ShellT.bootXCostG; omega),
    ?_, hcs1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the request
    have v0 := T0_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    have vK := TK_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    show Bx5 (T0 x D D2 Dv DL) = _
    rw [k5 (T0 x D D2 Dv DL) (by omega) T0_lt, k4 (T0 x D D2 Dv DL) (lt_of_lt_of_le T0_lt sd_le3), k3 (T0 x D D2 Dv DL) (by omega) (lt_of_lt_of_le T0_lt sd_le2)]
    exact i2'
  · rw [keep (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 2) (by rw [cs2_val]; omega) (by rw [cs2_val]; omega) (by rw [cs2_val]; omega), b0lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 2) (by
      have := cs_lt (x := x) (D := D) (D1 := 0) (D2 := D2) 2; omega), e2]
  · intro c hc
    have hne : c ≠ sTape (sk x 0) := by intro e; subst e; simp [kept] at hc
    have hv : c.val ≠ 0 := by
      intro e
      apply hne
      apply Fin.ext
      rw [e]; rfl
    have hlt := c.isLt
    rw [keep (cT (D := D) (D1 := 0) (D2 := D2) c) (by rw [cT_val]; exact hv) (by simp only [cT_val]; omega) (by simp only [cT_val]; omega),
      b0lo (cT (D := D) (D1 := 0) (D2 := D2) c) (by simp only [cT_val]; omega)]
    exact escr c hc
  · intro j
    by_cases hj : j = Fin.castAdd 1 (UnaryCalc.inputTape D)
    · subst hj
      show Bx5 (TC x D D2 Dv DL) = _
      rw [k5 (TC x D D2 Dv DL) (by rw [TK_val, TC_val]; omega) TC_lt, k4 (TC x D D2 Dv DL) (lt_of_lt_of_le TC_lt sd_le3), o8']
      simp only [Scrub.calcIn, Fin.addCases_left]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
    · have hj0 : j.val ≠ 0 := by
        intro e
        apply hj
        apply Fin.ext
        rw [e]; rfl
      have hlt := j.isLt
      rw [keep (wT (x := x) (D1 := 0) (D2 := D2) j) (by simp only [wT_val]; omega) (by simp only [wT_val]; omega) (by simp only [wT_val]; omega),
        b0lo_ge (wT (x := x) (D1 := 0) (D2 := D2) j) (by simp only [wT_val]; omega)]
      revert hj
      refine Fin.addCases (fun k => ?_) (fun u => ?_) j
      · intro hk
        have hk0 : k.val ≠ 0 := by
          intro e; apply hk; apply Fin.ext; simp only [Fin.val_castAdd]; rw [e]; rfl
        simp [Scrub.calcIn, RepairSource.ProjectionNormalization.DimensionPolynomial.input, hk0]
      · intro _
        simp [Scrub.calcIn]
  · rw [keep (lgT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [lgT_val]; omega) (by rw [lgT_val]; omega) (by rw [lgT_val]; omega),
      b0lo_ge (lgT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [lgT_val]; omega)]
  · rw [keep (drT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [drT_val]; omega) (by rw [drT_val]; omega) (by rw [drT_val]; omega),
      b0lo_ge (drT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [drT_val]; omega)]
  · have e := install_slot (![TO x D D2 Dv DL, TK x D D2 Dv DL]) (ListMachine.Row.pair_inj TO_ne_TK) Bx4
      (fun i => if i.val = 0 then List.replicate b true else RepairSource.VerifierDecoding.CompareMachine.word b) 1
    rw [hBx5]
    exact e
  · rw [keep (dT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by simp only [dT_val]; omega) (by simp only [dT_val]; omega) (by simp only [dT_val]; omega),
      b0lo (dT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by simp only [dT_val]; omega), edt]

end Boot

end NearCubicWires.WireExponent3_5.PrimAsm.ShellS
