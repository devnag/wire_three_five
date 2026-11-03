import Proof.Wire_3_5.Primitive.SeedFix.TS4Cap
import Proof.Wire_3_5.Primitive.Writers.SymDecReq
import Proof.Wire_3_5.Primitive.Writers.SymDecStreams
import Proof.Wire_3_5.Primitive.Writers.Emit
import Proof.Wire_3_5.Primitive.Writers.NumsX

/-! # thrStage4U, part 2: the numbers machine's three inputs `1^{|carriers|}`, `1^{cap_T}`, `1^V`

P3:3083-3086 (the named carriers), P3:3425-3430 (the THR filter's cap `cap_T = B_T(n)`, tr:B) and W6's count `V`
(`NumsPort4`'s `1^V`, dominating every register value): from the framed THR request `frame (reqW n mb codes cc tl)`
and the fill count `1^W`, a register program on PA's SYM-decode layout (`LNS 0`, `LNR`) leaves
* `1^{|cc|}` on stream `3` (PA's `reqParse_spec`: `n`, `a`, `|cc|`),
* `1^{cap_T}` on stream `4` (`starCapT_spec`: `cap_T = Ledger.rowBCap C .thr r s(n) n`),
* `1^{W + (n+1)^{26}}` on stream `5` (the count `V`: `W` read from the fill count, `(n+1)^{26}` by PA's `powConstW`),
the request and the fill count kept on streams `0`, `1`.

* the registers `rK1 … rB4`, `Rp`; `p0W`, `P0Need`, `p0Cost`, **`p0_spec`**;
* `fillS`, `σS`, `rawS`, `fillS_exec`; `p0P`, **`p0M`** (every head back at `0`), **`p0_step`**.

Paper quantities of the main type: `|carriers|`, the THR cap `B_T(n)`, and W6's count `V = W + (n+1)^{26}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-! ## The registers -/

def rK1 : Fin LNR := ⟨400, by decide⟩
def rT1 : Fin LNR := ⟨401, by decide⟩
def rO1 : Fin LNR := ⟨402, by decide⟩
def rO2 : Fin LNR := ⟨403, by decide⟩
def rO3 : Fin LNR := ⟨404, by decide⟩
def rW : Fin LNR := ⟨405, by decide⟩
def rB0 : Fin LNR := ⟨406, by decide⟩
def rB1 : Fin LNR := ⟨407, by decide⟩
def rB2 : Fin LNR := ⟨408, by decide⟩
def rB3 : Fin LNR := ⟨409, by decide⟩
def rB4 : Fin LNR := ⟨410, by decide⟩

/-- The power block: `rB0 ^ e` into `rB1`. -/
def Rp : Fin 5 ↪ Fin LNR := ⟨![rB0, rB1, rB2, rB3, rB4], by decide⟩

theorem Rp0 : Rp 0 = rB0 := rfl
theorem Rp1 : Rp 1 = rB1 := rfl

/-- The registers `400 …` are outside PA's star, sparse and cap blocks. -/
theorem out_hi (r : Fin LNR) (h : 400 ≤ r.val) : SymDec.Outside r := by
  unfold SymDec.Outside; omega

/-- **The prep program.** -/
def p0W (cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM (LNS 0) LNR :=
  .seq (reqParseW 0)
  (.seq (Emit.repRegW (sk 0 3) rO1 dNC rK1 rT1 [true])
  (.seq (capTW 0 cr ζ Cδ C)
  (.seq (Emit.repRegW (sk 0 4) rO2 (Hb 13) rK1 rT1 [true])
  (.seq (SymDec.readUW (sk 0 1) rW)
  (.seq (FinalPass.Hash4.wcopyR dN rB0 rT1)
  (.seq (.inc rB0)
  (.seq (UnaryPow.powConstW Rp 26)
  (.seq (addTo rB1 rW rT1)
  (Emit.repRegW (sk 0 5) rO3 rW rK1 rT1 [true])))))))))

/-- The THR cap at `n`. -/
def capTOf (cr n : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) : ℕ :=
  Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n

/-- **The prep's capacity needs** at the fill count `W` (capacity `2W + 2`). -/
structure P0Need (W n : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (cr a nc Kb : ℕ) : Prop where
  hq : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength a + 1) + 2 ^ (natBitLength nc + 1) + Kb + n + a + 1 ≤
    2 * W + 2
  hcS : 4 * n + 2 * cr + 20 ≤ 2 * W + 2
  hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1) ≤ 2 * W + 2
  hcC : SymDec.CapNeed C .thr n (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) (2 * W + 2)
  hcT : capTOf cr n h0 h1 Cδ C ≤ 2 * W + 2
  hV : (n + 1) ^ 26 ≤ W + 2

/-- The prep's cost bound. -/
def p0Cost (n cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (a nc Kb W : ℕ) : ℕ :=
  reqParseCost n a nc Kb + 1 + ((18 * nc + 3 + 1 + (nc * 12 + 1)) + 1 +
    (capTCost (2 * W + 2) n cr (Ledger.rowBt h0 h1 n) (Ledger.rowBSparse h0 h1 2 Cδ n) (Ledger.Lq n) +
      1 + ((18 * capTOf cr n h0 h1 Cδ C + 3 + 1 + (capTOf cr n h0 h1 Cδ C * 12 + 1)) + 1 + ((7 * W + 1) + 1 +
        ((18 * n + 3) + 1 + (3 + 1 + ((26 + 1) * (4 * UnaryPow.sq (2 * W + 2)) + 1 +
          ((18 * (n + 1) ^ 26 + 3) + 1 +
            (18 * (W + (n + 1) ^ 26) + 3 + 1 + ((W + (n + 1) ^ 26) * 12 + 1))))))))))

/-- The register-language state after the fill: registers `0` at capacity `2W + 2`, the request on `0`, the fill count
on `1`, the fill's marker tape on `2`, every head at `0`. -/
def σS (w : List Bool) (W : ℕ) : WState (LNS 0) LNR :=
  ⟨fun _ => 0, fun s => if s = sk 0 0 then RepairOrdinary.frame w else if s = sk 0 1 then List.replicate W true
    else if s = sk 0 2 then List.replicate (2 * W + 3) false else [], fun _ => 0, false⟩

theorem d01 : sk 0 0 ≠ sk 0 1 := by decide
theorem d02 : sk 0 0 ≠ sk 0 2 := by decide
theorem d03 : sk 0 0 ≠ sk 0 3 := by decide
theorem d04 : sk 0 0 ≠ sk 0 4 := by decide
theorem d05 : sk 0 0 ≠ sk 0 5 := by decide
theorem d12 : sk 0 1 ≠ sk 0 2 := by decide
theorem d13 : sk 0 1 ≠ sk 0 3 := by decide
theorem d14 : sk 0 1 ≠ sk 0 4 := by decide
theorem d15 : sk 0 1 ≠ sk 0 5 := by decide
theorem d23 : sk 0 2 ≠ sk 0 3 := by decide
theorem d24 : sk 0 2 ≠ sk 0 4 := by decide
theorem d25 : sk 0 2 ≠ sk 0 5 := by decide
theorem d34 : sk 0 3 ≠ sk 0 4 := by decide
theorem d35 : sk 0 3 ≠ sk 0 5 := by decide
theorem d45 : sk 0 4 ≠ sk 0 5 := by decide

section Spec
variable (cr : ℕ) (n : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
  (Cδ : ℕ) (C : Ledger.CapParams) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (Kb : ℕ) (W : ℕ)

/-- **The prep's run**: from the filled state, `1^{|cc|}`, `1^{cap_T}`, `1^V` on streams `3`, `4`, `5`; the request and
the fill count kept. -/
theorem p0_spec (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (hN : P0Need W n h0 h1 Cδ C cr codes.length cc.length Kb) :
    ∃ τ c, WExec (2 * W + 2) (p0W cr ζ Cδ C) (σS (Data.reqW n mb codes cc tl) W) τ c ∧
      τ.st (sk 0 0) = RepairOrdinary.frame (Data.reqW n mb codes cc tl) ∧ τ.st (sk 0 1) = List.replicate W true ∧
      τ.st (sk 0 3) = List.replicate cc.length true ∧ τ.st (sk 0 4) = List.replicate (capTOf cr n h0 h1 Cδ C) true ∧
      τ.st (sk 0 5) = List.replicate (W + (n + 1) ^ 26) true ∧
      c ≤ p0Cost n cr h0 h1 Cδ C codes.length cc.length Kb W := by
  set cap := 2 * W + 2 with hcap
  set w := Data.reqW n mb codes cc tl with hw
  set σ := σS w W with hσ
  have z : ∀ r, σ.val r = 0 := fun r => rfl
  have hq := hN.hq
  have q1 := Nat.one_le_two_pow (n := natBitLength n)
  have q2 := Nat.one_le_two_pow (n := natBitLength codes.length)
  have q3 := Nat.one_le_two_pow (n := natBitLength cc.length)
  have hnc : cc.length ≤ cap := by
    have a1 : cc.length < 2 ^ (Nat.log 2 cc.length + 1) := Nat.lt_pow_succ_log_self (by norm_num) cc.length
    have a2 : 2 ^ (Nat.log 2 cc.length + 1) ≤ 2 ^ (natBitLength cc.length + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by unfold natBitLength; omega)
    omega
  -- 1: n, a, |cc|
  obtain ⟨τ1, c1, e1, v1n, v1a, v1nc, v1F, v1C, v1P, v1T, v1K, o1, s1, h1s, c1c, k1⟩ :=
    reqParse_spec cap 0 n mb codes cc tl Kb hKb σ (by simp [hσ, σS, hw]) rfl (z _) (z _) (z _) (z _) (z _) (z _) (z _)
      (z _) (by omega)
  have o1' : ∀ r, 400 ≤ r.val → τ1.val r = 0 := fun r hr => by
    rw [o1 r (fun e => by subst e; simp [dN] at hr) (fun e => by subst e; simp [dA] at hr)
      (fun e => by subst e; simp [dNC] at hr) (fun e => by subst e; simp [dK] at hr)]; rfl
  -- 2: 1^{|cc|} on stream 3
  have e2 := Emit.repRegW_spec cap (sk 0 3) rO1 dNC rK1 rT1 (by decide) (by decide) (by decide) (by decide) [true] τ1
    (o1' _ (by decide)) (o1' _ (by decide)) (by rw [s1, h1s _ d03.symm]; simp [hσ, σS, d03.symm, d13.symm, d23.symm])
    (by rw [v1nc]; exact hnc) (by rw [o1' _ (by decide), v1nc]; simp; exact hnc)
  rw [v1nc, NumsX.reps_single] at e2
  obtain ⟨τ2, g2⟩ : ∃ y, y = appendO τ1 (sk 0 3) rO1 (List.replicate cc.length true) := ⟨_, rfl⟩
  rw [← g2] at e2
  have o2 : ∀ r, r ≠ rO1 → τ2.val r = τ1.val r := fun r h => by rw [g2]; simp [Function.update_of_ne h]
  have s2 : ∀ s, s ≠ sk 0 3 → τ2.st s = τ1.st s := fun s h => by rw [g2]; simp [Function.update_of_ne h]
  have sh2 : ∀ s, s ≠ sk 0 3 → τ2.sh s = τ1.sh s := fun s h => by rw [g2]; simp [Function.update_of_ne h]
  have st23 : τ2.st (sk 0 3) = List.replicate cc.length true := by
    rw [g2]; simp [s1, h1s _ d03.symm]; simp [hσ, σS, d03.symm, d13.symm, d23.symm]
  -- 3: the star numbers and the THR cap
  have zS : ∀ i, τ2.val (SGb i) = 0 := fun i => by
    rw [o2 _ (fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [rO1] at this; omega)]
    rw [o1 _ (fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [dN] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [dA] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [dNC] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [dK] at this; omega)]; rfl
  have zG : ∀ i, τ2.val (Gb i) = 0 := fun i => by
    rw [o2 _ (fun e => by have := congrArg Fin.val e; rw [Gb_val] at this; simp [rO1] at this; omega)]
    rw [o1 _ (fun e => by have := congrArg Fin.val e; rw [Gb_val] at this; simp [dN] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [Gb_val] at this; simp [dA] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [Gb_val] at this; simp [dNC] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [Gb_val] at this; simp [dK] at this; omega)]; rfl
  have zH : ∀ i, τ2.val (Hb i) = 0 := fun i => by
    rw [o2 _ (fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [rO1] at this; omega)]
    rw [o1 _ (fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dN] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dA] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dNC] at this; omega)
      (fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dK] at this; omega)]; rfl
  have zx : τ2.val xT = 0 := by
    rw [o2 _ (by decide), o1 _ (by decide) (by decide) (by decide) (by decide)]; rfl
  have n2 : τ2.val dN = n := by rw [o2 _ (by decide), v1n]
  obtain ⟨τ3, c3, e3, v3cap, o3, s3, sh3, c3c, k3⟩ :=
    capT_spec cap 0 cr h0 h1 Cδ C n τ2 n2 zS zG zH zx hN.hcS hN.hcP hN.hcC
  have o3' : ∀ r, 400 ≤ r.val → τ3.val r = τ2.val r := fun r hr => o3 r (out_hi r hr)
  -- 4: 1^{cap_T} on stream 4
  have e4 := Emit.repRegW_spec cap (sk 0 4) rO2 (Hb 13) rK1 rT1 (by decide) (by decide) (by decide) (by decide) [true] τ3
    (by rw [o3' _ (by decide), o2 _ (by decide), o1' _ (by decide)])
    (by rw [o3' _ (by decide), o2 _ (by decide), o1' _ (by decide)])
    (by rw [s3, sh3, s2 _ d34.symm, sh2 _ d34.symm, s1, h1s _ d04.symm]; simp [hσ, σS, d04.symm, d14.symm, d24.symm])
    (by rw [v3cap]; exact hN.hcT)
    (by rw [o3' _ (by decide), o2 _ (by decide), o1' _ (by decide), v3cap]; simp; exact hN.hcT)
  rw [v3cap, NumsX.reps_single] at e4
  change WExec cap _ τ3 (appendO τ3 (sk 0 4) rO2 (List.replicate (capTOf cr n h0 h1 Cδ C) true)) _ at e4
  obtain ⟨τ4, g4⟩ : ∃ y, y = appendO τ3 (sk 0 4) rO2 (List.replicate (capTOf cr n h0 h1 Cδ C) true) := ⟨_, rfl⟩
  rw [← g4] at e4
  have o4 : ∀ r, r ≠ rO2 → τ4.val r = τ3.val r := fun r h => by rw [g4]; simp [Function.update_of_ne h]
  have s4 : ∀ s, s ≠ sk 0 4 → τ4.st s = τ3.st s := fun s h => by rw [g4]; simp [Function.update_of_ne h]
  have sh4 : ∀ s, s ≠ sk 0 4 → τ4.sh s = τ3.sh s := fun s h => by rw [g4]; simp [Function.update_of_ne h]
  have st44 : τ4.st (sk 0 4) = List.replicate (capTOf cr n h0 h1 Cδ C) true := by
    rw [g4]; simp [s3, s2 _ d34.symm, s1, h1s _ d04.symm]; simp [hσ, σS, d04.symm, d14.symm, d24.symm]
  -- register facts from here on
  have hi4 : ∀ r, 400 ≤ r.val → r ≠ rO1 → r ≠ rO2 → τ4.val r = 0 := fun r hr a b => by
    rw [o4 r b, o3' r hr, o2 r a, o1' r hr]
  have n4 : τ4.val dN = n := by rw [o4 _ (by decide), o3 _ (by unfold SymDec.Outside; decide), n2]
  -- 5: W into rW
  have e5 := SymDec.readU_spec cap (sk 0 1) rW W 0 τ4
    (by rw [s4 _ d14, s3, s2 _ d13, s1]; simp [hσ, σS, d01.symm])
    (by rw [sh4 _ d14, sh3, sh2 _ d13, h1s _ d01.symm]; rfl)
    (hi4 _ (by decide) (by decide) (by decide)) (by omega)
  obtain ⟨τ5, g5⟩ : ∃ y, y = (τ4.seth (sk 0 1) W).setv rW (0 + W) := ⟨_, rfl⟩
  rw [← g5] at e5
  have o5 : ∀ r, r ≠ rW → τ5.val r = τ4.val r := fun r h => by rw [g5]; simp [Function.update_of_ne h]
  have s5 : τ5.st = τ4.st := by rw [g5]; rfl
  have sh5 : ∀ s, s ≠ sk 0 1 → τ5.sh s = τ4.sh s := fun s h => by rw [g5]; simp [Function.update_of_ne h]
  have w5 : τ5.val rW = W := by rw [g5]; simp
  -- 6, 7: n + 1 into rB0
  have e6 := FinalPass.Hash4.wcopyR_spec cap dN rB0 rT1 (by decide) (by decide) (by decide) τ5
    (by rw [o5 _ (by decide)]; exact hi4 _ (by decide) (by decide) (by decide))
    (by rw [o5 _ (by decide)]; exact hi4 _ (by decide) (by decide) (by decide))
    (by rw [o5 _ (by decide), n4]; omega)
  rw [o5 _ (by decide), n4] at e6
  obtain ⟨τ6, g6⟩ : ∃ y, y = τ5.setv rB0 n := ⟨_, rfl⟩
  rw [← g6] at e6
  have e7 := WExec.inc (cap := cap) rB0 τ6 (by rw [g6]; simp; omega)
  obtain ⟨τ7, g7⟩ : ∃ y, y = τ6.setv rB0 (τ6.val rB0 + 1) := ⟨_, rfl⟩
  rw [← g7] at e7
  have b7 : τ7.val rB0 = n + 1 := by rw [g7, g6]; simp
  have o7 : ∀ r, r ≠ rB0 → τ7.val r = τ5.val r := fun r h => by rw [g7, g6]; simp [Function.update_of_ne h]
  -- 8: (n+1)^26 into rB1
  have hpw : ∀ k ≤ 26, (n + 1) ^ k ≤ cap := by
    have hV := hN.hV
    intro k hk
    have := Nat.pow_le_pow_right (show 1 ≤ n + 1 by omega) hk
    omega
  have e8 := UnaryPow.powConstW_spec cap Rp 26 τ7
    (by rw [Rp1, o7 _ (by decide), o5 _ (by decide)]; exact hi4 _ (by decide) (by decide) (by decide))
    (by show τ7.val rB2 = 0; rw [o7 _ (by decide), o5 _ (by decide)]; exact hi4 _ (by decide) (by decide) (by decide))
    (by show τ7.val rB3 = 0; rw [o7 _ (by decide), o5 _ (by decide)]; exact hi4 _ (by decide) (by decide) (by decide))
    (by show τ7.val rB4 = 0; rw [o7 _ (by decide), o5 _ (by decide)]; exact hi4 _ (by decide) (by decide) (by decide))
    (by omega) (by rw [Rp0, b7]; exact hpw 1 (by norm_num) |>.trans' (by simp)) (by rw [Rp0, b7]; exact hpw)
  rw [Rp0, Rp1, b7] at e8
  obtain ⟨τ8, g8⟩ : ∃ y, y = τ7.setv rB1 ((n + 1) ^ 26) := ⟨_, rfl⟩
  rw [← g8] at e8
  have o8 : ∀ r, r ≠ rB1 → τ8.val r = τ7.val r := fun r h => by rw [g8]; simp [Function.update_of_ne h]
  have b8 : τ8.val rB1 = (n + 1) ^ 26 := by rw [g8]; simp
  -- 9: V = W + (n+1)^26 into rW
  have e9 := addTo_spec cap rB1 rW rT1 (by decide) (by decide) (by decide) τ8
    (by rw [o8 _ (by decide), o7 _ (by decide), o5 _ (by decide)]; exact hi4 _ (by decide) (by decide) (by decide))
    (by rw [b8]; exact hpw 26 le_rfl)
    (by rw [b8, o8 _ (by decide), o7 _ (by decide), w5]; have := hN.hV; omega)
  rw [b8, o8 _ (by decide), o7 _ (by decide), w5] at e9
  obtain ⟨τ9, g9⟩ : ∃ y, y = τ8.setv rW (W + (n + 1) ^ 26) := ⟨_, rfl⟩
  rw [← g9] at e9
  have o9 : ∀ r, r ≠ rW → τ9.val r = τ8.val r := fun r h => by rw [g9]; simp [Function.update_of_ne h]
  have v9 : τ9.val rW = W + (n + 1) ^ 26 := by rw [g9]; simp
  have st9 : τ9.st = τ4.st := by rw [g9, g8, g7, g6]; exact s5
  have sh9 : τ9.sh = τ5.sh := by rw [g9, g8, g7, g6]; rfl
  have hi9 : ∀ r, 400 ≤ r.val → r ≠ rO1 → r ≠ rO2 → r ≠ rW → r ≠ rB0 → r ≠ rB1 → τ9.val r = 0 := fun r hr a b c d e => by
    rw [o9 r c, o8 r e, o7 r d, o5 r c]; exact hi4 r hr a b
  -- 10: 1^V on stream 5
  have e10 := Emit.repRegW_spec cap (sk 0 5) rO3 rW rK1 rT1 (by decide) (by decide) (by decide) (by decide) [true] τ9
    (hi9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hi9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [st9, sh9, sh5 _ d15.symm, s4 _ d45.symm, sh4 _ d45.symm, s3, sh3, s2 _ d35.symm, sh2 _ d35.symm, s1,
      h1s _ d05.symm]; simp [hσ, σS, d05.symm, d15.symm, d25.symm])
    (by rw [v9]; have := hN.hV; omega)
    (by rw [v9, hi9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp; have := hN.hV; omega)
  rw [v9, NumsX.reps_single] at e10
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
    (WExec.seq e8 (WExec.seq e9 e10)))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [st9, s4 _ d04, s3, s2 _ d03, s1, d05]; simp [hσ, σS]
  · simp [st9, s4 _ d14, s3, s2 _ d13, s1, d15.symm, d15]; simp [hσ, σS, d01.symm]
  · simp [st9, s4 _ d34, s3, st23, d35]
  · simp [st9, st44, d45]
  · simp [st9, s4 _ d45.symm, s3, s2 _ d35.symm, s1]; simp [hσ, σS, d05.symm, d15.symm, d25.symm]
  · have := hN.hcT
    unfold p0Cost
    unfold capTOf at this ⊢
    rw [← hcap]
    have e12 : 8 * [true].length + 4 = 12 := rfl
    rw [e12]
    omega

end Spec

end NearCubicWires.WireExponent3_5.PrimT.TS4
