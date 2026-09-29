import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Guard

/-! # TopFrontPort3 body, part 2: the preparation (`1^n`, `1^{(n+1)^26}` from the request)

P3:3071-3091 (the call's circuits by their codes, the width `n` first in the request word). PA's verified split
(`Data.setupW`) and the decode block need `1^n` and `1^L`, `L = (n+1)^26 ≥` every circuit's description
size, beside the framed request at head `0`. Once the guard has seen `a' ≥ 1`, `TF2Ok` gives `(n+1)^26 ≤ 2V`, so the
register capacity `2V + 2` (the fill's) holds `n` and `(n+1)^26`, and `V` exceeds every head position the guard left:

* `pAW` / **`pA_spec`**: count `V` off the count stream, rewind the request by `V` (saturating), read `n` into
  register `8`, rewind again;
* `pBW` / **`pB_spec`**: `1^n` on `sNT`, `(n+1)^26` in register `12` (`UnaryPow.powConstW`), `1^{(n+1)^26}` on `sLT`,
  both heads back at `0`.

Paper quantities of the main types: the circuit width `n` and the description bound `(n+1)^26`, in unary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Prep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

theorem sIN_ne_sCT : sIN ≠ sCT := by decide
theorem sCT_ne_sIN : sCT ≠ sIN := by decide
theorem sNT_ne_sLT : sNT ≠ sLT := by decide
theorem sLT_ne_sNT : sLT ≠ sNT := by decide

theorem reps_true (m : ℕ) : FiltRec.reps m [true] = List.replicate m true := by
  induction m with
  | zero => rfl
  | succ m ih => rw [FiltRec.reps_succ, ih, List.replicate_succ']

/-- `powConstW`'s registers: the base in `10`, the power into `12`, scratch `11, 14, 15`. -/
def RP : Fin 5 ↪ Fin DR := ⟨![10, 12, 11, 14, 15], by decide⟩

/-- Part A: `V` off the count stream (register `5`, copied to `6`), the request rewound, `n` into `8`, rewound. -/
def pAW : WM DS DR :=
  .seq (SymDec.readUW sCT 5) (.seq (FinalPass.Hash4.wcopyR 5 6 7) (.seq (WM.rewind sIN 5)
    (.seq (ParseNat.readNatM true sIN 0 1 8 2 3) (WM.rewind sIN 6))))

/-- Part A's cost. -/
def pACost (n V : ℕ) : ℕ :=
  7 * V + 1 + 1 + (18 * V + 3 + 1 + (5 * V + 1 + 1 +
    ((natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + (5 * V + 1))))

/-- Part B: `1^n` on `sNT`, `(n+1)^26` into `12`, `1^{(n+1)^26}` on `sLT`, heads back at `0`. -/
def pBW : WM DS DR :=
  .seq (Emit.repRegW sNT 13 8 14 15 [true]) (.seq (WM.rewind sNT 13) (.seq (FinalPass.Hash4.wcopyR 8 10 11)
    (.seq (.inc 10) (.seq (UnaryPow.powConstW RP 26) (.seq (Emit.repRegW sLT 13 12 14 15 [true])
      (WM.rewind sLT 13))))))

/-- Part B's cost (`L` the description bound `(n+1)^26`). -/
def pBCost (n L cap : ℕ) : ℕ :=
  18 * n + 3 + 1 + (n * (8 * [true].length + 4) + 1) + 1 + (5 * n + 1 + 1 + (18 * n + 3 + 1 + (3 + 1 +
    ((26 + 1) * (4 * UnaryPow.sq cap) + 1 + (18 * L + 3 + 1 + (L * (8 * [true].length + 4) + 1) +
      1 + (5 * L + 1))))))

variable (cap : ℕ)

/-- **Part A's run**: from the count `1^V` at head `0`, the request at head `p ≤ V` and zero scratch, `n` in
register `8`, the request's head back at `0`, the count's head at `V`, nothing else changed. -/
theorem pA_spec (n : ℕ) (codes cc : List ℕ) (tl : List Bool) (V p : ℕ) (σ : WState DS DR)
    (hIN : σ.st sIN = frame (reqW n true codes cc tl)) (hINh : σ.sh sIN = p) (hp : p ≤ V)
    (hCT : σ.st sCT = List.replicate V true) (hCTh : σ.sh sCT = 0)
    (h0 : σ.val 0 = 0) (h1 : σ.val 1 = 0) (h2 : σ.val 2 = 0) (h3 : σ.val 3 = 0) (h5 : σ.val 5 = 0)
    (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0) (h8 : σ.val 8 = 0)
    (hV : V ≤ cap) (hn : 2 ^ (natBitLength n + 1) ≤ cap) (hnV : 2 * (RepairRepresentation.natWord n).length ≤ V) :
    WExec cap pAW σ (((σ.seth sCT V).seth sIN 0).setv 8 n) (pACost n V) := by
  have hIN' := hIN
  rw [enc_reqW] at hIN'
  have q1 := SymDec.readU_spec cap sCT 5 V 0 σ hCT hCTh h5 (by omega)
  set σ1 := (σ.seth sCT V).setv 5 (0 + V) with hσ1
  have q2 := FinalPass.Hash4.wcopyR_spec cap 5 6 7 (by decide) (by decide) (by decide) σ1
    (by simp [hσ1, h6]) (by simp [hσ1, h7]) (by simp [hσ1]; omega)
  set σ2 := σ1.setv 6 (σ1.val 5) with hσ2
  have q3 := wrewind_spec cap sIN 5 V σ2 (by simp [hσ2, hσ1]) (by simp [hσ2, hσ1]; omega)
  set σ3 := (σ2.setv 5 0).seth sIN (σ2.sh sIN - V) with hσ3
  have hs3 : σ3.sh sIN = 0 := by simp [hσ3, hσ2, hσ1, Function.update_of_ne sIN_ne_sCT, hINh]; omega
  have q4 := ParseNat.readNatM_spec cap true sIN 0 1 8 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n []
    (ParseNat.enc true [true] ++ (ParseNat.enc true (RepairRepresentation.natWord codes.length) ++
      (ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
        (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++
          (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false]))))))
    σ3 (by simp [hσ3, hσ2, hσ1, hIN']) (by simpa using hs3)
    (by simp [hσ3, hσ2, hσ1, h0]) (by simp [hσ3, hσ2, hσ1, h1]) (by simp [hσ3, hσ2, hσ1, h2])
    (by simp [hσ3, hσ2, hσ1, h3]) (by simp [hσ3, hσ2, hσ1, h8]; omega)
  set σ4 := (σ3.seth sIN ([].length + ParseNat.stp true * (RepairRepresentation.natWord n).length)).setv 8
    (σ3.val 8 + n) with hσ4
  have q5 := wrewind_spec cap sIN 6 V σ4 (by simp [hσ4, hσ3, hσ2, hσ1]) (by simp [hσ4, hσ3, hσ2, hσ1]; omega)
  refine WExec.cast cap (WExec.seq q1 (WExec.seq q2 (WExec.seq q3 (WExec.seq q4 q5)))) ?_
    (by simp [pACost, hσ1])
  apply WState.eq
  · funext s
    by_cases hs : s = sIN
    · subst hs
      simp [hσ4, hσ3, hσ2, hσ1, ParseNat.stp, Function.update_of_ne sIN_ne_sCT]
      have hl := ParseNat.natWord_length n
      omega
    · by_cases hc : s = sCT
      · subst hc
        simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne sCT_ne_sIN]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, hs, hc]
  · simp [hσ4, hσ3, hσ2, hσ1]
  · funext r
    by_cases h8r : r = 8
    · subst h8r
      simp [hσ4, hσ3, hσ2, hσ1, h8]
    · by_cases h5r : r = 5
      · subst h5r
        simp [hσ4, hσ3, hσ2, hσ1, h5]
      · by_cases h6r : r = 6
        · subst h6r
          simp [hσ4, hσ3, hσ2, hσ1, h6]
        · simp [hσ4, hσ3, hσ2, hσ1, Function.update_apply, h8r, h5r, h6r]
  · simp [hσ4, hσ3, hσ2, hσ1]

/-- **Part B's run**: from `n` in register `8`, blank `sNT`/`sLT` at head `0` and zero scratch, `1^n` on `sNT`,
`1^L` on `sLT` (`L = (n+1)^26`, heads `0`), `n + 1` in `10` and `L` in `12`, nothing else changed. -/
theorem pB_spec (n L : ℕ) (hL : (n + 1) ^ 26 = L) (σ : WState DS DR) (hNT : σ.st sNT = []) (hNTh : σ.sh sNT = 0)
    (hLT : σ.st sLT = []) (hLTh : σ.sh sLT = 0) (h8 : σ.val 8 = n) (h10 : σ.val 10 = 0) (h11 : σ.val 11 = 0)
    (h12 : σ.val 12 = 0) (h13 : σ.val 13 = 0) (h14 : σ.val 14 = 0) (h15 : σ.val 15 = 0) (hcap : L ≤ cap) :
    WExec cap pBW σ ((((σ.sets sNT (List.replicate n true)).sets sLT (List.replicate L true)).setv 10
      (n + 1)).setv 12 L) (pBCost n L cap) := by
  have hn1 : n + 1 ≤ L := hL ▸ Nat.le_self_pow (by norm_num) _
  have hpow : ∀ k ≤ 26, (n + 1) ^ k ≤ cap := fun k hk =>
    (Nat.pow_le_pow_right (by omega) hk).trans (hL ▸ hcap)
  have r1 := Emit.repRegW_spec cap sNT 13 8 14 15 (by decide) (by decide) (by decide) (by decide) [true] σ h14 h15
    (by rw [hNTh, hNT]; rfl) (by omega) (by rw [h13, h8]; simp; omega)
  rw [h8] at r1
  set τ1 := appendO σ sNT 13 (FiltRec.reps n [true]) with hτ1
  have r2 := wrewind_spec cap sNT 13 n τ1 (by simp [hτ1, h13, reps_true])
    (by simp [hτ1, h13, reps_true]; omega)
  set τ2 := (τ1.setv 13 0).seth sNT (τ1.sh sNT - n) with hτ2
  have r3 := FinalPass.Hash4.wcopyR_spec cap 8 10 11 (by decide) (by decide) (by decide) τ2
    (by simp [hτ2, hτ1, h10]) (by simp [hτ2, hτ1, h11]) (by simp [hτ2, hτ1, h8]; omega)
  have e28 : τ2.val 8 = n := by simp [hτ2, hτ1, h8]
  rw [e28] at r3
  set τ3 := τ2.setv 10 n with hτ3
  have r4 := WExec.inc (cap := cap) (10 : Fin DR) τ3 (by simp [hτ3]; omega)
  have e310 : τ3.val 10 = n := by simp [hτ3]
  rw [e310] at r4
  set τ4 := τ3.setv 10 (n + 1) with hτ4
  have r5 := UnaryPow.powConstW_spec cap RP 26 τ4 (by simp [RP, hτ4, hτ3, hτ2, hτ1, h12])
    (by simp [RP, hτ4, hτ3, hτ2, hτ1, h11]) (by simp [RP, hτ4, hτ3, hτ2, hτ1, h14])
    (by simp [RP, hτ4, hτ3, hτ2, hτ1, h15]) (by omega)
    (by simp [RP, hτ4]; omega)
    (fun k hk => by simp [RP, hτ4]; exact hpow k hk)
  have e40 : τ4.val (RP 0) ^ 26 = L := by simp [RP, hτ4]; exact hL
  rw [e40] at r5
  set τ5 := τ4.setv (RP 1) L with hτ5
  have e12 : τ5.val 12 = L := by simp [hτ5, RP]
  have e513 : τ5.val 13 = 0 := by simp [hτ5, RP, hτ4, hτ3, hτ2]
  have r6 := Emit.repRegW_spec cap sLT 13 12 14 15 (by decide) (by decide) (by decide) (by decide) [true] τ5
    (by simp [hτ5, RP, hτ4, hτ3, hτ2, hτ1, h14]) (by simp [hτ5, RP, hτ4, hτ3, hτ2, hτ1, h15])
    (by simp [hτ5, RP, hτ4, hτ3, hτ2, hτ1, hLT, hLTh, Function.update_of_ne sLT_ne_sNT]) (by rw [e12]; exact hcap)
    (by rw [e12, e513]; simp; exact hcap)
  rw [e12] at r6
  set τ6 := appendO τ5 sLT 13 (FiltRec.reps L [true]) with hτ6
  have e613 : τ6.val 13 = L := by
    simp only [hτ6, appendO_val, Function.update_self, e513, reps_true, List.length_replicate, Nat.zero_add]
  have r7 := wrewind_spec cap sLT 13 L τ6 e613 (by rw [e613]; exact hcap)
  refine WExec.cast cap (WExec.seq r1 (WExec.seq r2 (WExec.seq r3 (WExec.seq r4 (WExec.seq r5
    (WExec.seq r6 r7)))))) ?_ le_rfl
  have hne : sNT ≠ sLT := sNT_ne_sLT
  have hne' : sLT ≠ sNT := sLT_ne_sNT
  apply WState.eq
  · funext s
    by_cases hs : s = sNT
    · subst hs
      simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, hNTh, reps_true, Function.update_apply, hne, hne']
    · by_cases hl : s = sLT
      · subst hl
        simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, hLTh, reps_true, Function.update_apply, hne, hne']
      · simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, Function.update_apply, hs, hl]
  · funext s
    by_cases hs : s = sNT
    · subst hs
      simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, hNT, reps_true, Function.update_apply, hne, hne']
    · by_cases hl : s = sLT
      · subst hl
        simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, hLT, reps_true, Function.update_apply, hne, hne']
      · simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1, Function.update_apply, hs, hl]
  · funext r
    by_cases h10r : r = 10
    · subst h10r
      simp [hτ6, hτ5, RP, hτ4, hτ3, hτ2, hτ1]
    · by_cases h12r : r = 12
      · subst h12r
        simp [hτ6, hτ5, RP, hτ4, hτ3, hτ2, hτ1]
      · by_cases h13r : r = 13
        · subst h13r
          simp [hτ6, hτ5, RP, hτ4, hτ3, hτ2, hτ1, h13]
        · simp [hτ6, hτ5, RP, hτ4, hτ3, hτ2, hτ1, Function.update_apply, h10r, h12r, h13r]
  · simp [hτ6, hτ5, hτ4, hτ3, hτ2, hτ1]

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Prep
