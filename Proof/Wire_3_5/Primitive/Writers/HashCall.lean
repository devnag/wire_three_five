import Proof.Wire_3_5.Primitive.Writers.HashUnit
import Proof.Wire_3_5.Primitive.Writers.HashFlat
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.ShellT2
import Proof.Wire_3_5.Primitive.Writers.NumsXH

/-! # (HASH (b), (c)): the HASH unit decode at the call, and the HASH dimension stage

**(b) The call-level link.** At the call (`auxP` the aux filter's parameters, `thrPool` the THR pool), the decode's
emission `unitE TOT 1 0 (hrq auxP |thrPool|)` is the HASH tape unit by unit: `hbody_eq` (the decode's body is the unit
`HashFlat.hashUnit`, the aux seed `q mod nE` and the cell `q / nE` of `HashFlat.hashRowQ`), `hash_units` (every loop of
length `≥ nHash·5` prints `hashTape`, the units past `nHash·5` empty). The numbers the decode reads from the data word
`hashNums ++ thrCounts` are the call's: `hashNums_ee` (entry 13 is `thrCallE`, the aux filter's error exponent, at the
THR filter cap `B.capOf .thr n`), `hashNums_M`, `hash_pool` (`2Σ|X_j| + M = |thrPool|`).

**(c) The HASH dimension stage.** `dimOK_numsH`: `NumsXH.numsMH KL KH cr` meets `ShellTBoot.DimOK` at `mOfH KL KH P`
(the twin of `dimOK_numsT`).

Paper quantity of the main types: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226) and the HASH
writer's dimension `2^{mOfH}` (the aux cost `Θ(D·L³)`, P3:2210-2211). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCall
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.SymFlat NearCubicWires.WireExponent3_5.PrimAsm.HashFlat
open NearCubicWires.SupplierPipeline

/-! ## The emission reads its request map only at targets `s ≤ M` -/

theorem symEmit_congr (R M : ℕ) (rq rq' : ℕ → ℕ → ℕ → List Bool) (h : ∀ e r s, s ≤ M → rq e r s = rq' e r s)
    (j : ℕ) : symEmit R M rq j = symEmit R M rq' j := by
  have hm := Nat.mod_lt (j % (R * (M + 3) + 2) - 1) (show 0 < M + 3 by omega)
  unfold symEmit entryEmit rowEmit
  split_ifs <;> first | rfl | exact h _ _ _ (by omega)

/-- A loop longer than `T` whose units past `T` are empty prints the first `T` units. -/
theorem flatMap_range_tail (f : ℕ → List Bool) (T L : ℕ) (hTL : T ≤ L) (hf : ∀ j, T ≤ j → f j = []) :
    (List.range L).flatMap f = (List.range T).flatMap f := by
  obtain ⟨d, rfl⟩ : ∃ d, L = T + d := ⟨L - T, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show T + (d + 1) = (T + d) + 1 by omega, List.range_succ, List.flatMap_append, ih (by omega),
      List.flatMap_singleton, hf _ (by omega), List.append_nil]

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))

theorem hseed_aux (q : ℕ) :
    hseed (auxP alg I hs Cs carriers) q = auxEnum alg I hs Cs carriers (q % nE alg I hs Cs carriers) := by
  unfold hseed auxEnum
  congr 1
  exact Fin.ext (Nat.mod_mod _ _).symm

/-- **The decode's body is the HASH unit** (entry `q`: aux seed `q mod nE`, cell `q / nE`, the carrier prefix). -/
theorem hbody_eq (q : ℕ) :
    hbody (auxP alg I hs Cs carriers) (thrPool (I.starParams n hs) Cs carriers).length q =
      unitBody (hashRowQ alg I hs Cs carriers q) := by
  unfold hbody
  rw [hseed_aux, show 2 * (2 * (q / Fintype.card (GapSeed (auxP alg I hs Cs carriers)))) =
    4 * (q / nE alg I hs Cs carriers) by ring, ← Emit.labs_eq, ← List.range_eq_range']
  rfl

/-- The loop's unit count: `2^{seedBits}·2^{2k_h}·5 = nHash·5`. -/
theorem hash_tot : 2 ^ (auxP alg I hs Cs carriers).seedBits *
    2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2))) * 5 =
      nHash alg I hs Cs carriers * (1 * (0 + 3) + 2) := by
  unfold nHash nE
  rw [card_gapSeed, SeedFix.callKh, ← pow_mul]
  ring

/-- **The HASH decode's emissions print the HASH tape** (any loop of length `≥ nHash·5`). -/
theorem hash_units (Lp : ℕ) (hL : 2 ^ (auxP alg I hs Cs carriers).seedBits *
    2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2))) * 5 ≤ Lp) :
    (List.range Lp).flatMap (unitE (2 ^ (auxP alg I hs Cs carriers).seedBits *
      2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2))) * 5) 1 0
        (hrq (auxP alg I hs Cs carriers) (thrPool (I.starParams n hs) Cs carriers).length)) ++ [false] =
      hashTape alg I hs Cs carriers := by
  rw [flatMap_range_tail _ _ _ hL (fun j hj => by unfold unitE; rw [if_neg (by omega)]), hash_tot,
    ← hashTape_flat]
  refine congrArg (fun l => l ++ [false]) ?_
  refine List.flatMap_congr fun j hj => ?_
  rw [List.mem_range] at hj
  unfold unitE
  rw [if_pos hj]
  refine symEmit_congr 1 0 _ _ (fun e r s hs0 => ?_) j
  have : s = 0 := by omega
  subst this
  simp only [hrq, if_pos rfl, hashUnit]
  exact hbody_eq alg I hs Cs carriers e

/-! ## The numbers the decode reads -/

theorem hashNums_cap (P : StarParams) {a' : ℕ} (Cs' : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (cs : List (Carrier P.n)) (Dexp capT : ℕ) :
    (ThrData.hashNums P Cs' cs alg Dexp capT).getD 1 0 = capT := rfl

theorem hashNums_M (P : StarParams) {a' : ℕ} (Cs' : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (cs : List (Carrier P.n)) (Dexp capT : ℕ) :
    (ThrData.hashNums P Cs' cs alg Dexp capT).getD 8 0 = (thrOccs P Cs').length := rfl

/-- **The pool size**: `2Σ|X_j| + M = |thrPool|`. -/
theorem hash_pool (P : StarParams) {a' : ℕ} (Cs' : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (cs : List (Carrier P.n)) (Dexp capT : ℕ) :
    2 * (cs.map List.length).sum + (ThrData.hashNums P Cs' cs alg Dexp capT).getD 8 0 = (thrPool P Cs' cs).length := by
  rw [hashNums_M]
  unfold thrPool thrSlices
  rw [List.flatten_append, List.length_append, prefix_length]
  simp

/-- **The aux filter's error exponent**: entry 13 is `thrCallE` at the THR filter cap. -/
theorem hashNums_ee : (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (I.filterParams .thr n).cap).getD 13 0 =
    thrCallE alg I hs Cs carriers := by
  show (PrimThrW.Joins.thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap).ee = _
  have hA := PrimThrW.Joins.thrNumVals_A alg I hs Cs carriers.length (I.filterParams .thr n).cap
  have hD := PrimThrW.Joins.thrNumVals_den alg I hs Cs carriers.length (I.filterParams .thr n).cap
  unfold thrCallE
  rw [← hA, ← hD]
  rfl

theorem auxP_len : (auxP alg I hs Cs carriers).len = 2 * (carriers.map List.length).sum := rfl

theorem auxP_cap : (auxP alg I hs Cs carriers).cap = (carriers.length + 1) * 4096 * (I.filterParams .thr n).cap := by
  show (carriers.length + 1) * (4096 * (I.filterParams .thr n).cap) = _
  ring

theorem auxP_err : (auxP alg I hs Cs carriers).errExp = thrCallE alg I hs Cs carriers := rfl

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.HashCall

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.WireExponent3_5.PrimAsm.ShellX NearCubicWires.SupplierPipeline

section DimH
variable {x D D2 Dv DL : ℕ}

/-- **The HASH dimension stage meets `DimOK`** at `mOfH KL KH P` (ShellX's `x2_step` with `NumsXH.nums_stepH`). -/
theorem dimOK_numsH (KL KH cr : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (W : ℕ)
    (hW : 2 * P.n + cr + 16 + KL * (P.n + 2) ^ 2 + KH * (P.n + 2) ^ 3 ≤ W) :
    DimOK x D D2 Dv DL (NumsXH.numsMH KL KH cr) (2 * NumsXH.numsStageCostH P.n cr KL KH W + 2)
      (NumsXH.mOfH KL KH P) w W := by
  intro B h0 hct hb
  obtain ⟨tout, m, h, o, i, -⟩ := NumsXH.nums_stepH KL KH cr W P hrP sfx w hw hW
  have hJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hH : ∀ j, HI (q2 x D D2 Dv DL j) = 0 := by
    intro j
    apply HI_ne
    apply ne_TJ
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;>
      rw [e, hJ]
    · rw [T0_val]; omega
    · rw [TW_val]; omega
    · have := nu_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j; omega
  have hA : ∀ j, B (q2 x D D2 Dv DL j) =
      Fin.addCases (NumsX.rawInX w W) (fun _ : Fin 1 => List.replicate 0 false) j := by
    intro j
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;>
      rw [e]
    · subst h1
      rw [h0]
      simp [iN, NumsX.rawInX]
    · subst h2
      rw [hct]
      simp [cN, NumsX.rawInX, NumsX.xIN, NumsX.xCT, NumsX.sTape_eq_iffX]
    · rw [hb j]
      revert h1 h2
      refine Fin.addCases (fun t => ?_) (fun u => ?_) j
      · intro h1 h2
        have t1 : t ≠ sTape NumsX.xIN := fun e => h1 (by rw [e]; rfl)
        have t2 : t ≠ sTape NumsX.xCT := fun e => h2 (by rw [e]; rfl)
        simp [NumsX.rawInX, t1, t2]
      · intro _ _
        simp
  have d := dock0 h (q2 x D D2 Dv DL) q2_inj HI B hH hA
  refine ⟨_, d, ?_, ?_⟩
  · simp only [oN, Fin.addCases_left]
    exact o
  · simp only [iN, Fin.addCases_left]
    exact i

end DimH

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
