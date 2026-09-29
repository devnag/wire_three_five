import Proof.Wire_3_5.Filters.GaussColumn
import Proof.Wire_3_5.Filters.GF2Machines

/-! # C4.E, part 1: the elimination and its count exponent, loop-safe (P3:2950-2957)

Realizes, for a machine that eliminates many systems in a row, the paper's count: "Gaussian elimination gives
conditional probability zero if it is inconsistent, and `2^{−a}` if its remaining rank is `a`. The denominator divides
`2^S`" (P3:2953-2955). Scaled by `2^{rest}`, the completion count of a system over `rest` remaining seed bits is `0` or
`2^{rest − rank}`.

`gauss_run` starts from an empty rank tape and a column counter of exactly `nvars` cells. Tapes never shrink
, so inside a loop both are padded with blank cells (`ZeroPadding.pad`, base's `Step.pad`): the rank tape
is a blank capacity tape, the counter is `nvars` set cells over blanks. The deficit pass then reads the counter and the
tallied rank cells in lockstep: it clears every tallied cell (so the rank tape is blank again) and writes one set cell
of `X` for every column without a pivot, then a terminator.

Paper quantities of the main types: the consistency flag and the rank of `JoinElimination.gauss` (`gaussP_run`), and the
count exponent `rest − rank` in unary (`deficit_run`); `count_eq` is `condProbGauss`'s count `0` or `2^{rest−rank}`.

Results: `gaussP_run`, `gauss_rank_le`, `set_run`, **`deficit_run`**, `count_eq`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.JoinElimination NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)

/-! ## The elimination on padded rank and counter tapes -/

theorem colState_rank_le (s0 : Gauss.ColState) : ∀ c, (Gauss.colState s0 c).rank ≤ s0.rank + c
  | 0 => le_refl _
  | c + 1 => by
    have ih := colState_rank_le s0 c
    show (Gauss.colState s0 c).rank + (if Gauss.found (Gauss.colState s0 c).reps then 1 else 0) ≤ s0.rank + (c + 1)
    split <;> omega

/-- The rank is at most the number of columns. -/
theorem gauss_rank_le (nvars : ℕ) (rows : List Row) (hrows : ∀ r ∈ rows, r.1 < 2 ^ nvars) :
    (gauss nvars rows).2 ≤ nvars := by
  let s0 : Gauss.ColState := ⟨rows.map (Gauss.rowBits nvars), 0, [], [], []⟩
  have hg : Gauss.gaussDrop nvars rows =
      ((Gauss.colState s0 nvars).reps.all (fun r => !(r.headD false)), (Gauss.colState s0 nvars).rank) := by
    have hp := Gauss.colState_passes s0 nvars
    unfold Gauss.gaussDrop
    simp only [s0] at hp
    rw [← hp]
  rw [← Gauss.gaussDrop_eq nvars rows hrows, hg]
  have := colState_rank_le s0 nvars
  simpa [s0] using this

/-! ## The flag cell set -/

/-- Write `true` under the head, without moving. -/
def setM : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => some true, fun _ => .stay⟩ else none

theorem set_run (b : Bool) : Step setM 1 ![0] ![[b]] ![0] ![[true]] := by
  have hs : step setM ⟨setM.start, ![0], ![[b]]⟩ = some ⟨1, ![0], ![[true]]⟩ := by
    simp [step, setM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction, writeTapeBit]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := setM) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-! ## The deficit pass: tapes 0 the column counter, 1 the rank tape, 2 the exponent tape `X` -/

namespace Deficit
open Three (act cfg)

/-- One counter cell: a tallied rank cell is cleared; an untallied one appends a set cell to `X`. -/
def body : Machine 3 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 1 then act 1 none (some false) none .right .right .stay
        else act 1 none none (some true) .right .right .right)
    else none

theorem body_true (C K X : List Bool) (j x : ℕ) (hk : readTapeBit K j = true) :
    Step body 1 ![j, j, x] ![C, K, X] ![j + 1, j + 1, x] ![C, writeTapeBit K j false, X] := by
  have s1 : step body (cfg 0 C K X j j x) = some (cfg 1 C (writeTapeBit K j false) X (j + 1) (j + 1) x) := by
    rw [Three.step_cfg body 0 1 C K X j j x none (some false) none .right .right .stay (by simp [body, hk])]
    rfl
  obtain ⟨r, hr, hf, hs⟩ := (RecoveryExecution.Timed.single (p := body) rfl s1).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

theorem body_false (C K X : List Bool) (j x : ℕ) (hk : readTapeBit K j = false) :
    Step body 1 ![j, j, x] ![C, K, X] ![j + 1, j + 1, x + 1] ![C, K, writeTapeBit X x true] := by
  have s1 : step body (cfg 0 C K X j j x) = some (cfg 1 C K (writeTapeBit X x true) (j + 1) (j + 1) (x + 1)) := by
    rw [Three.step_cfg body 0 1 C K X j j x none none (some true) .right .right .right (by simp [body, hk])]
    rfl
  obtain ⟨r, hr, hf, hs⟩ := (RecoveryExecution.Timed.single (p := body) rfl s1).run rfl
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, by omega⟩

/-- The rank tape after `j` counter cells: the first `min j g` tallied cells cleared. -/
def rankAt (g cK j : ℕ) : List Bool :=
  List.replicate (min j g) false ++ List.replicate (g - j) true ++ List.replicate (cK - g) false

theorem read_rep_false (n i : ℕ) : readTapeBit (List.replicate n false) i = false := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem rankAt_read (g cK j : ℕ) : readTapeBit (rankAt g cK j) j = decide (j < g) := by
  unfold rankAt
  by_cases h : j < g
  · have e : List.replicate (min j g) false ++ List.replicate (g - j) true ++ List.replicate (cK - g) false =
        List.replicate j false ++ true :: (List.replicate (g - j - 1) true ++ List.replicate (cK - g) false) := by
      rw [Nat.min_eq_left (by omega)]
      have : g - j = (g - j - 1) + 1 := by omega
      rw [this, List.replicate_succ]
      simp
    have := Streaming.read_append (List.replicate j false)
      (List.replicate (g - j - 1) true ++ List.replicate (cK - g) false) true
    rw [List.length_replicate] at this
    rw [e, this, decide_eq_true h]
  · have e : List.replicate (min j g) false ++ List.replicate (g - j) true ++ List.replicate (cK - g) false =
        List.replicate (g + (cK - g)) false := by
      rw [Nat.min_eq_right (by omega), show g - j = 0 by omega, List.replicate_zero, List.append_nil,
        List.replicate_add]
    rw [e, read_rep_false, decide_eq_false h]

theorem rankAt_write (g cK j : ℕ) (h : j < g) : writeTapeBit (rankAt g cK j) j false = rankAt g cK (j + 1) := by
  unfold rankAt
  have e : List.replicate (min j g) false ++ List.replicate (g - j) true ++ List.replicate (cK - g) false =
      List.replicate j false ++ true :: (List.replicate (g - j - 1) true ++ List.replicate (cK - g) false) := by
    rw [Nat.min_eq_left (by omega)]
    have : g - j = (g - j - 1) + 1 := by omega
    rw [this, List.replicate_succ]
    simp
  have hw := write_mid (List.replicate j false)
    (List.replicate (g - j - 1) true ++ List.replicate (cK - g) false) true false
  rw [List.length_replicate] at hw
  rw [e, hw, Nat.min_eq_left (by omega : j + 1 ≤ g), show g - (j + 1) = g - j - 1 by omega, List.replicate_succ']
  simp

/-- The bank before counter cell `j`. -/
def defH (g j : ℕ) : Fin 3 → ℕ := ![j, j, j - g]
def defA (nvars g cC cK : ℕ) (Xold : List Bool) (j : ℕ) : Fin 3 → List Bool :=
  ![pad cC (List.replicate nvars true), rankAt g cK j, overlay (List.replicate (j - g) true) Xold]

theorem def_step (nvars g cC cK : ℕ) (Xold : List Bool) (j : ℕ) :
    Step body 1 (defH g j) (defA nvars g cC cK Xold j) (defH g (j + 1)) (defA nvars g cC cK Xold (j + 1)) := by
  by_cases h : j < g
  · have hr : readTapeBit (rankAt g cK j) j = true := by rw [rankAt_read]; simpa using h
    have hs := body_true (pad cC (List.replicate nvars true)) (rankAt g cK j)
      (overlay (List.replicate (j - g) true) Xold) j (j - g) hr
    rw [rankAt_write g cK j h] at hs
    refine (hs.congr_in ?_ ?_).congr ?_ ?_
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i
      · rfl
      · rfl
      · show j - g = j + 1 - g; omega
    · funext i; fin_cases i
      · rfl
      · rfl
      · show overlay (List.replicate (j - g) true) Xold = overlay (List.replicate (j + 1 - g) true) Xold
        rw [show j + 1 - g = j - g by omega]
  · have hr : readTapeBit (rankAt g cK j) j = false := by rw [rankAt_read]; simpa using h
    have hs := body_false (pad cC (List.replicate nvars true)) (rankAt g cK j)
      (overlay (List.replicate (j - g) true) Xold) j (j - g) hr
    have hw := overlay_write (List.replicate (j - g) true) Xold true
    rw [List.length_replicate] at hw
    rw [hw] at hs
    have hK : rankAt g cK j = rankAt g cK (j + 1) := by
      unfold rankAt
      rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega), show g - j = 0 by omega,
        show g - (j + 1) = 0 by omega]
    refine (hs.congr_in ?_ ?_).congr ?_ ?_
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i
      · rfl
      · rfl
      · show j - g + 1 = j + 1 - g; omega
    · funext i; fin_cases i
      · rfl
      · exact hK
      · show overlay (List.replicate (j - g) true ++ [true]) Xold = overlay (List.replicate (j + 1 - g) true) Xold
        rw [show j + 1 - g = (j - g) + 1 by omega, List.replicate_succ']

def slotX : Fin 1 → Fin 3 := ![2]

/-- **The deficit machine**: the lockstep pass over the counter, then the terminator of `X`. -/
noncomputable def machine := Composition.machine (StreamController.machine body 0) (RecoveryFocus.machine slotX Gauss.termM)

def cost (nvars : ℕ) : ℕ := nvars * (1 + 2) + 1 + 1 + 1

theorem dockH_slotX (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) : dockH slotX H v = ![H 0, H 1, v 0] := by
  funext i; fin_cases i
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_other _ _ _ _ (by decide)
  · exact dockH_slot _ (by decide) _ _ 0

theorem install_slotX (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slotX A v = ![A 0, A 1, v 0] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_other _ _ _ _ (by decide)
  · exact RecoveryRootRound.install_slot _ (by decide) _ _ 0

end Deficit

/-- **The count exponent in unary.** From the counter (`nvars` set cells over blanks), the rank tape with `g ≤ nvars`
tallied cells and any old exponent tape: the rank tape ends blank and `X` holds `nvars − g` set cells, then a
terminator, over its old content. -/
theorem deficit_run (nvars g cC cK : ℕ) (Xold : List Bool) (hg : g ≤ nvars) (hcK : nvars ≤ cK) :
    Step Deficit.machine (Deficit.cost nvars) ![0, 0, 0]
      ![pad cC (List.replicate nvars true), pad cK (List.replicate g true), Xold]
      ![nvars, nvars, nvars - g]
      ![pad cC (List.replicate nvars true), pad cK [], overlay (List.replicate (nvars - g) true ++ [false]) Xold] := by
  let W : WhileBody 3 _ :=
    { body := Deficit.body
      tape := 0
      bound := nvars
      H := Deficit.defH g
      A := Deficit.defA nvars g cC cK Xold
      cost := fun _ => 1
      step := fun j _ => Deficit.def_step nvars g cC cK Xold j
      cont := fun j hj => by
        show readTapeBit (pad cC (List.replicate nvars true)) j = true
        rw [ZeroPadding.read_pad, Gauss.read_rep]; simpa using hj
      halt := by
        show readTapeBit (pad cC (List.replicate nvars true)) nvars = false
        rw [ZeroPadding.read_pad, Gauss.read_rep]; simp }
  have hW := W.run
  rw [W.rest_const 1 (fun _ => rfl)] at hW
  have ht := dockRun (Gauss.term_run (List.replicate (nvars - g) true) Xold) Deficit.slotX (by decide)
    (Deficit.defH g nvars) (Deficit.defA nvars g cC cK Xold nvars)
    (by intro j; fin_cases j; show nvars - g = (List.replicate (nvars - g) true).length; simp)
    (by intro j; fin_cases j; rfl)
  rw [Deficit.dockH_slotX, Deficit.install_slotX] at ht
  have hall := hW.seq ht
  have e0 : Deficit.defA nvars g cC cK Xold 0 =
      ![pad cC (List.replicate nvars true), pad cK (List.replicate g true), Xold] := by
    funext i; fin_cases i
    · rfl
    · show Deficit.rankAt g cK 0 = pad cK (List.replicate g true)
      simp [Deficit.rankAt, pad]
    · show overlay (List.replicate (0 - g) true) Xold = Xold
      simp [overlay]
  have eK : Deficit.rankAt g cK nvars = pad cK [] := by
    unfold Deficit.rankAt
    rw [Nat.min_eq_right hg, show g - nvars = 0 by omega, List.replicate_zero, List.append_nil, ← List.replicate_add]
    simp [pad]
    omega
  refine (hall.congr_in ?_ e0).congr ?_ ?_
  · funext i; fin_cases i <;> simp [W, Deficit.defH]
  · funext i; fin_cases i <;> simp [Deficit.defH]
  · funext i; fin_cases i
    · rfl
    · exact eK
    · rfl

/-- **The count** of an eliminated system: `0` if inconsistent, else `2^{rest − rank}`, which is `condProbGauss`'s. -/
theorem count_eq (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    (if (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pre cons)).1 then
        2 ^ (twoH * ℓ - plen - (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pre cons)).2) else 0) =
      (condProbGauss p ℓ twoH k plen pre cons).1 := by
  unfold condProbGauss
  rfl

end NearCubicWires.WireExponent3_5.SeedFix
