import Proof.Wire_3_5.Primitive.SeedFix.SeedFixConsLoop
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixGaussPad

/-! # C4.E: one system eliminated, its conditional count written (P3:2950-2957)

Realizes one conditional coefficient of `samp:seed` and `filt:soft`: "For a fixed prefix, every assertion that a
sample lies at a specified position is a system of binary linear equations in the remaining seed bits. A product of
such indicators is their conjunction. Gaussian elimination gives conditional probability zero if it is inconsistent,
and `2^{−a}` if its remaining rank is `a`. The denominator divides `2^S`" (P3:2950-2955); for the hash, "Gaussian
elimination therefore computes each expectation exactly" (P3:2268-2269).

The block streams the constraint records through the rows block (`loop_run`), terminates the rows tape, eliminates
(`gaussP_run`) and writes the count exponent (`deficit_run`). Every scratch tape ends as it began or as stale
content the next call tolerates: the rank tape blank, the counter unchanged, every head at cell 0.

Paper quantities of the main type (`elim_run`): the flag `(gauss rest (system p ℓ 2h k plen pre cons)).1` and the
exponent `rest − rank` in unary on `X`; `elim_count` turns them into `condProbGauss`'s count, `0` or
`2^{rest − rank}`, i.e. `2^{rest}` times the conditional probability.

Results: `system_lt`, `system_length`, `rowsAll_run`, `count_run`, **`elim_run`**, `elim_ports`, **`elim_count`**, and the cost
**`elimCost_le`** (`≤ 3000 q⁶`) with `elim_within`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.JoinElimination
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)

/-! ## The system's rows are masks over the remaining bits -/

theorem fold_mask_lt (n : ℕ) (c : ℕ → Bool) : ∀ (l : List ℕ) (acc : ℕ), (∀ j ∈ l, j < n) → acc < 2 ^ n →
    l.foldl (fun acc j => if c j then acc ||| (1 <<< j) else acc) acc < 2 ^ n
  | [], _, _, h => h
  | j :: l, acc, hl, h => by
    rw [List.foldl_cons]
    refine fold_mask_lt n c l _ (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')) ?_
    split
    · have hj : j < n := hl j List.mem_cons_self
      have h1 : 1 <<< j < 2 ^ n := by rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hj
      exact Nat.or_lt_two_pow h h1
    · exact h

theorem system_lt (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    ∀ r ∈ system p ℓ twoH k plen pre cons, r.1 < 2 ^ (twoH * ℓ - plen) := by
  intro r hr
  unfold system at hr
  simp only [List.mem_flatMap, List.mem_map] at hr
  obtain ⟨con, _, cc, _, rfl⟩ := hr
  exact fold_mask_lt (twoH * ℓ - plen)
    (fun j => (JoinElimination.fmul p ℓ (2 ^ ((plen + j) % ℓ)) (JoinElimination.fpow p ℓ con.1 ((plen + j) / ℓ))).testBit cc)
    (List.range (twoH * ℓ - plen)) 0 (fun j hj => List.mem_range.mp hj) (Nat.two_pow_pos _)

theorem system_length (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) :
    (system p ℓ twoH k plen pre cons).length = cons.length * k := by
  unfold system
  simp [List.length_flatMap, List.map_const', List.sum_replicate]

/-! ## The bank (tapes 0–23 the record loop's, 24 the stage log, 25 the pass output, 26 the pivots, 27 the rank tape,
28 the column counter, 29 the flag `G`, 30 the exponent tape `X`) -/

def bank31 (p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE : ℕ) (R : Regs) (O S W P K C G X : List Bool) :
    Fin 31 → List Bool :=
  ![List.replicate twoH true ++ [false], List.replicate ℓ true ++ [false], frame (binary ℓ R.a), frame (binary ℓ R.c),
    R.T ++ List.replicate m false, frame (binary ℓ p), R.fl, frame (binary ℓ R.x), frame (binary ℓ R.z), [false],
    List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, List.replicate RV false,
    frame (binary plen pfx), frame (binary ℓ R.mc), R.r, [R.b], [false], O, frame (binary ℓ 1),
    List.replicate cap4 false, S, List.replicate cL false, List.replicate cE false, W, P, K, C, G, X]

def c24Term : Fin 1 → Fin 24 := ![19]

theorem install_c24Term (A : Fin 24 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install c24Term A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, v 0, A 20, A 21, A 22, A 23] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

theorem dockH_c24Term (H : Fin 24 → ℕ) (v : Fin 1 → ℕ) :
    dockH c24Term H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, v 0, H 20, H 21, H 22, H 23] := by
  funext i; fin_cases i
  all_goals first
    | exact dockH_slot _ (by decide) _ _ 0
    | exact dockH_other _ _ _ _ (by decide)

def e31Set : Fin 1 → Fin 31 := ![29]

theorem install_e31Set (A : Fin 31 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install e31Set A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, v 0, A 30] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def e31Gauss : Fin 10 → Fin 31 := ![19, 25, 26, 9, 10, 27, 28, 29, 11, 24]

theorem install_e31Gauss (A : Fin 31 → List Bool) (v : Fin 10 → List Bool) :
    RecoveryRootRound.install e31Gauss A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, v 3, v 4, v 8, A 12, A 13, A 14, A 15, A 16, A 17, A 18, v 0, A 20, A 21, A 22, A 23, v 9, v 1, v 2, v 5, v 6, v 7, A 30] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 4
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 5
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 6
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 7
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 8
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 9
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def e31Def : Fin 4 → Fin 31 := ![28, 27, 30, 24]

theorem install_e31Def (A : Fin 31 → List Bool) (v : Fin 4 → List Bool) :
    RecoveryRootRound.install e31Def A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, v 3, A 25, A 26, v 1, v 0, A 29, v 2] := by
  funext i; fin_cases i
  all_goals first
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 0
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 1
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 2
    | exact RecoveryRootRound.install_slot _ (by decide) _ _ 3
    | exact RecoveryRootRound.install_other _ _ _ _ (by decide)

def selE1 : Fin 24 → Bool :=
  ![false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, true, false, false, true, false]
def selG : Fin 9 → Bool := ![true, false, false, false, false, true, true, false, false]
def selD : Fin 3 → Bool := ![true, true, true]

noncomputable def termR := RecoveryFocus.machine c24Term Gauss.termM
/-- The rows of every record, the terminator, the record and rows heads rewound. -/
noncomputable def rowsAllM := TapeEmbedding.machine 6 (MaskedReset.machine (Composition.machine loopM termR) selE1)
noncomputable def setG := RecoveryFocus.machine e31Set setM
noncomputable def gaussE := RecoveryFocus.machine e31Gauss (MaskedReset.machine Gauss.gaussM selG)
noncomputable def defE := RecoveryFocus.machine e31Def (MaskedReset.machine Deficit.machine selD)

/-- The flag set, the elimination, the count exponent. -/
noncomputable def countM := Composition.machine (Composition.machine setG gaussE) defE

/-- **The elimination block**: the rows, then the count. -/
noncomputable def elimM := Composition.machine rowsAllM countM

def loopCost (ℓ twoH k plen n : ℕ) : ℕ := n * (recCost ℓ twoH k plen + 2) + 1
def rowsAllCost (ℓ twoH k plen n : ℕ) : ℕ := 2 * (loopCost ℓ twoH k plen n + 1 + 1) + 2
def countCost (nrows rest : ℕ) : ℕ := 1 + 1 + (2 * Gauss.gaussCost nrows rest + 2) + 1 + (2 * Deficit.cost rest + 2)
def elimCost (ℓ twoH k plen n : ℕ) : ℕ :=
  rowsAllCost ℓ twoH k plen n + 1 + countCost (n * k) (twoH * ℓ - plen)

theorem loopH_zero (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) : loopH p ℓ twoH k plen pfx cons 0 = fun _ => 0 := by
  funext j; fin_cases j <;> simp [loopH, hd24, rowsI]

/-- **The rows of all records**, terminated, with every head back at cell 0. -/
theorem rowsAll_run (p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL cE : ℕ) (R0 : Regs) (cons : List (ℕ × ℕ))
    (stale backingO W P K C G X : List Bool) (hℓ : 1 ≤ ℓ) (hkl : k ≤ ℓ) (h0 : R0.Ok ℓ twoH)
    (hcap : 2 * ℓ + 2 ≤ cap) (hcap2 : ℓ * (innerCost ℓ + 2) + 1 ≤ cap2)
    (hcap2' : ℓ * (mulIterCost ℓ + 2) + 1 ≤ cap2) (hcap2'' : plen * (phACost ℓ + 2) + 1 ≤ cap2)
    (hcap3 : tableCost ℓ twoH ≤ cap3) (hcap3' : passesCost ℓ plen (twoH * ℓ) ≤ cap3)
    (hcap4 : k * (rowCost ℓ plen (twoH * ℓ) + 2) + 1 ≤ cap4) (hplen : plen ≤ twoH * ℓ) (hm : 1 ≤ m)
    (hRV : 2 * ℓ + 1 ≤ RV) (hcL : 2 * ℓ + 1 ≤ cL) (hcE : loopCost ℓ twoH k plen cons.length + 1 + 1 ≤ cE) :
    Step rowsAllM (rowsAllCost ℓ twoH k plen cons.length) (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE R0 backingO (consTape ℓ k cons stale) W P K C G X)
      (fun _ => 0)
      (bank31 p ℓ twoH plen pfx m cap cap2 cap3 cap4 RV cL cE (regsAt p ℓ twoH k plen R0 cons cons.length)
        (overlay (rowsI p ℓ twoH k plen pfx cons cons.length ++ [false]) backingO) (consTape ℓ k cons stale)
        W P K C G X) := by
  have hl := loop_run p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO hℓ hkl h0 hcap hcap2 hcap2'
    hcap2'' hcap3 hcap3' hcap4 hplen hm hRV hcL
  rw [loopH_zero] at hl
  set n := cons.length
  set rows := rowsI p ℓ twoH k plen pfx cons n
  have ht := dockRun (Gauss.term_run rows backingO) c24Term (by decide) (loopH p ℓ twoH k plen pfx cons n)
    (loopA p ℓ twoH k plen pfx m cap cap2 cap3 cap4 RV cL R0 cons stale backingO n)
    (by intro j; fin_cases j; rfl) (by intro j; fin_cases j; rfl)
  rw [dockH_c24Term, install_c24Term] at ht
  have hs := hl.seq ht
  have hm1 := hs.mask (cap := cE) selE1 (fun _ _ => rfl) hcE
  have he := hm1.embed (fun _ : Fin 6 => 0) ![W, P, K, C, G, X]
  refine (he.congr_in ?_ ?_).congr ?_ ?_
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl
  · funext j; fin_cases j <;> rfl

/-- **The count**: the flag and the exponent written by `elim_run` are `condProbGauss`'s count, `0` or
`2^{rest − rank}`, the number of completions of the prefix meeting every constraint. -/
theorem elim_count (p ℓ twoH k plen pfx : ℕ) (cons : List (ℕ × ℕ)) :
    (if (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).1 then
        2 ^ (twoH * ℓ - plen - (gauss (twoH * ℓ - plen) (system p ℓ twoH k plen pfx cons)).2) else 0) =
      (condProbGauss p ℓ twoH k plen pfx cons).1 :=
  count_eq p ℓ twoH k plen pfx cons

/-! ## The cost in a named class -/

end NearCubicWires.WireExponent3_5.SeedFix
