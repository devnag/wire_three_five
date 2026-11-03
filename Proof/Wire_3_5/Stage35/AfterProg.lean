import Proof.Wire_3_5.Stage35.AfterKit
import W3.Recovery3.AfterParts2
import W3.Recovery3.After4Mach
import Proof.Wire_3_5.Stage35.UInst
import OuterM.ARun
import OuterM.Width
import CheckedPCPP.Harness
import Proof.CaseAnalysis.CaseTwoBudget
import Proof.CaseAnalysis.RecoveryFullBound
import Proof.Hierarchy.HierarchyFixedWord
import Proof.Wire_3_5.Stage35.Bundle

-- Port of W3 Recovery3/AfterProg.lean with the copies schedule (Stage35.WQ).

/-!
# The recovery after the refuter: the program

The near-cubic-gates paper's uniform recovery (sec:all-lengths): "The choices of sec:gadget-transfer are recovered in three stages … First, a formula
over the description of `B_src` with the `N` constraints (eq:source-check) … finds the first source circuit `B*_src`,
or shows that there is none, in which case the table is `X_z`. Second, the algorithm of imp:short-pcp is run
deterministically on `⟨B*_src⟩_ν` …; a formula with one variable per oracle address … finds the first oracle `O*`.
Third, a formula over the description of `B_pf` … finds the first `B*_pf`, or shows that there is none, in which case
the table is `Ô*`. … Run the general amplifier on `X_z` or `Ô*`. If no oracle `O*` exists at an exceptional initial
source length, the second stage detects that case and the slice is set to zero. In the small-oracle branch, the honest
PCPP proof and each AND helper are computable in polynomial time once the pair is known."

One finite oracle control graph (`OrdinaryOracleCompose.graph`) of 31 pieces on `T` ambient tapes: 32 shared tapes,
then one private block per piece. Shared tapes (index : content):
`0` Z = `frame z ++ post` (port), `1` PT = `frame point` (port), `2` OUT (output), `3` QRY (the one query tape),
`4` X1 = `frame z` (stage 1's table), `5` Q1, `7` QC, `10` Q3, `12` Q4 = `1^q`, `6` W1, `11` W3 = `1^W`, `15` WC
(the query-clear driver), `8` BC, `13` B4 = `1^B` (`B = q^G` cap), `9` NU = `1^ν`, `14` DS1 / `23` DS3 = the
descriptions found by stages 1 / 3, `16` FD = `frame (descriptor B*_src)`, `17` DESC = `descriptor B*_src`, `18` MW1 /
`24` MW2 = the word of `C_{⟨B*_src⟩_ν}`, `19` F1 / `31` F3 = the stage flags, `21` T3 / `22` T4 = copies of `frame O*`,
`25`–`28` XW1–XW4 / `29` XN = copies of `frame z` for the width / `ν` donors; `20`, `30` unused.

Pieces (path order): 0–15 preparation (copies of `frame z`, the width donor `1^q` ×4, `1^ν`, the capacities
`1^W` ×2 and the clear driver, the cap `1^B` ×2); 16 stage 1 → (17 Case 1 (i) | 18 clear, 19 canonical→native
converter, 20 unframe, 21 A-run, 22 stage 2 → (23 `false` | 24, 25 copies of `O*`, 26 clear, 27 stage 3 →
(28 Case 1 (iii) | 29 A-run, 30 Case 2))).
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.After

open Stage35 _root_.NearCubicGates.Close _root_.NearCubicGates.Close.Recovery3 _root_.NearCubicGates.Close.Recovery3.After

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-! ## The docked machines -/

/-- The width donor's rewound program (`1^q` from `frame z`). -/
noncomputable abbrev wP (s : WS35) (_g : WQ) : Program :=
  Rewind.program (OuterM.widthDonor s.mw s.SV).unary.program

/-- The A-run. -/
noncomputable abbrev aR (s : WS35) (_g : WQ) := OuterM.aRun s.mw s.SV

/-- Stages 1 and 3, clocked. -/
noncomputable abbrev pU (g : WQ) := clocked (ENP.UStage.program g.degree)

/-- Stage 2, clocked. -/
noncomputable abbrev pT {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ} (K : Kit s P g) :=
  clocked K.ts.program

/-- The listed table of a listed-pairs stage. -/
def tableL (d : ℕ) : Fin (ENP.UStage.tapes d) := (⟨1664 + 158, by unfold ENP.USupply.uTapes; omega⟩ : Fin _).castAdd 790
/-- The unary width `R` of a listed-pairs stage. -/
def rL (d : ℕ) : Fin (ENP.UStage.tapes d) := (⟨1664 + 159, by unfold ENP.USupply.uTapes; omega⟩ : Fin _).castAdd 790
/-- The unary workspace `W` of a listed-pairs stage. -/
def wL (d : ℕ) : Fin (ENP.UStage.tapes d) := (⟨1664 + 179, by unfold ENP.USupply.uTapes; omega⟩ : Fin _).castAdd 790

@[simp] theorem tableL_val (d : ℕ) : (tableL d).val = 1664 + 158 := rfl
@[simp] theorem rL_val (d : ℕ) : (rL d).val = 1664 + 159 := rfl
@[simp] theorem wL_val (d : ℕ) : (wL d).val = 1664 + 179 := rfl
@[simp] theorem flagPort_val (d : ℕ) : (ENP.UStage.flagPort d).val = 1664 + ENP.USupply.uTapes d + 369 := rfl
@[simp] theorem descPort_val (d : ℕ) : (ENP.UStage.descPort d).val = 1664 + ENP.USupply.uTapes d + 787 := rfl
@[simp] theorem queryPort_val (d : ℕ) : (ENP.UStage.queryPort d).val = 1664 + ENP.USupply.uTapes d + 356 := rfl
@[simp] theorem cslot_val (p : OrdinaryOracleProgram) (i : Fin p.base.tapeCount) : (cslot p i).val = i.val := rfl

theorem uinput_eq (d : ℕ) (table : List Bool) (R W : ℕ) (j : Fin (ENP.UStage.tapes d)) :
    ENP.UStage.input d table R W j =
      if j = tableL d then table else if j = rL d then List.replicate R true
      else if j = wL d then List.replicate W true else [] := by
  unfold ENP.UStage.input
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.addCases_left]
    unfold ENP.UGraph.input tableL rL wL
    simp only [Fin.ext_iff, Fin.val_castAdd]
  · rw [Fin.addCases_right]
    have hu : 342 ≤ ENP.USupply.uTapes d := by unfold ENP.USupply.uTapes; omega
    have hv : (Fin.natAdd (1664 + ENP.USupply.uTapes d) i).val = 1664 + ENP.USupply.uTapes d + i.val := rfl
    have h1 : Fin.natAdd (1664 + ENP.USupply.uTapes d) i ≠ tableL d := by
      intro h; have := congrArg Fin.val h; simp only [tableL, Fin.val_castAdd] at this; omega
    have h2 : Fin.natAdd (1664 + ENP.USupply.uTapes d) i ≠ rL d := by
      intro h; have := congrArg Fin.val h; simp only [rL, Fin.val_castAdd] at this; omega
    have h3 : Fin.natAdd (1664 + ENP.USupply.uTapes d) i ≠ wL d := by
      intro h; have := congrArg Fin.val h; simp only [wL, Fin.val_castAdd] at this; omega
    rw [if_neg h1, if_neg h2, if_neg h3]

/-! ## Layout -/

section

variable {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ}

/-- Private block sizes of the 31 pieces. -/
noncomputable def sz (K : Kit s P g) : ℕ → ℕ
  | 2 | 4 | 6 | 8 => (wP s g).tapeCount
  | 10 => nuDonor.t
  | 11 | 12 | 13 => 26
  | 14 | 15 => RecoveryFullBound.tapes g.degree
  | 16 | 27 => (pU g).base.tapeCount
  | 17 | 28 => K.c1.t
  | 19 => 135
  | 20 => unframe.t
  | 21 | 29 => (aR s g).t
  | 22 => (pT K).base.tapeCount
  | 23 => 2
  | 30 => K.ht.t
  | _ => 1

/-- The block offsets: 32 shared tapes, then the blocks in piece order. -/
noncomputable def off (K : Kit s P g) : ℕ → ℕ
  | 0 => 32
  | k + 1 => off K k + sz K k

/-- The ambient tape count. -/
noncomputable def T (K : Kit s P g) : ℕ := off K 31

theorem off_mono (K : Kit s P g) {i j : ℕ} (h : i ≤ j) : off K i ≤ off K j := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hi | hi
    · exact (ih (by omega)).trans (by simp only [off]; omega)
    · have : i = j + 1 := by omega
      subst this; exact le_rfl

theorem off_ge (K : Kit s P g) (k : ℕ) : 32 ≤ off K k := off_mono K (Nat.zero_le k)

theorem fits (K : Kit s P g) (k : ℕ) (hk : k < 31) : off K k + sz K k ≤ T K := by
  have := off_mono K (show k + 1 ≤ 31 by omega)
  simpa only [off, T] using this

theorem h32 (K : Kit s P g) : 32 ≤ T K := off_ge K 31

/-- Shared tape `i`. -/
noncomputable def sh (K : Kit s P g) (i : Fin 32) : Fin (T K) := Fin.castLE (h32 K) i

@[simp] theorem sh_val (K : Kit s P g) (i : Fin 32) : (sh K i).val = i.val := rfl

@[simp] theorem sh_inj (K : Kit s P g) (i j : Fin 32) : sh K i = sh K j ↔ i = j := by
  constructor
  · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro h; rw [h]

/-- The first private tape of block `k`. -/
noncomputable def blk (K : Kit s P g) (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) : Fin (T K) :=
  ⟨off K k, by have := fits K k hk; omega⟩

/-- A bank of piece `k` with ports listed against the 32 shared tapes. -/
noncomputable def mkBank (K : Kit s P g) (k : ℕ) (hk : k < 31) {t : ℕ} (ht : sz K k = t)
    (l : List (Fin t × Fin 32)) (h1 : (l.map Prod.fst).Nodup) (h2 : (l.map Prod.snd).Nodup) : Bank (T K) t where
  off := off K k
  fits := ht ▸ fits K k hk
  l := l.map fun p => (p.1, sh K p.2)
  fstNodup := by simpa [List.map_map, Function.comp_def] using h1
  sndNodup := by
    have he : ((l.map fun p => (p.1, sh K p.2)).map Prod.snd) = (l.map Prod.snd).map (sh K) := by
      simp [List.map_map, Function.comp_def]
    rw [he]
    exact h2.map (fun a b h => (sh_inj K a b).mp h)
  low := by
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    have := off_ge K k
    simp only [sh_val]
    omega

end

/-! ## Banks of the pieces -/

section

variable {s : WS35} {P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm} {g : WQ}

theorem nodup2 {α : Type} {a b : α} (h : a ≠ b) : [a, b].Nodup := by
  simp [List.nodup_cons, h]

/-- The capacity parameters: `1^W` with `W = 2^{A n + B}` for the stages, `2^{Aq n + Bq}` for the query clear. -/
structure Cfg where
  A : ℕ
  B : ℕ
  Aq : ℕ
  Bq : ℕ

/-- The width donor's bank: `frame z` from shared `xw`, `1^q` to shared `q`. -/
noncomputable def widBank (K : Kit s P g) (k : ℕ) (hk : k < 31) (ht : sz K k = (wP s g).tapeCount)
    (xw q : Fin 32) (h : xw ≠ q) : Bank (T K) (wP s g).tapeCount :=
  mkBank K k hk ht [(⟨0, by have := (wP s g).twoTapes; omega⟩, xw), ((wP s g).outputTape, q)]
    (by
      simp only [List.map_cons, List.map_nil]
      exact nodup2 (fun e => (wP s g).outputFresh (by rw [← e])))
    (by simpa using nodup2 h)

/-- The `ν` donor's bank: shared `29` (XN) to shared `9` (NU). -/
noncomputable def nuBank (K : Kit s P g) : Bank (T K) nuDonor.t :=
  mkBank K 10 (by decide) rfl [(nuDonor.inp, 29), (nuDonor.outp, 9)]
    (by simpa using nodup2 nuDonor.ne) (by decide)

/-- A capacity bank: `frame point` from shared `1` (PT), `1^{2^{A n + B}}` to shared `w`. -/
noncomputable def capBank (K : Kit s P g) (k : ℕ) (hk : k < 31) (ht : sz K k = 26) (w : Fin 32) (h : (1 : Fin 32) ≠ w) :
    Bank (T K) 26 :=
  mkBank K k hk ht [(0, 1), (24, w)] (by simp only [List.map_cons, List.map_nil]; decide)
    (by simpa using nodup2 h)

/-- A cap bank: `1^q` from shared `q` (kept), `1^{q^G cap}` to shared `b`. -/
noncomputable def fbBank (K : Kit s P g) (k : ℕ) (hk : k < 31) (ht : sz K k = RecoveryFullBound.tapes g.degree)
    (q b : Fin 32) (h : q ≠ b) : Bank (T K) (RecoveryFullBound.tapes g.degree) :=
  mkBank K k hk ht [(RecoveryFullBound.sourceSlot g.degree, q), (RecoveryFullBound.rawSlot g.degree, b)]
    (by
      simp only [List.map_cons, List.map_nil]
      refine nodup2 (fun e => ?_)
      have := congrArg Fin.val e
      simp [RecoveryFullBound.sourceSlot, RecoveryFullBound.rawSlot, RecoveryFullBound.old,
        RecoveryFullBound.extra] at this
      have h0 : 0 < RecoveryFullBound.base g.degree := by
        simp [RecoveryFullBound.base, ProjectionNormalization.DimensionPolynomial.tapes]
      omega)
    (by simpa using nodup2 h)

/-- A listed-pairs stage's bank (stages 1 and 3): table `x`, `1^R` from `r`, `1^W` from `w`, flag `f`, description
`ds`, the query on shared `3`. -/
noncomputable def uBank (K : Kit s P g) (k : ℕ) (hk : k < 31) (ht : sz K k = (pU g).base.tapeCount)
    (x r w f ds : Fin 32) (h : [x, r, w, f, ds, 3].Nodup) : Bank (T K) (pU g).base.tapeCount :=
  mkBank K k hk ht
    [(cslot _ (tableL g.degree), x), (cslot _ (rL g.degree), r), (cslot _ (wL g.degree), w),
      (cslot _ (ENP.UStage.flagPort g.degree), f), (cslot _ (ENP.UStage.descPort g.degree), ds),
      (cslot _ (ENP.UStage.queryPort g.degree), 3)]
    (by
      have hu : 342 ≤ ENP.USupply.uTapes g.degree := by unfold ENP.USupply.uTapes; omega
      apply List.Nodup.of_map Fin.val
      simp only [List.map_cons, List.map_nil, cslot_val, tableL_val, rL_val, wL_val, flagPort_val, descPort_val,
        queryPort_val, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or,
        not_false_eq_true]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega)
    (by simpa using h)

/-- The Case 1 machine's bank: table from `a`, the address from shared `1`, `1^q` from `q`, output to shared `2`. -/
noncomputable def c1Bank (K : Kit s P g) (k : ℕ) (hk : k < 31) (ht : sz K k = K.c1.t) (a q : Fin 32)
    (h : [a, 1, q, 2].Nodup) : Bank (T K) K.c1.t :=
  mkBank K k hk ht
    [(⟨0, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, a),
      (⟨1, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, 1),
      (⟨2, by have := K.c1.large; have := K.c1.output.isLt; omega⟩, q), (K.c1.output, 2)]
    (by
      have := K.c1.large
      apply List.Nodup.of_map Fin.val
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true, not_or, not_false_eq_true]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega)
    (by simpa using h)

/-- The converter's bank: the description from `14` (DS1), `1^q` from `7` (QC), `1^B` from `8` (BC), the framed native
descriptor to `16` (FD). -/
noncomputable def convBank (K : Kit s P g) : Bank (T K) 135 :=
  mkBank K 19 (by decide) rfl [(1, 14), (3, 7), (4, 8), (132, 16)] (by decide) (by decide)

/-- The unframe bank: `16` (FD) to `17` (DESC). -/
noncomputable def ufBank (K : Kit s P g) : Bank (T K) unframe.t :=
  mkBank K 20 (by decide) rfl [(unframe.src, 16), (unframe.dst, 17)] (by simpa using nodup2 unframe.ne)
    (by decide)

/-- The A-run's bank: the raw descriptor from `17` (DESC), `1^ν` from `9` (NU), the word to `mw`. -/
noncomputable def arBank (K : Kit s P g) (k : ℕ) (hk : k < 31) (ht : sz K k = (aR s g).t) (mw : Fin 32)
    (h : [17, 9, mw].Nodup) : Bank (T K) (aR s g).t :=
  mkBank K k hk ht [((aR s g).dIn, 17), ((aR s g).nIn, 9), ((aR s g).wOut, mw)]
    (by
      have hn := (aR s g).nodup
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hn
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true]
      tauto)
    (by simpa using h)

/-- Stage 2's bank: its query on shared `3`, its input word from `18` (MW1); flag and table stay in its block. -/
noncomputable def tBank (K : Kit s P g) : Bank (T K) (pT K).base.tapeCount :=
  mkBank K 22 (by decide) rfl [(cslot _ K.ts.program.queryTape, 3), (cslot _ K.ts.inPort, 18)]
    (by
      simp only [List.map_cons, List.map_nil]
      exact nodup2 (fun e => K.ts.inQuery (cslot_injective _ e).symm))
    (by simp only [List.map_cons, List.map_nil]; decide)

/-- The `false` writer's bank: its tape `0` is shared `2` (OUT). -/
noncomputable def fBank (K : Kit s P g) : Bank (T K) 2 :=
  mkBank K 23 (by decide) rfl [(0, 2)] (by decide) (by decide)

/-- The Case 2 producer's bank: the word from `24` (MW2), stage 3's description from `23` (DS3), the address from `1`,
`1^q` from `12` (Q4), `1^B` from `13` (B4), output to `2`. -/
noncomputable def htBank (K : Kit s P g) : Bank (T K) K.ht.t :=
  mkBank K 30 (by decide) rfl
    [(⟨0, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, 24),
      (⟨1, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, 23),
      (⟨2, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, 1),
      (⟨3, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, 12),
      (⟨4, by have := K.ht.large; have := K.ht.output.isLt; omega⟩, 13), (K.ht.output, 2)]
    (by
      have := K.ht.large
      apply List.Nodup.of_map Fin.val
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true, not_or, not_false_eq_true]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> omega)
    (by simp only [List.map_cons, List.map_nil]; decide)

/-- Stage 2's table tape (in the ambient bank). -/
noncomputable def tbl (K : Kit s P g) : Fin (T K) := (tBank K).slot (cslot _ K.ts.tablePort)

/-- Stage 2's flag tape (in the ambient bank). -/
noncomputable def flag2 (K : Kit s P g) : Fin (T K) := (tBank K).slot (cslot _ K.ts.flagPort)

/-- A three-tape slot `![a, b, log]` with the log in block `k`. -/
noncomputable def tslot (K : Kit s P g) (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) (a b : Fin (T K)) :
    Fin 3 → Fin (T K) :=
  ![a, b, blk K k hk hs]

/-- A framed copy `a → b` (proof 1's field mover). -/
noncomputable def copyP (K : Kit s P g) (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) (a b : Fin (T K)) : Piece (T K) :=
  ordinary (RecoveryFocus.machine (tslot K k hk hs a b) PCPFieldMoves.readyMachine)

/-- The query clear: shared `3` (QRY) erased with the driver on shared `15` (WC). -/
noncomputable def clearP (K : Kit s P g) (k : ℕ) (hk : k < 31) (hs : 1 ≤ sz K k) : Piece (T K) :=
  ordinary (RecoveryFocus.machine (tslot K k hk hs (sh K 3) (sh K 15)) (RecoveryScratchErase.resetMachine 1))

/-! ## The program -/

noncomputable def b2 (K : Kit s P g) := widBank K 2 (by decide) rfl 25 5 (by decide)
noncomputable def b4 (K : Kit s P g) := widBank K 4 (by decide) rfl 26 7 (by decide)
noncomputable def b6 (K : Kit s P g) := widBank K 6 (by decide) rfl 27 10 (by decide)
noncomputable def b8 (K : Kit s P g) := widBank K 8 (by decide) rfl 28 12 (by decide)
noncomputable def b11 (K : Kit s P g) := capBank K 11 (by decide) rfl 6 (by decide)
noncomputable def b12 (K : Kit s P g) := capBank K 12 (by decide) rfl 11 (by decide)
noncomputable def b13 (K : Kit s P g) := capBank K 13 (by decide) rfl 15 (by decide)
noncomputable def b14 (K : Kit s P g) := fbBank K 14 (by decide) rfl 7 8 (by decide)
noncomputable def b15 (K : Kit s P g) := fbBank K 15 (by decide) rfl 12 13 (by decide)
noncomputable def b16 (K : Kit s P g) := uBank K 16 (by decide) rfl 4 5 6 19 14 (by decide)
noncomputable def b17 (K : Kit s P g) := c1Bank K 17 (by decide) rfl 0 7 (by decide)
noncomputable def b21 (K : Kit s P g) := arBank K 21 (by decide) rfl 18 (by decide)
noncomputable def b27 (K : Kit s P g) := uBank K 27 (by decide) rfl 21 10 11 31 23 (by decide)
noncomputable def b28 (K : Kit s P g) := c1Bank K 28 (by decide) rfl 22 12 (by decide)
noncomputable def b29 (K : Kit s P g) := arBank K 29 (by decide) rfl 24 (by decide)

/-- The 31 pieces. -/
noncomputable def pieces (K : Kit s P g) (c : Cfg) : Fin 31 → Piece (T K) :=
  ![copyP K 0 (by decide) le_rfl (sh K 0) (sh K 4),
    copyP K 1 (by decide) le_rfl (sh K 0) (sh K 25),
    ordinary (RecoveryFocus.machine (b2 K).slot (wP s g).machine),
    copyP K 3 (by decide) le_rfl (sh K 0) (sh K 26),
    ordinary (RecoveryFocus.machine (b4 K).slot (wP s g).machine),
    copyP K 5 (by decide) le_rfl (sh K 0) (sh K 27),
    ordinary (RecoveryFocus.machine (b6 K).slot (wP s g).machine),
    copyP K 7 (by decide) le_rfl (sh K 0) (sh K 28),
    ordinary (RecoveryFocus.machine (b8 K).slot (wP s g).machine),
    copyP K 9 (by decide) le_rfl (sh K 0) (sh K 29),
    ordinary (RecoveryFocus.machine (nuBank K).slot nuDonor.M),
    ordinary (RecoveryFocus.machine (b11 K).slot (CloseoutCapacity.machine c.A c.B)),
    ordinary (RecoveryFocus.machine (b12 K).slot (CloseoutCapacity.machine c.A c.B)),
    ordinary (RecoveryFocus.machine (b13 K).slot (CloseoutCapacity.machine c.Aq c.Bq)),
    ordinary (RecoveryFocus.machine (b14 K).slot (RecoveryFullBound.machine g.degree)),
    ordinary (RecoveryFocus.machine (b15 K).slot (RecoveryFullBound.machine g.degree)),
    focused (pU g) (b16 K).slot,
    ordinary (RecoveryFocus.machine (b17 K).slot K.c1.M),
    clearP K 18 (by decide) le_rfl,
    ordinary (RecoveryFocus.machine (convBank K).slot CloseoutCaseTwo.Cold.machine),
    ordinary (RecoveryFocus.machine (ufBank K).slot unframe.M),
    ordinary (RecoveryFocus.machine (b21 K).slot (aR s g).M),
    focused (pT K) (tBank K).slot,
    ordinary (RecoveryFocus.machine (fBank K).slot (HierarchyFixedWord.machine [false])),
    copyP K 24 (by decide) le_rfl (tbl K) (sh K 21),
    copyP K 25 (by decide) le_rfl (tbl K) (sh K 22),
    clearP K 26 (by decide) le_rfl,
    focused (pU g) (b27 K).slot,
    ordinary (RecoveryFocus.machine (b28 K).slot K.c1.M),
    ordinary (RecoveryFocus.machine (b29 K).slot (aR s g).M),
    ordinary (RecoveryFocus.machine (htBank K).slot K.ht.M)]

/-- The control flow: the three stage flags branch, the four terminal pieces stop, every other piece falls through. -/
noncomputable def next (K : Kit s P g) (c : Cfg) (j : Fin 31) (_ : Fin (pieces K c j).states)
    (read : Fin (T K) → Bool) : Option (Fin 31) :=
  if j.val = 16 then some (if read (sh K 19) then 18 else 17)
  else if j.val = 22 then some (if read (flag2 K) then 24 else 23)
  else if j.val = 27 then some (if read (sh K 31) then 29 else 28)
  else if j.val = 17 ∨ j.val = 23 ∨ j.val = 28 ∨ j.val = 30 then none
  else if h : j.val + 1 < 31 then some ⟨j.val + 1, h⟩ else none

/-- The ports: output on shared `2`, the one query tape on shared `3`. -/
noncomputable def ports (K : Kit s P g) : Ports (T K) where
  twoTapes := by have := h32 K; omega
  outputTape := sh K 2
  outputFresh := by simp
  queryTape := sh K 3
  queryFresh := by simp

/-- **The after-prefix program** (the near-cubic-gates paper's uniform recovery). -/
noncomputable def prog (K : Kit s P g) (c : Cfg) : OrdinaryOracleProgram :=
  (ports K).program (graph (pieces K c) 0 (next K c))

end

end NearCubicGates.Close.Recovery3.After

