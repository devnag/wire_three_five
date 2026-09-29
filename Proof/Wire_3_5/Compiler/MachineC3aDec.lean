import Proof.Wire_3_5.Compiler.MachineC3aPlan
import Proof.Assembly.ColdSource

/-! # C3a machine, the decomposition stage: every carrier gate's exact children (P3:1602-1641)

Paper: alg:disjoint, "There is an explicitly constructible list of at most `max(1, fℓ)` integer affine equations
`E_j(x) = 0` such that `H(x) = Σ_j 1[E_j(x) = 0]` on the Boolean cube [...] Construction is polynomial in the explicit
output size" (P3:1602-1615), applied to every carrier gate (P3:1636-1641, "Decompose an original-coordinate threshold
using Lemma alg:disjoint").

Base already builds this cold: `Cold.entry_run` manufactures the source capacity `C = capacity a P` from `1^P`,
allocates the decomposition's reusable bank and rewinds, and `Prelude.occurrences_run` parses the stream's count
header, skips its top payload and runs the literal's decomposition constructor once per gate (`occurrence_run`). The
stage here, on the layout `Fin (Cold.tapes a + 1)` (base's tapes, then the doubly framed stream `frame seg`):
1. unframes `seg` onto the source port (its cursor stops at `|seg|`, base's entry convention);
2. moves the domain template's cursor to cell `1`;
3. runs `Cold.entryMachine` and the occurrence prelude + loop (`Prelude.occurrences`) on base's own layout;
4. closes the child counts with `false` (the pool builder's entry format);
and a masked reset returns every head to cell `0` (**`dec_run`**). `P = |seg|` covers the arity (the top payload is
`1^n`) and the stream itself (`|seg| ≤ 1000(P+2)^2`), which are base's `actual_capacity` hypotheses.

The paper quantity of the main theorem is the children of every carrier gate: the body port holds
`(GS a occ).flatMap exactWord`, the counts port `(counts a occ).flatMap natWord ++ [false]`, the total port
`false :: 1^{B}`, the driver `UnaryTemplate.tape |occ|`. Main declarations: the ports, `decM`, `decCost`,
**`dec_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Dec
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.WireExponent3_5.GF2

variable (a : DecompositionAlgorithm)

/-! ## The layout -/

/-- The stage's inner layout: base's cold tapes, then the framed stream. -/
abbrev DT : ℕ := Cold.tapes a + 1

/-- Base's tape `i` in the inner layout. -/
def iC (i : Fin (Cold.tapes a)) : Fin (DT a) := i.castAdd 1

/-- The framed stream's tape. -/
def iFS : Fin (DT a) := Fin.natAdd (Cold.tapes a) (0 : Fin 1)

/-- The ports of base's layout. -/
def pStr : Fin (Cold.tapes a) := Cold.port a (str a)
def pCnt : Fin (Cold.tapes a) := Cold.port a (cnt a)
def pBod : Fin (Cold.tapes a) := Cold.port a (bod a)
def pTot : Fin (Cold.tapes a) := Cold.port a (tot a)
def pDom : Fin (Cold.tapes a) := Cold.port a (dom a)
def pDrv : Fin (Cold.tapes a) := Cold.old a (Prelude.driverSlot a)
def pP : Fin (Cold.tapes a) :=
  ⟨Cold.Base a, by unfold Cold.tapes Cold.Power RepairSource.ProjectionNormalization.DimensionPolynomial.tapes; omega⟩

theorem pStr_val : (pStr a).val = SB a := rfl
theorem pCnt_val : (pCnt a).val = SB a + 1 := rfl
theorem pBod_val : (pBod a).val = SB a + 2 := rfl
theorem pTot_val : (pTot a).val = SB a + 3 := rfl
theorem pDom_val : (pDom a).val = SB a + 10 := rfl
theorem pDrv_val : (pDrv a).val = SB a + 13 := rfl
theorem pP_val : (pP a).val = SB a + 14 := rfl
theorem tapes_eq : Cold.tapes a = SB a + 14 + Cold.Power a := rfl

/-! ## One- and two-slot installs -/

theorem install_one {u : ℕ} (x : Fin u) (A : Fin u → List Bool) (v : Fin 1 → List Bool) :
    install ![x] A v = Function.update A x (v 0) := by
  classical
  funext i
  by_cases h : i = x
  · subst h
    rw [Function.update_self]
    exact install_slot ![i] (fun j k _ => Subsingleton.elim j k) A v 0
  · rw [Function.update_of_ne h]
    exact install_other ![x] A v i (by intro j hj; fin_cases j; exact h hj.symm)

theorem dockH_one {u : ℕ} (x : Fin u) (H : Fin u → ℕ) (v : Fin 1 → ℕ) :
    dockH ![x] H v = Function.update H x (v 0) := by
  classical
  funext i
  by_cases h : i = x
  · subst h
    rw [Function.update_self]
    exact dockH_slot ![i] (fun j k _ => Subsingleton.elim j k) H v 0
  · rw [Function.update_of_ne h]
    exact dockH_other ![x] H v i (by intro j hj; fin_cases j; exact h hj.symm)

theorem two_inj {u : ℕ} (x y : Fin u) (hxy : x ≠ y) : Function.Injective ![x, y] := by
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd h hxy
  · exact absurd h.symm hxy
  · rfl

theorem install_two {u : ℕ} (x y : Fin u) (hxy : x ≠ y) (A : Fin u → List Bool) (v : Fin 2 → List Bool) :
    install ![x, y] A v = Function.update (Function.update A x (v 0)) y (v 1) := by
  classical
  funext i
  by_cases hy : i = y
  · subst hy
    rw [Function.update_self]
    exact install_slot ![x, i] (two_inj x i hxy) A v 1
  · rw [Function.update_of_ne hy]
    by_cases hx : i = x
    · subst hx
      rw [Function.update_self]
      exact install_slot ![i, y] (two_inj i y hxy) A v 0
    · rw [Function.update_of_ne hx]
      exact install_other ![x, y] A v i (by intro j hj; fin_cases j; exact hx hj.symm; exact hy hj.symm)

theorem dockH_two {u : ℕ} (x y : Fin u) (hxy : x ≠ y) (H : Fin u → ℕ) (v : Fin 2 → ℕ) :
    dockH ![x, y] H v = Function.update (Function.update H x (v 0)) y (v 1) := by
  classical
  funext i
  by_cases hy : i = y
  · subst hy
    rw [Function.update_self]
    exact dockH_slot ![x, i] (two_inj x i hxy) H v 1
  · rw [Function.update_of_ne hy]
    by_cases hx : i = x
    · subst hx
      rw [Function.update_self]
      exact dockH_slot ![i, y] (two_inj i y hxy) H v 0
    · rw [Function.update_of_ne hx]
      exact dockH_other ![x, y] H v i (by intro j hj; fin_cases j; exact hx hj.symm; exact hy hj.symm)

/-- The masked heads of a whole-bank reset are all zero. -/
theorem mask_zero {t : ℕ} (H : Fin t → ℕ) :
    Fin.addCases (motive := fun _ => ℕ) (fun i : Fin t => if (fun _ : Fin t => true) i = true then 0 else H i)
      (fun _ : Fin 1 => 0) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem addCases_zero' {t : ℕ} :
    Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin t => 0) (fun _ : Fin 1 => 0) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-! ## The stage's machines -/

theorem fs_ne_str : iFS a ≠ iC a (pStr a) := by
  intro h
  have := congrArg Fin.val h
  simp [iFS, iC, pStr_val, Cold.tapes, Cold.Base, CT, T] at this
  omega

/-- Unframe the stream onto the source port. -/
noncomputable def d1M := RecoveryFocus.machine ![iFS a, iC a (pStr a)] GeneratedAmplifier.Copy.machine
/-- The domain template's cursor to cell `1`. -/
noncomputable def d2M := RecoveryFocus.machine ![iC a (pDom a)] moveM
/-- Base's capacity, allocation and rewind. -/
noncomputable def d3M := TapeEmbedding.machine 1 (Cold.entryMachine a)
/-- Base's prelude and occurrence loop on its own layout. -/
noncomputable def occM := RecoveryFocus.machine (Cold.old a) (Prelude.occurrences a)
noncomputable def d4M := TapeEmbedding.machine 1 (occM a)
/-- Close the child counts with `false`. -/
noncomputable def d5M := RecoveryFocus.machine ![iC a (pCnt a)] (putM false)

noncomputable def innerM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (d1M a) (d2M a)) (d3M a))
    (d4M a)) (d5M a)

/-- **The decomposition stage**, every head returned to cell `0`. -/
noncomputable def decM := MaskedReset.machine (innerM a) (fun _ => true)

/-! ## The run -/

/-- The gates' native stream with the arity as its top payload. -/
def segOf (n : ℕ) (occ : List (SupportedNormalizedGate n)) : List Bool := segment occ (List.replicate n true)

/-- The inner cost: unframe, move, base's entry, base's occurrences, close. -/
def innerCost (n : ℕ) (occ : List (SupportedNormalizedGate n)) : ℕ :=
  (((2 * (segOf n occ).length + 1) + 1 + 1) + 1 + Cold.entryBudget a (segOf n occ).length) + 1 +
    Prelude.occurrenceBudget a (SourceEnvelope.capacity a (segOf n occ).length) occ (List.replicate n true) + 1 + 1

/-- The stage's cost (masked). -/
def decCost (n : ℕ) (occ : List (SupportedNormalizedGate n)) : ℕ := 2 * innerCost a n occ + 2

theorem arity_le_seg (n : ℕ) (occ : List (SupportedNormalizedGate n)) : n ≤ (segOf n occ).length := by
  simp only [segOf, ExtDecompositionBatch.segment, List.length_append, frame_length', List.length_replicate]
  omega

theorem seg_le_sq (n : ℕ) (occ : List (SupportedNormalizedGate n)) :
    (segOf n occ).length ≤ 1000 * ((segOf n occ).length + 2) ^ 2 := by
  nlinarith

/-- The heads after the unframe and the move: base's entry heads, the stream's cursor past it. -/
theorem heads2 (L : ℕ) :
    Function.update (Function.update (Function.update (fun _ : Fin (DT a) => (0 : ℕ)) (iFS a) (2 * L + 1))
      (iC a (pStr a)) L) (iC a (pDom a)) 1 =
    Fin.addCases (Cold.heads a L) (fun _ : Fin 1 => 2 * L + 1) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    simp only [Function.update_apply, iC, iFS, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, pStr_val, pDom_val,
      Cold.heads]
    have := j.isLt
    have := tapes_eq a
    split_ifs <;> first | rfl | omega
  · rw [Fin.addCases_right]
    have hj : j = 0 := Fin.eq_zero j
    subst hj
    simp only [Function.update_apply, iC, iFS, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, pStr_val, pDom_val]
    have := tapes_eq a
    split_ifs <;> first | rfl | omega

/-- The tapes after the unframe: base's entry data with the stream on its source port. -/
theorem tapes2 (P q : ℕ) (seg : List Bool) :
    Function.update (Function.update (Fin.addCases (motive := fun _ => List Bool) (Cold.data a P q [])
      (fun _ : Fin 1 => frame seg)) (iFS a) (frame seg)) (iC a (pStr a)) seg =
    Fin.addCases (motive := fun _ => List Bool) (Cold.data a P q seg) (fun _ : Fin 1 => frame seg) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    simp only [Function.update_apply, iC, iFS, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, pStr_val]
    have := j.isLt
    have := tapes_eq a
    split_ifs with h1 h2
    · simp [Cold.data, h1]
    · omega
    · rw [Fin.addCases_left]
      simp [Cold.data, h1]
  · rw [Fin.addCases_right]
    have hj : j = 0 := Fin.eq_zero j
    subst hj
    simp only [Function.update_apply, iC, iFS, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, pStr_val]
    have := tapes_eq a
    split_ifs <;> first | rfl | omega

/-- Base's loop tapes at its ports. -/
theorem occ_ports (C q : ℕ) (source c1 c2 c3 : List Bool) (count : ℕ) :
    OccurrenceTemplate.tapes a C q source c1 c2 c3 count (live a (str a)) = source ∧
    OccurrenceTemplate.tapes a C q source c1 c2 c3 count (live a (cnt a)) = c1 ∧
    OccurrenceTemplate.tapes a C q source c1 c2 c3 count (live a (bod a)) = c2 ∧
    OccurrenceTemplate.tapes a C q source c1 c2 c3 count (live a (tot a)) = c3 ∧
    OccurrenceTemplate.tapes a C q source c1 c2 c3 count (live a (dom a)) = UnaryTemplate.tape q ∧
    OccurrenceTemplate.tapes a C q source c1 c2 c3 count (Prelude.driverSlot a) = UnaryTemplate.tape count := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp [OccurrenceTemplate.tapes, live, loopInA, loggedTapes, loopTapes, str, cnt, bod, tot, dom, ex]
  show Fin.addCases (motive := fun _ => List Bool) (loggedTapes a C (loopTapes a C q source c1 c2 c3))
    (fun _ => UnaryTemplate.tape count) (Fin.natAdd (CT a) (0 : Fin 1)) = _
  rw [Fin.addCases_right]

theorem occ_head_cnt (pos : ℕ) (c1 c2 c3 : List Bool) (d : ℕ) :
    OccurrenceTemplate.heads a pos c1 c2 c3 d (live a (cnt a)) = c1.length := by
  simp [OccurrenceTemplate.heads, live, loopInH, loopHeads, cnt, ex]

/-- **The decomposition stage runs** (alg:disjoint for every carrier gate, P3:1602-1641): from the stream framed on
its tape, the domain template `UnaryTemplate.tape n` and `1^{|seg|}` on base's ports (every other tape of base's
layout empty), every head at cell `0`, the stage leaves the gates' children on the body port, the closed counts, the
total and the driver, every head back at cell `0`. -/
theorem dec_run (n : ℕ) (occ : List (SupportedNormalizedGate n)) (cap : ℕ) (hcap : innerCost a n occ ≤ cap) :
    ∃ Af : Fin (DT a) → List Bool, Step (decM a) (decCost a n occ) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        (Fin.addCases (motive := fun _ => List Bool) (Cold.data a (segOf n occ).length n [])
          (fun _ : Fin 1 => frame (segOf n occ))) (fun _ : Fin 1 => List.replicate cap false))
      (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => List.replicate cap false)) ∧
      Af (iFS a) = frame (segOf n occ) ∧ Af (iC a (pStr a)) = segOf n occ ∧
      Af (iC a (pDom a)) = UnaryTemplate.tape n ∧
      Af (iC a (pCnt a)) = (counts a occ).flatMap natWord ++ [false] ∧
      Af (iC a (pBod a)) = (GS a occ).flatMap exactWord ∧
      Af (iC a (pTot a)) = false :: List.replicate (B a occ) true ∧
      Af (iC a (pDrv a)) = UnaryTemplate.tape occ.length := by
  classical
  set seg := segOf n occ with hseg
  set L := seg.length with hL
  set top := List.replicate n true with htop
  have hq : n ≤ L := arity_le_seg n occ
  have hi : (segment occ top).length ≤ 1000 * (L + 2) ^ 2 := seg_le_sq n occ
  have hp : L ≤ SourceEnvelope.capacity a L := SourceEnvelope.source_position a occ top L hi
  obtain ⟨hbody, _, _, _, _, hheader⟩ := SourceEnvelope.actual_capacity a occ top L hq hi
  set C := SourceEnvelope.capacity a L with hC
  have tq := tapes_eq a
  -- the bank of base's entry
  set A0 : Fin (DT a) → List Bool :=
    Fin.addCases (motive := fun _ => List Bool) (Cold.data a L n []) (fun _ : Fin 1 => frame seg) with hA0
  have a0FS : A0 (iFS a) = frame seg := by simp only [A0, iFS, Fin.addCases_right]
  have a0Str : A0 (iC a (pStr a)) = [] := by
    simp only [A0, iC, Fin.addCases_left]; simp [Cold.data, pStr_val]
  have a0Dom : A0 (iC a (pDom a)) = UnaryTemplate.tape n := by
    simp only [A0, iC, Fin.addCases_left]; simp [Cold.data, pDom_val]
  -- 1. unframe
  have u1 := Top.unframeStep0 [] seg []
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at u1
  have s1 := GF2.dockRun u1 ![iFS a, iC a (pStr a)] (two_inj _ _ (fs_ne_str a)) (fun _ => 0) A0
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j; exact a0FS; exact a0Str)
  rw [dockH_two _ _ (fs_ne_str a), install_two _ _ (fs_ne_str a)] at s1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at s1
  set H1 := Function.update (Function.update (fun _ : Fin (DT a) => (0 : ℕ)) (iFS a) (2 * L + 1)) (iC a (pStr a)) L
  set A1 := Function.update (Function.update A0 (iFS a) (frame seg)) (iC a (pStr a)) seg
  -- 2. the domain cursor
  have h1Dom : H1 (iC a (pDom a)) = 0 := by
    simp only [H1, Function.update_apply, iC, iFS, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, pStr_val, pDom_val]
    split_ifs <;> first | rfl | omega
  have a1Dom : A1 (iC a (pDom a)) = UnaryTemplate.tape n := by
    simp only [A1, Function.update_apply, iC, iFS, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, pStr_val, pDom_val]
    split_ifs <;> first | omega | exact a0Dom
  have s2 := GF2.dockRun (moveStep (UnaryTemplate.tape n) 0) ![iC a (pDom a)] (fun j k _ => Subsingleton.elim j k)
    H1 A1 (by intro j; fin_cases j; exact h1Dom) (by intro j; fin_cases j; exact a1Dom)
  rw [dockH_one, install_one] at s2
  simp only [Matrix.cons_val_zero] at s2
  rw [← a1Dom, Function.update_eq_self] at s2
  have eH2 := heads2 a L
  have eA2 : A1 = Fin.addCases (motive := fun _ => List Bool) (Cold.data a L n seg) (fun _ : Fin 1 => frame seg) :=
    tapes2 a L n seg
  rw [eH2, eA2] at s2
  rw [eA2] at s1
  -- 3. base's entry
  obtain ⟨O, e3, hO⟩ := Cold.entry_run a L n L seg hp
  have s3 := e3.embed (fun _ : Fin 1 => 2 * L + 1) (fun _ : Fin 1 => frame seg)
  -- 4. base's occurrences
  have e4 := Prelude.occurrences_run a C n occ top hheader hbody
  have e4' := e4.dock (Cold.old a) (Cold.old_injective a) (Cold.heads a 0) O (Cold.entry_heads a) (fun j => hO j)
  have s4 := e4'.embed (fun _ : Fin 1 => 2 * L + 1) (fun _ : Fin 1 => frame seg)
  set c1 := (counts a occ).flatMap natWord
  set c2 := (GS a occ).flatMap exactWord
  set c3 := false :: List.replicate (B a occ) true
  set outH := OccurrenceTemplate.heads a (segment occ top).length c1 c2 c3 1
  set outT := OccurrenceTemplate.tapes a C n (segment occ top) c1 c2 c3 occ.length
  have hports := occ_ports a C n (segment occ top) c1 c2 c3 occ.length
  -- 5. close the counts
  set H4 := Fin.addCases (motive := fun _ => ℕ) (dockH (Cold.old a) (Cold.heads a 0) outH) (fun _ : Fin 1 => 2 * L + 1)
  set A4 := Fin.addCases (motive := fun _ => List Bool) (install (Cold.old a) O outT) (fun _ : Fin 1 => frame seg)
  have h4Cnt : H4 (iC a (pCnt a)) = c1.length := by
    simp only [H4, iC, Fin.addCases_left, pCnt, Cold.port]
    rw [dockH_slot _ (Cold.old_injective a)]
    exact occ_head_cnt a _ c1 c2 c3 1
  have a4Cnt : A4 (iC a (pCnt a)) = c1 := by
    simp only [A4, iC, Fin.addCases_left, pCnt, Cold.port]
    rw [install_slot _ (Cold.old_injective a)]
    exact hports.2.1
  have s5 := GF2.dockRun (putStep false c1 c1.length) ![iC a (pCnt a)] (fun j k _ => Subsingleton.elim j k)
    H4 A4 (by intro j; fin_cases j; exact h4Cnt) (by intro j; fin_cases j; exact a4Cnt)
  rw [dockH_one, install_one] at s5
  simp only [Matrix.cons_val_zero] at s5
  rw [write_end] at s5
  have all := ((((s1.seq s2).seq s3).seq s4).seq s5)
  have m := all.mask (fun _ => true) (by intro i _; rfl) (cap := cap) (by unfold innerCost at hcap; exact hcap)
  refine ⟨Function.update A4 (iC a (pCnt a)) (c1 ++ [false]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (m.congr_in addCases_zero' rfl).congr (mask_zero _) rfl
  · rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h
      simp [iFS, iC, pCnt_val] at this; omega)]
    simp only [A4, iFS, Fin.addCases_right]
  · rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h
      simp [iC, pCnt_val, pStr_val] at this)]
    simp only [A4, iC, Fin.addCases_left, pStr, Cold.port]
    rw [install_slot _ (Cold.old_injective a)]
    exact hports.1
  · rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h
      simp [iC, pCnt_val, pDom_val] at this)]
    simp only [A4, iC, Fin.addCases_left, pDom, Cold.port]
    rw [install_slot _ (Cold.old_injective a)]
    exact hports.2.2.2.2.1
  · rw [Function.update_self]
  · rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h
      simp [iC, pCnt_val, pBod_val] at this)]
    simp only [A4, iC, Fin.addCases_left, pBod, Cold.port]
    rw [install_slot _ (Cold.old_injective a)]
    exact hports.2.2.1
  · rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h
      simp [iC, pCnt_val, pTot_val] at this)]
    simp only [A4, iC, Fin.addCases_left, pTot, Cold.port]
    rw [install_slot _ (Cold.old_injective a)]
    exact hports.2.2.2.1
  · rw [Function.update_of_ne (by
      intro h; have := congrArg Fin.val h
      simp [iC, pCnt_val, pDrv_val] at this)]
    simp only [A4, iC, Fin.addCases_left, pDrv]
    rw [install_slot _ (Cold.old_injective a)]
    exact hports.2.2.2.2.2

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Dec
