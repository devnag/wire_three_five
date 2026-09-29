import Proof.Wire_3_5.Compiler.MachineC3aTop

/-! # C3a′'s machine runs: from the input record to the pool and its children table (P3:1596-1664)

Paper: alg:disjoint (P3:1602-1615) for every carrier gate, then alg:pullback over every flip pattern (P3:1636-1664):
"Decompose an original-coordinate threshold using Lemma alg:disjoint, and then substitute these coordinate
functions". **`top_run`**: on every admissible request of C3a′ (`R.Pre`, `CoefFit`, `1 ≤ n`, `1 ≤ h`), the machine
`c3aM` runs in `c3aCost` steps from the padded entry bank (the framed input on tape 0, the logs blank at `c3aCapL`,
every other tape empty) to a bank with every head at cell `0` whose output tape (tape 70) is exactly C3a's encoding of
the reference: the pool stream, `false`, the children table. The stages are those of `Lay` in order; between them
every head is at cell `0` and the bank is tracked pointwise (`inst`). The paper quantity is the contract's output word.
Main declarations: the stage steps (`uw_step`, `len_step`, `cell_step`), `nLeft_eq`, `nRight_eq`, `L0`,
**`top_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Run
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Lay
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## Base's stages in the zero-head form -/

theorem uw_step (n : ℕ) :
    Step (UWalkUnary.machine false false) (2 * n + 6) (fun _ => 0) ![CompareMachine.word n, [], []] (fun _ => 0)
      ![CompareMachine.word n, List.replicate n true, List.replicate (n + 2) false] := by
  have h := CloseoutFinalSelector.step_of_clock (UWalkUnary.ready false false 0 n)
  refine (h.congr_in rfl ?_).congr rfl ?_
  · funext i; fin_cases i <;> simp [UWalkUnary.input, UWalkUnary.source, ZeroPadding.pad_zero]
  · funext i; fin_cases i <;> simp [UWalkUnary.result, UWalkUnary.source, UWalkUnary.output, UWalkUnary.lead,
      ZeroPadding.pad_zero]

theorem len_step (bits : List Bool) :
    Step ClockNumericPrep.ellMachine (4 * bits.length + 5) (fun _ => 0) ![frame bits, []] (fun _ => 0)
      ![frame bits, CompareMachine.word bits.length] :=
  CloseoutFinalSelector.step_of_clock (HierarchyAllocation.length_ready bits)

theorem cell_step : Step (cellM true) 1 (fun _ => 0) ![[false]] (fun _ => 0) ![[true]] := by
  refine ((cellStep true false).congr_in ?_ rfl).congr ?_ rfl <;> (funext i; fin_cases i; rfl)

/-! ## The request's facts -/

theorem ofFn_getD (side : List Bool) (n : ℕ) (hs : side.length = n) :
    List.ofFn (fun i : Fin n => side.getD i false) = side := by
  subst hs
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem nLeft_eq (side : List Bool) (n : ℕ) (hs : side.length = n) : nLeft side n = (side.filter id).length := by
  unfold nLeft; rw [ofFn_getD side n hs]

theorem nRight_eq (side : List Bool) (n : ℕ) (hs : side.length = n) :
    nRight side n = (side.filter (fun b => !b)).length := by
  unfold nRight; rw [ofFn_getD side n hs]

theorem nbl_le_of_lt (x h : ℕ) (h1 : 1 ≤ h) (hx : x < 2 ^ h) : natBitLength x ≤ h := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · subst hx0; simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) hx
    omega

theorem nbl_le_succ (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 x
  omega

theorem mem_le_sum {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := List.le_sum_of_mem hx

/-! ## The decomposition stage's ports -/

variable (a : DecompositionAlgorithm)

theorem pD_val (i : Fin 9) : (pD a i).val =
    ![Cold.tapes a, SB a, SB a + 10, SB a + 14, SB a + 1, SB a + 2, SB a + 3, SB a + 13, Cold.tapes a + 1] i := by
  fin_cases i <;> simp [pD, C3a.Dec.iFS, C3a.Dec.iC, C3a.Dec.pStr_val, C3a.Dec.pDom_val, C3a.Dec.pP_val,
    C3a.Dec.pCnt_val, C3a.Dec.pBod_val, C3a.Dec.pTot_val, C3a.Dec.pDrv_val]

theorem pD_inj : Function.Injective (pD a) := by
  have t := C3a.Dec.tapes_eq a
  intro i j h
  have hv := congrArg Fin.val h
  rw [pD_val, pD_val] at hv
  have hp : 14 ≤ Cold.Power a := by
    unfold Cold.Power RepairSource.ProjectionNormalization.DimensionPolynomial.tapes; omega
  generalize SB a = s at hv t
  generalize Cold.Power a = p at t hp
  generalize Cold.tapes a = T at hv t
  revert hv
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem qD_inj : Function.Injective qD := by decide

/-- The decomposition stage's entry: base's data with the stream framed and the log blank. -/
def decIn (P q : ℕ) (seg : List Bool) (cap : ℕ) : Fin (MR a) → List Bool :=
  Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (Cold.data a P q []) (fun _ : Fin 1 => frame seg))
    (fun _ : Fin 1 => List.replicate cap false)

theorem data_eval (P q : ℕ) (src : List Bool) (i : Fin (Cold.tapes a)) :
    Cold.data a P q src i = if i.val = SB a then src else if i.val = SB a + 10 then UnaryTemplate.tape q
      else if i.val = SB a + 14 then List.replicate P true else [] := by
  unfold Cold.data; rfl

theorem decIn_ports (P q : ℕ) (seg : List Bool) (cap : ℕ) :
    (fun i => decIn a P q seg cap (pD a i)) =
      ![frame seg, [], UnaryTemplate.tape q, List.replicate P true, [], [], [], [], List.replicate cap false] := by
  funext i
  fin_cases i
  · show decIn a P q seg cap ((C3a.Dec.iFS a).castAdd 1) = frame seg
    simp only [decIn, C3a.Dec.iFS, Fin.addCases_left, Fin.addCases_right]
  · show decIn a P q seg cap ((C3a.Dec.iC a (C3a.Dec.pStr a)).castAdd 1) = []
    simp only [decIn, C3a.Dec.iC, Fin.addCases_left]
    rw [data_eval, if_pos (C3a.Dec.pStr_val a)]
  · show decIn a P q seg cap ((C3a.Dec.iC a (C3a.Dec.pDom a)).castAdd 1) = UnaryTemplate.tape q
    simp only [decIn, C3a.Dec.iC, Fin.addCases_left]
    rw [data_eval, C3a.Dec.pDom_val, if_neg (by omega), if_pos rfl]
  · show decIn a P q seg cap ((C3a.Dec.iC a (C3a.Dec.pP a)).castAdd 1) = List.replicate P true
    simp only [decIn, C3a.Dec.iC, Fin.addCases_left]
    rw [data_eval, C3a.Dec.pP_val, if_neg (by omega), if_neg (by omega), if_pos rfl]
  · show decIn a P q seg cap ((C3a.Dec.iC a (C3a.Dec.pCnt a)).castAdd 1) = []
    simp only [decIn, C3a.Dec.iC, Fin.addCases_left]
    rw [data_eval, C3a.Dec.pCnt_val, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · show decIn a P q seg cap ((C3a.Dec.iC a (C3a.Dec.pBod a)).castAdd 1) = []
    simp only [decIn, C3a.Dec.iC, Fin.addCases_left]
    rw [data_eval, C3a.Dec.pBod_val, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · show decIn a P q seg cap ((C3a.Dec.iC a (C3a.Dec.pTot a)).castAdd 1) = []
    simp only [decIn, C3a.Dec.iC, Fin.addCases_left]
    rw [data_eval, C3a.Dec.pTot_val, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · show decIn a P q seg cap ((C3a.Dec.iC a (C3a.Dec.pDrv a)).castAdd 1) = []
    simp only [decIn, C3a.Dec.iC, Fin.addCases_left]
    rw [data_eval, C3a.Dec.pDrv_val, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · show decIn a P q seg cap (Fin.natAdd (C3a.Dec.DT a) (0 : Fin 1)) = List.replicate cap false
    simp only [decIn, Fin.addCases_right]

theorem decIn_other (P q : ℕ) (seg : List Bool) (cap : ℕ) (j : Fin (MR a)) (hj : ¬ ∃ i, pD a i = j) :
    decIn a P q seg cap j = [] := by
  have t := C3a.Dec.tapes_eq a
  have hB : Cold.Base a = SB a + 14 := rfl
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j hj
  · intro hj
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j' hj
    · intro hi
      simp only [decIn, Fin.addCases_left]
      unfold Cold.data
      split_ifs with h1 h2 h3
      · exact absurd ⟨1, Fin.ext (by simp [pD, C3a.Dec.iC, C3a.Dec.pStr_val]; omega)⟩ hi
      · exact absurd ⟨2, Fin.ext (by simp [pD, C3a.Dec.iC, C3a.Dec.pDom_val]; omega)⟩ hi
      · exact absurd ⟨3, Fin.ext (by simp [pD, C3a.Dec.iC, C3a.Dec.pP_val]; omega)⟩ hi
      · rfl
    · intro hi
      exact absurd ⟨0, Fin.ext (by simp [pD, C3a.Dec.iFS])⟩ hi
  · intro hj
    exact absurd ⟨8, Fin.ext (by simp [pD])⟩ hj

/-! ## Chaining the stages -/

theorem addCases_zero2 {t u : ℕ} :
    Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin t => 0) (fun _ : Fin u => 0) = fun _ => 0 := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- **One more stage on the left part**. -/
theorem thenZL {s0 s k c1 c2 : ℕ} {M : Machine (U a) s0} {A0 : Fin (U a) → List Bool}
    {L : Fin 81 → List Bool} {R : Fin (MR a) → List Bool} {p : Machine k s} {tin tout : Fin k → List Bool}
    (h1 : Step M c1 (fun _ => 0) A0 (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) L R))
    (h2 : Step p c2 (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin k → Fin 81) (hs : Function.Injective sl)
    (hL : ∀ j, L (sl j) = tin j) :
    Step (Composition.machine M (RecoveryFocus.machine (sh a sl) p)) (c1 + 1 + c2) (fun _ => 0) A0 (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) (inst sl L tout) R) :=
  h1.seq (dockZL' h2 sl hs L R hL)

/-- **A unary subtraction stage** (base's `sub_run`), its junk scratch left existential. -/
theorem thenSub {s0 c1 : ℕ} {M : Machine (U a) s0} {A0 : Fin (U a) → List Bool}
    {L : Fin 81 → List Bool} {R : Fin (MR a) → List Bool}
    (h1 : Step M c1 (fun _ => 0) A0 (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) L R))
    (sl : Fin 9 → Fin 81) (hs : Function.Injective sl) (x y S C : ℕ) (hy : y ≤ x) (hS : x + 2 ≤ S)
    (hC : 2 * x + 5 ≤ C) (h0 : L (sl 0) = List.replicate x true) (h1' : L (sl 1) = List.replicate y true)
    (hscr : ∀ j : Fin 9, 2 ≤ j.val → j.val < 8 → L (sl j) = List.replicate S false)
    (h8 : L (sl 8) = List.replicate C false) :
    ∃ X : Fin 9 → List Bool, Step (Composition.machine M (RecoveryFocus.machine (sh a sl) SourceRequest.CurComp.subLocal))
      (c1 + 1 + SourceRequest.CurComp.subCost x) (fun _ => 0) A0 (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        (inst sl L ![L (sl 0), L (sl 1), ZeroPadding.pad S (List.replicate (x - y) true), X 3, X 4, X 5, X 6, X 7, L (sl 8)])
        R) := by
  obtain ⟨E', st, e2, ekeep, _⟩ := SourceRequest.CurComp.sub_run x y 0 0 S C (fun j => L (sl j)) hy hS hC
    (by rw [ZeroPadding.pad_zero]; exact h0) (by rw [ZeroPadding.pad_zero]; exact h1') hscr h8
  have hE : E' = ![L (sl 0), L (sl 1), ZeroPadding.pad S (List.replicate (x - y) true), E' 3, E' 4, E' 5, E' 6, E' 7,
      L (sl 8)] := by
    funext j
    fin_cases j
    · exact ekeep 0 (by decide)
    · exact ekeep 1 (by decide)
    · exact e2
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ekeep 8 (by decide)
  refine ⟨E', ?_⟩
  have d := dockZL' st sl hs L R (fun _ => rfl)
  rw [hE] at d
  exact h1.seq d

/-- The decomposition stage's ports read off its exit bank (stated for abstract values: the kernel then checks one
small term). -/
theorem ports_vec (Af : Fin (C3a.Dec.DT a) → List Bool) (x0 x1 x2 x4 x5 x6 x7 x8 : List Bool)
    (f0 : Af (C3a.Dec.iFS a) = x0) (f1 : Af (C3a.Dec.iC a (C3a.Dec.pStr a)) = x1)
    (f2 : Af (C3a.Dec.iC a (C3a.Dec.pDom a)) = x2) (f3 : Af (C3a.Dec.iC a (C3a.Dec.pCnt a)) = x4)
    (f4 : Af (C3a.Dec.iC a (C3a.Dec.pBod a)) = x5) (f5 : Af (C3a.Dec.iC a (C3a.Dec.pTot a)) = x6)
    (f6 : Af (C3a.Dec.iC a (C3a.Dec.pDrv a)) = x7) :
    (fun i => Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => x8) (pD a i)) =
      ![x0, x1, x2, Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => x8) (pD a 3), x4, x5, x6, x7, x8] := by
  funext i
  fin_cases i
  · show Fin.addCases (motive := fun _ => List Bool) Af _ ((C3a.Dec.iFS a).castAdd 1) = _
    rw [Fin.addCases_left]; exact f0
  · show Fin.addCases (motive := fun _ => List Bool) Af _ ((C3a.Dec.iC a (C3a.Dec.pStr a)).castAdd 1) = _
    rw [Fin.addCases_left]; exact f1
  · show Fin.addCases (motive := fun _ => List Bool) Af _ ((C3a.Dec.iC a (C3a.Dec.pDom a)).castAdd 1) = _
    rw [Fin.addCases_left]; exact f2
  · rfl
  · show Fin.addCases (motive := fun _ => List Bool) Af _ ((C3a.Dec.iC a (C3a.Dec.pCnt a)).castAdd 1) = _
    rw [Fin.addCases_left]; exact f3
  · show Fin.addCases (motive := fun _ => List Bool) Af _ ((C3a.Dec.iC a (C3a.Dec.pBod a)).castAdd 1) = _
    rw [Fin.addCases_left]; exact f4
  · show Fin.addCases (motive := fun _ => List Bool) Af _ ((C3a.Dec.iC a (C3a.Dec.pTot a)).castAdd 1) = _
    rw [Fin.addCases_left]; exact f5
  · show Fin.addCases (motive := fun _ => List Bool) Af _ ((C3a.Dec.iC a (C3a.Dec.pDrv a)).castAdd 1) = _
    rw [Fin.addCases_left]; exact f6
  · show Fin.addCases (motive := fun _ => List Bool) Af _ (Fin.natAdd (C3a.Dec.DT a) (0 : Fin 1)) = _
    rw [Fin.addCases_right]; rfl

/-- The decomposition stage's run at the request, on its entry `decIn` (the stage log's capacity `capS`). -/
theorem dec_at (R : PoolReq) (capS : ℕ) (hcap : C3a.Dec.innerCost a R.n R.gates ≤ capS) :
    ∃ Af : Fin (C3a.Dec.DT a) → List Bool,
    Step (C3a.Dec.decM a) (C3a.Dec.decCost a R.n R.gates) (fun _ => 0)
      (decIn a (segR R).length R.n (segR R) capS) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => List.replicate capS false)) ∧
    (fun i => Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => List.replicate capS false)
      (pD a i)) = ![frame (segR R), segR R, UnaryTemplate.tape R.n,
        Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => List.replicate capS false) (pD a 3),
        (counts a R.gates).flatMap natWord ++ [false], (GS a R.gates).flatMap exactWord,
        false :: List.replicate (B a R.gates) true, UnaryTemplate.tape R.gates.length,
        List.replicate capS false] := by
  obtain ⟨Af, st, f0, f1, f2, f3, f4, f5, f6⟩ := C3a.Dec.dec_run a R.n R.gates capS hcap
  exact ⟨Af, st, ports_vec a Af _ _ _ _ _ _ _ _ f0 f1 f2 f3 f4 f5 f6⟩

theorem heads_ports : Fin.addCases (motive := fun _ => ℕ) (dockH qD (fun _ => 0) (fun i => (fun _ => 0) (pD a i)))
    (fun j => if ∃ i, pD a i = j then (fun _ : Fin (MR a) => 0) j else (fun _ => 0) j) = fun _ => 0 := by
  rw [dockH_existing qD (fun _ => 0) _ (fun _ => rfl)]
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- **The decomposition stage, docked** with its ports on the left part. -/
theorem decDocked (R : PoolReq) (capS : ℕ) (hcap : C3a.Dec.innerCost a R.n R.gates ≤ capS) (L : Fin 81 → List Bool)
    (hA : ∀ i, L (qD i) = decIn a (segR R).length R.n (segR R) capS (pD a i)) :
    ∃ (X : List Bool) (RD : Fin (MR a) → List Bool), Step (m4 a) (cst4 a R) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) L (fun _ : Fin (MR a) => [])) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        (inst qD L ![frame (segR R), segR R, UnaryTemplate.tape R.n, X, (counts a R.gates).flatMap natWord ++ [false],
          (GS a R.gates).flatMap exactWord, false :: List.replicate (B a R.gates) true,
          UnaryTemplate.tape R.gates.length, List.replicate capS false]) RD) := by
  obtain ⟨Af, st, hv⟩ := dec_at a R capS hcap
  have d := dockRun_ports st (pD a) qD (pD_inj a) qD_inj (fun _ => 0) L (fun _ => 0) (fun _ => [])
    (fun _ => rfl) hA (fun _ _ => rfl) (fun j hj => (decIn_other a _ _ _ _ j hj).symm)
  rw [hv, install_eq_inst qD qD_inj, heads_ports, addCases_zero2] at d
  exact ⟨_, _, d⟩

/-! ## The pool stage at the request -/

/-- The pool stage's entry bank at the request (MC6's entry with empty output and table, the atom count, the logs at
the capacities `cap … cap0`). -/
def poIn (R : PoolReq) (cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP cap0 : ℕ) : Fin (40 + 1) → List Bool :=
  Fin.addCases (motive := fun _ => List Bool) (Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool)
      (rA (rtPool ((GS a R.gates).flatMap exactWord ++ []) (false :: List.replicate (capKR a R) true) []
        (frame (binary R.h 0)) [] (List.replicate cap false) (List.replicate R.n true)
        (List.replicate capN2 false) (List.replicate (GS a R.gates).length true) (frame R.side ++ [])
        [] [] [] [] [] [] [] [] (List.replicate capC2 false)
        (streamTape (zeroRecs R.h (R.width - nLeft R.side R.n)) [])
        (streamTape (zeroRecs R.h (R.width - nRight R.side R.n)) []) [] (List.replicate capC3 false)
        (List.replicate capC4 false) (streamTape R.flips []) ((counts a R.gates).flatMap natWord ++ false :: [])
        (frame (binary (WcR a R) 0)) (frame (binary (WcR a R) 0)) (frame (binary (WcR a R) 0)) [false] [true]
        (frame (entC R.Q (R.flips.length * (counts a R.gates).sum) 0))
        (frame (shiftMask R.Q (R.flips.length * (counts a R.gates).sum)))
        (frame (entC R.Q (R.flips.length * (counts a R.gates).sum) 0)) [] (List.replicate cap5 false)
        (List.replicate capN7 false) (List.replicate capF8 false)))
      (fun _ : Fin 1 => List.replicate capP false))
    (fun _ : Fin 1 => List.replicate (R.flips.length * R.gates.length) true))
    (fun _ : Fin 1 => List.replicate cap0 false)

/-- The pool builder's conversions, summed (every child coefficient's conversion cost). -/
def convSum (R : PoolReq) : ℕ :=
  ((GS a R.gates).flatMap fun e => (List.ofFn e.weight ++ [e.target]).map fun z => convCost z.natAbs).sum

/-- **The pool stage at the request** (P3:1636-1664): the output word is C3a's encoding. -/
theorem po_at (R : PoolReq) (hR : R.Pre) (hfit : CoefFit a R) (hn : 1 ≤ R.n) (hh : 1 ≤ R.h)
    (cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP cap0 : ℕ)
    (hc1 : 2 * R.h + 1 ≤ cap) (hcF : 2 * R.n + 1 ≤ cap)
    (hcT1 : 2 * (R.Q + R.flips.length * (counts a R.gates).sum + 1) + 1 ≤ cap) (hcT2 : 2 * WcR a R + 2 ≤ cap)
    (hcT3 : 3 * WcR a R + 2 ≤ cap) (hconv : convSum a R ≤ cap)
    (hcN2 : capN2R R ≤ capN2) (hcN7 : capN7R a R ≤ capN7) (hcC2 : capC2R R ≤ capC2) (hcC3 : capC3R R ≤ capC3)
    (hcC4 : capC4R a R ≤ capC4) (hcF8 : capF8R a R ≤ capF8) (hc5 : cap5R a R ≤ cap5) (hcP : pcR a R ≤ capP)
    (hc0 : poInR a R ≤ cap0) :
    ∃ Af : Fin 40 → List Bool, Step C3a.PO.poM (cst23 a R) (fun _ => 0)
      (poIn a R cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP cap0) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) Af (fun _ : Fin 1 => List.replicate cap0 false)) ∧
      Af 21 = (poolRecs a R.h R.gates R.side R.width R.flips).flatMap frame ++
        false :: (childTable R.Q (shapeOf (densePool a R.gates R.side R.width R.flips))).flatMap atomStream := by
  obtain ⟨hs, hfl, hL, hR'⟩ := hR
  have hB : BR a R = (counts a R.gates).sum := B_eq_sum a R.gates
  have hok : ∀ e ∈ GS a R.gates, ∀ z ∈ List.ofFn e.weight ++ [e.target], CoefOk R.h (capKR a R) cap z := by
    intro e he z hz
    obtain ⟨g, hg, heg⟩ := List.mem_flatMap.mp he
    have hlt := hfit g hg e heg z hz
    refine ⟨hlt, (nbl_le_of_lt _ _ hh hlt).trans (by unfold capKR; omega), ?_⟩
    have hm := mem_le_sum (List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨z, hz, rfl⟩⟩ :
      convCost z.natAbs ∈ (GS a R.gates).flatMap fun e => (List.ofFn e.weight ++ [e.target]).map fun z => convCost z.natAbs)
    unfold convSum at hconv; omega
  have hcs : ∀ v ∈ counts a R.gates, v < 2 ^ WcR a R ∧ v ≤ BR a R ∧ natBitLength v ≤ capKR a R := by
    intro v hv
    have hvB : v ≤ BR a R := by rw [hB]; exact mem_le_sum hv
    have h2 : BR a R < 2 ^ BR a R := Nat.lt_two_pow_self
    have h3 : 2 ^ BR a R ≤ 2 ^ WcR a R := Nat.pow_le_pow_right (by norm_num) (by unfold WcR; omega)
    refine ⟨by omega, hvB, (nbl_le_succ v).trans (by unfold capKR; omega)⟩
  obtain ⟨Af, st, hf⟩ := C3a.PO.po_run a R.h R.Q (WcR a R) (BR a R) hh (by unfold WcR; omega) hn R.gates R.side R.width
    R.flips hs hfl hL hR' [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] 0 (capKR a R) cap capN2
    capN7 capC2 capC3 capC4 capF8 cap5 capP cap0 hok hcs hc1 hcF hcT1 hcT2 hcT3 hcN2 hcN7 hcC2 hcC3 hcC4 hcF8 hc5 hcP hc0
  exact ⟨Af, st, hf⟩

/-- The decomposition stage's entry read off the left part (abstract bank). -/
theorem hA_of (R : PoolReq) (capS : ℕ) (L : Fin 81 → List Bool) (h3 : L 3 = frame (segR R)) (h19 : L 19 = [])
    (h14 : L 14 = UnaryTemplate.tape R.n) (h17 : L 17 = List.replicate (segR R).length true) (h20 : L 20 = [])
    (h21 : L 21 = []) (h22 : L 22 = []) (h23 : L 23 = []) (h13 : L 13 = List.replicate capS false) :
    ∀ i, L (qD i) = decIn a (segR R).length R.n (segR R) capS (pD a i) := by
  have hv : (fun i => L (qD i)) = ![frame (segR R), [], UnaryTemplate.tape R.n, List.replicate (segR R).length true,
      [], [], [], [], List.replicate capS false] := by
    funext i
    fin_cases i
    · exact h3
    · exact h19
    · exact h14
    · exact h17
    · exact h20
    · exact h21
    · exact h22
    · exact h23
    · exact h13
  rw [← decIn_ports a (segR R).length R.n (segR R) capS] at hv
  exact congrFun hv

/-- **The decomposition stage after a prefix**. -/
theorem thenD' (R : PoolReq) (capS : ℕ) (hcap : C3a.Dec.innerCost a R.n R.gates ≤ capS) {s0 c1 : ℕ}
    {M : Machine (U a) s0} {A0 : Fin (U a) → List Bool} {L : Fin 81 → List Bool}
    (h1 : Step M c1 (fun _ => 0) A0 (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) L (fun _ : Fin (MR a) => [])))
    (hA : ∀ i, L (qD i) = decIn a (segR R).length R.n (segR R) capS (pD a i)) :
    ∃ (X : List Bool) (RD : Fin (MR a) → List Bool), Step (Composition.machine M (m4 a)) (c1 + 1 + cst4 a R)
      (fun _ => 0) A0 (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool)
        (inst qD L ![frame (segR R), segR R, UnaryTemplate.tape R.n, X, (counts a R.gates).flatMap natWord ++ [false],
          (GS a R.gates).flatMap exactWord, false :: List.replicate (B a R.gates) true,
          UnaryTemplate.tape R.gates.length, List.replicate capS false]) RD) := by
  obtain ⟨X, RD, d⟩ := decDocked a R capS hcap L hA
  exact ⟨X, RD, h1.seq d⟩

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Run
