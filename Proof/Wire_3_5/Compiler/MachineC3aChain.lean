import Proof.Wire_3_5.Compiler.MachineC3aRun

/-! # C3a′'s machine runs end to end (P3:1596-1664)

Paper: alg:disjoint for every carrier gate (P3:1602-1615), then alg:pullback over every flip pattern (P3:1636-1664).
**`top_run`**: on every admissible request of C3a′ (`R.Pre`, `CoefFit`, `1 ≤ n`, `1 ≤ h`), the machine `c3aM` runs in
`c3aCost` steps from the padded entry bank (`L0`: the framed input on tape 0, the logs blank at `c3aCapL`, every other
tape empty) to a bank with every head at cell `0` whose output tape (tape 70) is exactly C3a's encoding of the
reference: the pool stream, `false`, the children table. The paper quantity is the contract's output word. Main
declarations: `L0`, the stage capacities, `w2_word`, `w4_word`, **`top_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Chain
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Kit NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Lay
open NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Run
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (a : DecompositionAlgorithm)



/-- The padded entry bank of the left part at a capacity table: the framed input on tape 0, the logs blank. -/
def L0v (R : PoolReq) (cv : Fin 81 → ℕ) : Fin 81 → List Bool :=
  fun j => if j = 0 then frame (C3a.c3aInput R) else List.replicate (cv j) false

/-! ## The frame words the writers produce -/

theorem w2_word (B : ℕ) : [] ++ (List.replicate B [true, false]).flatten ++ [true, false, false] =
    frame (binary (B + 1) 0) := by
  rw [NearCubicWires.WireExponent3_5.GF2.binary_zero, Top.frame_pairs, List.map_replicate, List.replicate_succ',
    List.flatten_append]
  simp

theorem w4_word (Q W : ℕ) : [] ++ (List.replicate Q [true, false]).flatten ++ [true, false] ++
    (List.replicate W [true, true]).flatten ++ [false] = frame (shiftMask Q W) := by
  rw [shiftMask, Top.frame_pairs, List.map_append, List.map_replicate, List.map_replicate, List.replicate_succ']
  simp

/-! ## The machine and cost prefixes -/

/-- The first ten stages. -/
noncomputable def pre9 := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (m0 a) (m1 a))
  (m2 a)) (m3 a)) (m4 a)) (m5 a)) (m6 a)) (m7 a)) (m8 a)) (m9 a)

/-- Their cost. -/
def cost9 (R : PoolReq) : ℕ :=
  cst0 R + 1 + cst1 R + 1 + cst2 R + 1 + cst3 R + 1 + cst4 a R + 1 + cst5 a R + 1 + cst6 R + 1 + cst7 a R + 1 +
    cst8 R + 1 + cst9 R


/-- The bank's values at the indices the later stages read (FactsA). -/
def FactsA (R : PoolReq) (capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP : ℕ) (L : Fin 81 → List Bool) : Prop :=
    L 2 = List.replicate R.n true ∧
    L 4 = frame R.side ∧
    L 5 = List.replicate R.width true ∧
    L 6 = Kit.streamTape R.flips [] ∧
    L 7 = List.replicate R.h true ∧
    L 8 = List.replicate R.Q true ∧
    L 13 = List.replicate capS false ∧
    L 20 = (counts a R.gates).flatMap natWord ++ [false] ∧
    L 21 = (GS a R.gates).flatMap exactWord ∧
    L 24 = List.replicate (BR a R) true ∧
    L 27 = List.replicate (FR R * BR a R) true ∧
    L 29 = List.replicate (FR R * GR R) true ∧
    L 31 = List.replicate (R.side.filter id).length true ∧
    L 32 = List.replicate (R.side.filter (fun b => !b)).length true ∧
    L 33 = List.replicate S false ∧
    L 34 = List.replicate S false ∧
    L 35 = List.replicate S false ∧
    L 36 = List.replicate S false ∧
    L 37 = List.replicate S false ∧
    L 38 = List.replicate S false ∧
    L 39 = List.replicate Cs false ∧
    L 40 = List.replicate S false ∧
    L 41 = List.replicate S false ∧
    L 42 = List.replicate S false ∧
    L 43 = List.replicate S false ∧
    L 44 = List.replicate S false ∧
    L 45 = List.replicate S false ∧
    L 46 = List.replicate Cs false ∧
    L 47 = [] ∧
    L 48 = [] ∧
    L 49 = [] ∧
    L 50 = [] ∧
    L 51 = [] ∧
    L 52 = [false] ∧
    L 53 = [false] ∧
    L 54 = [] ∧
    L 55 = [] ∧
    L 56 = [] ∧
    L 57 = [] ∧
    L 58 = [] ∧
    L 59 = List.replicate capI false ∧
    L 60 = [] ∧
    L 61 = [] ∧
    L 62 = [] ∧
    L 63 = [] ∧
    L 64 = [] ∧
    L 65 = [] ∧
    L 66 = [] ∧
    L 67 = [] ∧
    L 68 = [] ∧
    L 69 = [] ∧
    L 70 = [] ∧
    L 71 = [] ∧
    L 72 = List.replicate cap false ∧
    L 73 = List.replicate capN2 false ∧
    L 74 = List.replicate capC2 false ∧
    L 75 = List.replicate capC3 false ∧
    L 76 = List.replicate capC4 false ∧
    L 77 = List.replicate cap5 false ∧
    L 78 = List.replicate capN7 false ∧
    L 79 = List.replicate capF8 false ∧
    L 80 = List.replicate capP false


/-- The bank's values at the indices the later stages read (FactsB). -/
def FactsB (R : PoolReq) (capS capI S _Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP : ℕ) (L : Fin 81 → List Bool) : Prop :=
    L 2 = List.replicate R.n true ∧
    L 4 = frame R.side ∧
    L 6 = Kit.streamTape R.flips [] ∧
    L 7 = List.replicate R.h true ∧
    L 8 = List.replicate R.Q true ∧
    L 13 = List.replicate capS false ∧
    L 20 = (counts a R.gates).flatMap natWord ++ [false] ∧
    L 21 = (GS a R.gates).flatMap exactWord ∧
    L 24 = List.replicate (BR a R) true ∧
    L 27 = List.replicate (FR R * BR a R) true ∧
    L 29 = List.replicate (FR R * GR R) true ∧
    L 33 = ZeroPadding.pad S (List.replicate (R.width - nTR R) true) ∧
    L 40 = ZeroPadding.pad S (List.replicate (R.width - nFR R) true) ∧
    L 47 = false :: List.replicate (R.h + BR a R + 1) true ∧
    L 48 = frame (List.replicate R.h false) ∧
    L 49 = frame (binary (WcR a R) 0) ∧
    L 50 = frame (binary (WcR a R) 0) ∧
    L 51 = frame (binary (WcR a R) 0) ∧
    L 52 = [false] ∧
    L 53 = [true] ∧
    L 54 = [] ∧
    L 55 = [] ∧
    L 56 = [] ∧
    L 57 = [] ∧
    L 58 = [] ∧
    L 59 = List.replicate capI false ∧
    L 60 = [] ∧
    L 61 = [] ∧
    L 62 = [] ∧
    L 63 = [] ∧
    L 64 = [] ∧
    L 65 = [] ∧
    L 66 = [] ∧
    L 67 = [] ∧
    L 68 = [] ∧
    L 69 = [] ∧
    L 70 = [] ∧
    L 71 = [] ∧
    L 72 = List.replicate cap false ∧
    L 73 = List.replicate capN2 false ∧
    L 74 = List.replicate capC2 false ∧
    L 75 = List.replicate capC3 false ∧
    L 76 = List.replicate capC4 false ∧
    L 77 = List.replicate cap5 false ∧
    L 78 = List.replicate capN7 false ∧
    L 79 = List.replicate capF8 false ∧
    L 80 = List.replicate capP false


/-- **Stages 0–9**: the load, the decomposition and the unary counts. -/
theorem segA (R : PoolReq) (hR : R.Pre) (hn : 1 ≤ R.n) (capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP : ℕ)
    (hS1 : 2 * (Top.loadRec (List.replicate R.n true) (frame (segR R)) (frame R.side) (List.replicate R.width true)
      (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true) [] [] [] []).length + 1 ≤ capS)
    (hS2 : Top.loadChainCost (List.replicate R.n true) (frame (segR R)) (frame R.side) (List.replicate R.width true)
      (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true) [] [] [] [] ≤ capS)
    (hS3 : C3a.Dec.innerCost a R.n R.gates ≤ capS) (hS4 : C3a.Count.nfLoopCost R.flips.length R.n ≤ capS)
    (hS5 : C3a.Count.scLoopCost R.side.length ≤ capS) :
    ∃ (La : Fin 81 → List Bool) (Ra : Fin (MR a) → List Bool),
      Step (pre9 a) (cost9 a R) (fun _ => 0)
        (Fin.addCases (motive := fun _ => List Bool)
          (L0v R (capVec capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP)) (fun _ : Fin (MR a) => []))
        (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) La Ra) ∧ FactsA a R capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP La := by
  have hfl : ∀ f ∈ R.flips, f.length = R.n := hR.2.1
  have r0 := dockZL' (Top.load_run (List.replicate R.n true) (frame (segR R)) (frame R.side)
    (List.replicate R.width true) (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true)
    [] [] [] [] capS hS1 hS2 : Step _ (cst0 R) _ _ _ _) l0 l0_inj
    (L0v R (capVec capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP)) (fun _ : Fin (MR a) => [])
    (by intro j; fin_cases j <;> rfl)
  have r1 := thenZL a r0 (PacketsGlue.RequestMeta.tpl_step R.n : Step _ (cst1 R) _ _ _ _) l1 l1_inj (by intro j; fin_cases j <;> rfl)
  have r2 := thenZL a r1 (len_step (segR R) : Step _ (cst2 R) _ _ _ _) l2 l2_inj (by intro j; fin_cases j <;> rfl)
  have r3 := thenZL a r2 (uw_step (segR R).length : Step _ (cst3 R) _ _ _ _) l3 l3_inj (by intro j; fin_cases j <;> rfl)
  obtain ⟨X4, RD, r4⟩ := thenD' a R capS hS3 r3 (hA_of a R capS _ rfl rfl rfl rfl rfl rfl rfl rfl rfl)
  have r5 := thenZL a r4 (uw_step (BR a R) : Step _ (cst5 a R) _ _ _ _) l5 l5_inj (by intro j; fin_cases j <;> rfl)
  have r6 := thenZL a r5 (C3a.Count.nf_run R.flips R.n hfl hn capS hS4 : Step _ (cst6 R) _ _ _ _) l6 l6_inj (by intro j; fin_cases j <;> rfl)
  have r7 := thenZL a r6 (PCJ6e421fabe2aa4155_SourceLiveCount.product_step (FR R) (BR a R) : Step _ (cst7 a R) _ _ _ _) l7 l7_inj (by intro j; fin_cases j <;> rfl)
  have r8 := thenZL a r7 (PacketsGlue.RequestMeta.prod_step (FR R) (GR R) : Step _ (cst8 R) _ _ _ _) l8 l8_inj (by intro j; fin_cases j <;> rfl)
  have r9 := thenZL a r8 (C3a.Count.sc_run R.side capS hS5 : Step _ (cst9 R) _ _ _ _) l9 l9_inj (by intro j; fin_cases j <;> rfl)
  exact ⟨_, _, r9, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩


/-- **Stages 10–17**: the padding counts, the counter, the zero registers, the cell. -/
theorem segB (R : PoolReq) (hR : R.Pre) (capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP : ℕ)
    (hS6 : C3a.Const.kRawCost R.h (BR a R) ≤ capS) (hS7 : Top.wRunCost R.h ≤ capS)
    (hS8 : Top.w2Cost [true, false] [true, false, false] (BR a R) ≤ capS) (hSw : R.width + 2 ≤ S)
    (hCs : 2 * R.width + 5 ≤ Cs) {s0 c0 : ℕ} {M : Machine (U a) s0} {A0 : Fin (U a) → List Bool} {La : Fin 81 → List Bool}
    {Ra : Fin (MR a) → List Bool}
    (h0 : Step M c0 (fun _ => 0) A0 (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) La Ra))
    (hA : FactsA a R capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP La) :
    ∃ Lb : Fin 81 → List Bool,
      Step (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
        (Composition.machine (Composition.machine (Composition.machine M (m10 a)) (m11 a)) (m12 a)) (m13 a)) (m14 a))
        (m15 a)) (m16 a)) (m17 a))
        (c0 + 1 + cst10 R + 1 + cst11 R + 1 + cst12 a R + 1 + cst13 R + 1 + cst14 a R + 1 + cst15 a R + 1 +
          cst16 a R + 1 + cst17 R) (fun _ => 0) A0 (fun _ => 0)
        (Fin.addCases (motive := fun _ => List Bool) Lb Ra) ∧ FactsB a R capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP Lb := by
  have hLw : nLeft R.side R.n ≤ R.width := hR.2.2.1
  have hRw : nRight R.side R.n ≤ R.width := hR.2.2.2
  have hnL := nLeft_eq R.side R.n hR.1
  have hnR := nRight_eq R.side R.n hR.1
  obtain ⟨f2, f4, f5, f6, f7, f8, f13, f20, f21, f24, f27, f29, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74, f75, f76, f77, f78, f79, f80⟩ := hA
  obtain ⟨X10, r10⟩ := thenSub a h0 l10 l10_inj R.width (nTR R) S Cs (by unfold nTR; omega) hSw hCs f5 f31
    (by intro j h2 h8; fin_cases j
        · simp at h2
        · simp at h2
        · exact f33
        · exact f34
        · exact f35
        · exact f36
        · exact f37
        · exact f38
        · simp at h8) f39
  obtain ⟨X11, r11⟩ := thenSub a r10 l11 l11_inj R.width (nFR R) S Cs (by unfold nFR; omega) hSw hCs f5 f32
    (by intro j h2 h8; fin_cases j
        · simp at h2
        · simp at h2
        · exact f40
        · exact f41
        · exact f42
        · exact f43
        · exact f44
        · exact f45
        · simp at h8) f46
  have r12 := thenZL a r11 (C3a.Const.k_run R.h (BR a R) capS hS6 : Step _ (cst12 a R) _ _ _ _) l12 l12_inj
    (by
      intro j
      fin_cases j
      · exact f7
      · exact f24
      · exact f47
      · exact f13)
  have r13 := thenZL a r12 (Top.wRun_run false R.h capS hS7 : Step _ (cst13 R) _ _ _ _) l13 l13_inj
    (by
      intro j
      fin_cases j
      · rfl
      · exact f48
      · rfl)
  have r14 := thenZL a r13 (Top.w2_run [true, false] [true, false, false] (BR a R) capS hS8 (frame (binary (WcR a R) 0)) (w2_word _) :
      Step _ (cst14 a R) _ _ _ _) l14 l14_inj
    (by
      intro j
      fin_cases j
      · rfl
      · exact f49
      · rfl)
  have r15 := thenZL a r14 (Top.w2_run [true, false] [true, false, false] (BR a R) capS hS8 (frame (binary (WcR a R) 0)) (w2_word _) :
      Step _ (cst15 a R) _ _ _ _) l15 l15_inj
    (by
      intro j
      fin_cases j
      · rfl
      · exact f50
      · rfl)
  have r16 := thenZL a r15 (Top.w2_run [true, false] [true, false, false] (BR a R) capS hS8 (frame (binary (WcR a R) 0)) (w2_word _) :
      Step _ (cst16 a R) _ _ _ _) l16 l16_inj
    (by
      intro j
      fin_cases j
      · rfl
      · exact f51
      · rfl)
  have r17 := thenZL a r16 (cell_step : Step _ (cst17 R) _ _ _ _) l17 l17_inj
    (by
      intro j
      fin_cases j
      · exact f53)
  exact ⟨_, r17, ⟨f2, f4, f6, rfl, f8, rfl, f20, f21, rfl, f27, f29, rfl, rfl, rfl, rfl, rfl, rfl, rfl, f52, rfl, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74, f75, f76, f77, f78, f79, f80⟩⟩


/-- **Stages 18–23**: the entry registers, the mask, the zero-padding streams, the pool and its output word. -/
theorem segC (R : PoolReq) (hR : R.Pre) (hfit : CoefFit a R) (hn : 1 ≤ R.n) (hh : 1 ≤ R.h) (capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP : ℕ)
    (hS9 : C3a.Const.entRawCost R.Q (PexR a R) ≤ capS)
    (hS10 : Top.w4Cost [true, false] [true, false] [true, true] [false] R.Q (PexR a R) ≤ capS)
    (hS11 : C3a.Const.zpRawCost R.h (kLR R) ≤ capS) (hS12 : C3a.Const.zpRawCost R.h (kRR R) ≤ capS)
    (hS13 : poInR a R ≤ capS) (hI : C3a.Const.recRawCost R.h ≤ capI)
    (hc1 : 2 * R.h + 1 ≤ cap) (hcF : 2 * R.n + 1 ≤ cap)
    (hcT1 : 2 * (R.Q + R.flips.length * (counts a R.gates).sum + 1) + 1 ≤ cap) (hcT2 : 2 * WcR a R + 2 ≤ cap)
    (hcT3 : 3 * WcR a R + 2 ≤ cap) (hconv : convSum a R ≤ cap)
    (hcN2 : capN2R R ≤ capN2) (hcN7 : capN7R a R ≤ capN7) (hcC2 : capC2R R ≤ capC2) (hcC3 : capC3R R ≤ capC3)
    (hcC4 : capC4R a R ≤ capC4) (hcF8 : capF8R a R ≤ capF8) (hc5 : cap5R a R ≤ cap5) (hcP : pcR a R ≤ capP) {s0 c0 : ℕ} {M : Machine (U a) s0} {A0 : Fin (U a) → List Bool} {Lb : Fin 81 → List Bool}
    {Rb : Fin (MR a) → List Bool}
    (h0 : Step M c0 (fun _ => 0) A0 (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) Lb Rb))
    (hB : FactsB a R capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP Lb) :
    ∃ Lf : Fin 81 → List Bool,
      Step (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
        (Composition.machine M (m18 a)) (m19 a)) (m20 a)) (m21 a)) (m22 a)) (m23 a))
        (c0 + 1 + cst18 a R + 1 + cst19 a R + 1 + cst20 a R + 1 + cst21 R + 1 + cst22 R + 1 + cst23 a R)
        (fun _ => 0) A0 (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) Lf Rb) ∧
      Lf 70 = (poolRecs a R.h R.gates R.side R.width R.flips).flatMap frame ++
        false :: (childTable R.Q (shapeOf (densePool a R.gates R.side R.width R.flips))).flatMap atomStream := by
  have hnL := nLeft_eq R.side R.n hR.1
  have hnR := nRight_eq R.side R.n hR.1
  have hBs := B_eq_sum a R.gates
  obtain ⟨f2, f4, f6, f7, f8, f13, f20, f21, f24, f27, f29, f33, f40, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74, f75, f76, f77, f78, f79, f80⟩ := hB
  have r18 := thenZL a h0 (C3a.Const.ent_run R.Q (PexR a R) capS hS9 : Step _ (cst18 a R) _ _ _ _) l18 l18_inj
    (by
      intro j
      fin_cases j
      · exact f8
      · exact f27
      · exact f54
      · exact f13)
  have r19 := thenZL a r18 (C3a.Const.ent_run R.Q (PexR a R) capS hS9 : Step _ (cst19 a R) _ _ _ _) l19 l19_inj
    (by
      intro j
      fin_cases j
      · rfl
      · rfl
      · exact f56
      · rfl)
  have r20 := thenZL a r19 (Top.w4_run [true, false] [true, false] [true, true] [false] R.Q (PexR a R) capS hS10
      (frame (shiftMask R.Q (PexR a R))) (w4_word _ _) : Step _ (cst20 a R) _ _ _ _) l20 l20_inj
    (by
      intro j
      fin_cases j
      · rfl
      · rfl
      · exact f55
      · rfl)
  have r21 := thenZL a r20 (C3a.Const.zp_run R.h (kLR R) S capI capS hI hS11 : Step _ (cst21 R) _ _ _ _) l21 l21_inj
    (by
      intro j
      fin_cases j
      · exact f7
      · exact f33
      · exact f57
      · exact f59
      · rfl)
  have r22 := thenZL a r21 (C3a.Const.zp_run R.h (kRR R) S capI capS hI hS12 : Step _ (cst22 R) _ _ _ _) l22 l22_inj
    (by
      intro j
      fin_cases j
      · rfl
      · exact f40
      · exact f58
      · rfl
      · rfl)
  obtain ⟨Af, st, hf⟩ := po_at a R hR hfit hn hh cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP capS hc1 hcF
    hcT1 hcT2 hcT3 hconv hcN2 hcN7 hcC2 hcC3 hcC4 hcF8 hc5 hcP hS13
  have r23 := thenZL a r22 st l23 l23_inj
    (by
      intro j
      fin_cases j
      · exact f21.trans (List.append_nil _).symm
      · exact f47
      · exact f60
      · exact f48.trans (congrArg frame (NearCubicWires.WireExponent3_5.GF2.binary_zero R.h).symm)
      · exact f61
      · exact f72
      · exact f2
      · exact f73
      · exact f24
      · exact f4.trans (List.append_nil _).symm
      · exact f62
      · exact f63
      · exact f64
      · exact f65
      · exact f66
      · exact f67
      · exact f68
      · exact f69
      · exact f74
      · (show _ = streamTape (zeroRecs R.h (R.width - nLeft R.side R.n)) []; rw [hnL]; rfl)
      · (show _ = streamTape (zeroRecs R.h (R.width - nRight R.side R.n)) []; rw [hnR]; rfl)
      · exact f70
      · exact f75
      · exact f76
      · exact f6
      · exact f20
      · exact f49
      · exact f50
      · exact f51
      · exact f52
      · exact f53
      · (show _ = frame (entC R.Q (R.flips.length * (counts a R.gates).sum) 0); rw [← hBs]; rfl)
      · (show _ = frame (shiftMask R.Q (R.flips.length * (counts a R.gates).sum)); rw [← hBs]; rfl)
      · (show _ = frame (entC R.Q (R.flips.length * (counts a R.gates).sum) 0); rw [← hBs]; rfl)
      · exact f71
      · exact f77
      · exact f78
      · exact f79
      · exact f80
      · exact f29
      · rfl)
  exact ⟨_, r23, hf⟩


/-- **C3a′'s machine on one request, on the padded bank, at any capacities that cover the stages**
(P3:1596-1664). -/
theorem top_run_gen (R : PoolReq) (hR : R.Pre) (hfit : CoefFit a R) (hn : 1 ≤ R.n) (hh : 1 ≤ R.h) (capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP : ℕ)
    (hS1 : 2 * (Top.loadRec (List.replicate R.n true) (frame (segR R)) (frame R.side) (List.replicate R.width true)
      (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true) [] [] [] []).length + 1 ≤ capS)
    (hS2 : Top.loadChainCost (List.replicate R.n true) (frame (segR R)) (frame R.side) (List.replicate R.width true)
      (Kit.streamTape R.flips []) (List.replicate R.h true) (List.replicate R.Q true) [] [] [] [] ≤ capS)
    (hS3 : C3a.Dec.innerCost a R.n R.gates ≤ capS) (hS4 : C3a.Count.nfLoopCost R.flips.length R.n ≤ capS)
    (hS5 : C3a.Count.scLoopCost R.side.length ≤ capS)
    (hS6 : C3a.Const.kRawCost R.h (BR a R) ≤ capS) (hS7 : Top.wRunCost R.h ≤ capS)
    (hS8 : Top.w2Cost [true, false] [true, false, false] (BR a R) ≤ capS) (hSw : R.width + 2 ≤ S)
    (hCs : 2 * R.width + 5 ≤ Cs)
    (hS9 : C3a.Const.entRawCost R.Q (PexR a R) ≤ capS)
    (hS10 : Top.w4Cost [true, false] [true, false] [true, true] [false] R.Q (PexR a R) ≤ capS)
    (hS11 : C3a.Const.zpRawCost R.h (kLR R) ≤ capS) (hS12 : C3a.Const.zpRawCost R.h (kRR R) ≤ capS)
    (hS13 : poInR a R ≤ capS) (hI : C3a.Const.recRawCost R.h ≤ capI)
    (hc1 : 2 * R.h + 1 ≤ cap) (hcF : 2 * R.n + 1 ≤ cap)
    (hcT1 : 2 * (R.Q + R.flips.length * (counts a R.gates).sum + 1) + 1 ≤ cap) (hcT2 : 2 * WcR a R + 2 ≤ cap)
    (hcT3 : 3 * WcR a R + 2 ≤ cap) (hconv : convSum a R ≤ cap)
    (hcN2 : capN2R R ≤ capN2) (hcN7 : capN7R a R ≤ capN7) (hcC2 : capC2R R ≤ capC2) (hcC3 : capC3R R ≤ capC3)
    (hcC4 : capC4R a R ≤ capC4) (hcF8 : capF8R a R ≤ capF8) (hc5 : cap5R a R ≤ cap5) (hcP : pcR a R ≤ capP) :
    ∃ (Lf : Fin 81 → List Bool) (Rf : Fin (MR a) → List Bool),
      Step (c3aM a) (c3aCost a R) (fun _ => 0)
        (Fin.addCases (motive := fun _ => List Bool)
          (L0v R (capVec capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP)) (fun _ : Fin (MR a) => []))
        (fun _ => 0) (Fin.addCases (motive := fun _ => List Bool) Lf Rf) ∧
      Lf 70 = (poolRecs a R.h R.gates R.side R.width R.flips).flatMap frame ++
        false :: (childTable R.Q (shapeOf (densePool a R.gates R.side R.width R.flips))).flatMap atomStream := by
  obtain ⟨La, Ra, rA, fA⟩ := segA a R hR hn capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP hS1 hS2 hS3 hS4 hS5
  obtain ⟨Lb, rB, fB⟩ := segB a R hR capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP hS6 hS7 hS8 hSw hCs rA fA
  obtain ⟨Lf, rC, hf⟩ := segC a R hR hfit hn hh capS capI S Cs cap capN2 capN7 capC2 capC3 capC4 capF8 cap5 capP hS9 hS10 hS11 hS12 hS13 hI hc1 hcF hcT1 hcT2 hcT3 hconv
    hcN2 hcN7 hcC2 hcC3 hcC4 hcF8 hc5 hcP rB fB
  exact ⟨Lf, Ra, rC, hf⟩

end NearCubicWires.WireExponent3_5.CompilerMachine.C3a.Chain
