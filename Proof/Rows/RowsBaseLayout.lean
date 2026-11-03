import Proof.Rows.RowsInitThrParams
import Proof.Rows.RowsThrBounds
import Proof.CaseAnalysis.FiveRowKeys

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.BankNF
open Lean Meta Elab Tactic

def leaves : List Name := [``NearCubicWires.RepairOrdinary.frame, ``List.replicate, ``HAppend.hAppend,
  ``List.append, ``List.flatMap, ``List.ofFn, ``NearCubicWires.RepairOrdinary.ZeroPadding.pad, ``List.cons,
  ``List.nil, ``NearCubicWires.RepairRepresentation.natWord,
  ``NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word,
  ``NearCubicWires.RepairOrdinary.UnaryTemplate.tape, ``NearCubicWires.RepairOrdinary.SignedSortKey.binary,
  ``PCJ45bee56da9f34d5a_NativeFamilyFlags.source]

def natUnfold : List Name := [``PCJ45bee56da9f34d5a_CircuitPowerInput.caps,
  ``PCJ45bee56da9f34d5a_SelectedPowerBank.caps, ``PCJ45bee56da9f34d5a_PowerBank.factorCap,
  ``PCJ45bee56da9f34d5a_CircuitFlagBank.caps]

def decideBranch (e : Expr) : MetaM (Option Expr) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if f.isConstOf ``ite && args.size == 5 then
    let inst ← whnf args[2]!
    if inst.isAppOf ``Decidable.isTrue then return some args[3]!
    if inst.isAppOf ``Decidable.isFalse then return some args[4]!
  if f.isConstOf ``dite && args.size == 5 then
    let inst ← whnf args[2]!
    if inst.isAppOf ``Decidable.isTrue then return some (mkApp args[3]! inst.appArg!)
    if inst.isAppOf ``Decidable.isFalse then return some (mkApp args[4]! inst.appArg!)
  return none

def natNorm (e : Expr) : MetaM Expr := do
  match e.getAppFn with
  | .const n _ =>
    if natUnfold.contains n then
      let some e' ← unfoldDefinition? e | return e
      let e' ← whnfCore e'
      match ← decideBranch e' with
      | some b => return b.headBeta
      | none => return e
    else return e
  | _ => return e

partial def norm (e : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then return e
  let e ← whnfCore e
  match e.getAppFn with
  | .const n _ =>
    if leaves.contains n then
      let args ← e.getAppArgs.mapM fun a => do
        let ty ← inferType a
        if ty.isAppOfArity ``List 1 && ty.appArg!.isConstOf ``Bool then norm a (fuel-1)
        else natNorm a
      return mkAppN e.getAppFn args
    match ← decideBranch e with
    | some b => return (← norm b (fuel-1))
    | none =>
    match ← unfoldDefinition? e with
    | some e' => norm e' (fuel-1)
    | none =>
      match ← reduceMatcher? e with
      | ReduceMatcherResult.reduced e' => norm e' (fuel-1)
      | _ => return e
  | _ => return e

/-- `bank_nf c`: rewrite the first full application of the bank `c` in the goal to its evaluated form. -/
elab "bank_nf " c:ident : tactic => withMainContext do
  let cname ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo c
  let ar := (← getConstInfo cname).type.getForallArity
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun s => s.isAppOf cname && s.getAppNumArgs == ar)
    | throwError "bank_nf: no full application of {cname}"
  let nf ← norm e 2000
  let heq ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e nf)
  let r ← (← getMainGoal).rewrite tgt heq
  let g ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g :: r.mvarIds)

end RowsConstruction.BankNF

namespace RowsConstruction.BaseLayout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination
open RowsConstruction.ThrCell RowsConstruction.MaskGeneric NearCubicWires.SupplierWalkBridge
noncomputable section

/-! ## 1. The four THR parameter functions of `(q, |input|)` (`ThrBounds.thr_numeric`) -/

/-- The four constants of `U`, `F` (`RowsInit.ThrParams.thr_numeric_explicit`): `U`, `F` are COMPUTABLE
(`UnaryCalc.value` runs), so the initializer can write the master words `1^U`, `0^U`, `1^F`, … exactly. -/
def thrCU : ℕ := Classical.choose RowsInit.ThrParams.thr_numeric_explicit
def thrDU : ℕ := Classical.choose (Classical.choose_spec RowsInit.ThrParams.thr_numeric_explicit)
def thrCF : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec RowsInit.ThrParams.thr_numeric_explicit))
def thrDF : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  RowsInit.ThrParams.thr_numeric_explicit)))
def Uf (q T : ℕ) : ℕ := ThrBounds.UOf thrCU thrDU q T
def Ff (q T : ℕ) : ℕ := ThrBounds.FOf thrCF thrDF q T
def Pf : ℕ → ℕ → ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec RowsInit.ThrParams.thr_numeric_explicit))))
def Bf : ℕ → ℕ → ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec (Classical.choose_spec RowsInit.ThrParams.thr_numeric_explicit)))))

theorem fns_poly : (∃ c d, ∀ q T : Nat, PolyBounded (Uf q T+Ff q T+Pf q T+Bf q T) (q+T) c d) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec RowsInit.ThrParams.thr_numeric_explicit)))))).1

theorem fns_thr :
    ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
      (four : r.circuits.length ≤ 4) (L target : Nat) (sel : ThresholdRows.Selection a r) (cutoff : Nat),
      cutoff = CloseoutFinalC10ThresholdRows.primeCutoff a r target →
      ∀ (prime : PrimeIndex cutoff) (o : Fin prime.val),
      (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ ThrWidth.T a r four L target ∧
      PCJ45bee56da9f34d5a_FourfoldPowerData.Bounds (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
        (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val (12*ThrWidth.T a r four L target+19)
        (Ff r.q (ThrWidth.T a r four L target)) (Uf r.q (ThrWidth.T a r four L target))
        (ThrWidth.T a r four L target) (ThrWidth.T a r four L target) (Pf r.q (ThrWidth.T a r four L target)) ∧
      (PCJ45bee56da9f34d5a_StreamPairPorts.coefficientWord (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
        (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel) prime.val (12*ThrWidth.T a r four L target+19)
        o.val).length ≤ Uf r.q (ThrWidth.T a r four L target) ∧
      (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ Uf r.q (ThrWidth.T a r four L target) ∧
      (∀ (I : Finset (Fin r.q)) (x : BitInput r.q),
        (PCJ45bee56da9f34d5a_StreamPair.flags r I x).length+1 ≤ Uf r.q (ThrWidth.T a r four L target)) ∧
      (∀ (I : Finset (Fin r.q)) (x : BitInput r.q),
        PCJ45bee56da9f34d5a_ThresholdTraversal.budget a r sel I x (ThrWidth.T a r four L target) L target
          (12*ThrWidth.T a r four L target+19) (Uf r.q (ThrWidth.T a r four L target))
          (Pf r.q (ThrWidth.T a r four L target)) ≤ Bf r.q (ThrWidth.T a r four L target)) :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec RowsInit.ThrParams.thr_numeric_explicit)))))).2

/-! ## 2. Loop sizes -/

/-- Every THR traversal input word is at most this long (`thr_input_len`). -/
def thrLmax (q T : Nat) : Nat :=
  PCJ45bee56da9f34d5a_UniformMinimumBounds.U T q (T+1) + PCJ45bee56da9f34d5a_UniformMinimumBounds.H T q (T+1) +
  PCJ45bee56da9f34d5a_UniformMinimumBounds.R T q (T+1) + P1Closure.HardwireBudget.C (T+1) +
  Uf q T + Ff q T + 2*T + PCJ45bee56da9f34d5a_ResidueProductBounds.resetCap (12*T+19) + 8*(12*T+19) +
  2*q + 4*T + 16

/-- The THR cell reserve: the traversal budget plus two, and every master. -/
def thrR (q T : Nat) : Nat := Bf q T + thrLmax q T + 2

/-- Loop counter capacities (both modes). -/
def loopCl (q : Nat) : Nat := 2*q+2
def loopDl (q : Nat) : Nat := 4*q+7

theorem H_pb : ∃ c d, ∀ m B q : Nat, B ≤ m → q ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_UniformMinimumBounds.H B q (B+1)) m c d :=
  ⟨_, _, fun m _ _ hB hq => (const 64 m 0).mul (PolyBound.add (PolyBound.add (PolyBound.add
    (SymBounds.pb_var hB) (SymBounds.pb_var hq)) (PolyBound.add (SymBounds.pb_var hB) (const 1 m 1)))
      (const 1 m 1))⟩

theorem Rm_pb : ∃ c d, ∀ m B q : Nat, B ≤ m → q ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_UniformMinimumBounds.R B q (B+1)) m c d :=
  ⟨_, _, fun m _ _ hB hq => (const 1024 m 0).mul (SymBounds.pb_sq (PolyBound.add (PolyBound.add (PolyBound.add
    (SymBounds.pb_var hB) (SymBounds.pb_var hq)) (PolyBound.add (SymBounds.pb_var hB) (const 1 m 1)))
      (const 1 m 1)))⟩

/-- **The THR cell reserve is one fixed polynomial of `q+|input|`.** -/
theorem thrR_pb : ∃ c d, ∀ q T : Nat, PolyBounded (thrR q T) (q+T) c d := by
  obtain ⟨c0, d0, h0⟩ := fns_poly
  obtain ⟨c1, d1, h1⟩ := SymBounds.U_pb
  obtain ⟨c2, d2, h2⟩ := H_pb
  obtain ⟨c3, d3, h3⟩ := Rm_pb
  exact ⟨_, _, fun q T =>
    have hT : T ≤ q+T := Nat.le_add_left T q
    have hq : q ≤ q+T := Nat.le_add_right q T
    have hw : PolyBounded (12*T+19) (q+T) (12*1+19) (max (0+1) 0) :=
      PolyBound.add ((const 12 (q+T) 0).mul (SymBounds.pb_var hT)) (const 19 (q+T) 0)
    have hUf : PolyBounded (Uf q T) (q+T) c0 d0 :=
      (h0 q T).mono (show Uf q T ≤ Uf q T+Ff q T+Pf q T+Bf q T by omega)
    have hFf : PolyBounded (Ff q T) (q+T) c0 d0 :=
      (h0 q T).mono (show Ff q T ≤ Uf q T+Ff q T+Pf q T+Bf q T by omega)
    have hBf : PolyBounded (Bf q T) (q+T) c0 d0 :=
      (h0 q T).mono (show Bf q T ≤ Uf q T+Ff q T+Pf q T+Bf q T by omega)
    PolyBound.add (PolyBound.add hBf
      (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
        (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
          (h1 (q+T) T q hT hq) (h2 (q+T) T q hT hq)) (h3 (q+T) T q hT hq))
          (PolyBound.add ((const 8 (q+T) 0).mul (PolyBound.add (SymBounds.pb_var hT) (const 1 (q+T) 1)))
            (const 12 (q+T) 0)))
          hUf) hFf)
          ((const 2 (q+T) 0).mul (SymBounds.pb_var hT)))
          ((const 32 (q+T) 0).mul (SymBounds.pb_sq (PolyBound.add hw (const 1 (q+T) 1)))))
          ((const 8 (q+T) 0).mul hw)) ((const 2 (q+T) 0).mul (SymBounds.pb_var hq)))
          ((const 4 (q+T) 0).mul (SymBounds.pb_var hT))) (const 16 (q+T) 0))) (const 2 (q+T) 0)⟩

/-! ## 3. The THR census: every traversal input word, port by port -/

set_option linter.unnecessarySeqFocus false in

theorem thr_input_len (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q))
    (x : BitInput r.q) {cutoff : Nat} (prime : PrimeIndex cutoff) (o : Fin prime.val) (T L target w F U v : Nat)
    (hnat : (PCJ45bee56da9f34d5a_NativeFamilyFlags.source 1 L target
      (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r)).length ≤ T)
    (hwf : ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words.flatMap frame).length ≤ T)
    (hc : (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).count ≤ 4)
    (i : Fin 254) :
    (PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four sel I x prime o T L target w F U v i).length ≤
      PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) + PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) +
      PCJ45bee56da9f34d5a_UniformMinimumBounds.R T r.q (T+1) + P1Closure.HardwireBudget.C (T+1) +
      U + F + 2*v + PCJ45bee56da9f34d5a_ResidueProductBounds.resetCap w + 8*w + 2*r.q + 4*T + 16 := by
  fin_cases i <;> (bank_nf PCJ45bee56da9f34d5a_ThresholdTraversal.input
    <;> (try simp only [List.length_replicate, frame_length, SignedSortKey.binary_length, ZeroPadding.pad_length,
      List.length_ofFn, List.length_cons, List.length_nil, UnaryTemplate.tape_length, CompareMachine.word])
    <;> omega)

/-! ## 4. The THR master bank of a row key -/

variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The family's live set (the row's `I`). -/
abbrev thrLive : Finset (Fin r.q) := PCJ9eff70d512234a4c_Fixed.CyclicChoice.live (thresholdFourfoldOccurrences r) L

/-- The ten THR key ports (the master words C5 rewrites, `RowsKeySucc.thrKeyPorts` minus the cell 109). -/
def thrKeySet : Finset (Fin 254) := {149, 209, 218, 220, 228, 229, 230, 231, 240, 242}

def keyPad (K : Finset (Fin 254)) (R : Nat) (i : Fin 254) (w : List Bool) : List Bool :=
  if i ∈ K then w else ZeroPadding.pad R w

theorem keyPad_key {K : Finset (Fin 254)} (R : Nat) {i : Fin 254} (hi : i ∈ K) (w : List Bool) :
    keyPad K R i w = w := by
  simp [keyPad, hi]

theorem keyPad_len (K : Finset (Fin 254)) (R : Nat) (i : Fin 254) (w : List Bool) (h : w.length ≤ R) :
    (keyPad K R i w).length ≤ R := by
  unfold keyPad
  split
  · exact h
  · simp only [ZeroPadding.pad_length]
    omega

/-- **The THR master bank of key `k`**: the traversal input of `k`'s `(selection, prime, residue)` at the
request's parameters, with the cell port 109 blank (`R` falses); non-key ports padded to `R` (`keyPad`). -/
def thrMasters (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) : Fin 254 → List Bool := fun i =>
  if i = 109 then List.replicate R false
  else keyPad thrKeySet R i (PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four k.selection (thrLive r L)
    (fun _ => false) k.prime k.residue (ThrWidth.T a r four L target) L target (12*ThrWidth.T a r four L target+19)
    (Ff r.q (ThrWidth.T a r four L target)) (Uf r.q (ThrWidth.T a r four L target)) (ThrWidth.T a r four L target) i)

theorem thr_hml (R : Nat) (hR : thrR r.q (ThrWidth.T a r four L target) ≤ R)
    (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 254) :
    (thrMasters a r four L target R k i).length ≤ R := by
  unfold thrMasters
  split
  · simp
  · refine keyPad_len _ _ _ _ (le_trans (thr_input_len a r four k.selection _ _ k.prime k.residue _ L target _ _ _ _
      (ThrBounds.native_le a r four L target) (ThrBounds.words_frame_le a r four L target k.selection) four i) ?_)
    unfold thrR thrLmax at hR
    omega

/-! ## 5. The THR row's mask loop on its own masters: the family row's selector -/

/-! ## 6. SYM: parameters, census, masters, and the row's mask loop -/

def symC : ℕ := Classical.choose SymBounds.sym_numeric
def symD : ℕ := Classical.choose (Classical.choose_spec SymBounds.sym_numeric)

theorem sym_spec : ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : Nat) (offset : Fin r.circuits.length → Nat),
    (∀ k, offset k ≤ (SymMeaning.symGates (r.circuits.get k)).length) →
    let T := ((PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).input a).length
    let w := T+3
    let cap := symC*(r.q+T+5)^symD
    (SymVerdict.src r L target).length ≤ T ∧ 4 < 2^w ∧ (∀ k : Fin 4, SymVerdict.N r k < 2^w) ∧
    (∀ k : Fin 4, SymVerdict.Tg r offset k < 2^w) ∧
    PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T ≤ cap ∧
    (∀ k : Fin 4, PCJ45bee56da9f34d5a_CountFlags.budget (SymVerdict.N r k) w ≤ cap) ∧
    (2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))) ≤ cap ∧
    PCJ45bee56da9f34d5a_CountFlags.budget 4 w ≤ cap ∧
    SymVerdict.cost r L target T w ≤ cap :=
  Classical.choose_spec (Classical.choose_spec SymBounds.sym_numeric)

/-- The SYM verdict's log capacity at request size. -/
def symCap (q T : Nat) : Nat := symC*(q+T+5)^symD

/-- Every SYM verdict input word is at most this long (`sym_input_len`). -/
def symLmax (q T : Nat) : Nat :=
  PCJ45bee56da9f34d5a_UniformMinimumBounds.U T q (T+1) + PCJ45bee56da9f34d5a_UniformMinimumBounds.H T q (T+1) +
  PCJ45bee56da9f34d5a_UniformMinimumBounds.R T q (T+1) + P1Closure.HardwireBudget.C (T+1) +
  symCap q T + (2*(T+3)+1) + 4*(T+3) + 2*q + 4*T + 16

/-- The SYM cell reserve. -/
def symR (q T : Nat) : Nat := symCap q T + 2 + symLmax q T

theorem symCap_pb : ∃ c d, ∀ q T : Nat, PolyBounded (symCap q T) (q+T) c d :=
  ⟨_, _, fun q T => comp (show PolyBounded (symCap q T) (q+T+4) symC symD from le_refl _)
    (show PolyBounded (q+T+4) (q+T) 5 1 by unfold PolyBounded; rw [pow_one]; omega)⟩

/-- **The SYM cell reserve is one fixed polynomial of `q+|input|`.** -/
theorem symR_pb : ∃ c d, ∀ q T : Nat, PolyBounded (symR q T) (q+T) c d := by
  obtain ⟨c0, d0, h0⟩ := symCap_pb
  obtain ⟨c1, d1, h1⟩ := SymBounds.U_pb
  obtain ⟨c2, d2, h2⟩ := H_pb
  obtain ⟨c3, d3, h3⟩ := Rm_pb
  exact ⟨_, _, fun q T =>
    have hT : T ≤ q+T := Nat.le_add_left T q
    have hq : q ≤ q+T := Nat.le_add_right q T
    have hw : PolyBounded (T+3) (q+T) (1+3) (max 1 0) := PolyBound.add (SymBounds.pb_var hT) (const 3 (q+T) 0)
    PolyBound.add (PolyBound.add (h0 q T) (const 2 (q+T) 0))
      (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
        (PolyBound.add (PolyBound.add (PolyBound.add
          (h1 (q+T) T q hT hq) (h2 (q+T) T q hT hq)) (h3 (q+T) T q hT hq))
          (PolyBound.add ((const 8 (q+T) 0).mul (PolyBound.add (SymBounds.pb_var hT) (const 1 (q+T) 1)))
            (const 12 (q+T) 0)))
          (h0 q T))
          (PolyBound.add ((const 2 (q+T) 0).mul hw) (const 1 (q+T) 0)))
          ((const 4 (q+T) 0).mul hw)) ((const 2 (q+T) 0).mul (SymBounds.pb_var hq)))
          ((const 4 (q+T) 0).mul (SymBounds.pb_var hT))) (const 16 (q+T) 0))⟩

set_option linter.unnecessarySeqFocus false in
theorem sym_input_len (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (I : Finset (Fin r.q))
    (x : BitInput r.q) (L target T w Dc cap : Nat) (offset : Fin r.circuits.length → Nat)
    (hsrc : (PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (SymMeaning.circuits r)).length ≤ T)
    (hN : ∀ c : Fin 4, SymVerdict.N r c ≤ T+1) (i : Fin 254) :
    (SymVerdict.input r I x L target T w Dc cap offset i).length ≤
      PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1) + PCJ45bee56da9f34d5a_UniformMinimumBounds.H T r.q (T+1) +
      PCJ45bee56da9f34d5a_UniformMinimumBounds.R T r.q (T+1) + P1Closure.HardwireBudget.C (T+1) +
      cap + Dc + 4*w + 2*r.q + 4*T + 16 := by
  have h0 := hN 0
  have h1 := hN 1
  have h2 := hN 2
  have h3 := hN 3
  fin_cases i <;> (bank_nf RowsConstruction.SymVerdict.input
    <;> (try simp only [List.length_replicate, frame_length, SignedSortKey.binary_length, ZeroPadding.pad_length,
      List.length_ofFn, List.length_cons, List.length_nil, CompareMachine.word])
    <;> omega)

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The SYM request's `T = |input|`. -/
abbrev symT : Nat := ((PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target).input a).length

abbrev symLive : Finset (Fin r.q) := PCJ9eff70d512234a4c_Fixed.CyclicChoice.live (symmetricFourfoldOccurrences r) L

theorem sym_N_le (c : Fin 4) : SymVerdict.N r c ≤ symT a r four L target+1 := by
  have hnat := SymBounds.native_le_input a (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target)
  have hflag := SymBounds.flagged_le_native r four L target ∅ (fun _ => false)
  have h := SymMeaning.driverLen_le r ∅ (fun _ => false) c.val
  rw [List.length_append, List.length_singleton] at h
  unfold SymVerdict.N symT
  omega

theorem sym_src_le : (PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (SymMeaning.circuits r)).length ≤
    symT a r four L target := by
  have hnat := SymBounds.native_le_input a (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target)
  change (SymVerdict.src r L target).length ≤ _
  rw [SymVerdict.src, SymMeaning.native_eq r four L target]
  exact hnat

/-- The four SYM key ports (the cumulative targets C5 rewrites). -/
def symKeySet : Finset (Fin 254) := {140, 141, 142, 143}

/-- **The SYM master bank of key `k`** (non-key ports padded to `R`, as `thrMasters`). -/
def symMasters (R : Nat) (k : RCFive.RowKeys.SymKey r L target) : Fin 254 → List Bool := fun i =>
  if i = 109 then List.replicate R false
  else keyPad symKeySet R i (SymVerdict.input r (symLive r L) (fun _ => false) L target (symT a r four L target)
    (symT a r four L target+3) (2*(symT a r four L target+3)+1) (symCap r.q (symT a r four L target)) k.offset i)

theorem sym_hml (R : Nat) (hR : symR r.q (symT a r four L target) ≤ R) (k : RCFive.RowKeys.SymKey r L target)
    (i : Fin 254) : (symMasters a r four L target R k i).length ≤ R := by
  unfold symMasters
  split
  · simp
  · refine keyPad_len _ _ _ _ (le_trans (sym_input_len r _ _ L target _ _ _ _ k.offset (sym_src_le a r four L target)
      (sym_N_le a r four L target) i) ?_)
    unfold symR symLmax at hR
    omega

/-- Every listed SYM key's offsets are within the circuits' gate counts. -/
theorem sym_offset_le (k : RCFive.RowKeys.SymKey r L target) (hk : k ∈ RCFive.RowKeys.symKeys r L target)
    (i : Fin r.circuits.length) : k.offset i ≤ (SymMeaning.symGates (r.circuits.get i)).length := by
  simp only [RCFive.RowKeys.symKeys, List.mem_flatMap, List.mem_map] at hk
  obtain ⟨_, _, off, hoff, rfl⟩ := hk
  simp only [PCJ9eff70d512234a4c_Fixed.Packets.symOffsetList, List.mem_map] at hoff
  obtain ⟨f, _, rfl⟩ := hoff
  simp only [SymMeaning.symGates, List.length_ofFn]
  exact Nat.lt_succ_iff.mp (f i).isLt

end Sym

/-! ## 7. The reserves the initializer computes (`UnaryCalc.value` of the unary `q+|input|`) -/

def thrRc : ℕ := Classical.choose thrR_pb
def thrRd : ℕ := Classical.choose (Classical.choose_spec thrR_pb)
theorem thrR_spec (q T : Nat) : PolyBounded (thrR q T) (q+T) thrRc thrRd :=
  Classical.choose_spec (Classical.choose_spec thrR_pb) q T
/-- **The THR cell reserve**, `(thrRc+1)·(q+T+1)^thrRd`: one fixed polynomial of `q+|input|`, computed once per
request by `UnaryCalc`, and at least `thrR q T`. -/
def thrRes (q T : Nat) : Nat := UnaryCalc.value thrRd (thrRc+1) (q+T)
theorem thrR_le_res (q T : Nat) : thrR q T ≤ thrRes q T := by
  have := driver_covers (thrR_spec q T)
  unfold thrRes
  omega

def symRc : ℕ := Classical.choose symR_pb
def symRd : ℕ := Classical.choose (Classical.choose_spec symR_pb)
theorem symR_spec (q T : Nat) : PolyBounded (symR q T) (q+T) symRc symRd :=
  Classical.choose_spec (Classical.choose_spec symR_pb) q T
/-- **The SYM cell reserve** (as `thrRes`). -/
def symRes (q T : Nat) : Nat := UnaryCalc.value symRd (symRc+1) (q+T)
theorem symR_le_res (q T : Nat) : symR q T ≤ symRes q T := by
  have := driver_covers (symR_spec q T)
  unfold symRes
  omega

/-- The Core's `privateWork` for an initializer region of `NI` ports. -/
abbrev rowsWork (NI : Nat) : Nat := NI+(8+64+(MT+1+1)+2+16)

/-- The seven-block work layout. -/
def workLayout {α : Type} {NI : Nat} (pub : Fin 2 → α) (init : Fin NI → α) (rowp : Fin 8 → α) (rcp : Fin 64 → α)
    (loop : Fin (MT+1+1) → α) (c6 : Fin 2 → α) (c5 : Fin 16 → α) : Fin (2+rowsWork NI) → α :=
  Fin.addCases pub (Fin.addCases init
    (Fin.addCases (Fin.addCases (Fin.addCases (Fin.addCases rowp rcp) loop) c6) c5))

def fixPort (NI : Nat) (f : Fin (8+64+(MT+1+1)+2+16)) : Fin (2+rowsWork NI) := (f.natAdd NI).natAdd 2
def pubPort (NI : Nat) (i : Fin 2) : Fin (2+rowsWork NI) := i.castAdd _
def initPort (NI : Nat) (i : Fin NI) : Fin (2+rowsWork NI) := (i.castAdd _).natAdd 2
def rowpPort (NI : Nat) (i : Fin 8) : Fin (2+rowsWork NI) :=
  fixPort NI ((((i.castAdd 64).castAdd (MT+1+1)).castAdd 2).castAdd 16)
def rcpPort (NI : Nat) (i : Fin 64) : Fin (2+rowsWork NI) :=
  fixPort NI ((((i.natAdd 8).castAdd (MT+1+1)).castAdd 2).castAdd 16)
def loopPort (NI : Nat) (i : Fin (MT+1+1)) : Fin (2+rowsWork NI) :=
  fixPort NI (((i.natAdd (8+64)).castAdd 2).castAdd 16)
def c6Port (NI : Nat) (i : Fin 2) : Fin (2+rowsWork NI) := fixPort NI ((i.natAdd (8+64+(MT+1+1))).castAdd 16)
def c5Port (NI : Nat) (i : Fin 16) : Fin (2+rowsWork NI) := fixPort NI (i.natAdd (8+64+(MT+1+1)+2))
/-- The loop port of cell master `i`. -/
def masterPort (NI : Nat) (i : Fin 254) : Fin (2+rowsWork NI) := loopPort NI (((masterP i).castAdd 1).castAdd 1)

theorem rowpPort_val (NI : Nat) (i : Fin 8) : (rowpPort NI i).val = 2+NI+i.val := by
  simp [rowpPort, fixPort]
  omega

section Ports
variable {α : Type} {NI : Nat} (pub : Fin 2 → α) (init : Fin NI → α) (rowp : Fin 8 → α) (rcp : Fin 64 → α)
  (loop : Fin (MT+1+1) → α) (c6 : Fin 2 → α) (c5 : Fin 16 → α)
@[simp] theorem layout_init (i : Fin NI) : workLayout pub init rowp rcp loop c6 c5 (initPort NI i) = init i := by
  simp [workLayout, initPort]
@[simp] theorem layout_loop (i : Fin (MT+1+1)) :
    workLayout pub init rowp rcp loop c6 c5 (loopPort NI i) = loop i := by
  simp [workLayout, loopPort, fixPort]
@[simp] theorem layout_c5 (i : Fin 16) : workLayout pub init rowp rcp loop c6 c5 (c5Port NI i) = c5 i := by
  simp [workLayout, c5Port, fixPort]
end Ports

/-- The eight `RowPorts` words (`cC = copyCap`, `hF = headerFuel`, `C = layout.C`, `n` the pool arity). -/
def rowpWords (n C cC hF : Nat) : Fin 8 → List Bool :=
  ![List.replicate cC true, List.replicate (cC+1) false,
    UnaryTemplate.tape (2*((n+1)/2)-(decide (n%2=1)).toNat+2), List.replicate (3*cC+2) false,
    List.replicate C true, List.replicate (34*cC+2) false, List.replicate (2*hF) true,
    List.replicate (2*hF+1) false]

/-- The mask loop's bank at loop start, with master block `M` and a blank `2^s` verdict tape. -/
def loopBank {q : Nat} (live : Finset (Fin q)) (R : Nat) (M : Fin 254 → List Bool) : Fin (MT+1+1) → List Bool :=
  Fin.addCases (Fin.addCases (tapes live liveᶜ.card R (loopCl q) (loopDl q) 0 0 M
      (List.replicate (2^liveᶜ.card) false))
    (fun _ : Fin 1 => CompareMachine.word (2^(liveᶜ.card/2))))
    (fun _ : Fin 1 => CompareMachine.word (2^((liveᶜ.card+1)/2)))

/-- C6's mask-length driver and log. -/
def c6Words (s : Nat) : Fin 2 → List Bool := ![List.replicate (2^s) true, List.replicate (2*2^s+1) false]

/-- C5's seed cursor: the index and the count of the family's seeds, framed binary. -/
def seedWords (e N : Nat) : Fin 2 → List Bool :=
  ![frame (SignedSortKey.binary (natBitLength N) e), frame (SignedSortKey.binary (natBitLength N) N)]

/-- The seed digit's scratch size: `2·(bit width of the seed count)+1`. -/
def seedScratch (N : Nat) : Nat := 2*natBitLength N+1

/-- The C5 block: seed cursor (0, 1), the unary prime cutoff (2), offsets (3–6), the seed digit step's scratch
(7–10: `0^S`, 11: `1^S`, 12: `0^(S+1)`), blanks (13–15). -/
def c5Words (seed : Fin 2 → List Bool) (cut : List Bool) (off : Fin 4 → List Bool) (S : Nat) :
    Fin 16 → List Bool :=
  Fin.addCases (m:=7) (n:=9) (Fin.addCases (m:=3) (n:=4) (Fin.addCases (m:=2) (n:=1) seed (fun _ => cut)) off)
    ![List.replicate S false, List.replicate S false, List.replicate S false, List.replicate S false,
      List.replicate S true, List.replicate (S+1) false, [], [], []]

section ThrBase
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

abbrev thrSeeds := PCJ9eff70d512234a4c_Fixed.Packets.seedList (thresholdFourfoldOccurrences r) (thrLive r L)
  (CloseoutFinalC10ThresholdRows.listDenominator a r target)

/-- The index of a THR key's seed in the family's seed list. -/
def thrSeedIdx (k : RCFive.RowKeys.ThrKey a r L target) : Nat :=
  (canonicalWalkSampleFinEquiv (2 ^ toeplitzWalkSideBits (canonicalGradedRank
    (thresholdFourfoldOccurrences r).length
    (PCJ9eff70d512234a4c_Fixed.LiveRows.bound (thresholdFourfoldOccurrences r) (thrLive r L))))
    (CloseoutFinalC10ThresholdRows.listDenominator a r target) k.seed).val

/-- The row key of row `j` (row `rows.length`, the exhausted state, wraps to key `0`). -/
def thrKeyAt (j : Nat) : Option (RCFive.RowKeys.ThrKey a r L target) :=
  (RCFive.RowKeys.thrKeys a r L target)[j % (RCFive.RowKeys.thrKeys a r L target).length]?

/-- The pool arity of the THR family (`RowsRowLevelCompose.rowN`). -/
abbrev thrN : Nat :=
  (PCJ9eff70d512234a4c_Fixed.Packets.residual (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target)+1)/2
    + PCJ9eff70d512234a4c_Fixed.Packets.residual (PCJ9eff70d512234a4c_Fixed.Packets.thrFamily a r L target)/2

/-- **`base j` for a THR request**: RC's blocks (request constants) and, per row, the masters of row `j`'s
key. -/
def thrBase (j : Nat) : Fin (2+rowsWork NI) → List Bool :=
  match thrKeyAt a r L target j with
  | none => workLayout pub init (rowpWords (thrN a r L target) C cC hF) rcp (fun _ => []) (fun _ => [])
      (fun _ => [])
  | some k => workLayout pub init (rowpWords (thrN a r L target) C cC hF) rcp
      (loopBank (thrLive r L) (thrRes r.q (ThrWidth.T a r four L target))
        (thrMasters a r four L target (thrRes r.q (ThrWidth.T a r four L target)) k))
      (c6Words (thrLive r L)ᶜ.card)
      (c5Words (seedWords (thrSeedIdx a r L target k) (thrSeeds a r L target).length)
        (List.replicate (CloseoutFinalC10ThresholdRows.primeCutoff a r target) true) (fun _ => [])
        (seedScratch (thrSeeds a r L target).length))

end ThrBase

section SymBase
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)
  (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

abbrev symSeeds := PCJ9eff70d512234a4c_Fixed.Packets.seedList (symmetricFourfoldOccurrences r) (symLive r L)
  (symmetricListDenominator r target)

def symSeedIdx (k : RCFive.RowKeys.SymKey r L target) : Nat :=
  (canonicalWalkSampleFinEquiv (2 ^ toeplitzWalkSideBits (canonicalGradedRank
    (symmetricFourfoldOccurrences r).length
    (PCJ9eff70d512234a4c_Fixed.LiveRows.bound (symmetricFourfoldOccurrences r) (symLive r L))))
    (symmetricListDenominator r target) k.seed).val

/-- The SYM key's offsets, framed at the counter width `T+3`. -/
def symOffWords (T : Nat) (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) : List Bool :=
  frame (SignedSortKey.binary (T+3) (if h : c.val < r.circuits.length then k.offset ⟨c.val, h⟩ else 0))

def symKeyAt (j : Nat) : Option (RCFive.RowKeys.SymKey r L target) :=
  (RCFive.RowKeys.symKeys r L target)[j % (RCFive.RowKeys.symKeys r L target).length]?

abbrev symN : Nat :=
  (PCJ9eff70d512234a4c_Fixed.Packets.residual (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target)+1)/2
    + PCJ9eff70d512234a4c_Fixed.Packets.residual (PCJ9eff70d512234a4c_Fixed.Packets.symFamily r L target)/2

/-- **`base j` for a SYM request.** -/
def symBase (j : Nat) : Fin (2+rowsWork NI) → List Bool :=
  match symKeyAt r L target j with
  | none => workLayout pub init (rowpWords (symN r L target) C cC hF) rcp (fun _ => []) (fun _ => [])
      (fun _ => [])
  | some k => workLayout pub init (rowpWords (symN r L target) C cC hF) rcp
      (loopBank (symLive r L) (symRes r.q (symT a r four L target))
        (symMasters a r four L target (symRes r.q (symT a r four L target)) k))
      (c6Words (symLive r L)ᶜ.card)
      (c5Words (seedWords (symSeedIdx r L target k) (symSeeds r L target).length) []
        (symOffWords r L target (symT a r four L target) k) (seedScratch (symSeeds r L target).length))

end SymBase

end
end RowsConstruction.BaseLayout
