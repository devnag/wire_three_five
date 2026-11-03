import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemTW
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.UnionCodec
import Proof.Wire_3_5.UnionMachine.FrontDecode
import Proof.Wire_3_5.UnionMachine.FrontOutRef
import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Wire_3_5.UnionMachine.FrontSemDecBase


noncomputable section


/-! # C6 front, the semantic core (4): the chain's checks decide the reference output (P3:3669-3691)

The front's reference output (`FrontOutRef.outRef`) is the valid branch's exactly when the witness decodes to a guess
passing the outer step's guards, the atom, sign and admissibility checks. The chain checks, in order: the walker's scan
(`okOf`), the cold front end's verdict (the pair's decoding and the guards of the outer step, paper v2 §H.5), the
entries' scan, the atoms' decoder at the description envelope, then (in the end) the calls' admissibility. This module
shows each failing check rejects the decoded guess (**`okOf_of`**, **`pair_of`**,
**`signs_of`**, **`atoms_fail`**), the passing checks decode the chain's guess `gOf` with its three checks
(**`valid_of`**), and evaluates the reference output on each branch (**`outRef_rej`**, **`outRef_valid`**: the valid
branch's output is the end's `endOut`).

Paper quantity of the main types: the front's reference output (its table, thresholds and capacities) per witness. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemDec
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter gridVal)

section Dec
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N}

/-- A decoded witness passes the walker's scan. -/
theorem okOf_of {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    FrontOracleField.okOf w = true := by
  obtain ⟨t, k, hw, hsc, -, -⟩ := decode_fwd g w h
  subst hw; exact hsc

/-- A decoded witness's pair field reads as the guess's pair. -/
theorem pair_of {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload w.tail) = some g.pair := by
  obtain ⟨t, k, hw, -, hv, -⟩ := decode_fwd g w h
  subst hw
  exact hv

/-- A decoded witness's tag bit is the guess's mode. -/
theorem mode_of {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    modeOf (w.headD false) = g.mode := by
  obtain ⟨t, k, hw, -, -, -⟩ := decode_fwd g w h
  subst hw
  show modeOf (modeTag g.mode) = g.mode
  generalize g.mode = m
  cases m <;> rfl

theorem rest_of {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    ∃ k, restOf w.tail = ((entsG g).map encE).flatten ++ List.replicate k false := by
  obtain ⟨t, k, hw, -, -, hr⟩ := decode_fwd g w h
  subst hw; exact ⟨k, hr⟩

theorem entN_eq (g : UnionGuess S z) : entN S z g.pair = (entsG g).length := (entsG_length g).symm

/-- **The entries' scan of a decoded witness is its guess's grid-sign check.** -/
theorem signs_of {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    (entScan (entN S z g.pair) (restOf w.tail)).isSome = (g.checkData g.translation).signsOk := by
  obtain ⟨k, hr⟩ := rest_of h
  rw [hr, entN_eq]
  exact entScan_fwd g _ k

/-- The payloads by index. -/
theorem pay_idx (g : UnionGuess S z) (Z : List Bool) (hg : ∀ e ∈ entsG g, e.1 ∈ gridSet) (X : PcppVar g.pcpp)
    (a : Fin g.s) :
    value (payOf (((entsG g).map encE).flatten ++ Z) (entsG g).length (X.val * g.s + a.val)) =
      g.mode.code (g.atom X a) := by
  have h2 := (restAfter_enc (entsG g) Z hg).2
  have hj : X.val * g.s + a.val < (entsG g).length := by rw [entsG_length]; exact idx_lt X a
  have hlen : (entsOf (entsG g).length (((entsG g).map encE).flatten ++ Z)).length = (entsG g).length := by
    rw [← List.length_map (f := fun e : (Bool × Bool) × List Bool => (gridVal e.1.1 e.1.2, value e.2)), h2]
  have hXa : (entsG g).getD (X.val * g.s + a.val) ((0 : ℤ), 0) = (g.sign X a, g.mode.code (g.atom X a)) :=
    FrontSemEnt.getD_linE _ _ X a
  have e1 : (((entsOf (entsG g).length (((entsG g).map encE).flatten ++ Z)).map
      (fun e => (gridVal e.1.1 e.1.2, value e.2))).getD (X.val * g.s + a.val) ((0 : ℤ), 0)).2 =
        ((entsG g).getD (X.val * g.s + a.val) ((0 : ℤ), 0)).2 := by
    rw [h2]
  rw [hXa, List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map] at e1
  unfold payOf
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact e1

end Dec

/-! ## The atoms' check -/

section Atoms
open NearCubicWires.RepairOrdinary
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N}

/-- **The atom test passes**: every atom within the description envelope. -/
theorem atoms_ok (g : UnionGuess S z) (Z : List Bool) (hg : ∀ e ∈ entsG g, e.1 ∈ gridSet) (Wd L : ℕ)
    (hWd : ∀ j, j < (entsG g).length →
      20 * (natBitLength (value (payOf (((entsG g).map encE).flatten ++ Z) (entsG g).length j)) + 4) ≤ Wd)
    (hv : FrontAtomLoop.verdictOf g.q Wd L g.mode (entsG g).length
      (payOf (((entsG g).map encE).flatten ++ Z) (entsG g).length) = 0) :
    ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ L := by
  intro X a
  have hj : X.val * g.s + a.val < (entsG g).length := by rw [entsG_length]; exact idx_lt X a
  have hp := verdict_zero hv _ hj
  have e := pay_idx g Z hg X a
  exact (FrontDescLoop.passedM_desc g.mode g.q Wd L _ (g.atom X a) (by rw [e]; exact decodeAtom_code _ _ _)
    (hWd _ hj)).1 hp

/-- **The atom test fails**: some atom outside the description envelope. -/
theorem atoms_bad (g : UnionGuess S z) (Z : List Bool) (hg : ∀ e ∈ entsG g, e.1 ∈ gridSet) (Wd L : ℕ)
    (hWd : ∀ j, j < (entsG g).length →
      20 * (natBitLength (value (payOf (((entsG g).map encE).flatten ++ Z) (entsG g).length j)) + 4) ≤ Wd)
    (hv : FrontAtomLoop.verdictOf g.q Wd L g.mode (entsG g).length
      (payOf (((entsG g).map encE).flatten ++ Z) (entsG g).length) ≠ 0) :
    ¬ ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ L := by
  intro hat
  obtain ⟨j, hj, hnp⟩ := verdict_ne hv
  obtain ⟨X, a, e⟩ := pay_fwd g Z hg j hj
  exact hnp ((FrontDescLoop.passedM_desc g.mode g.q Wd L _ (g.atom X a) (by rw [e]; exact decodeAtom_code _ _ _)
    (hWd j hj)).2 (hat X a))

/-- **The chain's checks pass**: the witness decodes to the chain's guess `gOf`, with grid signs. -/
theorem valid_of (b : Bool) (t : List Bool) (hsc : scanOK t = true)
    (O : NearCubicGates.Close.Outer.OuterGuess (S.width N))
    (hO : NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some O)
    (hE : (entScan (entN S z O) (restOf t)).isSome = true) (Wd L : ℕ)
    (hv : FrontAtomLoop.verdictOf (S.request z O).arity Wd L (modeOf b) (entN S z O)
      (payOf (restOf t) (entN S z O)) = 0) :
    decodeGuess S z (b :: t) = some (gOf S z b O (restOf t)) ∧
      ((gOf S z b O (restOf t)).checkData (gOf S z b O (restOf t)).translation).signsOk = true := by
  rw [FrontEntriesRef.entScan_isSome] at hE
  obtain ⟨v, hr, hvall⟩ : ∃ v, restAfter (entN S z O) (restOf t) = some v ∧ v.all (fun b => !b) = true := by
    revert hE
    cases h : restAfter (entN S z O) (restOf t) with
    | none => simp
    | some v => intro hv'; exact ⟨v, rfl, hv'⟩
  have hat : ∀ j, j < entN S z O → ∃ C : (modeOf b).Circuit (S.request z O).arity,
      decodeAtom (modeOf b) (S.request z O).arity (value (payOf (restOf t) (entN S z O) j)) = some C :=
    fun j hj => passed_dec _ _ _ _ _ (verdict_zero hv j hj)
  have hd := gOf_decode b t hsc O hO v hvall hr hat
  refine ⟨hd, ?_⟩
  have hs := signs_of hd
  rw [← hs]
  show (entScan (entN S z O) (restOf t)).isSome = true
  rw [FrontEntriesRef.entScan_isSome, hr]
  exact hvall

end Atoms

/-! ## The reference output per branch -/

section Out
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}

theorem goodOut_congr (hF : FrontOutRef.GridFacts S) {N : ℕ} {z : BitInput N} {g1 g2 : UnionGuess S z} (e : g1 = g2)
    (h1 : (g1.checkData g1.translation).schedule.all (FrontOutRef.callOkI (I := I)) = true)
    (h2 : (g2.checkData g2.translation).schedule.all (FrontOutRef.callOkI (I := I)) = true) (cap R Lg : ℕ) :
    FrontOutRef.goodOut S hF g1 h1 cap R Lg = FrontOutRef.goodOut S hF g2 h2 cap R Lg := by
  subst e; rfl

/-- **A rejected witness**: no decoded guess passes the checks. -/
theorem outRef_rej (hF : FrontOutRef.GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (N : ℕ) (x : BitInput N)
    (w : List Bool) (h : ∀ g, decodeGuess S x w = some g → ¬ FrontOutRef.GoodG S g) :
    FrontOutRef.outRef S hF onset capF RF LgF N x w = FrontGate.rejOut := by
  unfold FrontOutRef.outRef
  rw [dif_neg]
  rintro ⟨-, g, hg, hG⟩
  exact h g hg hG

/-- Below the onset. -/
theorem outRef_below (hF : FrontOutRef.GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (N : ℕ) (x : BitInput N)
    (w : List Bool) (hN : N < onset) : FrontOutRef.outRef S hF onset capF RF LgF N x w = FrontGate.rejOut := by
  unfold FrontOutRef.outRef
  rw [dif_neg]
  rintro ⟨h, -⟩
  omega

/-- **A valid witness**: its guess passes the outer step's guards, the atom and sign checks; the output is the end's. -/
theorem outRef_valid (hF : FrontOutRef.GridFacts S) (onset : ℕ) (capF RF LgF : ℕ → ℕ) (N : ℕ) (x : BitInput N)
    (w : List Bool) (g : UnionGuess S x) (hd : decodeGuess S x w = some g) (hN : onset ≤ N)
    (hsz : UnionGuards S x g)
    (hat : PlanW3.AtomsOkG g) (hsg : (g.checkData g.translation).signsOk = true) :
    FrontOutRef.outRef S hF onset capF RF LgF N x w = FrontSemTW.endOut hF g (capF N) (RF N) (LgF N) := by
  unfold FrontOutRef.outRef FrontSemTW.endOut
  by_cases hall : (g.checkData g.translation).schedule.all (FrontOutRef.callOkI (I := I)) = true
  · have hc : onset ≤ N ∧ ∃ g', decodeGuess S x w = some g' ∧ FrontOutRef.GoodG S g' :=
      ⟨hN, g, hd, hsz, hat, hsg, hall⟩
    rw [dif_pos hc, dif_pos hall]
    exact goodOut_congr hF (Option.some.inj ((Classical.choose_spec hc.2).1.symm.trans hd)) _ _ _ _ _
  · rw [dif_neg hall, dif_neg]
    rintro ⟨-, g', hg', hG⟩
    have e : g' = g := Option.some.inj (hg'.symm.trans hd)
    subst e
    exact hall hG.2.2.2

end Out

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemDec

end
