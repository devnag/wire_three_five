import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemPath
import Proof.Wire_3_5.UnionMachine.FrontTop
import Proof.Wire_3_5.Front35.Top
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.UnionCodec
import Proof.Wire_3_5.UnionMachine.FrontDecode
import Proof.Wire_3_5.UnionMachine.FrontOutRef
import Proof.Wire_3_5.UnionMachine.FrontSelReq
import Proof.Wire_3_5.UnionMachine.FrontSemDec
import Proof.Wire_3_5.UnionMachine.FrontSemEnt
import Proof.Wire_3_5.UnionMachine.FrontSemTW
import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Wire_3_5.UnionMachine.FrontSemRunBase


noncomputable section


/-! # The front's semantic core (6): the front machine's run is the reference output (paper v2, §H.5)

On every input and witness past the onset, the front machine (`Front35.Top.topM`) runs to the reference output's bank
(`FrontOutRef.outRef`): below the onset the rejecting bank; a failing check (the walker's scan, the outer step's guards
decided by the cold front end, the entries, the atoms) the rejecting bank, which is the reference output there since no
decoded guess passes; otherwise the chain's guess decodes, and the end's bank is the reference output's.

Paper quantity of the main type: the front's output bank on every input and witness (`FrontAtW3.run`), at the PCPP
output of `H_Γ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 120000

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemRun
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open W3.NearCubicWires.RepairSource.Outer3

/-! ## The chain's tapes after phase 2 -/

section Pos
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  {mw : NearCubicGates.Close.Outer.MWSource} {kh : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (kh + 2))} {L : ℕ}
  {SV : NearCubicGates.Close.Outer.SuccinctVerifier H L} {a : PointwisePCPPAlgorithm} {cutoff D degree copies : ℕ}
  {delta : ℚ} (CN : ColdNativeW mw SV a cutoff D degree copies delta) (k : ℕ)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + Front35.Ph2.PH2 CN ≤ tf)

/-- **The chain's read tapes after phase 2** lie below the chain's regions; the PCPP word's is not the width's. -/
theorem top_pos :
    (2 + NL P ≤ (FrontTop.q1 P tf k hp1).val ∧
      (FrontTop.q1 P tf k hp1).val < 2 + NL P + (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN)) ∧
    (2 + NL P ≤ (FrontTop.o1 P tf k hp1 13).val ∧
      (FrontTop.o1 P tf k hp1 13).val < 2 + NL P + (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN)) ∧
    (2 + NL P ≤ (Front35.Top.po2 P tf CN k hp2).val ∧
      (Front35.Top.po2 P tf CN k hp2).val < 2 + NL P + (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN)) ∧
    Front35.Top.po2 P tf CN k hp2 ≠ FrontTop.q1 P tf k hp1 := by
  have vq : (FrontTop.q1 P tf k hp1).val = 2 + NL P + (1 + 4 + (FrontWidth.qOut k).val) := FrontPh1.qT_val P tf k 1 hp1
  have vo : ∀ j : Fin FrontOracle.OS, (FrontTop.o1 P tf k hp1 j).val = 2 + NL P + (1 + 4 + FrontWidth.QT k + j.val) :=
    fun j => FrontPh1.orT_val P tf k 1 hp1 j
  have hqo := (FrontWidth.qOut k).isLt
  have hPH1 : FrontPh1.PH1 k = 4 + FrontWidth.QT k + FrontOracle.OS + FrontSizeStage.ST := rfl
  have hOS : FrontOracle.OS = 1421 := rfl
  have hPH2 : Front35.Ph2.PH2 CN = FrontOracle.OS + 4 + CN.tapes := rfl
  have key : (2 + NL P + (1 + FrontPh1.PH1 k) ≤ (Front35.Top.po2 P tf CN k hp2).val) ∧
      (Front35.Top.po2 P tf CN k hp2).val < 2 + NL P + (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN) := by
    unfold Front35.Top.po2 Front35.Ph2.poT Front35.Ph2.slK sl
    cases hj : Front35.Ph2.shK P tf CN (1 + FrontPh1.PH1 k) hp2 (CN.cacheSlots 0) with
    | none =>
      simp only [Option.getD_none, rg_val]
      have := (CN.cacheSlots 0).isLt
      unfold Front35.Ph2.oK
      constructor <;> omega
    | some b =>
      simp only [Option.getD_some]
      rcases Front35.Ph2.shK_some P tf CN (1 + FrontPh1.PH1 k) hp2 _ b hj with ⟨_, u⟩ | ⟨_, u⟩ <;> subst u
      · rw [Front35.Ph2.cx_val]; constructor <;> omega
      · rw [Front35.Ph2.td_val]; constructor <;> omega
  have v13 := vo 13
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, key.2⟩, fun e => ?_⟩
  have := congrArg Fin.val e
  omega

end Pos

/-! ## The chain after phase 2, per branch -/

section Rest
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt (esOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath (KcOf KdOf validCost PathCaps)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}

open Classical in
/-- **The chain's cost after phase 2** at a decoded pair: per branch (entries, atoms, the valid path). -/
noncomputable def restCostOf {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
    (Kw Dw De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT : ℕ) {d : ℕ} (c : Plan.C1At d) {N : ℕ}
    (x : BitInput N) (b : Bool) (t : List Bool) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) : ℕ :=
  let q := S.width N
  let sys := (S.pcppOf x O).systematicBits
  let aux := (S.pcppOf x O).auxiliaryBits
  let cb := (S.pcppOf x O).clauseBits
  let En := (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q
  if (entScan En (restOf t)).isSome = false then
    rejECost h0 h1 Dw Kw I.descDeg Kb Db Cδ q sys aux cb (List.ofFn x) (restOf t)
  else if FrontAtomLoop.verdictOf q (FrontAtomStageL.capP (List.ofFn x).length) ((q + 1) ^ I.descDeg) (modeOf b) En
      (payOf (restOf t) En) ≠ 0 then
    rejACost (modeOf b) h0 h1 Dw Kw I.descDeg Kb Db Cδ q sys aux cb (List.ofFn x) (restOf t)
  else if hpre : (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf (gOf S x b O (restOf t))) then
    validCost (gOf S x b O (restOf t)) h0 h1 Kw Dw I.descDeg De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c hpre
      (List.ofFn x) ((restOf t).length - (FrontTW.entsW (esOf (gOf S x b O (restOf t)))).length)
  else 0

end Rest

/-! ## The reference output on each branch after phase 2 -/

section OutB
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}

/-- The decoded guess's pair is the machine's. -/
theorem pair_eq {N : ℕ} {x : BitInput N} {b : Bool} {t : List Bool}
    {O : NearCubicGates.Close.Outer.OuterGuess (S.width N)}
    (hdec : NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some O)
    {g : UnionGuess S x} (hd : decodeGuess S x (b :: t) = some g) : g.pair = O :=
  Option.some.inj ((FrontSemDec.pair_of hd).symm.trans hdec)

/-- The request's arity is the width `q(N)` once the width reaches the PCPP's minimum arity. -/
theorem request_arity {N : ℕ} (x : BitInput N) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N))
    (hmin : S.pcppAlg.minimumArity ≤ S.width N) : (S.request x O).arity = S.width N := by
  unfold UnionSetup.request
  rw [requestAt_of S.mw S.SV S.pcppAlg (Nat.log 2 N) O hmin]
  rfl

/-- The entry count at the machine's width. -/
theorem entN_eq {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (hsS : ∀ q, S.gridSize q = Ledger.rowBSparse h0 h1 2 Cδ q) {N : ℕ} (x : BitInput N)
    (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (harity : (S.request x O).arity = S.width N) :
    entN S x O = ((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
      Ledger.rowBSparse h0 h1 2 Cδ (S.width N) := by
  unfold entN; rw [hsS]; exact congrArg _ (congrArg _ harity)

/-- **The entries fail**: no decoded guess passes. -/
theorem rejE_bad {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (hsS : ∀ q, S.gridSize q = Ledger.rowBSparse h0 h1 2 Cδ q)
    {N : ℕ} (x : BitInput N) (b : Bool) (t : List Bool) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N))
    (hdec : NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some O)
    (harity : (S.request x O).arity = S.width N)
    (hE : (entScan (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
      Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (restOf t)).isSome = false) :
    ∀ g, decodeGuess S x (b :: t) = some g → ¬ FrontOutRef.GoodG S g := by
  intro g hd hG
  have e := pair_eq hdec hd
  subst e
  have hs := FrontSemDec.signs_of hd
  rw [entN_eq h0 h1 Cδ hsS x g.pair harity] at hs
  have : (g.checkData g.translation).signsOk = false := by rw [← hs]; exact hE
  rw [hG.2.2.1] at this
  exact Bool.noConfusion this

/-- **An atom fails**: no decoded guess passes. -/
theorem rejA_bad {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (hsS : ∀ q, S.gridSize q = Ledger.rowBSparse h0 h1 2 Cδ q)
    {N : ℕ} (x : BitInput N) (b : Bool) (t : List Bool) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N))
    (hdec : NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some O)
    (harity : (S.request x O).arity = S.width N) (hx : (restOf t).length + 1 ≤ N)
    (hv : FrontAtomLoop.verdictOf (S.width N) (FrontAtomStageL.capP N)
      ((S.width N + 1) ^ I.descDeg) (modeOf b)
      (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N))
      (payOf (restOf t) (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) *
        Ledger.rowBSparse h0 h1 2 Cδ (S.width N))) ≠ 0) :
    ∀ g, decodeGuess S x (b :: t) = some g → ¬ FrontOutRef.GoodG S g := by
  intro g hd hG
  have e := pair_eq hdec hd
  subst e
  have hm := FrontSemDec.mode_of hd
  obtain ⟨k, hr⟩ := FrontSemDec.rest_of hd
  have hg : ∀ e ∈ entsG g, e.1 ∈ gridSet := (signs_iff g _).1 hG.2.2.1
  have hEq := entN_eq h0 h1 Cδ hsS x g.pair harity
  rw [FrontSemDec.entN_eq] at hEq
  have hrest := (restAfter_enc (entsG g) (List.replicate k false) hg).1
  change restOf t = _ at hr
  rw [← hEq, hr] at hv
  change modeOf b = g.mode at hm
  rw [hm, ← harity] at hv
  apply FrontSemDec.atoms_bad g (List.replicate k false) hg (FrontAtomStageL.capP N) _ (fun j hj => ?_) hv hG.2.1
  have hl := pay_le _ _ _ hrest j hj
  have hx' : (((entsG g).map encE).flatten ++ List.replicate k false).length + 1 ≤ N := by rw [← hr]; exact hx
  exact (FrontAtomStageL.capP_covers N _ (by omega)).1

end OutB

/-! ## The chain after phase 2 at a decoded pair -/

section RestRun
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt (esOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath (KcOf KdOf validCost PathCaps)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}
  (P : FusedPrimitive I) (tf : ℕ) {cutoff D copies : ℕ} {delta : ℚ}
  (CN : ColdNativeW S.mw S.SV S.pcppAlg cutoff D S.G copies delta) (k Dw De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + Front35.Ph2.PH2 CN ≤ tf)
  (hr : ∀ m : Mode, (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN) + FrontRest.RS m Dw I.descDeg I.carrierDeg De Dt c ≤ tf)

/-- **The chain after phase 2 at a decoded pair passing the outer step's guards**: the reference output's bank. -/
theorem rest_run (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db Cδ Ce Ct cr Vb aV bV aT bT crT KT AT : ℕ)
    (hpA : S.parityAtom = unionParityAtom) (hcA : S.constAtom = unionConstAtom) (hname : 2 ≤ I.nameCount)
    (hd4 : 4 ≤ I.descDeg) (hF : FrontOutRef.GridFacts S) (hsS : ∀ q, S.gridSize q = Ledger.rowBSparse h0 h1 2 Cδ q)
    (hmS : ∀ q, S.gridMass q = (Ledger.rowBLambda h0 h1 2 q : ℚ)) (hbV : 1 ≤ bV) (hbT : 1 ≤ bT)
    (hv0 : S.params.v0 = (aV : ℚ) / bV) (hτ : S.params.threshold = (aT : ℚ) / bT)
    (hr' : ∀ q, B.rOf q = Ledger.rowBr cr q)
    (onset : ℕ) (capF RF LgF : ℕ → ℕ) {N : ℕ} (x : BitInput N) (b : Bool) (t : List Bool)
    (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (hN : onset ≤ N) (hsc : scanOK t = true)
    (hdec : NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some O)
    (hsz : ∀ g : UnionGuess S x, g.pair = O → UnionGuards S x g)
    (harity : (S.request x O).arity = S.width N)
    (hStar : I.StarAt (S.width N)) (hFit : B.FitsAt (S.width N))
    (hcapF : capF N = FrontTail.capOf crT KT AT (S.width N))
    (hRF : RF N = FrontTail.rOf crT KT AT (S.width N))
    (hLgF : LgF N = FrontTail.rOf crT KT AT (S.width N) + 1)
    (hx : (restOf t).length + 1 ≤ (List.ofFn x).length) (hq3 : S.width N + 3 ≤ 2 * (List.ofFn x).length + 2)
    (hnums : FrontCh3P.NumsCaps (2 * (Kw * (S.width N + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ (S.width N)
      (S.pcppOf x O).systematicBits (S.pcppOf x O).auxiliaryBits (S.pcppOf x O).clauseBits)
    (hcaps : ∀ g : UnionGuess S x, g.pair = O → PlanW3.AtomsOkG g → (g.checkData g.translation).signsOk = true →
      PathCaps g h0 h1 Kw Dw I.descDeg De Ce Dt Ct Kb Db Cδ cr Vb c ∧
      FrontSemTW.EndCaps h0 h1 g (Kw * (g.q + 1) ^ Dw) Kb Db Cδ aV bV aT bT crT KT AT ∧
      (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf g))
    (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN))
    (hX : A (FrontPh1.xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H (FrontPh1.xT P tf) = 0)
    (hqT : A (FrontTop.q1 P tf k hp1) = List.replicate (S.width N) true ∧ H (FrontTop.q1 P tf k hp1) = 0)
    (hR : A (FrontTop.o1 P tf k hp1 13) = RepairOrdinary.frame (restOf t) ∧ H (FrontTop.o1 P tf k hp1 13) = 0)
    (hp : A (Front35.Top.po2 P tf CN k hp2) = pcppOutput (S.request x O) (S.pcppOf x O) ∧
      H (Front35.Top.po2 P tf CN k hp2) = 0) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (Front35.Top.restAt P tf CN k Dw I.descDeg I.carrierDeg De Dt c hp1 hp2 hr (modeOf b) Kw Kb Db true ζ Cδ
          Ce Ct cr (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT)
        (restCostOf h0 h1 Kw Dw De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c x b t O) H A H' A' ∧
      (∀ i, H' (lp P tf i) = bankH P ((FrontOutRef.outRef S hF onset capF RF LgF N x (b :: t)).kept P) i) ∧
      (∀ i, A' (lp P tf i) = bankA P (FrontOutRef.outRef S hF onset capF RF LgF N x (b :: t)).cap
        (FrontOutRef.outRef S hF onset capF RF LgF N x (b :: t)).R (FrontOutRef.outRef S hF onset capF RF LgF N x (b :: t)).Lg
        ((FrontOutRef.outRef S hF onset capF RF LgF N x (b :: t)).kept P) i) := by
  obtain ⟨hqL, hrL, hpL, hpq⟩ := top_pos P tf CN k hp1 hp2
  have hpw : A (Front35.Top.po2 P tf CN k hp2) = natWord 3 ++ natWord (S.pcppOf x O).systematicBits ++
      natWord (S.pcppOf x O).auxiliaryBits ++ natWord (S.pcppOf x O).clauseBits ++
      (FrontSemPO.sbOf (S.request x O) (S.pcppOf x O) ++ natWord (FrontSemPO.litsOf (S.request x O) (S.pcppOf x O)).length ++
        (FrontSemPO.litsOf (S.request x O) (S.pcppOf x O)).flatMap natWord) := by
    rw [hp.1, FrontSemPO.pcppOutput_poWord]; unfold C1Cnt.poWord; simp only [List.append_assoc]
  by_cases hE : (entScan (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (restOf t)).isSome = false
  · -- the entries fail
    have ho := FrontSemDec.outRef_rej hF onset capF RF LgF N x (b :: t) (rejE_bad h0 h1 Cδ hsS x b t O hdec harity hE)
    obtain ⟨H', A', s, hH, hA⟩ := FrontRest.rest_rejE P tf (modeOf b) Dw I.descDeg I.carrierDeg De Dt c
      (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN) (hr (modeOf b)) (FrontTop.q1 P tf k hp1) (FrontTop.o1 P tf k hp1 13)
      (Front35.Top.po2 P tf CN k hp2) Kw h0 h1 Kb Db true Cδ Ce Ct cr (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT)
      crT KT AT (S.width N) (S.pcppOf x O).systematicBits (S.pcppOf x O).auxiliaryBits
      (S.pcppOf x O).clauseBits (List.ofFn x) (restOf t) _ H A hPr hqL hrL hpL hX hqT hR ⟨hpw, hp.2⟩ hx hnums hE
    refine ⟨H', A', ?_, fun i => by rw [ho, FrontGate.rejOut_kept]; exact hH i,
      fun i => by rw [ho, FrontGate.rejOut_kept]; exact hA i⟩
    unfold restCostOf; simp only; rw [if_pos hE]; exact s
  have hE' : (entScan (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (restOf t)).isSome = true := by
    cases h : (entScan (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (restOf t)).isSome
    · exact absurd h hE
    · rfl
  obtain ⟨v, hrv, hvall⟩ : ∃ v, restAfter (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (restOf t) = some v ∧ v.all (fun b => !b) = true := by
    have e := hE'
    rw [FrontEntriesRef.entScan_isSome] at e
    revert e
    cases h : restAfter (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (restOf t) with
    | none => simp
    | some v => intro hv'; exact ⟨v, rfl, hv'⟩
  have hnv : 1 ≤ (S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits := by
    cases hl : ((S.pcppOf x O).clauses ⟨0, Nat.two_pow_pos _⟩).left with
    | positive i => have := i.isLt; omega
    | negative i => have := i.isLt; omega
  have hE1 : 1 ≤ (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by have := hnums.hs1; omega))
  by_cases hv : FrontAtomLoop.verdictOf (S.width N) (FrontAtomStageL.capP (List.ofFn x).length)
      ((S.width N + 1) ^ I.descDeg) (modeOf b) (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (payOf (restOf t) (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N))) ≠ 0
  · -- an atom fails
    have hxN : (restOf t).length + 1 ≤ N := by rw [List.length_ofFn] at hx; exact hx
    have ho := FrontSemDec.outRef_rej hF onset capF RF LgF N x (b :: t)
      (rejA_bad h0 h1 Cδ hsS x b t O hdec harity hxN (by rw [List.length_ofFn] at hv; exact hv))
    have hA := FrontSemPath.atomsOK_of (restOf t) v _ (List.ofFn x).length (S.width N) hrv hE1 hx hq3
    obtain ⟨H', A', s, hH, hA'⟩ := FrontRest.rest_rejA P tf (modeOf b) Dw I.descDeg I.carrierDeg De Dt c
      (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN) (hr (modeOf b)) (FrontTop.q1 P tf k hp1)
      (FrontTop.o1 P tf k hp1 13) (Front35.Top.po2 P tf CN k hp2) Kw h0 h1 Kb Db true Cδ Ce Ct cr
      (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT (S.width N) (S.pcppOf x O).systematicBits
      (S.pcppOf x O).auxiliaryBits (S.pcppOf x O).clauseBits (List.ofFn x) (restOf t) _ _ _ _ _ H A hPr hqL hrL hpL
      hX hqT hR ⟨hpw, hp.2⟩ hx hnums hE' hA hv
    refine ⟨H', A', ?_, fun i => by rw [ho, FrontGate.rejOut_kept]; exact hH i,
      fun i => by rw [ho, FrontGate.rejOut_kept]; exact hA' i⟩
    unfold restCostOf; simp only; rw [if_neg hE, if_pos hv]; exact s
  -- the valid path
  have hv0' : FrontAtomLoop.verdictOf (S.width N) (FrontAtomStageL.capP (List.ofFn x).length)
      ((S.width N + 1) ^ I.descDeg) (modeOf b) (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) (payOf (restOf t) (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N))) = 0 := by
    by_contra hne; exact hv hne
  have hEN := entN_eq h0 h1 Cδ hsS x O harity
  have hvA : FrontAtomLoop.verdictOf (S.request x O).arity (FrontAtomStageL.capP (List.ofFn x).length)
      ((S.width N + 1) ^ I.descDeg) (modeOf b) (entN S x O) (payOf (restOf t) (entN S x O)) = 0 := by
    rw [harity, hEN]; exact hv0'
  obtain ⟨hd, hsg⟩ := FrontSemDec.valid_of b t hsc O hdec (by rw [hEN]; exact hE') _ _ hvA
  set g := gOf S x b O (restOf t) with hgdef
  have hg : ∀ e ∈ entsG g, e.1 ∈ gridSet := (signs_iff g _).1 hsg
  obtain ⟨kz, hrz⟩ := FrontSemDec.rest_of hd
  change restOf t = _ at hrz
  have hEg : (((S.pcppOf x O).systematicBits + (S.pcppOf x O).auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ (S.width N)) = (entsG g).length := by rw [← hEN]; exact FrontSemDec.entN_eq g
  have hvg : FrontAtomLoop.verdictOf g.q (FrontAtomStageL.capP (List.ofFn x).length) ((g.q + 1) ^ I.descDeg) g.mode
      (entsG g).length (payOf (((entsG g).map encE).flatten ++ List.replicate kz false) (entsG g).length) = 0 := by
    have e := hv0'
    rw [hEg, hrz, ← harity] at e
    exact e
  have hrest := (restAfter_enc (entsG g) (List.replicate kz false) hg).1
  have hat : PlanW3.AtomsOkG g := FrontSemDec.atoms_ok g (List.replicate kz false) hg _ _ (fun j hj => by
    have hl := pay_le _ _ _ hrest j hj
    have hx' : (((entsG g).map encE).flatten ++ List.replicate kz false).length + 1 ≤ (List.ofFn x).length := by
      rw [← hrz]; exact hx
    exact (FrontAtomStageL.capP_covers _ _ (by omega)).1) hvg
  have ho := FrontSemDec.outRef_valid hF onset capF RF LgF N x (b :: t) g hd hN (hsz g rfl) hat hsg
  obtain ⟨hPC, hEC, hpre⟩ := hcaps g rfl hat hsg
  have hrr : restOf t = FrontTW.entsW (esOf g) ++
      List.replicate ((restOf t).length - (FrontTW.entsW (esOf g)).length) false := by
    have e1 : FrontTW.entsW (esOf g) = ((entsG g).map encE).flatten := FrontSemEnt.entsW_esOf g hg
    have e2 : (restOf t).length - (FrontTW.entsW (esOf g)).length = kz := by
      rw [hrz, e1, List.length_append, List.length_replicate]; omega
    rw [e2, e1]; exact hrz
  obtain ⟨H', A', s, hH, hA⟩ := FrontSemPath.valid_rest P tf Dw I.descDeg De Dt c g
    (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN) (hr (modeOf b)) (FrontTop.q1 P tf k hp1) (FrontTop.o1 P tf k hp1 13)
    (Front35.Top.po2 P tf CN k hp2) Kw h0 h1 Kb Db Cδ Ce Ct cr Vb aV bV aT bT crT KT AT hpA hcA
    (by show I.StarAt (S.request x O).arity; rw [harity]; exact hStar)
    (by show B.FitsAt (S.request x O).arity; rw [harity]; exact hFit) hname hd4 hsg hat hF (hsS g.q) (hmS g.q) hbV hbT
    hv0 hτ (hr' g.q) hpre hPC hEC (List.ofFn x) ((restOf t).length - (FrontTW.entsW (esOf g)).length) H A hPr hqL hrL hpL
    hpq hX (by show A (FrontTop.q1 P tf k hp1) = List.replicate (S.request x O).arity true ∧ _; rw [harity]; exact hqT)
    (by rw [← hrr]; exact hR) ⟨by rw [hp.1]; rfl, hp.2⟩ (by rw [← hrr]; exact hx)
    (by show (S.request x O).arity + 3 ≤ _; rw [harity]; exact hq3)
    (by
      have e := hv0'
      rw [hrr, ← harity] at e
      exact e)
  have ecap : FrontTail.capOf crT KT AT g.q = capF N := by rw [hcapF]; exact congrArg _ harity
  have eR : FrontTail.rOf crT KT AT g.q = RF N := by rw [hRF]; exact congrArg _ harity
  have eL : RF N + 1 = LgF N := by rw [hLgF, hRF]
  rw [ecap, eR, eL] at hH hA
  refine ⟨H', A', ?_, fun i => by rw [ho]; exact hH i, fun i => by rw [ho]; exact hA i⟩
  unfold restCostOf; simp only; rw [if_neg hE, if_neg hv, dif_pos hpre]; exact s

end RestRun

/-! ## The front machine's run -/

section Top
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath (PathCaps)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I}
  (P : FusedPrimitive I) (tf : ℕ) (htf : 1 ≤ tf) {cutoff D copies : ℕ} {delta : ℚ}
  (CN : ColdNativeW S.mw S.SV S.pcppAlg cutoff D S.G copies delta) (k Ap G Dw De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
  (hp1 : 1 + FrontPh1.PH1 k ≤ tf) (hp2 : (1 + FrontPh1.PH1 k) + Front35.Ph2.PH2 CN ≤ tf)
  (hr : ∀ m : Mode, (1 + FrontPh1.PH1 k + Front35.Ph2.PH2 CN) + FrontRest.RS m Dw I.descDeg I.carrierDeg De Dt c ≤ tf)
  (C : ℕ) (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db Cδ Ce Ct cr Vb aV bV aT bT crT KT AT : ℕ)

/-- **The facts the front's run reads at an input length past the onset.** -/
structure TopFacts (capF RF LgF : ℕ → ℕ) (N : ℕ) : Prop where
  hW : S.width N = Ledger.nativeWidth k Ap N
  hmin : S.pcppAlg.minimumArity ≤ S.width N
  hlive : S.live = true
  hon : S.onset ≤ Nat.log 2 N
  hcut : cutoff ≤ Nat.log 2 N
  hcon : CN.onset ≤ Nat.log 2 N
  hStar : I.StarAt (S.width N)
  hFit : B.FitsAt (S.width N)
  ph1 : ∀ (x : BitInput N) (w : List Bool), w.length = N / 16 → FrontTop.Ph1OK k Ap (List.ofFn x) w
  hq3 : S.width N + 3 ≤ 2 * N + 2
  nums : ∀ (x : BitInput N) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)), N = 2 ^ Nat.log 2 N →
    O.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound S.G (S.width N) →
      FrontCh3P.NumsCaps (2 * (Kw * (S.width N + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ (S.width N)
        (S.pcppOf x O).systematicBits (S.pcppOf x O).auxiliaryBits (S.pcppOf x O).clauseBits
  caps : ∀ (x : BitInput N) (g : UnionGuess S x), UnionGuards S x g → PlanW3.AtomsOkG g →
    (g.checkData g.translation).signsOk = true →
    PathCaps g h0 h1 Kw Dw I.descDeg De Ce Dt Ct Kb Db Cδ cr Vb c ∧
      FrontSemTW.EndCaps h0 h1 g (Kw * (g.q + 1) ^ Dw) Kb Db Cδ aV bV aT bT crT KT AT ∧
      (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf g)
  hcapF : capF N = FrontTail.capOf crT KT AT (S.width N)
  hRF : RF N = FrontTail.rOf crT KT AT (S.width N)
  hLgF : LgF N = FrontTail.rOf crT KT AT (S.width N) + 1

open Classical in
/-- **The front's cost on a witness** (per branch). -/
noncomputable def costOf {N : ℕ} (x : BitInput N) (w : List Bool) : ℕ :=
  if N < C then 2 * N + 1 + 1 + (3 + 1)
  else if FrontOracleField.okOf w = false then 4 * C + 1 + 1 + ((FrontTop.ph1C k Ap G (List.ofFn x) w + 1 + (3 + 1)) + 1)
  else if CN.passed (List.ofFn x) (payload w.tail) = false then
    4 * C + 1 + 1 + ((FrontTop.ph1C k Ap G (List.ofFn x) w + 1 + ((Front35.Top.ph2C CN x w + 1 + (3 + 1)) + 1)) + 1)
  else match NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload w.tail) with
    | none => 0
    | some O =>
      4 * C + 1 + 1 + ((FrontTop.ph1C k Ap G (List.ofFn x) w + 1 + ((Front35.Top.ph2C CN x w + 1 +
        ((restCostOf h0 h1 Kw Dw De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c x (w.headD false) w.tail O + 1)
          + 1)) + 1)) + 1)

/-- **A passing guess passes the cold front end**: the guards of a decoded guess are the cold front end's `Passes`. -/
theorem passed_of_guards {N : ℕ} (hcut : cutoff ≤ Nat.log 2 N) (hcon : CN.onset ≤ Nat.log 2 N)
    (x : BitInput N) (b : Bool) (t : List Bool) (g : UnionGuess S x) (hd : decodeGuess S x (b :: t) = some g)
    (hG : UnionGuards S x g) : CN.passed (List.ofFn x) (payload t) = true := by
  obtain ⟨-, hN, hon, hsrc, hpf, hfit, hcheck⟩ := hG
  have h1 := FrontSemDec.pair_of hd
  rw [List.tail_cons] at h1
  have hdec : NearCubicGates.Close.Worker.Decodes (S.width N) (payload t) g.pair :=
    (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf_iff_decodes (S.width N) (payload t) g.pair).1 h1
  have hP : Passes S.mw S.SV cutoff CN.onset S.G x (payload t) :=
    ⟨hN, hcut, hcon, S.onset_sv.trans hon, g.pair, hdec, hsrc, hpf, hfit, hcheck⟩
  exact (CN.passed_iff x (payload t)).2 hP

/-- **The front machine's run on every input and witness**: the reference output's bank. -/
theorem top_run (hpA : S.parityAtom = unionParityAtom) (hcA : S.constAtom = unionConstAtom) (hname : 2 ≤ I.nameCount)
    (hd4 : 4 ≤ I.descDeg) (hF : FrontOutRef.GridFacts S) (hsS : ∀ q, S.gridSize q = Ledger.rowBSparse h0 h1 2 Cδ q)
    (hmS : ∀ q, S.gridMass q = (Ledger.rowBLambda h0 h1 2 q : ℚ)) (hbV : 1 ≤ bV) (hbT : 1 ≤ bT)
    (hv0 : S.params.v0 = (aV : ℚ) / bV) (hτ : S.params.threshold = (aT : ℚ) / bT)
    (hr' : ∀ q, B.rOf q = Ledger.rowBr cr q) (capF RF LgF : ℕ → ℕ) {N : ℕ} (x : BitInput N)
    (w : List Bool) (hw : w.length = N / 16)
    (hT : C ≤ N → TopFacts (S := S) CN k Ap Dw De Dt c Kw h0 h1 Kb Db Cδ Ce Ct cr Vb aV bV aT bT crT KT AT capF RF LgF N) :
    ∃ (Hf : Fin (NW P tf) → ℕ) (Af : Fin (NW P tf) → List Bool),
      Step (Front35.Top.topM P tf htf CN k Ap G Dw I.descDeg I.carrierDeg De Dt c hp1 hp2 hr C Kw Kb Db true ζ Cδ Ce Ct cr
        (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT)
        (costOf (S := S) CN k Ap G Dw De Dt c C Kw h0 h1 Kb Db Cδ Ce Ct cr Vb aV bV aT bT crT KT AT x w) (fun _ => 0)
        (entryA x w) Hf Af ∧
      (∀ i, Hf (lp P tf i) = bankH P ((FrontOutRef.outRef S hF C capF RF LgF N x w).kept P) i) ∧
      (∀ i, Af (lp P tf i) = bankA P (FrontOutRef.outRef S hF C capF RF LgF N x w).cap
        (FrontOutRef.outRef S hF C capF RF LgF N x w).R (FrontOutRef.outRef S hF C capF RF LgF N x w).Lg
        ((FrontOutRef.outRef S hF C capF RF LgF N x w).kept P) i) := by
  by_cases hN : N < C
  · obtain ⟨H', A', s, hH, hA⟩ := Front35.Top.top_gate P tf htf CN k Ap G Dw I.descDeg I.carrierDeg De Dt c hp1 hp2 hr C
      Kw Kb Db true ζ Cδ Ce Ct cr (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT x w hN
    have ho := FrontSemDec.outRef_below hF C capF RF LgF N x w hN
    refine ⟨H', A', ?_, fun i => by rw [ho, FrontGate.rejOut_kept]; exact hH i,
      fun i => by rw [ho, FrontGate.rejOut_kept]; exact hA i⟩
    unfold costOf; rw [if_pos hN]; exact s
  have hCN : C ≤ N := by omega
  have TF := hT hCN
  have h1' := TF.ph1 x w hw
  by_cases hO : FrontOracleField.okOf w = false
  · obtain ⟨H', A', s, hH, hA⟩ := Front35.Top.top_rejO P tf htf CN k Ap G Dw I.descDeg I.carrierDeg De Dt c hp1 hp2 hr C
      Kw Kb Db true ζ Cδ Ce Ct cr (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT x w hCN h1' hO
    have ho := FrontSemDec.outRef_rej hF C capF RF LgF N x w (fun g hd _ => by
      have := FrontSemDec.okOf_of hd; rw [hO] at this; exact Bool.noConfusion this)
    refine ⟨H', A', ?_, fun i => by rw [ho, FrontGate.rejOut_kept]; exact hH i,
      fun i => by rw [ho, FrontGate.rejOut_kept]; exact hA i⟩
    unfold costOf; rw [if_neg hN, if_pos hO]; exact s
  have hO' : FrontOracleField.okOf w = true := by
    cases h : FrontOracleField.okOf w
    · exact absurd h hO
    · rfl
  obtain ⟨b, t, rfl⟩ : ∃ b t, w = b :: t := by
    cases w with
    | nil => exact absurd hO' (by simp [FrontOracleField.okOf])
    | cons b t => exact ⟨b, t, rfl⟩
  have hsc : scanOK t = true := hO'
  by_cases hpas : CN.passed (List.ofFn x) (payload (b :: t).tail) = false
  · obtain ⟨H', A', s, hH, hA⟩ := Front35.Top.top_rejP P tf htf CN k Ap G Dw I.descDeg I.carrierDeg De Dt c hp1 hp2 hr C
      Kw Kb Db true ζ Cδ Ce Ct cr (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT x (b :: t) hCN h1' hO' hpas
    have ho := FrontSemDec.outRef_rej hF C capF RF LgF N x (b :: t) (fun g hd hG => by
      have := passed_of_guards CN TF.hcut TF.hcon x b t g hd hG.1
      change CN.passed (List.ofFn x) (payload t) = false at hpas
      rw [hpas] at this; exact Bool.noConfusion this)
    refine ⟨H', A', ?_, fun i => by rw [ho, FrontGate.rejOut_kept]; exact hH i,
      fun i => by rw [ho, FrontGate.rejOut_kept]; exact hA i⟩
    unfold costOf; rw [if_neg hN, if_neg hO, if_pos hpas]; exact s
  have hpas' : CN.passed (List.ofFn x) (payload t) = true := by
    cases h : CN.passed (List.ofFn x) (payload t)
    · exact absurd h hpas
    · rfl
  obtain ⟨hNd, -, -, -, O, hdecs, hsrc, hpf, hfit, hcheck⟩ := (CN.passed_iff x (payload t)).1 hpas'
  have hdec : NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some O :=
    (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf_iff_decodes _ _ _).2 hdecs
  have hguard : ∀ g : UnionGuess S x, g.pair = O → UnionGuards S x g := fun g e => by
    subst e; exact ⟨TF.hlive, hNd, TF.hon, hsrc, hpf, hfit, hcheck⟩
  have harity : (S.request x O).arity = S.width N := request_arity x O TF.hmin
  have hx : (restOf t).length + 1 ≤ (List.ofFn x).length := by
    rw [List.length_ofFn]
    have h1 : (restOf t).length ≤ t.length := by unfold restOf; rw [List.length_drop]; omega
    have h2 : (b :: t).length = t.length + 1 := rfl
    have h3 : N / 16 ≤ N := Nat.div_le_self _ _
    omega
  have hq3 : S.width N + 3 ≤ 2 * (List.ofFn x).length + 2 := by rw [List.length_ofFn]; exact TF.hq3
  have hWl : Ledger.nativeWidth k Ap (List.ofFn x).length = S.width N := by
    rw [List.length_ofFn]; exact TF.hW.symm
  have T := Front35.Top.top_rest P tf htf CN k Ap G Dw I.descDeg I.carrierDeg De Dt c hp1 hp2 hr C Kw Kb Db true ζ Cδ Ce Ct
    cr (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT x (b :: t) hCN h1' hO' hpas' O hdecs (FrontDecode.modeOf b) rfl
    (fun H' A' => (∀ i, H' (lp P tf i) = bankH P ((FrontOutRef.outRef S hF C capF RF LgF N x (b :: t)).kept P) i) ∧
      (∀ i, A' (lp P tf i) = bankA P (FrontOutRef.outRef S hF C capF RF LgF N x (b :: t)).cap
        (FrontOutRef.outRef S hF C capF RF LgF N x (b :: t)).R (FrontOutRef.outRef S hF C capF RF LgF N x (b :: t)).Lg
        ((FrontOutRef.outRef S hF C capF RF LgF N x (b :: t)).kept P) i))
    (restCostOf h0 h1 Kw Dw De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c x b t O)
    (fun H A hPr hX hq hR hp => rest_run P tf CN k Dw De Dt c hp1 hp2 hr Kw h0 h1 Kb Db Cδ Ce Ct cr Vb aV bV aT
      bT crT KT AT hpA hcA hname hd4 hF hsS hmS hbV hbT hv0 hτ hr' C capF RF LgF x b t O hCN hsc hdec hguard harity
      TF.hStar TF.hFit TF.hcapF TF.hRF TF.hLgF hx hq3 (TF.nums x O hNd hpf)
      (fun g ho hat hsg => TF.caps x g (hguard g ho) hat hsg)
      H A hPr hX (by rw [hWl] at hq; exact hq) hR hp)
  obtain ⟨H', A', s, hQ⟩ := T
  refine ⟨H', A', ?_, hQ.1, hQ.2⟩
  unfold costOf; rw [if_neg hN, if_neg hO]
  simp only [List.tail_cons]
  rw [if_neg (by rw [hpas']; decide), hdec]
  exact s

end Top

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemRun

end
