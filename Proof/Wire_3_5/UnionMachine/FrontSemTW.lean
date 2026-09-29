import Proof.Wire_3_5.UnionMachine.FrontCallOk
import Proof.Wire_3_5.UnionMachine.FrontRest
import Proof.Wire_3_5.UnionMachine.FrontSemEnt

/-! # C6 front, the semantic core (3): the table writer's data at a guess (P3:3672-3691)

At a decoded guess `g` (check data `D = g.checkData g.translation`) the chain leaves the table writer's ten sources:
the PCPP output word, the entries, the head `natWord q ++ [mode] ++ natWord 4`, the translation, the constant's code,
the fold's parity and carrier codes and envelope bits, and the all-ones flag strings. **`twD g deg`** is that data;
**`twRel`** (the sources hold `D`), **`twFlags`** (the flag strings are the envelope bits `fDI`, `fEI`: the atom test
passed, the parities and the constant are small), **`twHolds`** (the sources sit on the streams).

Paper quantity of the main types: the guess's check data as the table writer reads it. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt (esOf)

/-- `frame` on a concatenation. -/
theorem frame_app (u v : List Bool) : RepairOrdinary.frame (u ++ v) = PrimAsm.ParseNat.enc true u ++ RepairOrdinary.frame v := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    show true :: b :: RepairOrdinary.frame (u ++ v) = _
    rw [ih]
    simp [PrimAsm.ParseNat.enc, RepairOrdinary.Streaming.marks]

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- The variable count. -/
abbrev nvG : ℕ := g.pcpp.systematicBits + g.pcpp.auxiliaryBits

/-- **The table writer's data at a guess.** -/
noncomputable def twD (deg : ℕ) : TWData :=
  ⟨natWord g.q ++ [modeBit g.mode] ++ natWord 4, natListWord g.translation, natWord (CWConst.constCode g.mode),
    (List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).pw,
    (List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).cw, esOf g,
    List.replicate (nvG g * g.s) true, List.replicate (nvG g) true,
    (List.range (foldOf (g.checkData g.translation)).nv).map ((foldOf (g.checkData g.translation)).eb deg)⟩

variable {g}

/-- **The sources hold the guess's check data.** -/
theorem twRel (hpA : S.parityAtom = unionParityAtom) (hcA : S.constAtom = unionConstAtom) (deg : ℕ) :
    TWRel (g.checkData g.translation) (twD g deg) where
  hd := rfl
  tl := rfl
  cc := by
    show natWord (CWConst.constCode g.mode) = natWord (g.mode.code (S.constAtom g.mode g.q))
    rw [hcA, CWConst.constCode_eq]
  pcs X := FrontFoldSem.pcs_get (D := g.checkData g.translation) (by show S.parityAtom g.mode g.q = unionParityAtom g.mode g.q; rw [hpA]) X
  crs X := FrontFoldSem.crs_get (D := g.checkData g.translation) (by show S.parityAtom g.mode g.q = unionParityAtom g.mode g.q; rw [hpA]) X
  esx X a := by
    show ((esOf g).getD (X.val * g.s + a.val) (false, false, 0)).2.1 = _
    rw [FrontSemEnt.esOf_getD]; rfl
  esb X a := by
    show ((esOf g).getD (X.val * g.s + a.val) (false, false, 0)).1 = _
    rw [FrontSemEnt.esOf_getD]; rfl
  esc X a := by
    show ((esOf g).getD (X.val * g.s + a.val) (false, false, 0)).2.2 = _
    rw [FrontSemEnt.esOf_getD]; rfl

theorem getD_rep (n i : ℕ) (hi : i < n) : (List.replicate n true).getD i false = true := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

/-- **The flag strings are the envelope bits.** -/
theorem twFlags (hpA : S.parityAtom = unionParityAtom) (hd4 : 4 ≤ I.descDeg) (hat : PlanW3.AtomsOkG g) :
    TWFlags (g.checkData g.translation) (twD g I.carrierDeg) (FrontCallOk.fDI (I := I) g.mode g.q)
      (FrontCallOk.fEI (I := I)) where
  pf X := by
    show (List.replicate (nvG g) true).getD X.val false = _
    rw [getD_rep (nvG g) X.val X.isLt]
    symm
    unfold FrontCallOk.fDI
    rw [decide_eq_true_iff]
    show g.mode.descriptionBits (S.parityAtom g.mode g.q _) ≤ _
    rw [hpA]
    exact (unionParityAtom_descriptionBits_le _ _ _).trans (Nat.pow_le_pow_right (by omega) hd4)
  df X a := by
    show (List.replicate (nvG g * g.s) true).getD (X.val * g.s + a.val) false = _
    refine (getD_rep (nvG g * g.s) _ (FrontDecode.idx_lt X a)).trans ?_
    symm
    unfold FrontCallOk.fDI
    rw [decide_eq_true_iff]
    exact hat X a
  ef X := by
    rw [show (twD g I.carrierDeg).ef = (List.range (foldOf (g.checkData g.translation)).nv).map
      ((foldOf (g.checkData g.translation)).eb I.carrierDeg) from rfl,
      FrontFoldSem.efs_get (D := g.checkData g.translation) (by show S.parityAtom g.mode g.q = unionParityAtom g.mode g.q; rw [hpA])]
    apply Bool.eq_iff_iff.2
    rw [FrontFoldSem.envB_iff]
    unfold FrontCallOk.fEI
    exact (@decide_eq_true_iff _ (Classical.propDecidable _)).symm

end Guess

/-! ## The table writer on every guess (both verdicts) -/

section Sem2
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge (entryOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- The call table's entry words in the passes' order (no admissibility needed). -/
def twWords (D : UnionCheckData) : List Bool :=
  (myV D).flatMap (fun t => Entry.entryWord (entryOf 0 D.s t)) ++
    (myQ D).flatMap (fun t => Entry.entryWord (entryOf 1 D.s t)) ++
      (myMu D).flatMap (fun t => Entry.entryWord (entryOf 2 D.s t))

/-- **The table writer on any guess**: the entry words, then `OK = [schedule.all okR]` (twSem without the calls'
admissibility, for the rejecting verdict too). -/
theorem twSem2 (cap : ℕ) (src : Fin 11 → List Bool) (cl : Bool) (D : UnionCheckData) (d : TWData) (hr : TWRel D d)
    (fD : D.mode.Circuit D.q → Bool) (fE : Stars.Carrier D.q → Bool) (hf : TWFlags D d fD fE)
    (hd : d.Holds src) (Bn : ℕ) (hB : d.Bnd Bn) (v0 : Fin NR → ℕ) (hc : ClauseRegs cap d Bn v0) (hv : RdOK v0)
    (hC : decide (v0 rCDF ≠ 0) = fD D.const) (hSS : v0 rSS = D.s) (hSYS : v0 rSYS = D.pcpp.systematicBits)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hmr : MagRegs D Λ v0)
    (hPO : POLayout cap src v0 (litsD D) (2 ^ D.pcpp.clauseBits)) (hl : LitsOK cap d v0 (litsD D) (2 ^ D.pcpp.clauseBits))
    (cV cQ cM Rb : ℕ)
    (hcV : ∀ i < 2 ^ D.pcpp.clauseBits, 7 * litA (litsD D) i + 1 + 1 + (110 * (litA (litsD D) i * v0 rSS) +
      110 * litA (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS + costV Bn (posRegs (Function.update (Function.update v0 rL1
        (litB (litsD D) i)) rLIT (litA (litsD D) i))) + 120) + 1 + (7 * litB (litsD D) i + 1 + 1 +
          (110 * (litB (litsD D) i * v0 rSS) + 110 * litB (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS +
            costV Bn (posRegs (Function.update v0 rLIT (litB (litsD D) i))) + 120)) ≤ cV)
    (hcQ : ∀ i < 2 ^ D.pcpp.clauseBits, 7 * litA (litsD D) i + 1 + 1 + (110 * (litA (litsD D) i * v0 rSS) +
      110 * litA (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS + mbCost Bn (posRegs (Function.update (Function.update v0 rL1
        (litB (litsD D) i)) rLIT (litA (litsD D) i))) rMb (patQ 0) + 120) + 1 + (7 * litB (litsD D) i + 1 + 1 +
          (110 * (litB (litsD D) i * v0 rSS) + 110 * litB (litsD D) i + 110 * v0 rSS + 30 * v0 rSYS +
            mbCost Bn (posRegs (Function.update v0 rLIT (litB (litsD D) i))) rMb (patQ 0) + 120)) ≤ cQ)
    (hcM : ∀ i < 2 ^ D.pcpp.clauseBits, 100 * (litA (litsD D) i + 1) * (v0 rSS + 1) +
      100 * (litB (litsD D) i + 1) * (v0 rSS + 1) + costMu Bn (FrontTW.muRegs v0 (litA (litsD D) i) (litB (litsD D) i)) +
        100 ≤ cM)
    (hrd : ∀ x ∈ litsD D, rdCost x ≤ Rb ∧ 2 ^ (natBitLength x + 1) ≤ cap) (hT : v0 rT = 0) (hBc : v0 rBIG ≤ cap)
    (hMc : 2 ^ D.pcpp.clauseBits + 1 ≤ cap)
    (okR : PrimRequest → Bool)
    (hokV : ∀ (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (pat : Fin 4 → FrontTableRef.FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ FrontTableRef.cand D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (pat k)) →
      okR (D.vCall pos t) = okT D fD fE (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) false t)
    (hokM : ∀ (i : Fin (2 ^ D.pcpp.clauseBits)) (pat : Fin 4 → FrontTableRef.FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ FrontTableRef.cand D (posVar D.pcpp i 0) (posVar D.pcpp i 1) (pat k)) →
      okR (D.muCall i t) = okT D fD fE (posVar D.pcpp i 0) (posVar D.pcpp i 1) true t)
    (hlen : (twWords D).length + 30 * Bn + 41 ≤ cap) :
    WExec cap twP (ts src 0 [] (regsOf v0 Z4 Z4 Z4 1) cl)
      (ts src 0 (twWords D ++ [false]) (regsOf v0 Z4 Z4 Z4 (if D.schedule.all okR then 1 else 0)) cl)
      (3 * (60 * v0 rBIG + 250 + 18 * 2 ^ D.pcpp.clauseBits + 2 ^ D.pcpp.clauseBits * (2 * Rb + cV + cQ + cM + 8)) + 10) := by
  have hmass : D.mass ≠ 0 := by rw [hm]; exact_mod_cast (show Λ ≠ 0 by omega)
  have eV := accW_V_eq D d hr v0 Λ hm hΛ hs hsg hSS hSYS hmr
  have eQ := accW_Q_eq D d hr v0 Λ hm hΛ hs hsg hSS hSYS hmr
  have eM := accW_Mu_eq D d hr v0 Λ hm hΛ hs hsg hSS hmr
  have bV := accB_V_eq D d hr fD fE hf v0 hC hSS okR Λ hmr hSYS hokV
  have bQ := accB_Q_eq D d hr fD fE hf v0 hC hSS okR Λ hmr hSYS hokV
  have bM := accB_Mu_eq D d hr fD fE hf v0 hC hSS okR hokM
  have tw := twT cap src cl v0 hv hT hBc (litsD D) (2 ^ D.pcpp.clauseBits) hPO (WVof d v0) (WQof d v0) (WMof d v0)
    (bVof d v0) (bQof d v0) (bMof d v0) (30 * Bn + 40) cV cQ cM Rb
    (bodyV_ok cap src cl d hd Bn hB v0 hc (litsD D) _ hl cV hcV) (bodyQ_ok cap src cl d hd Bn hB v0 hc (litsD D) _ hl cQ hcQ)
    (bodyMu_ok cap src cl d hd Bn hB v0 hc (litsD D) _ hl cM hcM) hrd hMc
    (by rw [eV, eQ, eM]; unfold twWords at hlen; simp only [List.length_append] at hlen; omega)
  rw [eV, eQ, eM, bV, bQ, bM, ok_eq D hmass hs okR] at tw
  exact tw

end Sem2

/-! ## The sources, the registers, the layout at a guess -/

section Src
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The writer's streams from the ten sources (stream `0` the empty output). -/
def srcF (v : Fin 10 → List Bool) (j : Fin 11) : List Bool :=
  if h : j.val = 0 then [] else v ⟨j.val - 1, by have := j.isLt; omega⟩

theorem srcF_succ (v : Fin 10 → List Bool) (i : Fin 10) : srcF v i.succ = v i := by
  unfold srcF; simp

variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- **The chain's ten sources at a guess** (the valid path's `srcV`). -/
noncomputable def srcG (deg : ℕ) (tail : List Bool) : Fin 10 → List Bool :=
  FrontRest.srcV (pcppOutput (S.request z g.oracle) g.pcpp) (entsW (esOf g) ++ tail)
    (RepairOrdinary.frame (natWord g.q ++ [modeBit g.mode] ++ natWord 4)) (RepairOrdinary.frame (natListWord g.translation))
    (CWConst.constWord g.mode)
    (((List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).pw).flatMap
      RepairOrdinary.frame)
    (((List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).cw).flatMap
      RepairOrdinary.frame)
    (nvG g * g.s) (nvG g) ((List.range (foldOf (g.checkData g.translation)).nv).map
      ((foldOf (g.checkData g.translation)).eb deg))

/-- **The sources sit on the writer's streams.** -/
theorem twHolds (deg : ℕ) (tail : List Bool) : (twD g deg).Holds (srcF (srcG g deg tail)) where
  hd := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD, FrontTWKit.frItems]⟩
  tl := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD, FrontTWKit.frItems]⟩
  cc := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD, FrontTWKit.frItems, CWConst.constWord]⟩
  pc := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD, FrontTWKit.frItems, List.flatMap_def]⟩
  cr := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD, FrontTWKit.frItems, List.flatMap_def]⟩
  es := ⟨tail, by simp [srcF, srcG, FrontRest.srcV, twD]⟩
  df := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD]⟩
  pf := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD]⟩
  ef := ⟨[], by simp [srcF, srcG, FrontRest.srcV, twD]⟩

end Src

section Regs
open NearCubicWires.WireExponent3_5.FinalPass.Tm
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {g : UnionGuess S z} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

theorem numCap_ge (s Λ q sys aux cb : ℕ) :
    s * s * s * s + 1 ≤ numCap s Λ q sys aux cb ∧ Λ * Λ * (s * s) + 1 ≤ numCap s Λ q sys aux cb ∧
    Λ * (s * s * s) + Λ * (s * s * s) + 1 ≤ numCap s Λ q sys aux cb ∧
    Λ * Λ * Λ * s + Λ * Λ * Λ * s + 1 ≤ numCap s Λ q sys aux cb ∧ Λ * Λ * Λ * Λ + 1 ≤ numCap s Λ q sys aux cb ∧
    Λ * (s * s * s) + 1 ≤ numCap s Λ q sys aux cb ∧ s + 1 ≤ numCap s Λ q sys aux cb := by
  unfold numCap
  generalize 2 ^ (cb + 1) = p2
  generalize s * s * s * s = a1
  generalize Λ * Λ * (s * s) = a2
  generalize Λ * (s * s * s) = a3
  generalize Λ * Λ * Λ * s = a4
  generalize Λ * Λ * Λ * Λ = a5
  omega

theorem esOf_len (deg : ℕ) : (twD g deg).es.length = nvG g * g.s := FrontSemEnt.esOf_length g

/-- **The clause registers** after the numbers. -/
theorem clauseRegs (cap Kb Db Cδ deg : ℕ) (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q) (hnv : 1 ≤ nvG g)
    (hB1 : Kb * (g.q + 1) ^ Db + 1 ≤ cap)
    (hc : numCap (Ledger.rowBSparse h0 h1 2 Cδ g.q) (Ledger.rowBLambda h0 h1 2 g.q) g.q g.pcpp.systematicBits
      g.pcpp.auxiliaryBits g.pcpp.clauseBits ≤ cap) :
    ClauseRegs cap (twD g deg) (Kb * (g.q + 1) ^ Db)
      (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits) := by
  have hN := FrontPw.nV_out h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits
  have hs1 : g.s ≤ nvG g * g.s := Nat.le_mul_of_pos_left _ hnv
  have hnv' : 1 ≤ g.pcpp.systematicBits + g.pcpp.auxiliaryBits := hnv
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := numCap_ge (Ledger.rowBSparse h0 h1 2 Cδ g.q) (Ledger.rowBLambda h0 h1 2 g.q) g.q
    g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits
  refine ⟨⟨scr_numOut _ hN, hN.big, hN.zero _ (by decide), hN.zero _ (by decide), hN.zero _ (by decide),
    hN.zero _ (by decide), hN.zero _ (by decide), by rw [esOf_len]; simp [twD], hB1, ?_⟩,
    hN.zero _ (by decide), hN.zero _ (by decide), hN.zero _ (by decide), hN.zero _ (by decide), hN.zero _ (by decide),
    hN.zero _ (by decide), hN.zero _ (by decide), hN.zero _ (by decide), hN.zero _ (by decide), hN.zero _ (by decide),
    by rw [hN.ss, esOf_len, ← hsS]; exact hs1, ⟨by show 0 < ((List.range (nvG g)).map _).length; rw [List.length_map, List.length_range]; exact hnv,
      by show 0 < ((List.range (nvG g)).map _).length; rw [List.length_map, List.length_range]; exact hnv⟩, by rw [hN.ss]; exact c7.trans hc⟩
  rintro M (rfl | rfl | rfl | rfl | rfl | rfl)
  · rw [hN.ma]; exact c1.trans hc
  · rw [hN.mb]; exact c2.trans hc
  · rw [hN.mc]; exact c3.trans hc
  · rw [hN.md]; exact c4.trans hc
  · rw [hN.me]; exact c5.trans hc
  · rw [hN.mf]; exact c6.trans hc

end Regs

/-! ## The PCPP stream's layout and the clauses' variables -/

section Layout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {g : UnionGuess S z} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

theorem litsD_eq : litsD (g.checkData g.translation) = FrontSemPO.litsOf (S.request z g.oracle) g.pcpp :=
  (FrontSemPO.litsOf_eq g).symm

theorem po_eq (deg : ℕ) (tail : List Bool) :
    srcF (srcG g deg tail) sPO = natWord 3 ++ natWord g.pcpp.systematicBits ++ natWord g.pcpp.auxiliaryBits ++
      natWord g.pcpp.clauseBits ++ FrontSemPO.sbOf (S.request z g.oracle) g.pcpp ++
      natWord (litsD (g.checkData g.translation)).length ++ (litsD (g.checkData g.translation)).flatMap natWord ++ [] := by
  rw [List.append_nil, litsD_eq]
  show pcppOutput (S.request z g.oracle) g.pcpp = _
  rw [FrontSemPO.pcppOutput_poWord]
  rfl

/-- **The PCPP stream's layout** at a guess. -/
theorem poLayout (cap Kb Db Cδ deg : ℕ) (tail : List Bool)
    (c1 : natBitLength 3 + natBitLength g.pcpp.systematicBits + natBitLength g.pcpp.auxiliaryBits +
      natBitLength g.pcpp.clauseBits + natBitLength (2 * 2 ^ g.pcpp.clauseBits) + g.pcpp.systematicBits * g.q + 1 ≤ cap)
    (c2 : (pcppOutput (S.request z g.oracle) g.pcpp).length ≤ Kb * (g.q + 1) ^ Db)
    (c3 : 20 * (natBitLength 3 + natBitLength g.pcpp.systematicBits + natBitLength g.pcpp.auxiliaryBits +
      natBitLength g.pcpp.clauseBits + natBitLength (2 * 2 ^ g.pcpp.clauseBits)) + 16 * (g.pcpp.systematicBits * g.q) +
        110 ≤ Kb * (g.q + 1) ^ Db * 40 + 200) :
    POLayout cap (srcF (srcG g deg tail))
      (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
      (litsD (g.checkData g.translation)) (2 ^ g.pcpp.clauseBits) := by
  have hN := FrontPw.nV_out h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits
  have hl : (litsD (g.checkData g.translation)).length = 2 * 2 ^ g.pcpp.clauseBits := pairsOf_length _ _
  have hsb : (FrontSemPO.sbOf (S.request z g.oracle) g.pcpp).length = g.pcpp.systematicBits * g.q :=
    FrontSemPO.sbOf_length _ _
  refine ⟨⟨3, g.pcpp.systematicBits, g.pcpp.auxiliaryBits, g.pcpp.clauseBits,
    FrontSemPO.sbOf (S.request z g.oracle) g.pcpp, [], po_eq deg tail, by rw [hN.sq, hsb], by rw [hl, hsb]; exact c1,
    ?_, by rw [hl, hsb, hN.big]; exact c3⟩, hl, hN.mm⟩
  rw [hN.big]
  refine le_trans (le_of_eq ?_) c2
  rw [FrontSemPO.pcppOutput_poWord, ← litsD_eq]
  rfl

theorem litIdx_lt {n : ℕ} (l : SourceInterfaces.Literal n) : RepairRepresentation.literalIndex l < 2 * n := by
  cases l with
  | positive i => have := i.isLt; show 2 * i.val < 2 * n; omega
  | negative i => have := i.isLt; show 2 * i.val + 1 < 2 * n; omega

theorem litA_lt (i : ℕ) (hi : i < 2 ^ g.pcpp.clauseBits) :
    litA (litsD (g.checkData g.translation)) i < 2 * nvG g ∧ litB (litsD (g.checkData g.translation)) i < 2 * nvG g := by
  have e := pairsOf_get (fun i : Fin (2 ^ g.pcpp.clauseBits) => RepairRepresentation.literalIndex (g.pcpp.clauses i).left)
    (fun i => RepairRepresentation.literalIndex (g.pcpp.clauses i).right) ⟨i, hi⟩
  have ea : litA (litsD (g.checkData g.translation)) i =
      RepairRepresentation.literalIndex (g.pcpp.clauses ⟨i, hi⟩).left := e.1
  have eb : litB (litsD (g.checkData g.translation)) i =
      RepairRepresentation.literalIndex (g.pcpp.clauses ⟨i, hi⟩).right := e.2
  exact ⟨by rw [ea]; exact litIdx_lt _, by rw [eb]; exact litIdx_lt _⟩

theorem xok (cap deg : ℕ) (x : ℕ) (hx : x < nvG g) (hcap : nvG g * g.s + 1 ≤ cap) :
    XOK cap (twD g deg) g.s x := by
  have h1 : x * g.s + g.s ≤ nvG g * g.s := by
    have := Nat.mul_le_mul_right g.s (show x + 1 ≤ nvG g by omega)
    rw [Nat.add_mul, one_mul] at this; exact this
  have hr : ∀ (f : ℕ → List Bool), ((List.range (foldOf (g.checkData g.translation)).nv).map f).length = nvG g :=
    fun f => by rw [List.length_map, List.length_range]; rfl
  have hr2 : ((List.range (foldOf (g.checkData g.translation)).nv).map
      ((foldOf (g.checkData g.translation)).eb deg)).length = nvG g := by
    rw [List.length_map, List.length_range]; rfl
  refine ⟨by rw [esOf_len]; exact h1, ?_, ?_, ?_, ?_, by omega⟩
  · show x < ((List.range (foldOf (g.checkData g.translation)).nv).map _).length; rw [hr]; exact hx
  · show x < (List.replicate (nvG g) true).length; rw [List.length_replicate]; exact hx
  · show x < ((List.range (foldOf (g.checkData g.translation)).nv).map _).length; rw [hr]; exact hx
  · show x < ((List.range (foldOf (g.checkData g.translation)).nv).map _).length; rw [hr2]; exact hx

/-- **The clauses' variables are valid.** -/
theorem litsOK (cap Kb Db Cδ deg : ℕ) (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q)
    (hvar : nvG g * g.s + 1 ≤ cap) (hlit : 4 * nvG g * (g.s + 1) + g.s + g.pcpp.systematicBits + 1 ≤ cap) :
    LitsOK cap (twD g deg)
      (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
      (litsD (g.checkData g.translation)) (2 ^ g.pcpp.clauseBits) := by
  have hN := FrontPw.nV_out h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits
  intro i hi
  obtain ⟨ha, hb⟩ := litA_lt i hi
  rw [hN.ss, hN.sy, ← hsS]
  refine ⟨xok cap deg _ (by omega) hvar, xok cap deg _ (by omega) hvar, ?_⟩
  have e1 : litA (litsD (g.checkData g.translation)) i + litA (litsD (g.checkData g.translation)) i * g.s ≤
      2 * nvG g * (g.s + 1) := by
    have := Nat.mul_le_mul_right (g.s + 1) (show litA (litsD (g.checkData g.translation)) i ≤ 2 * nvG g by omega)
    rw [Nat.mul_add, mul_one] at this; omega
  have e2 : litB (litsD (g.checkData g.translation)) i + litB (litsD (g.checkData g.translation)) i * g.s ≤
      2 * nvG g * (g.s + 1) := by
    have := Nat.mul_le_mul_right (g.s + 1) (show litB (litsD (g.checkData g.translation)) i ≤ 2 * nvG g by omega)
    rw [Nat.mul_add, mul_one] at this; omega
  have e3 : 4 * nvG g * (g.s + 1) = 2 * nvG g * (g.s + 1) + 2 * nvG g * (g.s + 1) := by ring
  omega

end Layout

/-! ## The writer's run at a guess -/

section Run
open NearCubicWires.WireExponent3_5.FinalPass.Tm
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- A clause's cost in the first pass. -/
def cVf (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (i : ℕ) : ℕ :=
  7 * litA lits i + 1 + 1 + (110 * (litA lits i * v0 rSS) + 110 * litA lits i + 110 * v0 rSS + 30 * v0 rSYS +
    costV Bn (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) + 120) + 1 +
      (7 * litB lits i + 1 + 1 + (110 * (litB lits i * v0 rSS) + 110 * litB lits i + 110 * v0 rSS + 30 * v0 rSYS +
        costV Bn (posRegs (Function.update v0 rLIT (litB lits i))) + 120))

/-- A clause's cost in the second pass. -/
def cQf (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (i : ℕ) : ℕ :=
  7 * litA lits i + 1 + 1 + (110 * (litA lits i * v0 rSS) + 110 * litA lits i + 110 * v0 rSS + 30 * v0 rSYS +
    mbCost Bn (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) rMb
      (FrontTableRef.patQ 0) + 120) + 1 + (7 * litB lits i + 1 + 1 + (110 * (litB lits i * v0 rSS) +
        110 * litB lits i + 110 * v0 rSS + 30 * v0 rSYS +
          mbCost Bn (posRegs (Function.update v0 rLIT (litB lits i))) rMb (FrontTableRef.patQ 0) + 120))

/-- A clause's cost in the third pass. -/
def cMf (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (i : ℕ) : ℕ :=
  100 * (litA lits i + 1) * (v0 rSS + 1) + 100 * (litB lits i + 1) * (v0 rSS + 1) +
    costMu Bn (FrontTW.muRegs v0 (litA lits i) (litB lits i)) + 100

/-- The largest value of `f` below `M`. -/
def supR (f : ℕ → ℕ) (M : ℕ) : ℕ := ((List.range M).map f).foldr max 0

theorem le_supR (f : ℕ → ℕ) (M i : ℕ) (hi : i < M) : f i ≤ supR f M :=
  FrontOutRef.le_foldr_max _ _ (List.mem_map_of_mem (List.mem_range.2 hi))

/-- The table writer's cost at a guess. -/
def twCost (Bn : ℕ) (v0 : Fin NR → ℕ) (lits : List ℕ) (cb : ℕ) : ℕ :=
  3 * (60 * v0 rBIG + 250 + 18 * 2 ^ cb + 2 ^ cb * (2 * ((lits.map rdCost).foldr max 0) + supR (cVf Bn v0 lits) (2 ^ cb) +
    supR (cQf Bn v0 lits) (2 ^ cb) + supR (cMf Bn v0 lits) (2 ^ cb) + 8)) + 10

/-- **The writer's cap facts at a guess** (the table writer, the word program, the tail stage). -/
structure EndCaps (g : UnionGuess S z) (W Kb Db Cδ aV bV aT bT crT KT AT : ℕ) : Prop where
  nv : 1 ≤ nvG g
  bnd : (twD g I.carrierDeg).Bnd (Kb * (g.q + 1) ^ Db)
  hB : 2 * (natWord g.q).length ≤ Kb * (g.q + 1) ^ Db
  hK : Kb ≤ 2 * W + 2
  hq4 : g.q + 4 ≤ 2 * W + 2
  hPw : ∀ k ≤ Db, (g.q + 1) ^ k ≤ 2 * W + 2
  hB1 : Kb * (g.q + 1) ^ Db + 1 ≤ 2 * W + 2
  hB2 : (natWord 3).length + (natWord g.pcpp.systematicBits).length + (natWord g.pcpp.auxiliaryBits).length +
    (natWord g.pcpp.clauseBits).length ≤ Kb * (g.q + 1) ^ Db
  cq : 2 ^ (natBitLength g.q + 1) ≤ 2 * W + 2
  c3 : 2 ^ (natBitLength 3 + 1) ≤ 2 * W + 2
  cs : 2 ^ (natBitLength g.pcpp.systematicBits + 1) ≤ 2 * W + 2
  ca : 2 ^ (natBitLength g.pcpp.auxiliaryBits + 1) ≤ 2 * W + 2
  cc : 2 ^ (natBitLength g.pcpp.clauseBits + 1) ≤ 2 * W + 2
  hsp : PrimAsm.SparseNum.sparseBound ζ Cδ (Ledger.Lq g.q) (Ledger.rowBt h0 h1 g.q - 1) ≤ 2 * W + 2
  hc : numCap (Ledger.rowBSparse h0 h1 2 Cδ g.q) (Ledger.rowBLambda h0 h1 2 g.q) g.q g.pcpp.systematicBits
    g.pcpp.auxiliaryBits g.pcpp.clauseBits ≤ 2 * W + 2
  hthr : thrCap (Ledger.rowBSparse h0 h1 2 Cδ g.q * Ledger.rowBSparse h0 h1 2 Cδ g.q * Ledger.rowBSparse h0 h1 2 Cδ g.q *
    Ledger.rowBSparse h0 h1 2 Cδ g.q) (Ledger.Lq g.q) (2 ^ g.pcpp.clauseBits) (Ledger.rowBLambda h0 h1 2 g.q) aV bV aT bT ≤
      2 * W + 2
  po1 : natBitLength 3 + natBitLength g.pcpp.systematicBits + natBitLength g.pcpp.auxiliaryBits +
    natBitLength g.pcpp.clauseBits + natBitLength (2 * 2 ^ g.pcpp.clauseBits) + g.pcpp.systematicBits * g.q + 1 ≤
      2 * W + 2
  po2 : (pcppOutput (S.request z g.oracle) g.pcpp).length ≤ Kb * (g.q + 1) ^ Db
  po3 : 20 * (natBitLength 3 + natBitLength g.pcpp.systematicBits + natBitLength g.pcpp.auxiliaryBits +
    natBitLength g.pcpp.clauseBits + natBitLength (2 * 2 ^ g.pcpp.clauseBits)) + 16 * (g.pcpp.systematicBits * g.q) +
      110 ≤ Kb * (g.q + 1) ^ Db * 40 + 200
  var : nvG g * g.s + 1 ≤ 2 * W + 2
  lit : 4 * nvG g * (g.s + 1) + g.s + g.pcpp.systematicBits + 1 ≤ 2 * W + 2
  rdc : ∀ x ∈ litsD (g.checkData g.translation), 2 ^ (natBitLength x + 1) ≤ 2 * W + 2
  mc : 2 ^ g.pcpp.clauseBits + 1 ≤ 2 * W + 2
  tw : (twWords (g.checkData g.translation)).length + 30 * (Kb * (g.q + 1) ^ Db) + 41 ≤ 2 * W + 2
  hcr : 1 ≤ crT
  h4 : 4 * Ledger.rowBr crT g.q ≤ g.q
  hKT : 1 ≤ KT
  capW : KT * (g.q + 1) ^ AT + 1000 * (g.q + 7) + 2 * crT + 100 ≤ 2 * W + 2
  hpc : Ledger.Lq g.q ≤ FrontTail.capOf crT KT AT g.q
  hac : ∀ i, FrontOutRef.accStart S (g.checkData g.translation) (Ledger.Lq g.q) i ≤ FrontTail.capOf crT KT AT g.q
  hpW : Ledger.Lq g.q ≤ 2 * W + 2
  haW : ∀ i, FrontOutRef.accStart S (g.checkData g.translation) (Ledger.Lq g.q) i ≤ 2 * W + 2

variable {g : UnionGuess S z}

/-- **The table writer's run at a guess** (from the numbers' registers). -/
theorem tw_run (hpA : S.parityAtom = unionParityAtom) (hcA : S.constAtom = unionConstAtom)
    (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount) (hd4 : 4 ≤ I.descDeg)
    (hsg : (g.checkData g.translation).signsOk = true) (hat : PlanW3.AtomsOkG g) (hF : FrontOutRef.GridFacts S)
    (W Kb Db Cδ aV bV aT bT crT KT AT : ℕ) (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q)
    (hmS : S.gridMass g.q = (Ledger.rowBLambda h0 h1 2 g.q : ℚ))
    (hEC : EndCaps h0 h1 g W Kb Db Cδ aV bV aT bT crT KT AT) (tail : List Bool) :
    WExec (2 * W + 2) twP
      (ts (srcF (srcG g I.carrierDeg tail)) 0 []
        (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits) false)
      (ts (srcF (srcG g I.carrierDeg tail)) 0 (twWords (g.checkData g.translation) ++ [false])
        (regsOf (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
          Z4 Z4 Z4 (if (g.checkData g.translation).schedule.all (FrontOutRef.callOkI (I := I)) then 1 else 0)) false)
      (twCost (Kb * (g.q + 1) ^ Db)
        (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
        (litsD (g.checkData g.translation)) g.pcpp.clauseBits) := by
  have hN := FrontPw.nV_out h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits
  have hpar : ∀ (m : Mode) (n : ℕ), m.gates (S.parityAtom m n ∅) = [] := fun m n => by
    rw [hpA, unionParityAtom_gates]; simp [staircaseGates]
  have hC : decide (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits
      rCDF ≠ 0) = FrontCallOk.fDI (I := I) g.mode g.q (g.checkData g.translation).const := by
    rw [hN.cdf]
    unfold FrontCallOk.fDI
    show true = decide (g.mode.descriptionBits (S.constAtom g.mode g.q) ≤ _)
    rw [hcA, unionConstAtom_descriptionBits]
    exact (decide_eq_true (Nat.one_le_pow _ _ (by omega))).symm
  have tw := twSem2 (2 * W + 2) (srcF (srcG g I.carrierDeg tail)) false (g.checkData g.translation)
    (twD g I.carrierDeg) (twRel hpA hcA _) _ _ (twFlags hpA hd4 hat) (twHolds g _ tail) (Kb * (g.q + 1) ^ Db)
    hEC.bnd _ (clauseRegs h0 h1 _ Kb Db Cδ _ hsS hEC.nv hEC.hB1 hEC.hc) (rdOK_numOut _ hN) hC
    (hN.ss.trans hsS.symm) hN.sy (Ledger.rowBLambda h0 h1 2 g.q) hmS (Transfer.one_le_lambda h0 h1 g.q)
    (FrontOutRef.s_ne hF g) hsg (magRegs_numOut _ _ hN hsS)
    (poLayout h0 h1 _ Kb Db Cδ _ tail hEC.po1 hEC.po2 hEC.po3) (litsOK h0 h1 _ Kb Db Cδ _ hsS hEC.var hEC.lit)
    _ _ _ _ (fun i hi => le_supR (cVf (Kb * (g.q + 1) ^ Db) (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits) (litsD (g.checkData g.translation))) _ i hi)
    (fun i hi => le_supR (cQf (Kb * (g.q + 1) ^ Db) (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits) (litsD (g.checkData g.translation))) _ i hi)
    (fun i hi => le_supR (cMf (Kb * (g.q + 1) ^ Db) (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits) (litsD (g.checkData g.translation))) _ i hi)
    (fun x hx => ⟨FrontOutRef.le_foldr_max _ _ (List.mem_map_of_mem hx), hEC.rdc x hx⟩) (hN.zero _ (by decide))
    (by rw [hN.big]; have := hEC.hB1; omega) hEC.mc (FrontOutRef.callOkI (I := I))
    (fun pos pat t ht => FrontCallOk.callOk_V g hpar hStar hFit hname pos pat t ht)
    (fun i pat t ht => FrontCallOk.callOk_Mu g hpar hStar hFit hname i pat t ht) hEC.tw
  rw [regsOf_numOut _ hN] at tw
  exact tw

end Run

/-! ## The front's end at a guess -/

section End
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The valid branch's kept data**: the table word, position `0`, `p = L(q)`, the slack thresholds. -/
theorem goodOut_kept (P : FusedPrimitive I) (hF : FrontOutRef.GridFacts S) (g : UnionGuess S z)
    (h : (g.checkData g.translation).schedule.all (FrontOutRef.callOkI (I := I)) = true) (cap R Lg : ℕ) :
    (FrontOutRef.goodOut S hF g h cap R Lg).kept P =
      ⟨twWords (g.checkData g.translation) ++ [false], 0, Ledger.Lq g.q,
        FrontOutRef.accStart S (g.checkData g.translation) (Ledger.Lq g.q)⟩ := by
  unfold FrontOutRef.goodOut FrontOut.kept Sched.KOf
  simp only
  rw [tblOf_tableAll]
  congr 1

/-- The output of the front's end at a guess: the valid branch's, or the rejecting one. -/
noncomputable def endOut (hF : FrontOutRef.GridFacts S) (g : UnionGuess S z) (cap R Lg : ℕ) : FrontOut I :=
  if h : (g.checkData g.translation).schedule.all (FrontOutRef.callOkI (I := I)) = true then
    FrontOutRef.goodOut S hF g h cap R Lg else FrontGate.rejOut

/-- The end's cost (the valid branch's; the rejecting one is below it). -/
def endCost (W nT crT KT AT q L : ℕ) : ℕ :=
  (11 * W + 20) + 1 + (1 + 1 + (2 * (nT + 1 + (1 + 1)) + 2)) + 1 +
    ((11 * W + 20) + 1 + (1 + 1 + (nT + FrontTail.tailCost crT KT AT q L (2 * W + 2))) + 1 +
      (2 * FrontTail.rOf crT KT AT q + 4) + 1)

variable {g : UnionGuess S z}

/-- **The front's end at a guess**: from the chain's ten sources and the count `1^W`, the loop bank of the valid
branch if every scheduled call is admissible, the rejecting bank otherwise. -/
theorem end_sem (P : FusedPrimitive I) (tf : ℕ) (hpA : S.parityAtom = unionParityAtom)
    (hcA : S.constAtom = unionConstAtom)
    (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount) (hd4 : 4 ≤ I.descDeg)
    (hsg : (g.checkData g.translation).signsOk = true) (hat : PlanW3.AtomsOkG g) (hF : FrontOutRef.GridFacts S)
    (W Kb Db Cδ aV bV aT bT crT KT AT : ℕ) (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q)
    (hmS : S.gridMass g.q = (Ledger.rowBLambda h0 h1 2 g.q : ℚ)) (hbV : 1 ≤ bV) (hbT : 1 ≤ bT)
    (hv0 : S.params.v0 = (aV : ℚ) / bV) (hτ : S.params.threshold = (aT : ℚ) / bT)
    (hEC : EndCaps h0 h1 g W Kb Db Cδ aV bV aT bT crT KT AT) (tail : List Bool)
    (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (k1 : ℕ) (hk1 : k1 + WT 11 56 ≤ tf) (k0 : ℕ)
    (hk : k0 + WT 25 105 ≤ tf) (hk01 : k1 + WT 11 56 ≤ k0)
    (hsI : Function.Injective srcT) (hsL : ∀ i, 2 + NL P ≤ (srcT i).val ∧ (srcT i).val < 2 + NL P + k1)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k1) (hcs : ∀ i, srcT i ≠ cntT)
    (H0 : Fin (NW P tf) → ℕ) (A0 : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H0 A0 k1)
    (hsrc : ∀ i : Fin 10, A0 (srcT i) = srcG g I.carrierDeg tail i ∧ H0 (srcT i) = 0)
    (hcnt : A0 cntT = List.replicate W true ∧ H0 cntT = 0) :
    ∃ (H1 : Fin (NW P tf) → ℕ) (A1 : Fin (NW P tf) → List Bool),
      Step (FrontEnd.endM P tf (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT srcT cntT k1 hk1 k0 hk)
        (endCost W (FrontPw.pwCost (2 * W + 2) h0 h1 Kb Db aV bV aT bT g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits
          g.pcpp.clauseBits (twCost (Kb * (g.q + 1) ^ Db) (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits) (litsD (g.checkData g.translation)) g.pcpp.clauseBits))
          crT KT AT g.q (twWords (g.checkData g.translation) ++ [false]).length) H0 A0 H1 A1 ∧
      (∀ i, H1 (lp P tf i) = bankH P ((endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
        (FrontTail.rOf crT KT AT g.q + 1)).kept P) i) ∧
      (∀ i, A1 (lp P tf i) = bankA P (endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
        (FrontTail.rOf crT KT AT g.q + 1)).cap (endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
        (FrontTail.rOf crT KT AT g.q + 1)).R (endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
        (FrontTail.rOf crT KT AT g.q + 1)).Lg ((endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
        (FrontTail.rOf crT KT AT g.q + 1)).kept P) i) := by
  set src := srcF (srcG g I.carrierDeg tail) with hsrcd
  have tw := tw_run h0 h1 hpA hcA hStar hFit hname hd4 hsg hat hF W Kb Db Cδ aV bV aT bT crT KT AT hsS hmS hEC tail
  have hH : src sHd = PrimAsm.ParseNat.enc true (natWord g.q) ++ RepairOrdinary.frame ([modeBit g.mode] ++ natWord 4) := by
    rw [← frame_app, ← List.append_assoc]; rfl
  have hP : src sPO = natWord 3 ++ natWord g.pcpp.systematicBits ++ natWord g.pcpp.auxiliaryBits ++
      natWord g.pcpp.clauseBits ++ (FrontSemPO.sbOf (S.request z g.oracle) g.pcpp ++
        natWord (litsD (g.checkData g.translation)).length ++ (litsD (g.checkData g.translation)).flatMap natWord) := by
    rw [hsrcd, po_eq]; simp only [List.append_assoc, List.append_nil]
  obtain ⟨τT, hPw, hkeep, hcl, hqq, hst, hsh, hop, hll, hok, hacc⟩ := FrontPw.pw_spec (2 * W + 2) h0 h1 src false Kb Db
    true Cδ aV bV aT bT g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits _ _ hH hP hEC.hB hEC.hK
    hEC.hq4 hEC.hPw (by have := hEC.hB1; omega) hEC.hB2 hEC.cq hEC.c3 hEC.cs hEC.ca hEC.cc hEC.hsp hEC.hc
    (twWords (g.checkData g.translation) ++ [false])
    (if (g.checkData g.translation).schedule.all (FrontOutRef.callOkI (I := I)) then 1 else 0) _ tw hbV hbT hEC.hthr
    (g.checkData g.translation) hsS hmS rfl S.params.v0 S.params.threshold hv0 hτ
  have hsT : ∀ i, (ts src 0 [] (fun _ => 0) false).sh i = 0 := fun i => by
    unfold ts; simp only; split_ifs <;> rfl
  have hvT : ∀ r, (ts src 0 [] (fun _ => 0) false).val r = 0 := fun r => by
    unfold ts; simp only [List.length_nil]; rw [Function.update_apply]; split_ifs <;> rfl
  have hkeep' : ∀ i : Fin 10, τT.st i.succ = (ts src 0 [] (fun _ => 0) false).st i.succ := fun i => by
    rw [hkeep _ (Fin.succ_ne_zero i), ts_st _ _ _ _ _ _ (Fin.succ_ne_zero i)]
  have hsrc' : ∀ i : Fin 10, A0 (srcT i) = (ts src 0 [] (fun _ => 0) false).st i.succ ∧ H0 (srcT i) = 0 := fun i => by
    rw [ts_st _ _ _ _ _ _ (Fin.succ_ne_zero i), hsrcd, srcF_succ]; exact hsrc i
  have hsc : (twWords (g.checkData g.translation) ++ [false]).length ≤ 2 * W + 2 := by
    have := hEC.tw; simp only [List.length_append, List.length_singleton]; omega
  by_cases hall : (g.checkData g.translation).schedule.all (FrontOutRef.callOkI (I := I)) = true
  · have hok' : τT.val 12 ≠ 0 := by rw [show (12 : Fin NR) = rOK from rfl, hok, if_pos hall]; omega
    obtain ⟨H1, A1, s1, hH1, hA1⟩ := FrontEnd.endGood P tf (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) (2 * W + 2)
      (ts src 0 [] (fun _ => 0) false) τT _ hPw hsT hvT rfl (by simp) hkeep' W le_rfl crT KT AT g.q (Ledger.Lq g.q)
      (FrontOutRef.accStart S (g.checkData g.translation) (Ledger.Lq g.q)) (twWords (g.checkData g.translation) ++ [false])
      hqq hst hsh hop hll (fun i => congrFun hacc i) hEC.hcr hEC.h4 hEC.hKT hEC.capW hEC.hpc hEC.hac hEC.hpW hEC.haW hsc
      hok' srcT cntT k1 hk1 k0 hk hk01 hsI hsL hcL hcs H0 A0 hPr hsrc' hcnt
    refine ⟨H1, A1, s1, fun i => ?_, fun i => ?_⟩
    · unfold endOut; rw [dif_pos hall, goodOut_kept]; exact hH1 i
    · unfold endOut; rw [dif_pos hall, goodOut_kept]; exact hA1 i
  · have hok0 : τT.val 12 = 0 := by rw [show (12 : Fin NR) = rOK from rfl, hok, if_neg hall]
    obtain ⟨H1, A1, s1, hH1, hA1⟩ := FrontEnd.endBad P tf (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) (2 * W + 2)
      (ts src 0 [] (fun _ => 0) false) τT _ hPw hsT hvT rfl (by simp) hkeep' W le_rfl crT KT AT hok0
      srcT cntT k1 hk1 k0 hk hsI hsL hcL hcs H0 A0 hPr hsrc' hcnt
    refine ⟨H1, A1, Step.enlarge s1 (by unfold endCost; omega), fun i => ?_, fun i => ?_⟩
    · unfold endOut; rw [dif_neg hall, FrontGate.rejOut_kept]; exact hH1 i
    · unfold endOut; rw [dif_neg hall, FrontGate.rejOut_kept]; exact hA1 i

end End

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW
