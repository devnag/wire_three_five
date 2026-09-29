import Proof.Wire_3_5.UnionMachine.FrontSemDec

/-! # C6 front, the semantic core (5): the chain after phase 2 at a decoded guess (P3:3672-3691)

At a witness whose checks pass (the entries' scan and the atom test at the description envelope), the chain after
phase 2 (`FrontRest.restM` at the guess's mode) runs to the end's bank (`FrontSemTW.endOut`): the entries' positions
and payloads form the atom stage's input (**`atomsOK_of`**), the guess's words are the chain's sources, C1's carrier
loop reads the guess's carriers and literal list, and the end is `FrontSemTW.end_sem` (**`valid_rest`**).

Paper quantity of the main type: the front's output bank at a valid witness. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter gridWord)
open NearCubicWires.RepairOrdinary

/-! ## The atom stage's input -/

section Atoms

theorem shape_len (r : List Bool) (p : ℕ) (b x : Bool) (pay rest : List Bool)
    (h : r.drop p = gridWord b x ++ (List.replicate pay.length true ++ false :: pay) ++ rest) :
    p + 2 * pay.length + 5 ≤ r.length := by
  have hl := congrArg List.length h
  simp only [List.length_drop, List.length_append, List.length_replicate, List.length_cons, gridWord,
    List.length_nil] at hl
  omega

theorem pos_ge (r : List Bool) (En : ℕ) (hpos0 : posOf r En 0 = 0)
    (hpos : ∀ j, j < En → posOf r En (j + 1) = posOf r En j + 2 * (payOf r En j).length + 5) :
    ∀ j, j ≤ En → 5 * j ≤ posOf r En j
  | 0, _ => by omega
  | j + 1, hj => by
    have := pos_ge r En hpos0 hpos j (by omega)
    rw [hpos j (by omega)]; omega

/-- The atom stage's per-atom constants. -/
noncomputable def KcOf (pay : ℕ → List Bool) (En : ℕ) : ℕ := FrontSemTW.supR (fun j => 70 * ((pay j).length + 2)) En
noncomputable def KdOf (nx : ℕ) (pay : ℕ → List Bool) (En : ℕ) : ℕ :=
  FrontSemTW.supR (fun j => CloseoutRowsCircuitWholeBudget.budget (FrontAtomStageL.capP nx) (pay j).length) En

/-- **The entries' positions and payloads are the atom stage's input.** -/
theorem atomsOK_of (r v : List Bool) (En nx q : ℕ) (hr : restAfter En r = some v) (hE1 : 1 ≤ En)
    (hrx : r.length + 1 ≤ nx) (hq : q + 3 ≤ 2 * nx + 2) :
    FrontAtP.AtomsOK r nx q En nx (posOf r En) (payOf r En) (KcOf (payOf r En) En) (KdOf nx (payOf r En) En) := by
  obtain ⟨h0, hent, hk, hpos⟩ := atom_shapes En r v hr
  have hlen : ∀ j, j < En → posOf r En j + 2 * (payOf r En j).length + 5 ≤ r.length := fun j hj => by
    obtain ⟨b, x, rest, e⟩ := hent j hj; exact shape_len r _ b x _ rest e
  have hcov := fun j (hj : j < En) => FrontAtomStageL.capP_covers nx (payOf r En j) (by have := hlen j hj; omega)
  refine ⟨hE1, h0, hent, hk, hpos, fun j hj => (hcov j hj).2.2, fun j hj => (hcov j hj).2.1, fun j hj => ?_, hq, ?_,
    fun j hj => FrontSemTW.le_supR (fun j => 70 * ((payOf r En j).length + 2)) En j hj,
    fun j hj => FrontSemTW.le_supR (fun j => CloseoutRowsCircuitWholeBudget.budget (FrontAtomStageL.capP nx)
      (payOf r En j).length) En j hj⟩
  · have := hlen j hj; omega
  · have h5 := pos_ge r En h0 hpos (En - 1) (by omega)
    have := hlen (En - 1) (by omega)
    omega

end Atoms

/-! ## The end's tape positions on the valid path -/

section Pos
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.WireExponent3_5.UnionMachine.FrontRest
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (m : Mode) (Dw Dl deg De Dt : ℕ) {d : ℕ} (c : Plan.C1At d) (k0 : ℕ) (h : k0 + RS m Dw Dl deg De Dt c ≤ tf)
  (qT rT poT : Fin (NW P tf))

theorem c1R_lt : (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT).val < 2 + NL P + oE m Dw Dl deg De Dt c k0 := by
  unfold c1R FrontC1D.c1O
  rw [sl_none P tf _ _ _ _ (FrontCh5.insL_none_of P tf _ _ (by
    intro p hp
    simp only [FrontC1D.c1L, List.mem_cons, List.not_mem_nil, or_false] at hp
    have e : (FrontC1D.stL c (C1Stage.outT c)).val = 1436 + C1Stage.TC c + 1 := rfl
    have hNB : C1Stage.NB (C1Stage.TC c) = 1436 + C1Stage.TC c + 12 := rfl
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega))), rg_val]
  have := (FrontC1D.stL c (C1Stage.outT c)).isLt
  unfold oE
  show 2 + NL P + (oC m Dw Dl deg De Dt k0 + 8 + _) < 2 + NL P + (oC m Dw Dl deg De Dt k0 + (8 + FrontC1D.NC c))
  omega

/-- **The end's positions, as arithmetic**: ten values and a count in the known layout. -/
theorem pos_arith (b k0 Dw Dl OA AP0 O5 NS OC CP OE po a1 a2 a3 a4 a5 a6 a7 a8 a9 aw : ℕ)
    (hpo1 : b ≤ po) (hpo2 : po < b + k0) (haw : aw = b + (k0 + 4 + (3 + 2 * Dw)))
    (ha2 : a2 = b + (k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 2))
    (ha7 : a7 = b + (k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 15 + 0))
    (ha8 : a8 = b + (k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 15 + 7))
    (hOA : OA = k0 + 4 + (14 + 2 * Dw) + (14 + 2 * Dl) + 8 + 8 + 15 + 71 + 22) (hO5 : O5 = OA + AP0)
    (ha1 : a1 = b + (O5 + 2)) (ha4 : a4 = b + (O5 + 40 + 0)) (ha5 : a5 = b + (O5 + 50 + 5))
    (ha6 : a6 = b + (O5 + 50 + 6)) (ha9 : a9 = b + (O5 + 50 + 7)) (hOC : OC = O5 + 50 + NS) (hNS : 1225 ≤ NS)
    (hOE : OE = OC + CP) (ha3 : b + OC ≤ a3) (ha3' : a3 < b + OE) :
    Function.Injective (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) ∧
    (∀ i, b ≤ (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) i ∧
      (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) i < b + OE) ∧
    (b ≤ aw ∧ aw < b + OE) ∧ (∀ i, (![po, a1, a2, a3, a4, a5, a6, a7, a8, a9] : Fin 10 → ℕ) i ≠ aw) := by
  have c1 : po < a2 := by omega
  have c2 : a2 < a7 := by omega
  have c3 : a7 < a8 := by omega
  have c4 : a8 < a1 := by omega
  have c5 : a1 < a4 := by omega
  have c6 : a4 < a5 := by omega
  have c7 : a5 < a6 := by omega
  have c8 : a6 < a9 := by omega
  have c9 : a9 < a3 := by omega
  have w1 : po < aw := by omega
  have w2 : aw < a2 := by omega
  have e1 : b ≤ aw := by omega
  have e2 : a3 < b + OE := ha3'
  clear haw ha2 ha7 ha8 hOA hO5 ha1 ha4 ha5 ha6 ha9 hOC hOE ha3 hNS hpo2 ha3'
  refine ⟨fun i j hij => ?_, fun i => ?_, ⟨e1, by omega⟩, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  · fin_cases i <;> simp <;> omega
  · fin_cases i <;> simp <;> omega

/-- **The end's tape positions**: the ten sources and the count lie below the end's regions, pairwise apart. -/
theorem end_pos (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0) :
    Function.Injective (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT) ∧
    (∀ i, 2 + NL P ≤ (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i).val ∧
      (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i).val < 2 + NL P + oE m Dw Dl deg De Dt c k0) ∧
    (2 + NL P ≤ (wcR P tf m Dw Dl deg De Dt c k0 h qT).val ∧
      (wcR P tf m Dw Dl deg De Dt c k0 h qT).val < 2 + NL P + oE m Dw Dl deg De Dt c k0) ∧
    (∀ i, srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i ≠ wcR P tf m Dw Dl deg De Dt c k0 h qT) := by
  obtain ⟨o1, o2, o3, o4, o5e, o6, o7⟩ := offs m Dw Dl deg De Dt k0
  have hfun : (fun i => (srcR P tf m Dw Dl deg De Dt c k0 h qT rT poT i).val) = ![poT.val, (unR P tf m Dw Dl deg De Dt c k0 h qT rT).val, (hdR P tf m Dw Dl deg De Dt c k0 h qT).val,
      (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT).val, (ccR P tf m Dw Dl deg De Dt c k0 h).val,
      (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)).val,
      (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)).val,
      (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val, (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val,
      (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num)).val] := by
    funext i; fin_cases i <;> rfl
  have A := pos_arith (2 + NL P) k0 Dw Dl (oA Dw Dl k0) FrontAtP.AP (o5 Dw Dl k0) (FrontCh5.NSF m deg De Dt)
    (oC m Dw Dl deg De Dt k0) (FrontC1D.C1P c) (oE m Dw Dl deg De Dt c k0) poT.val
    (unR P tf m Dw Dl deg De Dt c k0 h qT rT).val (hdR P tf m Dw Dl deg De Dt c k0 h qT).val
    (c1R P tf m Dw Dl deg De Dt c k0 h qT rT poT).val (ccR P tf m Dw Dl deg De Dt c k0 h).val
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num)).val
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num)).val
    (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 0).val (nuR P tf m Dw Dl deg De Dt c k0 h qT poT 6).val
    (fiR P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num)).val (wcR P tf m Dw Dl deg De Dt c k0 h qT).val
    hpL.1 hpL.2 (wcR_v P tf m Dw Dl deg De Dt c k0 h qT)
    (by rw [hdR_v, o1, o2])
    (by rw [nuR_v0, o1, o2, o3])
    (by rw [nuR_v6, o1, o2, o3])
    (by rw [o4, o1, o2, o3]) o5e (unR_v P tf m Dw Dl deg De Dt c k0 h qT rT) (ccR_v P tf m Dw Dl deg De Dt c k0 h)
    (by rw [fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 5 (by norm_num) (by norm_num)])
    (by rw [fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 6 (by norm_num) (by norm_num)])
    (by rw [fiR_v P tf m Dw Dl deg De Dt c k0 h qT rT poT 7 (by norm_num) (by norm_num)]) o6 o7 rfl
    (c1R_ge P tf m Dw Dl deg De Dt c k0 h qT rT poT) (c1R_lt P tf m Dw Dl deg De Dt c k0 h qT rT poT)
  rw [← hfun] at A
  obtain ⟨A1, A2, A3, A4⟩ := A
  exact ⟨fun i j hij => A1 (congrArg Fin.val hij), A2, A3, fun i hi => A4 i (congrArg Fin.val hi)⟩

end Pos

/-! ## The valid path -/

section Valid
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.WireExponent3_5.UnionMachine.FrontRest NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.WireExponent3_5.UnionMachine.C1Loop (bank rlR rndM wSl)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt (esOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG srcG)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N}

/-- The entries' code width. -/
noncomputable def WnG (g : UnionGuess S z) : ℕ :=
  FrontSemTW.supR (fun e => (natWord (FrontFmtCA.codeE (esOf g) e)).length) (esOf g).length

/-- The atoms' codes' width. -/
noncomputable def WaG (g : UnionGuess S z) : ℕ :=
  ((foldOf (g.checkData g.translation)).as.map List.length).foldr max 0

/-- The fold's round fuel. -/
noncomputable def cwG (g : UnionGuess S z) (T : ℕ) : ℕ :=
  FrontSemTW.supR (fun X => FrontFoldLoop.rcost (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode)
    (foldOf (g.checkData g.translation)) T (WaG g) X) (foldOf (g.checkData g.translation)).nv

/-- The carrier loop's round fuel. -/
noncomputable def cG (g : UnionGuess S z) (Hd Vb : ℕ) : ℕ :=
  FrontSemTW.supR (fun x => C1Gates.rcost (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (nvG g) Hd Vb
    ((List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).cw) x) (nvG g)

/-- The rest of the PCPP output word after its counts. -/
noncomputable def restPG (g : UnionGuess S z) : List Bool :=
  FrontSemPO.sbOf (S.request z g.oracle) g.pcpp ++ natWord (C1Ref.litsG g).length ++
    (C1Ref.litsG g).flatMap natWord

theorem po_restPG (g : UnionGuess S z) :
    pcppOutput (S.request z g.oracle) g.pcpp = natWord 3 ++ natWord g.pcpp.systematicBits ++
      natWord g.pcpp.auxiliaryBits ++ natWord g.pcpp.clauseBits ++ restPG g := by
  rw [FrontSemPO.pcppOutput_poWord, FrontSemPO.litsOf_eq]
  unfold C1Cnt.poWord restPG
  simp only [List.append_assoc]

/-- **The valid path's capacities** at a guess (the chain after phase 2 and C1's call). -/
structure PathCaps (g : UnionGuess S z) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb : ℕ)
    {d : ℕ} (c : Plan.C1At d) : Prop where
  nums : FrontCh3P.NumsCaps (2 * (Kw * (g.q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ g.q g.pcpp.systematicBits
    g.pcpp.auxiliaryBits g.pcpp.clauseBits
  capC : (nvG g + 1) * (2 * (Ledger.rowBSparse h0 h1 2 Cδ g.q * WnG g) + 2 * WnG g + 3) +
    Ledger.rowBSparse h0 h1 2 Cδ g.q + nvG g ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2
  capB1 : (nvG g + 1) * (2 * g.q + 1) + g.q + g.pcpp.systematicBits + g.pcpp.auxiliaryBits + 1 ≤
    2 * (Kw * (g.q + 1) ^ Dw) + 2
  capB2 : natBitLength 3 + natBitLength g.pcpp.systematicBits + natBitLength g.pcpp.auxiliaryBits +
    natBitLength g.pcpp.clauseBits + 1 ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2
  Z0 : (foldOf (g.checkData g.translation)).nv + 1 ≤ value Dt Ct (Kw * (g.q + 1) ^ Dw)
  env : ∀ X < (foldOf (g.checkData g.translation)).nv,
    FrontFoldLoop.EnvFit ((foldOf (g.checkData g.translation)).car X) I.carrierDeg (value De Ce (Kw * (g.q + 1) ^ Dw))
  cwT : cwG g (value De Ce (Kw * (g.q + 1) ^ Dw)) + 1 ≤ value Dt Ct (Kw * (g.q + 1) ^ Dw)
  len : ∀ X ≤ (foldOf (g.checkData g.translation)).nv, ∀ t,
    ((foldOf (g.checkData g.translation)).st I.carrierDeg (value De Ce (Kw * (g.q + 1) ^ Dw))
      (value Dt Ct (Kw * (g.q + 1) ^ Dw)) X (FrontCh5.PwM g.mode).t (FrontCh5.CwM g.mode).t t).length ≤
        value Dt Ct (Kw * (g.q + 1) ^ Dw)
  sV : g.pcpp.systematicBits ≤ Vb
  aV : g.pcpp.auxiliaryBits ≤ Vb
  cV : g.pcpp.clauseBits ≤ Vb
  lV : (C1Ref.litsG g).length ≤ Vb
  vV : ∀ l ∈ C1Ref.litsG g, l ≤ Vb
  xV : nvG g ≤ Vb
  v3 : 3 ≤ Vb
  Hd : ∀ x < nvG g, max (2 * (natWord (C1Ref.CsG g x).code).length + 1)
    (C1CarPre.carPreCost (C1Ref.CsG g x) 0 0 + 1) ≤ Kw * (g.q + 1) ^ Dw
  xc : nvG g ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2
  capR : ∀ x < nvG g, g.pcpp.systematicBits * g.q + g.q + (C1Ref.litsG g).length + 6 * Vb + 8 + x + g.q +
    GateConv.capNeed (C1Ref.CsG g x) + 2 * ((C1Ref.CsG g x).flatMap GateConv.selGate).length +
    C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x + (C1Ref.CsG g x).length + C1Cnt.cntOf x (C1Ref.litsG g) +
    g.pcpp.clauseBits + C1Gates.npF (C1Ref.litsG g) x + 2 ^ (g.pcpp.clauseBits + 2) +
    (RepairOrdinary.Streaming.marks (natListWord (List.range' (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x)
      (C1Ref.CsG g x).length))).length +
    (RepairOrdinary.Streaming.marks (NearCubicWires.WireExponent3_5.ratWord
      ((C1Cnt.cntOf x (C1Ref.litsG g) : ℚ) / 2 ^ (g.pcpp.clauseBits + 1)))).length +
    6 * natBitLength (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x + (C1Ref.CsG g x).length) +
    6 * natBitLength (C1Cnt.cntOf x (C1Ref.litsG g) + 2 ^ (g.pcpp.clauseBits + 1)) + 40
      ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2
  cap1 : 20 * (g.q + 2) + 4 * cr + 100 ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2
  cap2 : g.q + Ledger.rowBr cr g.q + C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g) +
    C1Gates.npF (C1Ref.litsG g) (nvG g) + 6 * (natBitLength g.q + natBitLength (Ledger.rowBr cr g.q) +
      natBitLength (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g)) +
      natBitLength (C1Gates.npF (C1Ref.litsG g) (nvG g))) +
    (RepairOrdinary.frame (Plan.selWord (FrontSelReq.selReqOf g))).length + 50 ≤ 2 * (Kw * (g.q + 1) ^ Dw) + 2
  capC1 : 8 * (SelectionMachine.selArgmin (FrontSelReq.selReqOf g)).length +
    2 * (natListWord (SelectionMachine.selArgmin (FrontSelReq.selReqOf g))).length + 17 ≤
      2 * (Kw * (g.q + 1) ^ Dw) + 2

/-- A PCPP output has a variable (its first clause's literal names one). -/
theorem nv_pos (g : UnionGuess S z) : 1 ≤ nvG g := by
  cases h : (g.pcpp.clauses ⟨0, Nat.two_pow_pos _⟩).left with
  | positive i => have := i.isLt; show 1 ≤ g.pcpp.systematicBits + g.pcpp.auxiliaryBits; omega
  | negative i => have := i.isLt; show 1 ≤ g.pcpp.systematicBits + g.pcpp.auxiliaryBits; omega

/-- **The valid path's cost** (the chain after phase 2 at a guess, through the end). -/
noncomputable def validCost (g : UnionGuess S z) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
    (Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT : ℕ) {d : ℕ} (c : Plan.C1At d)
    (hpre : (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf g)) (xs : List Bool) (k : ℕ) : ℕ :=
  let r := FrontTW.entsW (esOf g) ++ List.replicate k false
  let En := (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q
  let W := Kw * (g.q + 1) ^ Dw
  let ch3 := FrontCh3P.ch3Cost h0 h1 Dw Kw Dl Kb Db Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits
    g.pcpp.clauseBits xs r
  let atc := FrontAtP.atCost g.mode r xs.length g.q En xs.length ((g.q + 1) ^ Dl) (KcOf (payOf r En) En)
    (KdOf xs.length (payOf r En) En) (payOf r En)
  let ch5 := FrontCh5.ch5Cost g.mode W r.length (Ledger.rowBSparse h0 h1 2 Cδ g.q) (WnG g)
    (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits W
    I.carrierDeg De Ce Dt Ct (foldOf (g.checkData g.translation)).nv (cwG g (value De Ce W))
  let asm := C1Asm.asmCost cr g.q (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g))
    (C1Gates.npF (C1Ref.litsG g) (nvG g)) (C1Gates.GF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g))
    (C1Gates.PF (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (nvG g))
  let c1 := FrontC1D.c1Cost W (g.pcpp.systematicBits + g.pcpp.auxiliaryBits)
    ((nvG g * (cG g W Vb + 2) + 1) + 1 + ((2 * asm + 2) + 1 +
      ((Plan.c1sized d c.E₁ c.c₁).budget ⟨FrontSelReq.selReqOf g, hpre⟩ + 1 +
        (2 * C1Stage.convCost (SelectionMachine.selArgmin (FrontSelReq.selReqOf g)) + 2))))
  let nE := FrontSemTW.endCost W (FrontPw.pwCost (2 * W + 2) h0 h1 Kb Db aV bV aT bT g.q g.pcpp.systematicBits
    g.pcpp.auxiliaryBits g.pcpp.clauseBits (FrontSemTW.twCost (Kb * (g.q + 1) ^ Db)
      (FrontPw.nV h0 h1 Kb Db true Cδ g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits)
      (FrontTW.litsD (g.checkData g.translation)) g.pcpp.clauseBits))
    crT KT AT g.q (FrontSemTW.twWords (g.checkData g.translation) ++ [false]).length
  (8 * xs.length + 14) + 1 + (ch3 + 1 + ((atc + 1 + ((ch5 + 1 + (c1 + 1 + nE)) + 1)) + 1))

/-- **The chain after phase 2 at a valid witness**: from the state after phase 2 (the copy of `x`, `1^q`, the rest of
the witness, the PCPP output word), the chain at the guess's mode runs to the end's bank. -/
theorem valid_rest (P : FusedPrimitive I) (tf : ℕ) (Dw Dl De Dt : ℕ) {d : ℕ} (c : Plan.C1At d)
    (g : UnionGuess S z) (k0 : ℕ) (h : k0 + RS g.mode Dw Dl I.carrierDeg De Dt c ≤ tf) (qT rT poT : Fin (NW P tf))
    (Kw : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Kb Db Cδ Ce Ct cr Vb aV bV aT bT crT KT AT : ℕ)
    (hpA : S.parityAtom = unionParityAtom) (hcA : S.constAtom = unionConstAtom)
    (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount) (hd4 : 4 ≤ I.descDeg)
    (hsg : (g.checkData g.translation).signsOk = true) (hat : PlanW3.AtomsOkG g) (hF : FrontOutRef.GridFacts S)
    (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q) (hmS : S.gridMass g.q = (Ledger.rowBLambda h0 h1 2 g.q : ℚ))
    (hbV : 1 ≤ bV) (hbT : 1 ≤ bT) (hv0 : S.params.v0 = (aV : ℚ) / bV) (hτ : S.params.threshold = (aT : ℚ) / bT)
    (hr' : B.rOf g.q = Ledger.rowBr cr g.q) (hpre : (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf g))
    (hPC : PathCaps g h0 h1 Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb c)
    (hEC : FrontSemTW.EndCaps h0 h1 g (Kw * (g.q + 1) ^ Dw) Kb Db Cδ aV bV aT bT crT KT AT)
    (xs : List Bool) (k : ℕ) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hPr : PristineH P tf H A k0)
    (hqL : 2 + NL P ≤ qT.val ∧ qT.val < 2 + NL P + k0) (hrL : 2 + NL P ≤ rT.val ∧ rT.val < 2 + NL P + k0)
    (hpL : 2 + NL P ≤ poT.val ∧ poT.val < 2 + NL P + k0) (hpq : poT ≠ qT)
    (hX : A (FrontPh1.xT P tf) = RepairOrdinary.frame xs ∧ H (FrontPh1.xT P tf) = 0)
    (hq : A qT = List.replicate g.q true ∧ H qT = 0)
    (hR : A rT = RepairOrdinary.frame (FrontTW.entsW (esOf g) ++ List.replicate k false) ∧ H rT = 0)
    (hp : A poT = pcppOutput (S.request z g.oracle) g.pcpp ∧ H poT = 0)
    (hx : (FrontTW.entsW (esOf g) ++ List.replicate k false).length + 1 ≤ xs.length)
    (hq3 : g.q + 3 ≤ 2 * xs.length + 2)
    (hv : FrontAtomLoop.verdictOf g.q (FrontAtomStageL.capP xs.length) ((g.q + 1) ^ Dl) g.mode
      ((g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q)
      (payOf (FrontTW.entsW (esOf g) ++ List.replicate k false)
        ((g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q)) = 0) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (restM P tf g.mode Dw Dl I.carrierDeg De Dt c k0 h qT rT poT Kw Kb Db true ζ Cδ Ce Ct cr
          (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT) crT KT AT)
        (validCost g h0 h1 Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr Vb aV bV aT bT crT KT AT c hpre xs k) H A H' A' ∧
      (∀ i, H' (lp P tf i) = bankH P ((FrontSemTW.endOut hF g (FrontTail.capOf crT KT AT g.q)
        (FrontTail.rOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q + 1)).kept P) i) ∧
      (∀ i, A' (lp P tf i) = bankA P (FrontSemTW.endOut hF g (FrontTail.capOf crT KT AT g.q)
          (FrontTail.rOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q + 1)).cap
        (FrontSemTW.endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
          (FrontTail.rOf crT KT AT g.q + 1)).R
        (FrontSemTW.endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
          (FrontTail.rOf crT KT AT g.q + 1)).Lg
        ((FrontSemTW.endOut hF g (FrontTail.capOf crT KT AT g.q) (FrontTail.rOf crT KT AT g.q)
          (FrontTail.rOf crT KT AT g.q + 1)).kept P) i) := by
  have hg : ∀ e ∈ entsG g, e.1 ∈ gridSet := (signs_iff g _).1 hsg
  have hEeq : (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q = (entsG g).length := by
    rw [entsG_length, ← hsS]
  have hrr : FrontTW.entsW (esOf g) ++ List.replicate k false = ((entsG g).map encE).flatten ++ List.replicate k false := by
    rw [FrontSemEnt.entsW_esOf g hg]
  have hrest : restAfter ((g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q)
      (FrontTW.entsW (esOf g) ++ List.replicate k false) = some (List.replicate k false) := by
    rw [hEeq, hrr]; exact (restAfter_enc (entsG g) _ hg).1
  have hE1 : 1 ≤ (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := nv_pos g; unfold nvG at this; omega)
      (by have := hPC.nums.hs1; omega))
  have hA := atomsOK_of _ _ _ xs.length g.q hrest hE1 hx hq3
  have hE : (entScan ((g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q)
      (FrontTW.entsW (esOf g) ++ List.replicate k false)).isSome = true := by
    rw [FrontEntriesRef.entScan_isSome, hrest]; simp
  have hp' : A poT = natWord 3 ++ natWord g.pcpp.systematicBits ++ natWord g.pcpp.auxiliaryBits ++
      natWord g.pcpp.clauseBits ++ restPG g ∧ H poT = 0 := ⟨by rw [hp.1, po_restPG], hp.2⟩
  have hrP : restPG g = FrontSemPO.sbOf (S.request z g.oracle) g.pcpp ++
      (natWord (C1Ref.litsG g).length ++ (C1Ref.litsG g).flatMap natWord) := by
    unfold restPG; simp only [List.append_assoc]
  have hes : (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * Ledger.rowBSparse h0 h1 2 Cδ g.q ≤ (esOf g).length := by
    rw [FrontSemEnt.esOf_length, ← hsS]
  have has : FrontFmtCA.itemsOf (esOf g) (Ledger.rowBSparse h0 h1 2 Cδ g.q)
      (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) = (foldOf (g.checkData g.translation)).as.flatMap
        RepairOrdinary.frame := by
    rw [← hsS]
    exact FrontFmtSem.ca_eq (D := g.checkData g.translation) (esOf g) (fun X a => FrontSemEnt.codeE_esOf g X a)
  obtain ⟨Hn, An, sL, hHn, D, kk, -, hAn⟩ := C1Gates.gates_loop (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (nvG g)
    (natWord 3 ++ natWord g.pcpp.systematicBits ++ natWord g.pcpp.auxiliaryBits ++ natWord g.pcpp.clauseBits ++
      restPG g)
    (((List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).cw).flatMap
      RepairOrdinary.frame)
    (2 * (Kw * (g.q + 1) ^ Dw) + 2) (Kw * (g.q + 1) ^ Dw) Vb (cG g (Kw * (g.q + 1) ^ Dw) Vb)
    ((List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).cw) []
    (FrontSemPO.sbOf (S.request z g.oracle) g.pcpp) [] g.pcpp.systematicBits g.pcpp.auxiliaryBits
    (by simp [FrontTWKit.frItems, List.flatMap_def])
    (by rw [← po_restPG, FrontSemPO.pcppOutput_poWord, FrontSemPO.litsOf_eq, List.append_nil])
    (FrontSemPO.sbOf_length _ _)
    (fun x hx => ⟨by rw [List.length_map, List.length_range]; exact hx, by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range (show x < (foldOf (g.checkData g.translation)).nv from hx)]
      simp only [Option.map_some, Option.getD_some, FrontFoldLoop.FoldIn.cw]
      rw [FrontFoldSem.car_eq (D := g.checkData g.translation)
        (by show S.parityAtom g.mode g.q = unionParityAtom g.mode g.q; rw [hpA]) ⟨x, hx⟩]
      exact congrArg (fun C => natWord (Stars.Carrier.code C)) (C1Ref.CsG_val g ⟨x, hx⟩).symm⟩)
    hPC.sV hPC.aV hPC.cV hPC.lV hPC.vV hPC.xV hPC.v3 hPC.Hd hPC.xc hPC.capR
    (fun x hx => FrontSemTW.le_supR (fun x => C1Gates.rcost (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits (nvG g)
      (Kw * (g.q + 1) ^ Dw) Vb ((List.range (foldOf (g.checkData g.translation)).nv).map
        (foldOf (g.checkData g.translation)).cw) x) _ x hx) (fun _ => List.replicate (Kw * (g.q + 1) ^ Dw) false)
    (fun _ => by rw [List.length_replicate]) 0
  have hloop : ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) (nvG g * (cG g (Kw * (g.q + 1) ^ Dw) Vb + 2) + 1) (fun _ => 0)
        (bank (fun _ => List.replicate (Kw * (g.q + 1) ^ Dw) false)
          (rlR (2 * (Kw * (g.q + 1) ^ Dw) + 2) (C1Gates.Sj (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits
            (g.pcpp.systematicBits + g.pcpp.auxiliaryBits)
            (natWord 3 ++ natWord g.pcpp.systematicBits ++ natWord g.pcpp.auxiliaryBits ++ natWord g.pcpp.clauseBits ++
              restPG g)
            (((List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).cw).flatMap
              RepairOrdinary.frame) 0) 0) (Kw * (g.q + 1) ^ Dw)) Hn An ∧
      Hn = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ),
        An = bank D (rlR (2 * (Kw * (g.q + 1) ^ Dw) + 2) (C1Gates.Sj (C1Ref.CsG g) (C1Ref.litsG g) g.pcpp.clauseBits
          (g.pcpp.systematicBits + g.pcpp.auxiliaryBits)
          (natWord 3 ++ natWord g.pcpp.systematicBits ++ natWord g.pcpp.auxiliaryBits ++ natWord g.pcpp.clauseBits ++
            restPG g)
          (((List.range (foldOf (g.checkData g.translation)).nv).map (foldOf (g.checkData g.translation)).cw).flatMap
            RepairOrdinary.frame) (g.pcpp.systematicBits + g.pcpp.auxiliaryBits)) k) (Kw * (g.q + 1) ^ Dw) :=
    ⟨Hn, An, sL, hHn, D, kk, hAn⟩
  obtain ⟨hinj, hsL, hcL, hcs⟩ := end_pos P tf g.mode Dw Dl I.carrierDeg De Dt c k0 h qT rT poT hpL
  exact rest_path P tf g.mode Dw Dl I.carrierDeg De Dt c k0 h qT rT poT (FrontPw.pwW Kb Db true ζ Cδ aV bV aT bT)
    crT KT AT Kw h0 h1 Kb Db true Cδ Ce Ct cr g.q g.pcpp.systematicBits g.pcpp.auxiliaryBits g.pcpp.clauseBits xs
    (FrontTW.entsW (esOf g) ++ List.replicate k false) (restPG g) _ _ _ _ H A hPr hqL hrL hpL hpq hX hq hR hp' hx
    hPC.nums hE hA hv (esOf g) (List.replicate k false) (WnG g) (WaG g) (cwG g (value De Ce (Kw * (g.q + 1) ^ Dw)))
    (FrontSemPO.sbOf (S.request z g.oracle) g.pcpp) (natWord (C1Ref.litsG g).length ++ (C1Ref.litsG g).flatMap natWord)
    (foldOf (g.checkData g.translation)) rfl hrP hes (fun e he => FrontSemTW.le_supR (fun e => (natWord (FrontFmtCA.codeE (esOf g) e)).length) _ e he) hPC.capC
    (FrontSemPO.sbOf_length _ _) hPC.capB1 hPC.capB2
    (fun a ha => FrontOutRef.le_foldr_max _ _ (List.mem_map_of_mem ha)) hPC.Z0 hPC.env
    (fun X hX => FrontSemTW.le_supR (fun X => FrontFoldLoop.rcost (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode)
      (foldOf (g.checkData g.translation)) (value De Ce (Kw * (g.q + 1) ^ Dw)) (WaG g) X) _ X hX) hPC.cwT hPC.len (FrontSemPO.bm_rows g) has rfl rfl
    (C1Ref.CsG g) (C1Ref.litsG g) _ hloop (FrontSelReq.selReqOf g) hpre (C1Ref.reqWord_selWord g cr hr')
    hPC.cap1 hPC.cap2 hPC.capC1 _ _ (fun H5 A5 hPr5 hsrc5 hcnt5 => by
      have hsrc' : ∀ i, A5 (srcR P tf g.mode Dw Dl I.carrierDeg De Dt c k0 h qT rT poT i) =
          srcG g I.carrierDeg (List.replicate k false) i ∧ H5 (srcR P tf g.mode Dw Dl I.carrierDeg De Dt c k0 h qT rT poT i) = 0 := by
        intro i
        have e := hsrc5 i
        rw [← po_restPG, FrontSelReq.selArgmin_selReq g hStar, ← hsS] at e
        exact e
      exact FrontSemTW.end_sem h0 h1 P tf hpA hcA hStar hFit hname hd4 hsg hat hF (Kw * (g.q + 1) ^ Dw) Kb Db Cδ aV bV
        aT bT crT KT AT hsS hmS hbV hbT hv0 hτ hEC (List.replicate k false) _ _ _ (hr6 tf g.mode Dw Dl I.carrierDeg De Dt c k0 h)
        _ (hr7 tf g.mode Dw Dl I.carrierDeg De Dt c k0 h) le_rfl hinj hsL hcL hcs H5 A5 hPr5 hsrc' hcnt5)

end Valid

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPath
