import Proof.Wire_3_5.FinalPass.SymF4
import Proof.Wire_3_5.FinalPass.TabFlat
import Proof.Wire_3_5.Primitive.SeedFix.S3Big1

/-! # SWf (the SYM words writer's flat tables), part 5: the unit machine and the seeds' flat tables

**`tabUP W`**: the decode (`decWP`), PA's POP setup program (`PopSetupRun.popProg`, at its polynomial need, part 4),
the table stages (`tabPrePM`), the emission (`emitTP`). **`tabEmitP Pl L j`**: unit `j`'s piece, the flat table of list seed `j`
(`Enum.flatSeedEquiv`) without its closing `false`, after a separating `false` when `j > 0`; nothing past the seeds.
**`unit_okP`**: every unit meets the shell unit interface `PrimThrW.Shell.UnitOK`. **`tabEmitP_flat`**: for every
loop bound `b ≥ |FlatSeed|`, the units' emissions closed by the shell's blank marker are **`flatWord Pl L`**, every
list seed's flat table in the enumeration's order (`tablesJ` at `L = |G_j|`, `flatWord_tablesJ`).

Paper quantity of the main type: the list seeds' flat tables `flatTable Pl e L` in `flatSeedEquiv` order, one word
(`tablesJ`, list:flatten P3:1508-1520). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires.WireExponent3_5.PrimAsm.PopCellW NearCubicWires.WireExponent3_5.PrimAsm.PopRecW
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.FinalPass.Flat

variable (cap : ℕ) (W : WalkBankProducer)

/-- **The flat tables writer's unit machine.** -/
noncomputable def tabUP := Composition.machine (Composition.machine (Composition.machine
  (decWP W.x).toProg.compile (PopSetupRun.popProg W.x).toProg.compile) (tabPrePM W)) (emitTP W.x).toProg.compile

/-- The seed's table without its closing `false`. -/
def seedTab (Pl : FlatListParams) (L : ℕ) (i : Fin (Fintype.card Pl.FlatSeed)) : List Bool :=
  tableW Pl.walkLen Pl.base.J (rowKP Pl ((Enum.flatSeedEquiv Pl).symm i) L)

/-- **Unit `j`'s piece of the flat tables word.** -/
def tabEmitP (Pl : FlatListParams) (L j : ℕ) : List Bool :=
  if h : j < Fintype.card Pl.FlatSeed then (if j = 0 then [] else [false]) ++ seedTab Pl L ⟨j, h⟩ else []

/-- **Every list seed's flat table**, in the enumeration's order. -/
def flatWord (Pl : FlatListParams) (L : ℕ) : List Bool :=
  (List.finRange (Fintype.card Pl.FlatSeed)).flatMap fun i => flatTable Pl ((Enum.flatSeedEquiv Pl).symm i) L

/-- The circuit-`j` flat tables are `flatWord` at `L = |G_j|`. -/
theorem flatWord_tablesJ (k : Seams.SymCall) (j : Fin 4) :
    PrimT.S3.tablesJ k j = flatWord k.Pl (PrimT.S3.gatesJ k j).length := rfl

/-- The table's length: `t·((J+1)(2L+1)+1)`. -/
def tabLenP (Pl : FlatListParams) (L : ℕ) : ℕ := Pl.walkLen * ((Pl.base.J + 1) * (2 * L + 1) + 1)

theorem seedTab_len (Pl : FlatListParams) (L : ℕ) (i : Fin (Fintype.card Pl.FlatSeed)) :
    (seedTab Pl L i).length = tabLenP Pl L := by
  have h := PrimT.S3.flatTable_len Pl ((Enum.flatSeedEquiv Pl).symm i) L
  rw [PopPipe.flatTable_eq, List.length_append, List.length_singleton] at h
  unfold seedTab tabLenP
  rw [show (Pl.base.J + 1) * (2 * L + 1) + 1 = 1 + (Pl.base.J + 1) * (2 * L + 1) by ring]
  omega

theorem flatTable_seedTab (Pl : FlatListParams) (L : ℕ) (i : Fin (Fintype.card Pl.FlatSeed)) :
    flatTable Pl ((Enum.flatSeedEquiv Pl).symm i) L = seedTab Pl L i ++ [false] :=
  PopPipe.flatTable_eq Pl _ L

/-- **Every unit meets the shell's unit interface.** -/
theorem unit_okP (Pl : FlatListParams) (n L j : ℕ) (w out u : List Bool) (nU : ℕ)
    (hw : w = TabW.reqT n Pl.M Pl.B Pl.errExp L 0 (Fintype.card Pl.FlatSeed))
    (hN : ∀ f off, f ≤ Fintype.card Pl.FlatSeed → off ≤ Fintype.card Pl.FlatSeed →
      PopSetupRun.runNeed Pl.M Pl.B Pl.errExp f 0 0 0 0 off L ≤ cap)
    (hcapC : 8 * sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ cap)
    (hO : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < cap)
    (hcT : tabLenP Pl L ≤ cap) (hc : 2 * w.length + 2 ≤ cap) (hj : j + 1 ≤ cap)
    (hnU : cpCost u.length + 1 + (decBoundP w.length j + 1 + PopSetupRun.popCost cap + 1 +
      tabPrePCost Pl L (popRW Pl) (popRW Pl) + 1 + emitPBound cap j (tabLenP Pl L)) ≤ nU) :
    PrimThrW.Shell.UnitOK cap W.x (tabUP W) nU w u (tabEmitP Pl L) j out := by
  set K := Fintype.card Pl.FlatSeed with hK
  set g := if j < K then j else 0 with hg
  have hgK : g < K := by
    rw [hg]
    split
    · assumption
    · exact Enum.card_flatSeed_pos Pl
  -- the decode
  obtain ⟨σD, m1, e1, c1, hIn⟩ := dec_specP cap W.x n Pl.M Pl.B Pl.errExp L K j w out u hw hc hj
  -- the POP setup program, to the table-ready state
  obtain ⟨τ, e2, t0, t1, t1h, t2, t2h, hTR, rOff, rW, rJ, rL, rz⟩ :=
    tab_ready cap W Pl g hgK L (K - j) w out u j σD (hN g (K - j) hgK.le (Nat.sub_le _ _)) hcapC hO hIn
  -- the table
  obtain ⟨σC, sC, hT6, hT6h, hkeep, hval⟩ := tabPreP cap W τ Pl _ L _ _ hTR
  have k0 := hkeep 0 (by decide)
  have k1 := hkeep 1 (by decide)
  have k2 := hkeep 2 (by decide)
  -- the emission
  obtain ⟨σE, m4, e4, c4, o1, o1h, o2, oK⟩ := emitTP_spec cap W.x σC out (seedTab Pl L ⟨g, hgK⟩) [false] j (K - j)
    Pl.walkLen Pl.base.J L (by rw [k1.1, t1]) (by rw [k1.2, t1h]) (by rw [k2.1, t2])
    (by rw [k2.2, t2h]) (by rw [hT6, ← flatTable_seedTab]) hT6h
    (by rw [hval _ (by decide), rOff]) (by rw [hval _ (by decide), rW]) (by rw [hval _ (by decide), rJ])
    (by rw [hval _ (by decide), rL]) (fun q h1 h2 => by rw [hval q (by omega)]; exact rz q h1 (by omega))
    (by rw [seedTab_len]; rfl) (by unfold FlatListParams.walkLen; omega)
    (by rw [seedTab_len]; exact hcT) hj
  have hem : (if K - j = 0 then [] else (if j = 0 then [] else [false]) ++ seedTab Pl L ⟨g, hgK⟩) =
      tabEmitP Pl L j := by
    unfold tabEmitP
    by_cases h : j < K
    · rw [if_neg (by omega), dif_pos h]
      have eg : (⟨g, hgK⟩ : Fin K) = ⟨j, h⟩ := Fin.ext (by show g = j; rw [hg, if_pos h])
      rw [eg]
    · rw [if_pos (by omega), dif_neg h]
  refine ⟨σE, _, Step.seq (Step.seq (Step.seq (WExec.exec cap e1).step (WExec.exec cap e2).step) sC)
    (WExec.exec cap e4).step, ?_, by rw [o1, hem], by rw [o1h, hem], o2, ?_⟩
  · rw [oK _ (TabW.skn W.x 0 1 (by decide)) (TabW.skn W.x 0 2 (by decide)), k0.1, t0]
  · have hb : m4 ≤ emitPBound cap j (tabLenP Pl L) := by rw [← seedTab_len Pl L ⟨g, hgK⟩]; exact c4
    omega

theorem range_prefix (Pl : FlatListParams) (L : ℕ) : ∀ k, k < Fintype.card Pl.FlatSeed →
    (List.range (k + 1)).flatMap (tabEmitP Pl L) ++ [false] =
      (List.range (k + 1)).flatMap fun j =>
        if h : j < Fintype.card Pl.FlatSeed then flatTable Pl ((Enum.flatSeedEquiv Pl).symm ⟨j, h⟩) L else []
  | 0, h => by
    rw [show List.range (0 + 1) = [0] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    unfold tabEmitP
    rw [dif_pos h, dif_pos h, flatTable_seedTab]
    simp
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← range_prefix Pl L k (by omega)]
    unfold tabEmitP
    rw [dif_pos h, dif_pos h, flatTable_seedTab, if_neg (by omega)]
    simp

/-- **The units' emissions are the seeds' flat tables**, closed by the shell's blank marker. -/
theorem tabEmitP_flat (Pl : FlatListParams) (L b : ℕ) (hb : Fintype.card Pl.FlatSeed ≤ b) :
    (List.range b).flatMap (tabEmitP Pl L) ++ [false] = flatWord Pl L := by
  set K := Fintype.card Pl.FlatSeed with hK
  have hK1 : 0 < K := Enum.card_flatSeed_pos Pl
  have hsplit : List.range b = List.range K ++ (List.range (b - K)).map (K + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  have htail : ((List.range (b - K)).map (K + ·)).flatMap (tabEmitP Pl L) = [] := by
    rw [List.flatMap_map]
    apply List.flatMap_eq_nil_iff.mpr
    intro i _
    unfold tabEmitP
    rw [dif_neg (by omega)]
  rw [hsplit, List.flatMap_append, htail, List.append_nil, show K = (K - 1) + 1 by omega,
    range_prefix Pl L (K - 1) (by omega), show K - 1 + 1 = K by omega, TabW.range_flatMap_finRange, flatWord]
  apply List.flatMap_congr
  intro i _
  rw [dif_pos i.isLt]

end NearCubicWires.WireExponent3_5.FinalPass.SymF
