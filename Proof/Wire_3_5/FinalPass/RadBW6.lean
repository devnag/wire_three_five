import Proof.Wire_3_5.FinalPass.RadBW5

/-! # RADIX stage 5b, part 6: the block writer reading in place

**`radBlockW3 : RadSpec3.RadBlockW3`** (the type): the same program `radProg`, need and bound as `radBlockW2`, run
from a state whose table word and digit indices sit at the heads of `T` and `GS` with any suffix after them
(`radRun3`, from `phB3_spec`, `phP3_spec`); the exit is again `appendO σ O OP (marks (true :: blockC …))`.

Paper quantity of the main type: the RADIX row's factor blocks (row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.RadB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.UnionMachine.RadSpec
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists

theorem radRun3 {ns nr : ℕ} (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr)
    (OP : Fin nr) (hOT : O ≠ T) (hOG : O ≠ GS) (_hTG : T ≠ GS) (_hSc : Function.Injective Sc)
    (_hSc' : ∀ i, Sc i ≠ O ∧ Sc i ≠ T ∧ Sc i ≠ GS) (hOP : ∀ j, Rg j ≠ OP) (Dl : ListData) (gis : List ℕ)
    (G row t : ℕ) (sgn : Bool) (cap : ℕ) (restT restG : List Bool) (σ : WState ns nr)
    (hTd : (σ.st T).drop (σ.sh T) =
      FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W (FinalPass.ListEval.rowsOf Dl gis.length) ++ restT)
    (hGd : (σ.st GS).drop (σ.sh GS) = gisWord gis ++ restG) (ho : σ.sh O = (σ.st O).length)
    (_hS : ∀ i, σ.st (Sc i) = [] ∧ σ.sh (Sc i) = 0) (h0 : σ.val (Rg 0) = gis.length) (h1 : σ.val (Rg 1) = G)
    (h2 : σ.val (Rg 2) = row) (h3 : σ.val (Rg 3) = t) (h4 : σ.val (Rg 4) = (if sgn then 1 else 0))
    (h5 : σ.val (Rg 5) = 3 * ListMachine.listBound Dl) (h6 : σ.val (Rg 6) = capC Dl gis.length)
    (hz : ∀ j : Fin radBlkK, 7 ≤ j.val → σ.val (Rg j) = 0)
    (hN : radNeed (blkSize Dl gis G row t sgn (σ.st O).length) ≤ cap)
    (hOPc : σ.val OP + (Streaming.marks (true :: blockC Dl gis.length t sgn false
      (CompilerMachine.Pool.labsOf G row gis))).length ≤ cap) :
    WExec cap (radProg O T GS Sc Rg OP) σ
      (appendO σ O OP (Streaming.marks (true :: blockC Dl gis.length t sgn false
        (CompilerMachine.Pool.labsOf G row gis))))
      (radBound cap) := by
  have hne : ∀ {i j : Fin 64}, i ≠ j → Rg i ≠ Rg j := fun h => Rg.injective.ne h
  have hv : ∀ (u : List Bool) (j : Fin 64), j ≠ 7 → (appendO σ O (Rg 7) u).val (Rg j) = σ.val (Rg j) :=
    fun u j h => aO_val_ne σ O (hne h) u
  have hz' : ∀ (u : List Bool) (j : Fin 64), 8 ≤ j.val → (appendO σ O (Rg 7) u).val (Rg j) = 0 := fun u j h => by
    rw [hv u j (Fin.ne_of_val_ne (by show j.val ≠ 7; omega))]; exact hz j (by omega)
  have h7 : σ.val (Rg 7) = 0 := hz 7 (by decide)
  have hv7 : ∀ u : List Bool, (appendO σ O (Rg 7) u).val (Rg 7) = u.length := fun u => by
    rw [aO_val_self, h7, Nat.zero_add]
  have hsT : ∀ u : List Bool, (appendO σ O (Rg 7) u).st T = σ.st T := fun u => by
    simp [Function.update_of_ne (Ne.symm hOT)]
  have hhT : ∀ u : List Bool, (appendO σ O (Rg 7) u).sh T = σ.sh T := fun u => by
    simp [Function.update_of_ne (Ne.symm hOT)]
  have hsG : ∀ u : List Bool, (appendO σ O (Rg 7) u).st GS = σ.st GS := fun u => by
    simp [Function.update_of_ne (Ne.symm hOG)]
  have hhG : ∀ u : List Bool, (appendO σ O (Rg 7) u).sh GS = σ.sh GS := fun u => by
    simp [Function.update_of_ne (Ne.symm hOG)]
  -- the block, field by field
  have hlabs : CompilerMachine.Pool.labsOf G row gis = gLabs (4 * row) G gis := labsOf_eq G row gis
  have hBE := PrimAsm.PopRec.blockE_eq Dl gis.length t sgn false (CompilerMachine.Pool.labsOf G row gis)
  rw [hlabs, cap1C_eq gis.length _ (gLabs_length _ _ _)] at hBE
  obtain ⟨N, hNd⟩ : ∃ x, x = blkSize Dl gis G row t sgn (σ.st O).length := ⟨_, rfl⟩
  rw [← hNd] at hN
  unfold blkSize at hNd
  unfold radNeed at hN
  rw [hlabs, hBE] at hNd hOPc ⊢
  have hcC : capC Dl gis.length = 4 * ((FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W
      (FinalPass.ListEval.rowsOf Dl gis.length)).length + gis.length + 1) := rfl
  obtain ⟨lw, hlw⟩ : ∃ x, x = FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W (FinalPass.ListEval.rowsOf Dl gis.length) :=
    ⟨_, rfl⟩
  rw [← hlw] at hTd hcC hNd hOPc ⊢
  obtain ⟨labs, hlb⟩ : ∃ x, x = gLabs (4 * row) G gis := ⟨_, rfl⟩
  rw [← hlb] at hNd hOPc ⊢
  have hBl := PrimAsm.PopBlockW.blockE_length (4 * gis.length) (3 * ListMachine.listBound Dl) (labSum labs) labs
    (lw.flatMap m2) t sgn (capC Dl gis.length) false
  have hpB := pieceB_len labs (labSum labs)
  rw [hBl] at hNd hOPc
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20, n21⟩ :=
    radNum cap N (σ.st O).length gis.length (3 * ListMachine.listBound Dl) t (capC Dl gis.length) lw.length
      (gisWord gis).length G row (labAdd labs) (labs.flatMap labE).length
      (pieceA (4 * gis.length) (3 * ListMachine.listBound Dl)).length (pieceB labs (labSum labs)).length
      (PrimAsm.PopRec.pieceP (lw.flatMap m2) t sgn (capC Dl gis.length) false).length hN hNd
      (len_le_gisWord gis) hcC hpB
  -- the marker
  have s0 := emitW_spec cap O (Rg 7) [true, true] σ ho (by rw [h7]; exact n1)
  -- the bank's first fields
  obtain ⟨nA, sA, bA⟩ := phA_spec cap O T hOT Rg (appendO σ O (Rg 7) [true, true]) gis.length
    (3 * ListMachine.listBound Dl) (by rw [hv _ 0 (by decide), h0]) (by rw [hv _ 5 (by decide), h5])
    (hz' _ 8 (by decide)) (hz' _ 9 (by decide)) (hz' _ 10 (by decide)) (aO_ho σ ho _) (by rw [hv7]; exact n2)
  rw [appendO_append] at sA
  -- the labels
  obtain ⟨nB, sB, bB⟩ := phB3_spec cap O GS hOG Rg
    (appendO σ O (Rg 7) ([true, true] ++ pieceA (4 * gis.length) (3 * ListMachine.listBound Dl))) gis G row
    (gisWord gis).length restG (by rw [hsG, hhG]; exact hGd) (by rw [hv _ 1 (by decide), h1])
    (by rw [hv _ 2 (by decide), h2]) (hz' _ 9 (by decide)) (hz' _ 11 (by decide)) (hz' _ 14 (by decide))
    (hz' _ 15 (by decide)) (hz' _ 17 (by decide)) (hz' _ 18 (by decide)) (hz' _ 19 (by decide))
    (hz' _ 20 (by decide)) (hz' _ 21 (by decide)) (hz' _ 37 (by decide)) (aO_ho σ ho _)
    (fun gi h => Nat.le_trans (Nat.le_add_right gi 2) (mem_le_gisWord gi gis h)) n3 n4 n5
    (by rw [hv7, ← hlb]; simp only [List.length_append, List.length_cons, List.length_nil]; clear * - n6; omega)
    (by rw [hv7, ← hlb]; simp only [List.length_append, List.length_cons, List.length_nil]; clear * - n7; omega)
  rw [← hlb, appendO_append] at sB
  rw [← hlb] at bB
  -- the stage-3∘5 data
  obtain ⟨nP, sP, bP⟩ := phP3_spec cap O T hOT Rg
    (appendO σ O (Rg 7) ([true, true] ++ pieceA (4 * gis.length) (3 * ListMachine.listBound Dl) ++
      pieceB labs (labSum labs))) lw gis.length t (capC Dl gis.length) sgn restT (by rw [hsT, hhT]; exact hTd)
    (by rw [hv _ 0 (by decide), h0]) (by rw [hv _ 3 (by decide), h3]) (by rw [hv _ 4 (by decide), h4])
    (by rw [hv _ 6 (by decide), h6]) hcC (hz' _ 38 (by decide)) (hz' _ 39 (by decide)) (hz' _ 40 (by decide))
    (hz' _ 41 (by decide)) (hz' _ 42 (by decide)) (hz' _ 51 (by decide)) (hz' _ 61 (by decide))
    (hz' _ 62 (by decide)) (aO_ho σ ho _) n8 n9
    (by rw [hv7]; simp only [List.length_append, List.length_cons, List.length_nil]; clear * - n10; omega)
  rw [appendO_append] at sP
  -- the output's position
  obtain ⟨B', hB'⟩ : ∃ x, x = [true, true] ++ pieceA (4 * gis.length) (3 * ListMachine.listBound Dl) ++
      pieceB labs (labSum labs) ++ PrimAsm.PopRec.pieceP (lw.flatMap m2) t sgn (capC Dl gis.length) false :=
    ⟨_, rfl⟩
  rw [← hB'] at sP
  have hB'l : B'.length = 2 + ((pieceA (4 * gis.length) (3 * ListMachine.listBound Dl)).length +
      ((pieceB labs (labSum labs)).length +
        (PrimAsm.PopRec.pieceP (lw.flatMap m2) t sgn (capC Dl gis.length) false).length)) := by
    rw [hB']; simp only [List.length_append, List.length_cons, List.length_nil]; clear * -; omega
  have hBN : B'.length ≤ N := by rw [hB'l]; exact n21
  have sM := wmove_spec cap (Rg 7) OP (hOP 7) B'.length (appendO σ O (Rg 7) B') (hv7 B')
    (by rw [hv7]; clear * - hBN n16 hN; omega)
    (by rw [hv7, aO_val_ne σ O (Ne.symm (hOP 7)) B', hB'l]; exact hOPc)
  have hEq : PrimAsm.PopRec.blockE (4 * gis.length) (3 * ListMachine.listBound Dl) (labSum labs) labs
      (lw.flatMap m2) t sgn (capC Dl gis.length) false = B' := by
    rw [hB']; unfold PrimAsm.PopRec.blockE; simp only [List.append_assoc]
  have efin : ((appendO σ O (Rg 7) B').setv (Rg 7) 0).setv OP ((appendO σ O (Rg 7) B').val OP +
      (appendO σ O (Rg 7) B').val (Rg 7)) = appendO σ O OP B' := by
    rw [hv7, aO_val_ne σ O (Ne.symm (hOP 7)) B']
    apply WState.eq
    · simp
    · simp
    · funext j
      simp only [WState.setv_val, appendO_val, Function.update_apply]
      by_cases a1 : j = OP
      · subst a1; simp [Ne.symm (hOP 7)]
      · by_cases a2 : j = Rg 7
        · subst a2; simp [hOP 7, h7]
        · simp [a1, a2]
    · simp
  rw [efin] at sM
  rw [hEq]
  -- the cost
  have hgB : gisB (4 * row) G (gisWord gis).length ≤ 1000 * (N + 1) :=
    gisB_le (4 * row) G (gisWord gis).length N n11 n12 n13 n14
  have hC := radCost cap N gis.length (3 * ListMachine.listBound Dl) t (capC Dl gis.length) lw.length
    (gisWord gis).length row (labSum labs) nA nB nP (gisB (4 * row) G (gisWord gis).length) B'.length hN n15 n16 n17
    n18 n19 n12 n13 n20 hBN bA bB bP hgB
  exact WExec.cast cap (WExec.seq s0 (WExec.seq sA (WExec.seq sB (WExec.seq sP sM)))) rfl hC

/-- **The RADIX block writer, reading in place** (stage 5b): `RadSpec3.RadBlockW3`. -/
def radBlockW3 : UnionMachine.RadSpec3.RadBlockW3 where
  prog := radProg
  need := radNeed
  bound := radBound
  C := 100000
  D := 2
  need_le := fun N => by
    have := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) (N + 1)
    unfold radNeed; omega
  bound_le := fun _ => le_rfl
  run := radRun3

end NearCubicWires.WireExponent3_5.FinalPass.RadB
