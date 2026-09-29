import Proof.Wire_3_5.Primitive.SeedFix.FlipsOff

/-! # FLIPS, part 12: the writer's set-up reaches the loops' invariant (P3:1206-1207, 1224)

"Use all `2^s` cosets in each block. This gives `2^{rs}` partitions" (P3:1206-1207): the call's translation codes
pick one coset per block, and the partition's offset point `C4Geo.offset P σ` is, in block `j`, the unit vector of
the column `t_j` (`0` when `t_j = 0`), and `0` on the unblocked coordinates. Here:

* `errBits_zero`, `offBlock_codes`, **`offW_eq`**: the word `offPart` writes is `List.ofFn (C4Geo.offset P σ)` at the
  call's translation `σ = translationOfCodes ts` (P3:1206-1207);
* `head_caps`: the header skip's register bounds from the request word's length;
* `initAll_spec`: the error words' stale frames (`n` zeros) and the three counters at `0`;
* **`init_spec`**: from the writer's start state (`σG`), the star numbers, the header skip, the offset, the
  streams' set-up and the row flag reach the loops' invariant `FS` at the first cell (`L = R = 0`), no output yet,
  with the coset offset `C4Geo.offset P σ` on `sOFF`.

Paper quantity of the main types: the coset offset `C4Geo.offset P σ` (the partition's point, P3:1206-1207). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT gNT gCT gAUX σG)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-! ## The offset word is the coset offset -/

theorem errBits_zero (P : StarParams) (σ : SyndromeVec P.s) (i : Fin P.b) :
    P.errBits (P.errorOf σ fun _ => false) i = decide ((finFunctionFinEquiv σ : ℕ) = i.val + 1) := by
  have hz : ((finFunctionFinEquiv (0 : SyndromeVec P.s) : Fin (2 ^ P.s)) : ℕ) = 0 := by
    simp [finFunctionFinEquiv_apply]
  unfold StarParams.errBits StarParams.errorOf
  simp only [C4Geo.syndrome_false P, zero_add]
  split_ifs with h
  · subst h
    rw [hz]
    simp
  · have hne : (finFunctionFinEquiv σ : ℕ) ≠ 0 := by
      intro e
      apply h
      apply finFunctionFinEquiv.injective
      apply Fin.ext
      rw [e, hz]
    rw [decide_eq_decide]
    simp only [Option.some.injEq, Fin.ext_iff]
    constructor <;> intro e <;> omega

/-- **Block `j` of the offset is the unit vector of the code `t_j`** (its column, P3:1202-1207). -/
theorem offBlock_codes (P : StarParams) (ts : List ℕ) (j : Fin P.r) (i : Fin P.b) :
    C4Geo.offBlock P (P.translationOfCodes ts) j i = decide (ts.getD j.val 0 % 2 ^ P.s = i.val + 1) := by
  unfold C4Geo.offBlock
  rw [errBits_zero]
  simp [StarParams.translationOfCodes]

/-- **The offset word is the partition's coset offset** at the call's translation (P3:1206-1207). -/
theorem offW_eq (P : StarParams) (ts : List ℕ) (hl : ts.length = P.r) (hts : ∀ t ∈ ts, t < 2 ^ P.s) :
    offW P.b (P.n - P.r * P.b) ts = List.ofFn (C4Geo.offset P (P.translationOfCodes ts)) := by
  have hrb := P.r_mul_b_le
  have hbp := P.b_pos
  have hL : (ts.flatMap (FinalPass.Sample.oneHot P.b)).length = P.r * P.b := by
    rw [FinalPass.Sample.length_flatMap_oneHot, hl]
  apply List.ext_getElem
  · simp only [offW, List.length_append, hL, List.length_replicate, List.length_ofFn]
    omega
  · intro q h1 h2
    rw [List.getElem_ofFn]
    have hq : q < P.n := by simpa using h2
    unfold offW
    by_cases hqb : q < P.r * P.b
    · rw [List.getElem_append_left (by rw [hL]; exact hqb), FinalPass.Sample.getElem_flatMap_oneHot]
      have hj : q / P.b < P.r := (Nat.div_lt_iff_lt_mul hbp).mpr hqb
      have hi : q % P.b < P.b := Nat.mod_lt _ hbp
      have hx : (⟨q, hq⟩ : Fin P.n) = P.blockCoord ⟨q / P.b, hj⟩ ⟨q % P.b, hi⟩ := by
        apply Fin.ext
        rw [C4Geo.bc_val]
        exact (Nat.div_add_mod' q P.b).symm
      rw [hx, C4Geo.offset_block, offBlock_codes]
      have hjl : q / P.b < ts.length := by rw [hl]; exact hj
      have hg : ts.getD (q / P.b) 0 = ts[q / P.b] := by simp [List.getD_eq_getElem?_getD, hjl]
      simp only [Fin.val_mk]
      rw [hg, Nat.mod_eq_of_lt (hts _ (List.getElem_mem hjl))]
    · rw [List.getElem_append_right (by rw [hL]; omega), List.getElem_replicate]
      exact (C4Geo.offset_free P _ ⟨q, hq⟩ (by show P.r * P.b ≤ q; omega)).symm

/-! ## Arithmetic of the call's star numbers -/

theorem half_split (P : StarParams) : P.r * P.b = P.r / 2 * P.b + P.r / 2 * P.b := by
  obtain ⟨k, hk⟩ := P.r_even
  rw [hk, show (k + k) / 2 = k by omega]
  ring

theorem kh_le (P : StarParams) : P.s * (P.r / 2) ≤ P.n := by
  have h0 : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  have h1 : P.s ≤ P.b := by have := P.b_succ; omega
  have h2 : P.s * (P.r / 2) ≤ P.b * (P.r / 2) := Nat.mul_le_mul_right _ h1
  have h3 : P.b * (P.r / 2) ≤ P.r * P.b := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
  have := P.r_mul_b_le
  omega

/-! ## The header's register bounds -/

theorem nw_le_flatMap : ∀ (xs : List ℕ) (x : ℕ), x ∈ xs → (natWord x).length ≤ (xs.flatMap natWord).length
  | [], x, h => by simp at h
  | y :: ys, x, h => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with e | e
    · rw [e]; omega
    · have := nw_le_flatMap ys x e; omega

theorem count_le_flatMap : ∀ (xs : List ℕ), xs.length ≤ (xs.flatMap natWord).length
  | [] => by simp
  | y :: ys => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, natWord_length']
    have := count_le_flatMap ys
    omega

/-- The header skip's register bounds, from `4|w| + 4 ≤ cap`. -/
theorem head_caps (r : PrimRequest) (cap : ℕ) (hc : 4 * r.word.length + 4 ≤ cap) :
    2 ^ (natBitLength r.a + 1) ≤ cap ∧ (∀ x ∈ PrimAsm.Codec.codeList r, natBitLength x + 1 ≤ cap) ∧ r.a ≤ cap ∧
      2 ^ (natBitLength (PrimAsm.Codec.carrierCodes r).length + 1) ≤ cap ∧
      (∀ x ∈ PrimAsm.Codec.carrierCodes r, natBitLength x + 1 ≤ cap) ∧ (PrimAsm.Codec.carrierCodes r).length ≤ cap ∧
      natBitLength r.translation.length + 1 ≤ cap := by
  have hlen : r.word.length = (natWord r.n).length + 1 + (natWord r.a).length +
      ((PrimAsm.Codec.codeList r).flatMap natWord).length + (natWord (PrimAsm.Codec.carrierCodes r).length).length +
      ((PrimAsm.Codec.carrierCodes r).flatMap natWord).length + (natWord r.translation.length).length +
      (r.translation.flatMap natWord).length := by
    rw [word_split]
    simp only [preT, List.length_append, List.length_singleton]
    try omega
  have hcl' : (PrimAsm.Codec.codeList r).length = r.a := by simp [PrimAsm.Codec.codeList]
  have c1 := count_le_flatMap (PrimAsm.Codec.codeList r)
  have c2 := count_le_flatMap (PrimAsm.Codec.carrierCodes r)
  have p1 := PrimAsm.CopyNat.two_pow_natBitLength_le r.a
  have p2 := PrimAsm.CopyNat.two_pow_natBitLength_le (PrimAsm.Codec.carrierCodes r).length
  have n3 := natWord_length' r.translation.length
  refine ⟨?_, fun x hx => ?_, ?_, ?_, fun x hx => ?_, ?_, ?_⟩
  · rw [pow_succ]; omega
  · have := nw_le_flatMap _ x hx; have := natWord_length' x; omega
  · omega
  · rw [pow_succ]; omega
  · have := nw_le_flatMap _ x hx; have := natWord_length' x; omega
  · omega
  · omega

/-! ## The streams' set-up -/

section Setup
variable (cap : ℕ)

theorem sG_blank (w : List Bool) (n W : ℕ) (i : Fin (GS + 1)) (h0 : i ≠ gIN) (h1 : i ≠ gNT) (h2 : i ≠ gCT)
    (h3 : i ≠ gAUX) : (σG w n W).st i = [] := by
  simp [σG, h0, h1, h2, h3]

/-- The error words' stale frames and the three counters at `0`. -/
def initAll : WM GS GR :=
  .seq (initStream sEL 0) (.seq (initStream sER 0) (.seq (initStream sCL 8) (.seq (initStream sCR 8)
    (initStream sTOT 8))))

/-- Its cost. -/
def initAllCost (n kh : ℕ) : ℕ :=
  initCost n + 1 + (initCost n + 1 + (initCost kh + 1 + (initCost kh + 1 + initCost kh)))

theorem initAll_spec (σ : WState GS GR) (n kh : ℕ) (h0 : σ.val 0 = n) (h8 : σ.val 8 = kh)
    (hEL : σ.st sEL = []) (hELh : σ.sh sEL = 0) (hER : σ.st sER = []) (hERh : σ.sh sER = 0)
    (hCL : σ.st sCL = []) (hCLh : σ.sh sCL = 0) (hCR : σ.st sCR = []) (hCRh : σ.sh sCR = 0)
    (hT : σ.st sTOT = []) (hTh : σ.sh sTOT = 0) (hJ : σ.val rJ = 0) (hM : σ.val rTmp = 0) (hO : σ.val rOc = 0)
    (hn : 2 * n + 2 ≤ cap) (hk : 2 * kh + 2 ≤ cap) :
    ∃ τ, WExec cap initAll σ τ (initAllCost n kh) ∧
      τ.st sEL = frameP (List.replicate n false) ++ [false] ∧ τ.sh sEL = 0 ∧
      τ.st sER = frameP (List.replicate n false) ++ [false] ∧ τ.sh sER = 0 ∧
      τ.st sCL = frameP (List.replicate kh false) ++ [false] ∧ τ.sh sCL = 0 ∧
      τ.st sCR = frameP (List.replicate kh false) ++ [false] ∧ τ.sh sCR = 0 ∧
      τ.st sTOT = frameP (List.replicate kh false) ++ [false] ∧ τ.sh sTOT = 0 ∧
      (∀ i, i ≠ sEL → i ≠ sER → i ≠ sCL → i ≠ sCR → i ≠ sTOT → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ q, τ.val q = σ.val q) ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, e1, a1, b1, c1, d1, f1⟩ := initStream_spec cap sEL 0 (by decide) (by decide) (by decide) σ n h0
    hEL hELh hJ hM hO hn
  obtain ⟨τ2, e2, a2, b2, c2, d2, f2⟩ := initStream_spec cap sER 0 (by decide) (by decide) (by decide) τ1 n
    (by rw [d1, h0]) (by rw [(c1 sER (by decide)).1, hER]) (by rw [(c1 sER (by decide)).2, hERh])
    (by rw [d1, hJ]) (by rw [d1, hM]) (by rw [d1, hO]) hn
  obtain ⟨τ3, e3, a3, b3, c3, d3, f3⟩ := initStream_spec cap sCL 8 (by decide) (by decide) (by decide) τ2 kh
    (by rw [d2, d1, h8]) (by rw [(c2 sCL (by decide)).1, (c1 sCL (by decide)).1, hCL])
    (by rw [(c2 sCL (by decide)).2, (c1 sCL (by decide)).2, hCLh])
    (by rw [d2, d1, hJ]) (by rw [d2, d1, hM]) (by rw [d2, d1, hO]) hk
  obtain ⟨τ4, e4, a4, b4, c4, d4, f4⟩ := initStream_spec cap sCR 8 (by decide) (by decide) (by decide) τ3 kh
    (by rw [d3, d2, d1, h8])
    (by rw [(c3 sCR (by decide)).1, (c2 sCR (by decide)).1, (c1 sCR (by decide)).1, hCR])
    (by rw [(c3 sCR (by decide)).2, (c2 sCR (by decide)).2, (c1 sCR (by decide)).2, hCRh])
    (by rw [d3, d2, d1, hJ]) (by rw [d3, d2, d1, hM]) (by rw [d3, d2, d1, hO]) hk
  obtain ⟨τ5, e5, a5, b5, c5, d5, f5⟩ := initStream_spec cap sTOT 8 (by decide) (by decide) (by decide) τ4 kh
    (by rw [d4, d3, d2, d1, h8])
    (by rw [(c4 sTOT (by decide)).1, (c3 sTOT (by decide)).1, (c2 sTOT (by decide)).1, (c1 sTOT (by decide)).1, hT])
    (by rw [(c4 sTOT (by decide)).2, (c3 sTOT (by decide)).2, (c2 sTOT (by decide)).2, (c1 sTOT (by decide)).2, hTh])
    (by rw [d4, d3, d2, d1, hJ]) (by rw [d4, d3, d2, d1, hM]) (by rw [d4, d3, d2, d1, hO]) hk
  refine ⟨τ5, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i i1 i2 i3 i4 i5 => ⟨?_, ?_⟩, fun q => ?_, ?_⟩
  · rw [(c5 sEL (by decide)).1, (c4 sEL (by decide)).1, (c3 sEL (by decide)).1, (c2 sEL (by decide)).1, a1]
  · rw [(c5 sEL (by decide)).2, (c4 sEL (by decide)).2, (c3 sEL (by decide)).2, (c2 sEL (by decide)).2, b1]
  · rw [(c5 sER (by decide)).1, (c4 sER (by decide)).1, (c3 sER (by decide)).1, a2]
  · rw [(c5 sER (by decide)).2, (c4 sER (by decide)).2, (c3 sER (by decide)).2, b2]
  · rw [(c5 sCL (by decide)).1, (c4 sCL (by decide)).1, a3]
  · rw [(c5 sCL (by decide)).2, (c4 sCL (by decide)).2, b3]
  · rw [(c5 sCR (by decide)).1, a4]
  · rw [(c5 sCR (by decide)).2, b4]
  · exact a5
  · exact b5
  · rw [(c5 i i5).1, (c4 i i4).1, (c3 i i3).1, (c2 i i2).1, (c1 i i1).1]
  · rw [(c5 i i5).2, (c4 i i4).2, (c3 i i3).2, (c2 i i2).2, (c1 i i1).2]
  · rw [d5, d4, d3, d2, d1]
  · rw [f5, f4, f3, f2, f1]

end Setup

/-! ## From the start state to the loops' invariant -/

/-- **The set-up**: the star numbers, the header skip, the offset, the streams, the row flag. -/
def initW (cr : ℕ) : WM GS GR :=
  .seq (PrimAsm.GeoNums.p1W cr) (.seq skipHead (.seq offPart (.seq initAll (.inc rGoL))))

/-- Its cost. -/
def initWCost (r : PrimRequest) (P : StarParams) (cr : ℕ) : ℕ :=
  numsCost P.n cr + 1 + (skipHeadCost r + 1 + (offCost P.b (P.n - P.r * P.b) r.translation + 1 +
    (initAllCost P.n (P.s * (P.r / 2)) + 1 + 3)))

theorem RD_hi : ∀ i : Fin 12, 4 ≤ i.val → 20 ≤ (RD i).val := by decide

/-- **The set-up reaches the loops' invariant** at the first cell, no output yet, the coset offset
`C4Geo.offset P σ` on `sOFF` (P3:1206-1207). -/
theorem init_spec (cr W : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (r : PrimRequest) (hn : r.n = P.n)
    (hl : r.translation.length = P.r) (hts : ∀ t ∈ r.translation, t < 2 ^ P.s) (hW : 2 * P.n + cr + 20 ≤ W)
    (hcap : 4 * r.word.length + 8 * P.n + 8 ≤ 2 * W + 2) :
    ∃ σ, WExec (2 * W + 2) (initW cr) (σG r.word P.n W) σ (initWCost r P cr) ∧
      FS P.s P.b (P.r / 2) (P.n - P.r * P.b) (σG r.word P.n W) σ
        (List.ofFn (C4Geo.offset P (P.translationOfCodes r.translation)))
        (List.replicate P.n false) (List.replicate P.n false) 0 0 [] 0 1 := by
  have hrb := P.r_mul_b_le
  have hsplit := half_split P
  have hkh := kh_le P
  have hbs := P.b_succ
  have hbn := PrimAsm.GeoNums.b_le P
  have hr4 := P.four_r_le_n
  -- the numbers
  have hw : r.word = natWord P.n ++ ([PrimAsm.Codec.modeBit r.mode] ++ natWord r.a ++
      (PrimAsm.Codec.codeList r).flatMap natWord ++ natWord (PrimAsm.Codec.carrierCodes r).length ++
      (PrimAsm.Codec.carrierCodes r).flatMap natWord ++ natWord r.translation.length ++
      r.translation.flatMap natWord) := by
    rw [word_split, ← hn]
    simp only [preT, List.append_assoc]
  obtain ⟨σ2, e2, s2, h2g, h2o, v0, v3, v4, v5, v6, v7, v8, vz, c2⟩ := nums_spec cr W P hrP r.word _ hw hW
  -- the header
  obtain ⟨ha, hcode, hcl, hk, hcc, hkl, htl⟩ := head_caps r (2 * W + 2) (by omega)
  have hst2 : σ2.st gIN = marks (preT r ++ r.translation.flatMap natWord) ++ [false] := by
    rw [s2]
    simp only [σG, ↓reduceIte]
    rw [PrimAsm.GeoNums.frame_marksG, word_split]
  obtain ⟨σ3, e3, s3, h3g, h3o, v3a, c3⟩ := skipHead_spec (2 * W + 2) r σ2 hst2 (by rw [h2g, hn]) vz ha hcode hcl
    hk hcc hkl htl
  -- the offset
  have hst3 : σ3.st gIN = marks (preT r) ++ marks (r.translation.flatMap natWord) ++ [false] := by
    rw [s3, hst2, Streaming.marks_append]
  obtain ⟨σ4, e4, o4, oh4, g4, gh4, f4, v4a, c4⟩ := offPart_spec (2 * W + 2) P.b (P.n - P.r * P.b) r.translation
    (marks (preT r)) [false] σ3 hst3 (by rw [h3g, Streaming.marks_length])
    (by rw [s3, s2]; exact sG_blank _ _ _ _ (by decide) (by decide) (by decide) (by decide))
    (by rw [h3o sOFF (by decide), h2o sOFF (by decide)])
    ((v3a rReg).trans (v3.trans hl.symm)) ((v3a bReg).trans v5) ((v3a tReg).trans v7)
    (fun q hq => (v3a q).trans (vz q hq))
    (fun t ht => by have := hts t ht; omega)
    (fun t ht => by
      have h1 := hts t ht
      have h2 := PrimAsm.CopyNat.two_pow_natBitLength_le t
      rw [pow_succ]
      omega)
    (by rw [hl, Nat.mul_comm P.b P.r]; omega) (by rw [hl]; omega)
  -- the streams
  have hEm : ∀ i, i ≠ sOFF → i ≠ gIN → i ≠ gNT → i ≠ gCT → i ≠ gAUX → σ4.st i = [] ∧ σ4.sh i = 0 := by
    intro i i1 i2 i3 i4 i5
    refine ⟨?_, ?_⟩
    · rw [(f4 i i1 i2).1, s3, s2]
      exact sG_blank _ _ _ _ i2 i3 i4 i5
    · rw [(f4 i i1 i2).2, h3o i i2, h2o i i2]
  obtain ⟨σ5, e5, a5, a5h, b5, b5h, cl5, cl5h, cr5, cr5h, t5, t5h, o5, v5a, c5⟩ := initAll_spec (2 * W + 2) σ4
    P.n (P.s * (P.r / 2)) (by rw [v4a, v3a, v0]) (by rw [v4a, v3a, v8])
    (hEm sEL (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (hEm sEL (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (hEm sER (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (hEm sER (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (hEm sCL (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (hEm sCL (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (hEm sCR (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (hEm sCR (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (hEm sTOT (by decide) (by decide) (by decide) (by decide) (by decide)).1
    (hEm sTOT (by decide) (by decide) (by decide) (by decide) (by decide)).2
    (by rw [v4a, v3a]; exact vz _ (by decide)) (by rw [v4a, v3a]; exact vz _ (by decide))
    (by rw [v4a, v3a]; exact vz _ (by decide)) (by omega) (by omega)
  -- the row flag
  have e6 := WExec.inc (cap := 2 * W + 2) rGoL σ5 (by rw [v5a, v4a, v3a, vz rGoL (by decide)]; omega)
  have vI : ∀ q, q ≠ rGoL → (σ5.setv rGoL (σ5.val rGoL + 1)).val q = σ2.val q := by
    intro q hq
    simp only [WState.setv, Function.update_apply, if_neg hq]
    rw [v5a, v4a, v3a]
  have hoff := offW_eq P r.translation hl hts
  have hlo : (offW P.b (P.n - P.r * P.b) r.translation).length = P.r * P.b + (P.n - P.r * P.b) := by
    simp only [offW, List.length_append, FinalPass.Sample.length_flatMap_oneHot, List.length_replicate, hl]
  refine ⟨_, WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))), ?_⟩
  exact {
    lOF := by rw [← hoff, hlo]; omega
    lEL := by rw [List.length_replicate]; omega
    lER := by rw [List.length_replicate]; omega
    stOF := by
      show σ5.st sOFF = _
      rw [(o5 sOFF (by decide) (by decide) (by decide) (by decide) (by decide)).1, o4, hoff]
    shOF := by
      show σ5.sh sOFF = 0
      rw [(o5 sOFF (by decide) (by decide) (by decide) (by decide) (by decide)).2, oh4]
    stEL := a5
    shEL := a5h
    stER := b5
    shER := b5h
    nL := ⟨by show σ5.st sCL = _; rw [cl5, binary_zero, frame_eq_frameP], cl5h⟩
    nR := ⟨by show σ5.st sCR = _; rw [cr5, binary_zero, frame_eq_frameP], cr5h⟩
    nT := ⟨by show σ5.st sTOT = _; rw [t5, binary_zero, frame_eq_frameP], t5h⟩
    sO := by
      show σ5.st gOUT = []
      rw [(o5 gOUT (by decide) (by decide) (by decide) (by decide) (by decide)).1]
      exact (hEm gOUT (by decide) (by decide) (by decide) (by decide) (by decide)).1
    hO := by
      show σ5.sh gOUT = ([] : List Bool).length
      rw [(o5 gOUT (by decide) (by decide) (by decide) (by decide) (by decide)).2]
      exact (hEm gOUT (by decide) (by decide) (by decide) (by decide) (by decide)).2
    sIN := by
      show σ5.st gIN = _
      rw [(o5 gIN (by decide) (by decide) (by decide) (by decide) (by decide)).1, g4, s3, s2]
    vS := by rw [vI _ (RD_goL 0)]; exact v4
    vB := by rw [vI _ (RD_goL 1)]; exact v5
    vH := by rw [vI _ (RD_goL 2)]; exact v6
    vT := by rw [vI _ (RD_goL 3)]; exact v7
    vZ := fun i hi => by rw [vI _ (RD_goL i)]; exact vz _ (RD_hi i hi)
    vAcc := by rw [vI _ (by decide)]; exact vz _ (by decide)
    vCnt := by rw [vI _ (by decide)]; exact vz _ (by decide)
    vNz := by rw [vI _ (by decide)]; exact vz _ (by decide)
    vScn := by rw [vI _ (by decide)]; exact vz _ (by decide)
    vF := by rw [vI _ (by decide)]; exact vz _ (by decide)
    vR := by rw [vI _ (by decide)]; exact vz _ (by decide)
    vgR := by rw [vI _ (by decide)]; exact vz _ (by decide)
    vgL := by
      simp only [WState.setv, Function.update_apply, ↓reduceIte]
      rw [v5a, v4a, v3a, vz rGoL (by decide)] }

end NearCubicWires.WireExponent3_5.PrimT.Flips
