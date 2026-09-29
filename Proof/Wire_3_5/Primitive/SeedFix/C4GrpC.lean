import Proof.Wire_3_5.Primitive.SeedFix.C4GrpB

/-! # C4.K side conditions, part 3: the group's sizes at the call's entries (the T-b; `GroupSmall`)

P3:3011-3016, 3034-3038: at the enumeration context `jX P (chunk 2^{kh} n_T R batch) TWd Cap p'` of a child prefix,
every size the group's machines read (the fields' widths, the entries, each fold state, row and product, the final
fold state, the output before counter value `j`) is below one explicit number `qG` of the call's `ℓ`, `kh`, `n_T`,
`R`, `TWd`, `|p'|` and `b = bsz batch`: `Fs = b^{8R}·(T₀ + 8R·b + 1) + 1` bounds every fold word
(`T₀ = 2(16kh + 8ℓ + 2) + 2` the coefficient term's word), `n_T·2^w·Fs + 1` the output.

* `ESzT`, `FoldSmallT`, `EntsSmallT`, `GroupSmallT` (definitionally `ESz`, `FoldSmall`, `EntsSmall`,
  `GroupSmall`), `T0`, `Fs`, `qG`; `cf_inv`, `inv_fcSt`, **`groupSmall_of`**.

Paper quantity of the main type: the sizes of the printed objective's groups at the call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Grp
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open Split Cells Valid Cons FetchAll FetchCells Emit JBank JStages JBody SplitT JEnum

/-! ## The size predicates (the reference one, verbatim) -/

def ESzT (q : ℕ) (V : SExpr) : Prop := (exprWord V).length ≤ q ∧ V.length ≤ q

def FoldSmallT (q : ℕ) (s0 : FoldSt) (rs : List SExpr) : Prop :=
  rs.length ≤ q ∧ ∀ r, r < rs.length → ESzT q (foldAt s0 rs r).A ∧ ESzT q (rs.getD r []) ∧
    (exprWord (smul (foldAt s0 rs r).A (rs.getD r []))).length ≤ q

def EntsSmallT (q : ℕ) (ents : List (List SExpr)) : Prop :=
  ents.length ≤ q ∧ ∀ j, j < ents.length → (ents.getD j []).length ≤ q ∧ ∀ V ∈ ents.getD j [], (exprWord V).length ≤ q

def GroupSmallT (q : ℕ) (X : JCtx) (j : ℕ) (V : SExpr) : Prop :=
  X.P.ell ≤ q ∧ 2 * X.P.kh ≤ q ∧ 8 ≤ q ∧ X.plen ≤ q ∧ (X.consJ j).length ≤ q ∧ X.eJ j ≤ q ∧ X.TWd ≤ q ∧ X.Wt ≤ q ∧
    (X.esJ j).length ≤ q ∧ EntsSmallT q X.ents ∧
    (∀ k, k < (X.esJ j).length →
      FoldSmallT q (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) k) (X.ents.getD ((X.esJ j).getD k 0) []) ∧
        ((X.csJ j).getD k []).length ≤ q) ∧
    (exprWord V).length ≤ q ∧
    (exprWord (FetchCells.fcSt (aOnly (X.cfJ j)) X.ents (X.esJ j) (X.esJ j).length).A).length ≤ q

/-! ## The bounds -/

/-- The coefficient term's word bound. -/
def T0 (P : SeedParams) : ℕ := 2 * (16 * P.kh + 8 * P.ell + 2) + 2

/-- Every fold word's bound. -/
def Fs (P : SeedParams) (R b : ℕ) : ℕ := b ^ (8 * R) * (T0 P + 8 * R * b + 1) + 1

/-- **The group's size bound** at the call. -/
def qG (P : SeedParams) (nT R b TWd plen : ℕ) : ℕ :=
  8 * P.ell + 2 * P.kh + TWd + 8 + plen + R + b + nT * (2 ^ P.kh) ^ 2 +
    (nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + 1) * Fs P R b

theorem cf_inv (X : JCtx) (j : ℕ) : Inv (X.cfJ j) 1 (T0 X.P) := by
  refine ⟨by simp [JCtx.cfJ, coefT], fun a ha => ?_⟩
  simp only [JCtx.cfJ, coefT, List.mem_singleton] at ha
  subst ha
  rw [termWord_len, coefWord_len]
  have hc : (binary 8 j).count true ≤ 8 := le_trans (List.count_le_length) (by simp)
  have he : X.eJ j ≤ 8 * X.P.ell := Nat.sub_le_sub_right (Nat.sub_le _ _) _ |>.trans (Nat.sub_le _ _)
  have hn : ((if parity (binary 8 j) = true then (-1 : ℤ) else 1) * 2 ^ (2 * X.P.kh * SeedFix.cnt (binary 8 j)
      (binary 8 j).length + X.eJ j)).natAbs.bits.length = 2 * X.P.kh * SeedFix.cnt (binary 8 j) (binary 8 j).length + X.eJ j + 1 := by
    rw [Int.natAbs_mul]
    split_ifs <;> simp [Nat.size_eq_bits_len, Nat.size_pow]
  rw [hn]
  have hcn : SeedFix.cnt (binary 8 j) (binary 8 j).length ≤ 8 := by
    unfold SeedFix.cnt; exact le_trans List.count_le_length (by simp)
  have : 2 * X.P.kh * SeedFix.cnt (binary 8 j) (binary 8 j).length ≤ 2 * X.P.kh * 8 := Nat.mul_le_mul_left _ hcn
  simp only [List.flatMap_nil, List.length_nil]
  unfold T0
  omega

/-- The fetched entries' fold. -/
theorem inv_fcSt (ents : List (List SExpr)) (R b : ℕ) (hb : 1 ≤ b) :
    ∀ (L : List ℕ) (s : FoldSt) (c T : ℕ), Inv s.A c T →
      (∀ e ∈ L, (ents.getD e []).length ≤ R ∧ ∀ V ∈ ents.getD e [], RowOk b V) →
      Inv (L.foldl (fun s e => foldAt s (ents.getD e []) (ents.getD e []).length) s).A (c * b ^ (L.length * R))
        (T + L.length * R * b)
  | [], s, c, T, h, _ => by simpa using h
  | e :: L, s, c, T, h, he => by
    rw [List.foldl_cons]
    have hrows : (foldAt s (ents.getD e []) (ents.getD e []).length).A =
        ((ents.getD e []).foldl FoldSt.step s).A := by
      unfold foldAt; rw [List.take_length]
    have h1 := inv_foldl b (ents.getD e []) s c T h (he e List.mem_cons_self).2
    rw [← hrows] at h1
    have hlen := (he e List.mem_cons_self).1
    have h1' := inv_mono h1 (Nat.mul_le_mul_left c (Nat.pow_le_pow_right hb hlen))
      (Nat.add_le_add_left (Nat.mul_le_mul_right b hlen) T)
    have h2 := inv_fcSt ents R b hb L _ (c * b ^ R) (T + R * b) h1' (fun e' he' => he e' (List.mem_cons_of_mem _ he'))
    refine inv_mono h2 (le_of_eq ?_) (le_of_eq ?_)
    · simp only [List.length_cons]; rw [Nat.mul_assoc, ← pow_add]; ring_nf
    · simp only [List.length_cons]; ring

theorem inv_flatMap {α : Type} (f : α → SExpr) (c T : ℕ) :
    ∀ (l : List α), (∀ i ∈ l, Inv (f i) c T) → Inv (l.flatMap f) (l.length * c) T
  | [], _ => ⟨by simp, by simp⟩
  | i :: l, h => by
    have h1 := h i List.mem_cons_self
    have h2 := inv_flatMap f c T l (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))
    refine ⟨?_, fun a ha => ?_⟩
    · simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := h1.1; have := h2.1; nlinarith
    · rw [List.flatMap_cons, List.mem_append] at ha
      rcases ha with ha | ha
      · exact h1.2 a ha
      · exact h2.2 a ha

theorem chunk_entry_len (N nT R : ℕ) (batch : List SExpr) (e : ℕ) :
    ((JLink.chunk N nT R batch).getD e []).length ≤ R := by
  by_cases he : e < (JLink.chunk N nT R batch).length
  · rw [List.getD_eq_getElem _ _ he]
    unfold JLink.chunk
    simp
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

section Call
variable (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (TWd Cap : ℕ) (p' : List Bool)

/-- **The group's sizes at the call's entries** (`GroupSmall` at `qG`). -/
theorem groupSmall_of (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (hplen : p'.length ≤ 8 * P.ell) (j : ℕ)
    (hj : j < nT * 2 ^ (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p').w) :
    GroupSmallT (qG P nT R (bsz batch) TWd p'.length)
      (at_ (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p')
        (tOf (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') j)) j
      (outAt (C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') j) := by
  set X := C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p' with hX
  set b := bsz batch with hbd
  have hb := bsz_pos batch
  rw [← hbd] at hb
  have hw : X.w = 8 + 8 * P.ell + 8 * P.kh := rfl
  have hFq : Fs P R b ≤ qG P nT R b TWd p'.length := by
    have := Nat.le_mul_of_pos_left (Fs P R b) (by omega : 0 < nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + 1)
    unfold qG; omega
  have hrow : ∀ e, ∀ V ∈ (JLink.chunk (2 ^ P.kh) nT R batch).getD e [], RowOk b V :=
    chunk_rowOk _ _ _ batch hpm
  have hmono : ∀ {A : SExpr} {m : ℕ}, m ≤ 8 * R → Inv A (1 * b ^ m) (T0 P + m * b) →
      Inv A (b ^ (8 * R)) (T0 P + 8 * R * b) := by
    intro A m hm h
    refine inv_mono h ?_ ?_
    · rw [Nat.one_mul]; exact Nat.pow_le_pow_right hb hm
    · exact Nat.add_le_add_left (Nat.mul_le_mul_right b hm) _
  have hFs : ∀ {A : SExpr}, Inv A (b ^ (8 * R)) (T0 P + 8 * R * b) → (exprWord A).length ≤ Fs P R b ∧
      A.length ≤ Fs P R b := by
    intro A h
    refine ⟨inv_expr h, le_trans h.1 ?_⟩
    have := Nat.le_mul_of_pos_right (b ^ (8 * R)) (by omega : 0 < T0 P + 8 * R * b + 1)
    unfold Fs; omega
  -- the output
  have hout : Inv (outAt X j) (j * b ^ (8 * R)) (T0 P + 8 * R * b) := by
    have := inv_flatMap (fun i => (at_ X (tOf X i)).emitJ i) (b ^ (8 * R)) (T0 P + 8 * R * b) (List.range j)
      (fun i _ => by
        show Inv ((at_ X (tOf X i)).emitJ i) _ _
        unfold JCtx.emitJ
        split_ifs
        · have hrs : ((at_ X (tOf X i)).rowsJ i).length ≤ 8 * R := by
            unfold JCtx.rowsJ
            rw [List.length_flatMap]
            have := List.sum_le_card_nsmul (((at_ X (tOf X i)).esJ i).map fun e =>
              ((at_ X (tOf X i)).ents.getD e []).length) R (fun y hy => by
                obtain ⟨e, -, rfl⟩ := List.mem_map.mp hy
                exact chunk_entry_len _ _ _ _ _)
            simp only [List.length_map, esJ_length, smul_eq_mul] at this
            omega
          have h1 := inv_sfold b ((at_ X (tOf X i)).rowsJ i) ((at_ X (tOf X i)).cfJ i) 1 (T0 P) (cf_inv _ i)
            (fun V hV => by
              unfold JCtx.rowsJ at hV
              obtain ⟨e, -, hV⟩ := List.mem_flatMap.mp hV
              exact hrow e V hV)
          exact hmono hrs h1
        · exact ⟨by simp, by simp⟩)
    rw [List.length_range] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_⟩
  · show P.ell ≤ _; unfold qG; omega
  · show 2 * P.kh ≤ _; unfold qG; omega
  · unfold qG; omega
  · show p'.length ≤ _; unfold qG; omega
  · have : ((at_ X (tOf X j)).consJ j).length ≤ 8 := by
      unfold JCtx.consJ consL
      exact le_trans (List.length_filterMap_le _ _) (by simp)
    unfold qG; omega
  · have : (at_ X (tOf X j)).eJ j ≤ 8 * P.ell := by
      unfold JCtx.eJ
      exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
    unfold qG; omega
  · show TWd ≤ _; unfold qG; omega
  · show 2 * P.kh + TWd ≤ _; unfold qG; omega
  · rw [esJ_length]; unfold qG; omega
  · refine ⟨?_, fun e _ => ⟨?_, fun V hV => ?_⟩⟩
    · show (JLink.chunk (2 ^ P.kh) nT R batch).length ≤ _
      rw [chunk_length]; unfold qG; omega
    · exact le_trans (chunk_entry_len _ _ _ _ _) (by unfold qG; omega)
    · exact le_trans (hrow e V hV).1 (by unfold qG; omega)
  · -- the fold of entry `k`
    rw [esJ_length] at hk
    set es := (at_ X (tOf X j)).esJ j with hes
    set rs := (at_ X (tOf X j)).ents.getD (es.getD k 0) [] with hrs
    have hsk : Inv (fcSt (aOnly ((at_ X (tOf X j)).cfJ j)) (at_ X (tOf X j)).ents es k).A
        (1 * b ^ ((es.take k).length * R)) (T0 P + (es.take k).length * R * b) :=
      inv_fcSt _ R b hb (es.take k) _ 1 (T0 P) (cf_inv _ j)
        (fun e _ => ⟨chunk_entry_len _ _ _ _ _, hrow e⟩)
    have htk : (es.take k).length ≤ k := by simp
    have hrsR : rs.length ≤ R := chunk_entry_len _ _ _ _ _
    refine ⟨⟨le_trans hrsR (by unfold qG; omega), fun r hr => ?_⟩, ?_⟩
    · have hfr := inv_foldl b (rs.take r) _ _ _ hsk (fun V hV => hrow _ V (List.mem_of_mem_take hV))
      have htr : (rs.take r).length ≤ r := by simp
      have hm1 : (es.take k).length * R + (rs.take r).length + 1 ≤ 8 * R := by
        have : (es.take k).length * R ≤ 7 * R := Nat.mul_le_mul_right R (by omega)
        omega
      have hfr' : Inv (foldAt (fcSt (aOnly ((at_ X (tOf X j)).cfJ j)) (at_ X (tOf X j)).ents es k) rs r).A
          (1 * b ^ ((es.take k).length * R + (rs.take r).length))
          (T0 P + ((es.take k).length * R + (rs.take r).length) * b) := by
        refine inv_mono hfr (le_of_eq ?_) (le_of_eq ?_)
        · rw [Nat.mul_assoc, ← pow_add]
        · ring
      have hrV := hrow _ (rs.getD r []) (by
        rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr)
      have hsm := inv_smul hfr' (rs.getD r []) b hrV.1 hrV.2
      have hsm' : Inv (smul (foldAt (fcSt (aOnly ((at_ X (tOf X j)).cfJ j)) (at_ X (tOf X j)).ents es k) rs r).A
          (rs.getD r [])) (1 * b ^ ((es.take k).length * R + (rs.take r).length + 1))
          (T0 P + ((es.take k).length * R + (rs.take r).length + 1) * b) := by
        refine inv_mono hsm (le_of_eq ?_) (le_of_eq ?_)
        · rw [pow_succ]; ring
        · ring
      obtain ⟨a1, a2⟩ := hFs (hmono (by omega) hfr')
      obtain ⟨c1, -⟩ := hFs (hmono hm1 hsm')
      refine ⟨⟨le_trans a1 hFq, le_trans a2 hFq⟩, ⟨le_trans hrV.1 (by unfold qG; omega),
        le_trans (len_le_expr _) (le_trans hrV.1 (by unfold qG; omega))⟩, le_trans c1 hFq⟩
    · have : ((at_ X (tOf X j)).csJ j).getD k [] ∈ (at_ X (tOf X j)).csJ j := by
        rw [List.getD_eq_getElem _ _ (by rw [csJ_length]; exact hk)]; exact List.getElem_mem _
      rw [csJ_width _ j _ this]
      show 2 * P.kh ≤ _
      unfold qG; omega
  · -- the output
    have h1 := inv_expr hout
    have h2 : j * b ^ (8 * R) * (T0 P + 8 * R * b + 1) + 1 ≤ nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) * Fs P R b + 1 := by
      have hj' : j ≤ nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) := by rw [← hw]; omega
      have : b ^ (8 * R) * (T0 P + 8 * R * b + 1) ≤ Fs P R b := by unfold Fs; omega
      calc j * b ^ (8 * R) * (T0 P + 8 * R * b + 1) + 1 = j * (b ^ (8 * R) * (T0 P + 8 * R * b + 1)) + 1 := by ring
        _ ≤ nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) * Fs P R b + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul hj' this) 1
    refine le_trans h1 (le_trans h2 ?_)
    unfold qG; nlinarith
  · -- the final fold state
    have h8 := inv_fcSt (at_ X (tOf X j)).ents R b hb ((at_ X (tOf X j)).esJ j) (aOnly ((at_ X (tOf X j)).cfJ j))
      1 (T0 P) (cf_inv (at_ X (tOf X j)) j) (fun e _ => ⟨chunk_entry_len _ _ _ _ _, hrow e⟩)
    rw [esJ_length] at h8
    have hfin : fcSt (aOnly ((at_ X (tOf X j)).cfJ j)) (at_ X (tOf X j)).ents ((at_ X (tOf X j)).esJ j)
        ((at_ X (tOf X j)).esJ j).length = ((at_ X (tOf X j)).esJ j).foldl
          (fun s e => foldAt s ((at_ X (tOf X j)).ents.getD e []) ((at_ X (tOf X j)).ents.getD e []).length)
          (aOnly ((at_ X (tOf X j)).cfJ j)) := by
      unfold fcSt; rw [List.take_length]
    rw [hfin]
    exact le_trans (hFs (hmono le_rfl h8)).1 hFq

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4Grp
