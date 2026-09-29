import Proof.Wire_3_5.Primitive.Writers.PopSetupSpecB2

/-! # PA POP setup, part 1: the POP row's block bound, the need's measure and the power scale

C2's POP row record (`popRowRec … (popStates …)`, P3:1519-1526) at Route B's capacities (`PopCap.popKc`, `popPW`,
`popCapB`) is what the POP setup must make room for. This part fixes the numbers `PopSetupSpecB2` asks for:
* **`blockC_len`**, **`blockC_le`**: the exact length of a visit factor's block, and `2·|blockC| + 2 ≤ blF` (the block
  bound `PopNums.blF` is tight); with it **`pop_hok`** (`PopReady.hok` at the explicit `popR`, `popCp`);
* **`rank_facts`** (`PopReady.hpad`, `hps`, `hsd`, `hlb`, `hnJ`);
* the need's measure **`popX`** (`PopSetupSpecB2.need_le`'s: `(8L+2)^(3·lbP+1) + popMlab + r4 + M + B + errExp +
  |FlatSeed| + 2`), the power scale **`popU = 2^20·popX`** and the need **`popNeed = popU^40`**, with
  **`popNeed_le`** (`popNeed ≤ 2^800·popX^40`);
* every number of the row against `U` (**`basic`**: `L`, `3·lbP`, `M`, the walk length, the threshold, `Mlab`,
  `r4 + G + off`, `J`, `S`, `errExp`, the rank and side bits, `Q = (8L+2)^d` at most `U`; `|levelWord| ≤ U^7`,
  `capP ≤ U^8`, `CAP`, `LL ≤ U^3`).

Paper quantity of the main type: C2's POP row capacities (Route B) and the POP setup's capacity need, polynomial in
the row's numbers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetupMath
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec

theorem clog_le_self' (x : ℕ) : Nat.clog 2 x ≤ x := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem frame_len (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [frame, List.length_cons, ih]; ring

theorem fieldsWord_len (ws : List (List Bool)) :
    (fieldsWord ws).length = (ws.map fun w => 2 * w.length + 1).sum := by
  unfold fieldsWord
  rw [List.length_flatMap]
  simp only [frame_len]

theorem dataC_list (D : ListData) (L s : ℕ) (sgn neg : Bool) :
    List.ofFn (dataC D L s sgn neg) =
      ListEval.levelWord D.M D.J D.W (ListEval.rowsOf D L) :: ListEval.unary s ::
        List.replicate (capC D L + 1) false :: [sgn] ::
        (List.replicate 15 (List.replicate (capC D L + 1) false) ++ [[neg]]) := by
  rfl

theorem labelWord_len (labs : List ℕ) : (labelWord labs).length = (labs.map fun lab => lab + 1).sum + 1 := by
  unfold labelWord
  rw [List.length_append, List.length_flatMap]
  simp [Rec.atomCode]

theorem blockC_len (D : ListData) (L s : ℕ) (sgn neg : Bool) (labs : List ℕ) :
    (blockC D L s sgn neg labs).length = 64 * L + 2 * (3 * listBound D) + 2 * (labs.map fun lab => lab + 1).sum +
      2 * cap1C L labs + 2 * (ListEval.levelWord D.M D.J D.W (ListEval.rowsOf D L)).length + 2 * s +
      32 * capC D L + 93 := by
  unfold blockC factorBlock
  rw [fieldsWord_len]
  unfold factorFields
  rw [dataC_list, List.map_append, List.sum_append]
  have hx : Print.xsAt (4 * L) (3 * listBound D) 0 = SignedSortKey.binary (4 * L) 0 := rfl
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_append, List.sum_append,
    List.map_replicate, List.sum_replicate, hx, frame_len, SignedSortKey.binary_length, List.length_replicate,
    List.length_cons, List.length_nil, List.length_append, labelWord_len, ListEval.unary, smul_eq_mul]
  ring

theorem labE_flat_len (labs : List ℕ) : (labs.flatMap labE).length = 4 * (labs.map fun lab => lab + 1).sum := by
  rw [List.length_flatMap]
  simp only [Emit.labE_length]
  induction labs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring

theorem cap1C_eq (L : ℕ) (labs : List ℕ) (hlen : labs.length = 4 * L) : cap1C L labs = labSum labs := by
  unfold cap1C
  rw [← hlen, labCost_eq]
  have := labSum_ge labs
  unfold labSum
  omega

/-- **The visit block's bound** (`hBL` of `popStates_okB` at `BL = blF …`): `2·|blockC| + 2 ≤ blF`. -/
theorem blockC_le (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (k : Fin P.walkLen) (s : ℕ) (hs : s ≤ P.M)
    (sgn neg : Bool) (labs : List ℕ) (hlen : labs.length = 4 * L) :
    2 * (blockC (visitData P e k) L s sgn neg labs).length + 2 ≤
      PopNums.blF L (3 * PopLink.lbP P) (PopLink.capP P L) (labSum labs) ((labs.flatMap labE).length)
        (PopParams.lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J L + P.M + 2) P.M := by
  rw [blockC_len, PopLink.listBound_visit, PopLink.capC_visit, cap1C_eq L labs hlen, labE_flat_len]
  have hlw := PopParams.levelWord_length P.base L (ListEval.rowsOf (visitData P e k) L)
    (fun j _ => by simp [ListEval.rowsOf])
  have e1 : (ListEval.levelWord (visitData P e k).M (visitData P e k).J (visitData P e k).W
      (ListEval.rowsOf (visitData P e k) L)).length =
      PopParams.lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.base.B)) P.base.J L + P.base.M + 2 := hlw
  rw [e1]
  have hM : P.base.M = P.M := rfl
  unfold PopNums.blF
  rw [hM]
  omega

/-! ## The POP-ready state's facts at the setup's explicit parameters -/

theorem sliceLabs_length (r4 G off L : ℕ) : (Emit.sliceLabs r4 G off L).length = 4 * L := by
  unfold Emit.sliceLabs Emit.gateLabs
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  induction L generalizing off with
  | zero => simp
  | succ L ih =>
    rw [List.range'_succ, List.map_cons, List.sum_cons, ih]
    ring

theorem slice_lab_le (r4 G off L lab : ℕ) (h : lab ∈ Emit.sliceLabs r4 G off L) :
    lab ≤ PopSetup.popMlab r4 G off L := by
  simp only [Emit.sliceLabs, Emit.gateLabs, List.mem_flatMap, List.mem_range', List.mem_map, List.mem_range] at h
  obtain ⟨gi, ⟨i, hi, rfl⟩, k, hk, rfl⟩ := h
  have : (r4 + k) * G ≤ (r4 + 4) * G := Nat.mul_le_mul_right _ (by omega)
  unfold PopSetup.popMlab
  omega

/-- **`PopReady.hok`** at the setup's explicit `popR`, `popCp` (Route B's capacities dominate, `popStates_okB` with
the block bound `blockC_le`). -/
theorem pop_hok (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1))
    (hlabs : 4 * L ≤ (Emit.sliceLabs r4 G off L).length) :
    ∀ st ∈ popStates Pl e L sgn (Emit.sliceLabs r4 G off L) hlabs s,
      StateOk Pl.walkLen (PopSetup.popR Pl r4 G off L) (PopSetup.popCp Pl r4 G off L) st :=
  PopCap.popStates_okB Pl e L sgn (Emit.sliceLabs r4 G off L) hlabs (sliceLabs_length r4 G off L)
    (PopSetup.popMlab r4 G off L) (fun lab h => slice_lab_le r4 G off L lab h) _
    (fun s' k neg => blockC_le Pl e L k s'.val (Nat.le_of_lt_succ s'.isLt) sgn neg _ (sliceLabs_length r4 G off L)) s

/-- **The rank facts** (`PopReady.hpad`, `hps`, `hsd`, `hlb`, `hnJ`). -/
theorem rank_facts (Pl : FlatListParams) :
    Flat.padB Pl.base.rank ≤ 1 ∧ Flat.padB Pl.base.rank ≤ Flat.sideB Pl.base.rank ∧
    2 * Pl.base.rank - 1 + Pl.base.rank ≤ 2 * Flat.sideB Pl.base.rank - Flat.padB Pl.base.rank ∧
    1 ≤ Pl.base.rank ∧ Pl.base.J + 1 ≤ Pl.base.rank + 1 := by
  have hJ : Pl.base.J ≤ Pl.base.rank := le_max_left _ _
  have hJ9 : 9 ≤ Pl.base.J := by unfold BaseListParams.J; omega
  obtain ⟨h1, h2, h3⟩ := Flat.sideB_facts Pl.base.rank (by omega)
  exact ⟨h1, h2, by omega, by omega, by omega⟩

/-! ## The need's measure and the power scale `U = 2^20·X` -/

section Need
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink

/-- The need's measure (`PopSetupSpecB2.need_le`'s). -/
noncomputable def popX (Pl : FlatListParams) (L r4 G off : ℕ) : ℕ :=
  (8 * L + 2) ^ (3 * lbP Pl + 1) + popMlab r4 G off L + r4 + Pl.M + Pl.B + Pl.errExp + Fintype.card Pl.FlatSeed + 2

/-- The power scale: every quantity of the POP row is at most a power of `U = 2^20·X`. -/
noncomputable def popU (Pl : FlatListParams) (L r4 G off : ℕ) : ℕ := 2 ^ 20 * popX Pl L r4 G off

/-- **The POP setup's need**: `U^40`. -/
noncomputable def popNeed (Pl : FlatListParams) (L r4 G off : ℕ) : ℕ := popU Pl L r4 G off ^ 40

theorem popNeed_le (Pl : FlatListParams) (L r4 G off : ℕ) :
    popNeed Pl L r4 G off ≤ 2 ^ 800 * popX Pl L r4 G off ^ 40 := by
  unfold popNeed popU
  rw [mul_pow, ← pow_mul]

/-! ### Powers of `U` -/

theorem u_mono {U a i j : ℕ} (hU : 1 ≤ U) (ha : a ≤ U ^ i) (hij : i ≤ j) : a ≤ U ^ j :=
  le_trans ha (Nat.pow_le_pow_right hU hij)

/-! ### The row's numbers against `U` -/

section Base
variable (Pl : FlatListParams) (L r4 G off : ℕ)

theorem x_ge : 2 ≤ popX Pl L r4 G off := by unfold popX; omega

theorem u_ge : 2 ^ 20 ≤ popU Pl L r4 G off := by
  unfold popU; have := x_ge Pl L r4 G off; nlinarith

theorem x_le_u : popX Pl L r4 G off ≤ popU Pl L r4 G off := by
  unfold popU; exact Nat.le_mul_of_pos_left _ (by norm_num)

/-- `c·X ≤ U` for `c ≤ 2^20`. -/
theorem cx_le_u {c : ℕ} (hc : c ≤ 2 ^ 20) : c * popX Pl L r4 G off ≤ popU Pl L r4 G off := by
  unfold popU; exact Nat.mul_le_mul_right _ hc

theorem y_le_x : (8 * L + 2) ^ (3 * lbP Pl + 1) ≤ popX Pl L r4 G off := by unfold popX; omega
theorem mlab_le_x : popMlab r4 G off L ≤ popX Pl L r4 G off := by unfold popX; omega
theorem r4_le_x : r4 ≤ popX Pl L r4 G off := by unfold popX; omega
theorem M_le_x : Pl.M ≤ popX Pl L r4 G off := by unfold popX; omega
theorem B_le_x : Pl.B ≤ popX Pl L r4 G off := by unfold popX; omega
theorem err_le_x : Pl.errExp ≤ popX Pl L r4 G off := by unfold popX; omega
theorem card_le_x : Fintype.card Pl.FlatSeed ≤ popX Pl L r4 G off := by unfold popX; omega

theorem L_le_x : 8 * L + 2 ≤ popX Pl L r4 G off := by
  have h := y_le_x Pl L r4 G off
  have : 8 * L + 2 ≤ (8 * L + 2) ^ (3 * lbP Pl + 1) := Nat.le_self_pow (by omega) _
  omega

theorem lbP_le_x : 3 * lbP Pl + 1 ≤ popX Pl L r4 G off := by
  have h := y_le_x Pl L r4 G off
  have h1 : 3 * lbP Pl + 1 < 2 ^ (3 * lbP Pl + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (3 * lbP Pl + 1) ≤ (8 * L + 2) ^ (3 * lbP Pl + 1) := Nat.pow_le_pow_left (by omega) _
  omega

theorem Q_le_x : (8 * L + 2) ^ (3 * lbP Pl) * (8 * L + 2) ≤ popX Pl L r4 G off := by
  have h := y_le_x Pl L r4 G off
  rw [pow_succ] at h
  exact h

theorem G_off_le_x : G ≤ popX Pl L r4 G off ∧ off ≤ popX Pl L r4 G off ∧ L ≤ popX Pl L r4 G off := by
  have h := mlab_le_x Pl L r4 G off
  unfold popMlab at h
  have : G ≤ (r4 + 4) * G := Nat.le_mul_of_pos_left _ (by omega)
  exact ⟨by omega, by omega, by omega⟩

end Base

end Need

section Derived
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
variable (Pl : FlatListParams) (L r4 G off : ℕ)

theorem two_clog_le (B : ℕ) : 2 ^ Nat.clog 2 B ≤ 2 * B + 1 := by
  rcases Nat.lt_or_ge B 2 with h | h
  · rw [Nat.clog_of_right_le_one (by omega)]
    omega
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < B by omega)
    rw [Nat.pred_eq_sub_one] at h1
    have h2 : 1 ≤ Nat.clog 2 B := Nat.clog_pos (by norm_num) (by omega)
    have e : 2 ^ Nat.clog 2 B = 2 * 2 ^ (Nat.clog 2 B - 1) := by
      conv_lhs => rw [show Nat.clog 2 B = (Nat.clog 2 B - 1) + 1 by omega]
      rw [pow_succ]; ring
    omega

theorem J_le : Pl.base.J ≤ popU Pl L r4 G off := by
  have hB := B_le_x Pl L r4 G off
  have hc : Nat.clog 2 Pl.base.B ≤ Pl.base.B := clog_le_self' _
  have := cx_le_u Pl L r4 G off (c := 10) (by norm_num)
  have hx := x_ge Pl L r4 G off
  have hBb : Pl.base.B = Pl.B := rfl
  unfold BaseListParams.J
  omega

theorem twoJ_le : 2 ^ Pl.base.J ≤ popU Pl L r4 G off := by
  have hB := B_le_x Pl L r4 G off
  have h := two_clog_le Pl.base.B
  have hBb : Pl.base.B = Pl.B := rfl
  have := cx_le_u Pl L r4 G off (c := 2000) (by norm_num)
  have hx := x_ge Pl L r4 G off
  unfold BaseListParams.J
  rw [pow_add]
  omega

theorem S_le : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) ≤ popU Pl L r4 G off := by
  have h := LevelW.natCeilSqrt_le (64 ^ 2 * Pl.base.B)
  have hB := B_le_x Pl L r4 G off
  have hBb : Pl.base.B = Pl.B := rfl
  have := cx_le_u Pl L r4 G off (c := 5000) (by norm_num)
  have hx := x_ge Pl L r4 G off
  omega

theorem rank_le : Pl.base.rank ≤ popU Pl L r4 G off ∧ Flat.sideB Pl.base.rank ≤ popU Pl L r4 G off := by
  have hJ := J_le Pl L r4 G off
  have hM := M_le_x Pl L r4 G off
  have hc : Nat.clog 2 Pl.base.M ≤ Pl.base.M := clog_le_self' _
  have hMb : Pl.base.M = Pl.M := rfl
  have := cx_le_u Pl L r4 G off (c := 20) (by norm_num)
  have hx := x_ge Pl L r4 G off
  have hr : Pl.base.rank ≤ Pl.base.J + Pl.base.M := by
    unfold BaseListParams.rank; exact max_le (by omega) (by omega)
  have hJx : Pl.base.J ≤ Pl.B + 9 := by
    have hc2 : Nat.clog 2 Pl.base.B ≤ Pl.base.B := clog_le_self' _
    have hBb : Pl.base.B = Pl.B := rfl
    unfold BaseListParams.J; omega
  have hB := B_le_x Pl L r4 G off
  constructor
  · omega
  · unfold Flat.sideB SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits
    omega

theorem wl_le : Pl.walkLen ≤ popU Pl L r4 G off ∧ SupplierWalk.majorityThreshold Pl.walkLen ≤ popU Pl L r4 G off := by
  have he := err_le_x Pl L r4 G off
  have hx := x_le_u Pl L r4 G off
  have hx2 := x_ge Pl L r4 G off
  unfold FlatListParams.walkLen SupplierWalk.majorityThreshold
  constructor <;> omega

end Derived

section Derived2
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
variable (Pl : FlatListParams) (L r4 G off : ℕ)

theorem u2 (U : ℕ) (hU : 2 ^ 20 ≤ U) {a : ℕ} (h : a ≤ 3 * U + 64) : a ≤ U ^ 2 := by
  have : 3 * U + 64 ≤ U * U := by nlinarith
  rw [pow_two]; omega

theorem win_le (j : ℕ) (hj : j ≤ Pl.base.J) :
    LevelW.winAt (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J j ≤ popU Pl L r4 G off ^ 2 := by
  have h := LevelW.winAt_le (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J j
  have hS := S_le Pl L r4 G off
  have h2 : 2 ^ (j / 3) ≤ 2 ^ Pl.base.J := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hJ := twoJ_le Pl L r4 G off
  exact u2 _ (u_ge Pl L r4 G off) (by omega)

theorem lwSum_le : PopParams.lwSumF (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J L ≤
    popU Pl L r4 G off ^ 6 := by
  obtain ⟨U, hUd⟩ : ∃ u, u = popU Pl L r4 G off := ⟨_, rfl⟩
  rw [← hUd]
  have hU := u_ge Pl L r4 G off
  rw [← hUd] at hU
  have hL : L ≤ U := by have := (G_off_le_x Pl L r4 G off).2.2; have := x_le_u Pl L r4 G off; omega
  have hJ : Pl.base.J ≤ U := by rw [hUd]; exact J_le Pl L r4 G off
  have hterm : ∀ j ∈ Finset.range (Pl.base.J + 1),
      LevelW.winAt (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J j +
        2 ^ Nat.clog 2 (2 * LevelW.winAt (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J j + 1) +
        L + 3 ≤ U ^ 4 := by
    intro j hj
    have hjJ : j ≤ Pl.base.J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hw := win_le Pl L r4 G off j hjJ
    rw [← hUd] at hw
    have hc := two_clog_le (2 * LevelW.winAt (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J j + 1)
    have h4 : U ^ 4 = U ^ 2 * U ^ 2 := by ring
    have h22 : 8 * U ^ 2 ≤ U ^ 2 * U ^ 2 := Nat.mul_le_mul_right _ (le_trans (by norm_num) (Nat.pow_le_pow_left hU 2))
    have hU1 : 1 ≤ U ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hLU : L ≤ U ^ 2 := le_trans hL (Nat.le_self_pow (by norm_num) _)
    have hUU : U ≤ U ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hs := Finset.sum_le_card_nsmul (Finset.range (Pl.base.J + 1)) _ (U ^ 4) hterm
  rw [Finset.card_range, smul_eq_mul] at hs
  unfold PopParams.lwSumF
  refine le_trans hs ?_
  have h1 : Pl.base.J + 1 ≤ U ^ 2 := by
    have : U + 1 ≤ U * U := by nlinarith
    rw [pow_two]; omega
  calc (Pl.base.J + 1) * U ^ 4 ≤ U ^ 2 * U ^ 4 := Nat.mul_le_mul_right _ h1
    _ = U ^ 6 := by ring

theorem lw_le : popLw Pl L ≤ popU Pl L r4 G off ^ 7 := by
  have h := lwSum_le Pl L r4 G off
  have hM := M_le_x Pl L r4 G off
  have hx := x_le_u Pl L r4 G off
  have hU := u_ge Pl L r4 G off
  have h6 : popU Pl L r4 G off ^ 6 * 3 ≤ popU Pl L r4 G off ^ 7 := by
    rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega)
  have h61 : popU Pl L r4 G off ≤ popU Pl L r4 G off ^ 6 :=
    Nat.le_self_pow (by norm_num) _
  unfold popLw
  omega

theorem capP_eq : capP Pl L = 4 * (popLw Pl L + L + 1) := by
  unfold capP FinalPass.ListEval.capOf popLw
  rw [PopParams.levelWord_length Pl.base L (fun _ => List.replicate L false) (fun j _ => by simp)]
  rfl

theorem capP_le : capP Pl L ≤ popU Pl L r4 G off ^ 8 := by
  rw [capP_eq]
  have h := lw_le Pl L r4 G off
  have hL := (G_off_le_x Pl L r4 G off).2.2
  have hx := x_le_u Pl L r4 G off
  have hU := u_ge Pl L r4 G off
  have h7 : popU Pl L r4 G off ≤ popU Pl L r4 G off ^ 7 := Nat.le_self_pow (by norm_num) _
  have h8 : popU Pl L r4 G off ^ 7 * 9 ≤ popU Pl L r4 G off ^ 8 := by
    rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem sumlab_le (B : ℕ) : ∀ labs : List ℕ, (∀ lab ∈ labs, lab ≤ B) →
    (labs.map fun lab => 2 * lab + 10).sum ≤ labs.length * (2 * B + 10)
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := sumlab_le B xs (fun l hl => h l (List.mem_cons_of_mem x hl))
    have e : (xs.length + 1) * (2 * B + 10) = xs.length * (2 * B + 10) + (2 * B + 10) := by ring
    rw [e]
    omega

theorem CAP_LL_le : popCAP r4 G off L ≤ popU Pl L r4 G off ^ 3 ∧ popLL r4 G off L ≤ popU Pl L r4 G off ^ 3 := by
  have hlab : ∀ lab ∈ Emit.sliceLabs r4 G off L, lab ≤ popMlab r4 G off L := slice_lab_le r4 G off L
  have hlen := sliceLabs_length r4 G off L
  have h1 := sumlab_le (popMlab r4 G off L) _ hlab
  rw [hlen] at h1
  have hm := mlab_le_x Pl L r4 G off
  have hL := (G_off_le_x Pl L r4 G off).2.2
  have hx := x_le_u Pl L r4 G off
  have hU := u_ge Pl L r4 G off
  obtain ⟨U, hUd⟩ : ∃ u, u = popU Pl L r4 G off := ⟨_, rfl⟩
  rw [← hUd] at hx hU ⊢
  have hLU : L ≤ U := by omega
  have hmU : popMlab r4 G off L ≤ U := by omega
  have k1 : 4 * L * (2 * popMlab r4 G off L + 10) ≤ 4 * U * (2 * U + 10) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hLU) (by omega)
  have k2 : 4 * U * (2 * U + 10) + 5 ≤ U ^ 3 := by
    have : 4 * U * (2 * U + 10) + 5 ≤ 9 * U * U := by nlinarith
    have : 9 * U * U ≤ U * U * U := by nlinarith
    have e3 : U ^ 3 = U * U * U := by ring
    omega
  have hll : popLL r4 G off L = 4 * ((Emit.sliceLabs r4 G off L).map fun lab => lab + 1).sum := labE_flat_len _
  have h2 : ((Emit.sliceLabs r4 G off L).map fun lab => lab + 1).sum ≤ (Emit.sliceLabs r4 G off L).length *
      (popMlab r4 G off L + 1) := by
    have := List.sum_le_card_nsmul ((Emit.sliceLabs r4 G off L).map fun lab => lab + 1) (popMlab r4 G off L + 1)
      (by intro x hx; obtain ⟨lab, hl, rfl⟩ := List.mem_map.mp hx; have := hlab lab hl; omega)
    rw [List.length_map, smul_eq_mul] at this; exact this
  rw [hlen] at h2
  have k3 : 4 * (4 * L * (popMlab r4 G off L + 1)) ≤ 16 * U * (U + 1) := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hLU) (show popMlab r4 G off L + 1 ≤ U + 1 by omega)
    nlinarith
  have k4 : 16 * U * (U + 1) ≤ U ^ 3 := by
    have : 16 * U * (U + 1) ≤ 32 * U * U := by nlinarith
    have : 32 * U * U ≤ U * U * U := by nlinarith
    have e3 : U ^ 3 = U * U * U := by ring
    omega
  refine ⟨?_, ?_⟩
  · unfold popCAP labSum; omega
  · rw [hll]
    have := Nat.mul_le_mul_left 4 h2
    omega

end Derived2

/-! ## The capacities as powers of `U` -/

section Powers
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
variable (Pl : FlatListParams) (L r4 G off : ℕ)

theorem pw_lt {U : ℕ} (hU : 2 ^ 20 ≤ U) {i j : ℕ} (h : i < j) : 2 ^ 20 * U ^ i ≤ U ^ j := by
  have e : U ^ j = U ^ i * U ^ (j - i) := by rw [← pow_add, Nat.add_sub_cancel' h.le]
  rw [e, mul_comm]
  exact Nat.mul_le_mul_left _ (le_trans hU (Nat.le_self_pow (by omega) U))

/-- The basic quantities, each at most `U` (or a small power). -/
theorem basic :
    L + 1 ≤ popU Pl L r4 G off ∧ 3 * lbP Pl + 1 ≤ popU Pl L r4 G off ∧ Pl.M + 1 ≤ popU Pl L r4 G off ∧
    Pl.walkLen ≤ popU Pl L r4 G off ∧ SupplierWalk.majorityThreshold Pl.walkLen ≤ popU Pl L r4 G off ∧
    popMlab r4 G off L + 1 ≤ popU Pl L r4 G off ∧ r4 + G + off ≤ popU Pl L r4 G off ∧
    Pl.base.J + 1 ≤ popU Pl L r4 G off ∧
    CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) ≤ popU Pl L r4 G off ∧
    Pl.errExp ≤ popU Pl L r4 G off ∧ Pl.base.rank ≤ popU Pl L r4 G off ∧
    Flat.sideB Pl.base.rank ≤ popU Pl L r4 G off ∧
    (8 * L + 2) ^ (3 * lbP Pl) * (8 * L + 2) + 2 ≤ popU Pl L r4 G off ∧
    (8 * L + 2) ^ (3 * lbP Pl) ≤ popU Pl L r4 G off ∧
    popLw Pl L ≤ popU Pl L r4 G off ^ 7 ∧ capP Pl L ≤ popU Pl L r4 G off ^ 8 ∧
    popCAP r4 G off L ≤ popU Pl L r4 G off ^ 3 ∧ popLL r4 G off L ≤ popU Pl L r4 G off ^ 3 ∧
    2 ^ 20 ≤ popU Pl L r4 G off := by
  have hx2 := cx_le_u Pl L r4 G off (c := 3) (by norm_num)
  have hxg := x_ge Pl L r4 G off
  have hL := L_le_x Pl L r4 G off
  have hd := lbP_le_x Pl L r4 G off
  have hM := M_le_x Pl L r4 G off
  have hm := mlab_le_x Pl L r4 G off
  have hr := r4_le_x Pl L r4 G off
  have hGo := G_off_le_x Pl L r4 G off
  have he := err_le_x Pl L r4 G off
  have hQ := Q_le_x Pl L r4 G off
  have hQ1 : (8 * L + 2) ^ (3 * lbP Pl) ≤ (8 * L + 2) ^ (3 * lbP Pl) * (8 * L + 2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hwl := wl_le Pl L r4 G off
  have hrk := rank_le Pl L r4 G off
  have hS := S_le Pl L r4 G off
  have htJ := twoJ_le Pl L r4 G off
  have hJ2 : Pl.base.J < 2 ^ Pl.base.J := Nat.lt_two_pow_self
  have hlw := lw_le Pl L r4 G off
  have hc := capP_le Pl L r4 G off
  have hCL := CAP_LL_le Pl L r4 G off
  have hU := u_ge Pl L r4 G off
  refine ⟨by omega, by omega, by omega, hwl.1, hwl.2, by omega, by omega, by omega, hS, by omega, hrk.1, hrk.2,
    by omega, by omega, hlw, hc, hCL.1, hCL.2, hU⟩

end Powers

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetupMath
