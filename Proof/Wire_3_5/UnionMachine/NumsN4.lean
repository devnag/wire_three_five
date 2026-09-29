import Proof.Wire_3_5.Primitive.Writers.SBEmit
import Proof.Wire_3_5.UnionMachine.NumsN3

/-! # SWn, part 4: the post program `postN` and its run from the front exit

After the SYM front (`FrontOutB`) on NW's bank `x ≥ DT + 8`, **`postN`** clears the scratch block
`100 … 159`, runs phases H, T, Q (NumsN3; the template length program `tp` an argument with `TplIface`), writes the
eighteen registers `[dA, G41, rL j, rH j, rT j, rQ j]` as a unary list onto the output stream `oOut = sT (DT+7)` (`SBEmit.emitList`), rewinds it and clears every register.

**`postRun`**: for any SYM call `k` whose front exit is `FrontOutB x _ k.Cs k.Pl w Bnd τ0`, at every capacity above
`capP Kt Et Bnd`, the output stream holds `unaryList (ofFn (symNums k))` (the eighteen call numbers), the request is
kept, every other stream within the capacity, heads and registers `0`, the cell `false`, within `4000·cap + 4000`
steps.

* `WExec.val_steps` (a register grows by at most the step count), **`tplNum_le`** (the interface bounds the template
  length), `tabH_le_tape`, `tab_arith`, `tvOf_le`, `unaryList_len_le`, `emitListCost_le`, `get_of_map`;
* `dt3`, `slotT`, `oOut`, `scrL`, `l18`, `postN`, `capP`, **`postRun`**.

Paper quantities of the main type: the SYM call numbers `symNums k` (P3:3170-3178) on the call's output stream. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2

/-! ## Generic facts -/

section Gen
variable {ns nr : ℕ} {cap : ℕ}

/-- **A register grows by at most the step count.** -/
theorem WExec.val_steps {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) :
    ∀ r, τ.val r ≤ σ.val r + n := by
  induction h with
  | skip => intro r; omega
  | inc q σ hv =>
    intro r
    simp only [WState.setv_val, Function.update_apply]
    split_ifs with hq
    · subst hq; omega
    · omega
  | dec q σ hv =>
    intro r
    simp only [WState.setv_val, Function.update_apply]
    split_ifs with hq
    · subst hq; omega
    · omega
  | fwd j σ => intro r; simp
  | bwd j σ => intro r; simp
  | wr j b σ => intro r; simp
  | setc v σ => intro r; simp
  | seq _ _ ih1 ih2 => intro r; have := ih1 r; have := ih2 r; omega
  | ifrT _ _ ih => intro r; have := ih r; omega
  | ifrF _ _ ih => intro r; have := ih r; omega
  | ifsT _ _ ih => intro r; have := ih r; omega
  | ifsF _ _ ih => intro r; have := ih r; omega
  | whrF _ => intro r; omega
  | whrT _ _ _ ih1 ih2 => intro r; have := ih1 r; have := ih2 r; omega
  | whsF _ => intro r; omega
  | whsT _ _ _ ih1 ih2 => intro r; have := ih1 r; have := ih2 r; omega
  | mono _ hnm ih => intro r; have := ih r; omega

end Gen

/-- A bank for probing the interface. -/
def wT : Fin 30 ↪ Fin 35 := ⟨fun i => ⟨5 + i.val, by have := i.isLt; omega⟩,
  fun i j h => by simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

/-- **The interface bounds the template length**: `tplNum M B L ≤ Kt·(M+B+L+2)^Et` (the counter grows by at most the
steps). -/
theorem tplNum_le (Kt Et : ℕ)
    (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr)
    (htp : TplIface Kt Et tp) (M B L : ℕ) : tplNum M B L ≤ Kt * (M + B + L + 2) ^ Et := by
  have hW : ∀ i, wT i ∉ [(0 : Fin 35), 1, 2, 3, 4] := by decide
  obtain ⟨τ, c, e, v1, -, -, -, -, -, hc⟩ := htp (Kt * (M + B + L + 2) ^ Et) (0 : Fin 1) wT 0 1 2 3 4 (by decide) hW
    (⟨fun _ => 0, fun _ => [], fun q => [M, B, (⟨M, B⟩ : Lists.BaseListParams).J, L].getD q.val 0, false⟩ :
      WState 0 35) M B L rfl rfl rfl rfl rfl
    (fun i => by
      show [M, B, (⟨M, B⟩ : Lists.BaseListParams).J, L].getD (5 + i.val) 0 = 0
      exact List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega))
    rfl rfl le_rfl
  have h1 := WExec.val_steps e 4
  rw [v1] at h1
  have h0 : (⟨fun _ => 0, fun _ => [], fun q => [M, B, (⟨M, B⟩ : Lists.BaseListParams).J, L].getD q.val 0, false⟩ :
      WState 0 35).val 4 = 0 := rfl
  omega

/-- The gate table's width is at most its tape's length. -/
theorem tabH_le_tape {n : ℕ} (G : List (NormalizedThresholdGate n)) :
    PrimT.tabH G ≤ (FinalPass.Corner.gatesW (PrimT.tabH G) G).length := by
  cases G with
  | nil => exact Nat.zero_le _
  | cons g G =>
    rw [FinalPass.ThrPt.gatesW_len, List.length_cons]
    obtain ⟨h, hh⟩ : ∃ v, v = PrimT.tabH (g :: G) := ⟨_, rfl⟩
    rw [← hh]
    have a1 : h ≤ 1 * (2 * (2 * h + 1)) := by omega
    have a2 : 1 * (2 * (2 * h + 1)) ≤ (n + 1) * (2 * (2 * h + 1)) := Nat.mul_le_mul_right _ (by omega)
    have a3 : 1 + (n + 1) * (2 * (2 * h + 1)) ≤ (G.length + 1) * (1 + (n + 1) * (2 * (2 * h + 1))) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The flat table length's capacity condition, within `(3(U+2))³`. -/
theorem tab_arith (L J Wl U : ℕ) (hL : L ≤ U) (hJ : J ≤ U) (hW : Wl ≤ U) :
    ((2 * L + 1) * (J + 1) + 1) * (Wl + 1) + L + J + 2 ≤ (3 * (U + 2)) ^ 3 := by
  obtain ⟨A, hA⟩ : ∃ v, v = U + 2 := ⟨_, rfl⟩
  have a1 : (2 * L + 1) * (J + 1) + 1 ≤ (2 * L + 2) * (J + 2) := by
    have e : (2 * L + 2) * (J + 2) = (2 * L + 1) * (J + 1) + 2 * L + J + 3 := by ring
    omega
  have a2 : (2 * L + 2) * (J + 2) ≤ (2 * A) * A := Nat.mul_le_mul (by omega) (by omega)
  have a3 : ((2 * L + 1) * (J + 1) + 1) * (Wl + 1) ≤ ((2 * A) * A) * A := Nat.mul_le_mul (le_trans a1 a2) (by omega)
  have e3 : (3 * (U + 2)) ^ 3 = 27 * (A * A * A) := by rw [← hA]; ring
  have e4 : (2 * A) * A * A = 2 * (A * A * A) := by ring
  have b1 : A ≤ A * A := Nat.le_mul_of_pos_left _ (by omega)
  have b2 : A * A ≤ A * A * A := Nat.le_mul_of_pos_right _ (by omega)
  rw [e3]
  omega

theorem tvOf_le (L J Wl : ℕ) : tvOf L J Wl ≤ ((2 * L + 1) * (J + 1) + 1) * (Wl + 1) := by
  unfold tvOf
  have e : ((2 * L + 1) * (J + 1) + 1) * (Wl + 1) = ((2 * L + 1) * (J + 1) + 1) * Wl + ((2 * L + 1) * (J + 1) + 1) := by
    ring
  omega

theorem unaryList_len_le (V : ℕ) : ∀ (vs : List ℕ), (∀ v ∈ vs, v ≤ V) →
    (Data.unaryList vs).length ≤ vs.length * (V + 1)
  | [], _ => by simp [Data.unaryList]
  | v :: vs, h => by
    have e : Data.unaryList (v :: vs) = (List.replicate v true ++ [false]) ++ Data.unaryList vs := by
      simp [Data.unaryList]
    rw [e, List.length_append, List.length_append, List.length_replicate, List.length_singleton, List.length_cons]
    have h1 := h v (by simp)
    have h2 := unaryList_len_le V vs (fun u hu => h u (by simp [hu]))
    have e2 : (vs.length + 1) * (V + 1) = vs.length * (V + 1) + (V + 1) := by ring
    omega

theorem emitListCost_le (V : ℕ) : ∀ (vs : List ℕ), (∀ v ∈ vs, v ≤ V) →
    SBEmit.emitListCost vs ≤ vs.length * (11 * V + 10)
  | [], _ => by simp [SBEmit.emitListCost]
  | v :: vs, h => by
    have h1 := h v (by simp)
    have h2 := emitListCost_le V vs (fun u hu => h u (by simp [hu]))
    have e2 : (vs.length + 1) * (11 * V + 10) = vs.length * (11 * V + 10) + (11 * V + 10) := by ring
    show 11 * v + 9 + 1 + SBEmit.emitListCost vs ≤ (vs.length + 1) * (11 * V + 10)
    omega

theorem get_of_map {α β : Type} (l : List α) (f : α → β) (vs : List β) (h : l.map f = vs) :
    ∀ i (h1 : i < l.length) (h2 : i < vs.length), f (l.get ⟨i, h1⟩) = vs.get ⟨i, h2⟩ := by
  subst h
  intro i h1 h2
  simp

/-! ## The post program -/

theorem dt3 {x : ℕ} (hx : DataDock.DT + 8 ≤ x) : DataDock.DT + 3 ≤ x := by omega

section Post
variable (x : ℕ) (hx : DataDock.DT + 8 ≤ x)

/-- Circuit `j`'s gate table (the front's slot tape). -/
def slotT (j : Fin 4) : Fin (LNS x + 1) := tmapA x (dt3 hx) (DataDock.iSym j)

/-- **The numbers' output stream.** -/
def oOut : Fin (LNS x + 1) := sT x ⟨DataDock.DT + 7, by omega⟩

theorem oOut_val : (oOut x hx).val = 161 + (DataDock.DT + 7) := rfl

/-- The scratch block `100 … 159`. -/
def scrL : List (Fin LNR) := (List.finRange LNR).filter (fun q => decide (100 ≤ q.val ∧ q.val < 160))

theorem scr_mem (q : Fin LNR) : q ∈ scrL ↔ 100 ≤ q.val ∧ q.val < 160 := by
  simp [scrL]

theorem scrL_len : scrL.length ≤ 512 :=
  le_trans (List.length_filter_le _ _) (by rw [List.length_finRange])

/-- The eighteen numbers' registers, in `symNums`' order. -/
def l18 : List (Fin LNR) := [SymDec.dA, SymDec.G 41, rL 0, rL 1, rL 2, rL 3, rH 0, rH 1, rH 2, rH 3, rT 0, rT 1, rT 2,
  rT 3, rQ 0, rQ 1, rQ 2, rQ 3]

/-- **SWn's post program.** -/
def postN (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr) :
    WM (LNS x) LNR :=
  .seq (FinalPass.S5T.clearL scrL) (.seq (tabHs (slotT x hx)) (.seq tabLens (.seq (tpls tp (oT x hx))
    (.seq (SBEmit.emitList (oOut x hx) rOP l18) (.seq (WM.rewind (oOut x hx) rOP) FinalPass.S5T.clearAll)))))

/-- The post program's capacity. -/
def capP (Kt Et Bnd : ℕ) : ℕ := 100 * (Kt + 8) * (3 * (Bnd + 2)) ^ (Et + 3)

/-- **SWn's post run** from the front exit: the eighteen call numbers on the output stream. -/
theorem postRun (Kt Et : ℕ)
    (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr)
    (htp : TplIface Kt Et tp) (k : FinalPass.Seams.SymCall) (w : List Bool) (Bnd cap : ℕ) (τ0 : St x)
    (hF : FinalPass.SymFront.FrontOutB x (dt3 hx) k.Cs k.Pl w Bnd τ0) (hcap : capP Kt Et Bnd ≤ cap) :
    ∃ (τ : St x) (c : ℕ), WExec cap (postN x hx tp) τ0 τ c ∧ c ≤ 4000 * cap + 4000 ∧
      τ.st (oOut x hx) = Data.unaryList (List.ofFn (PrimT.S3.symNums k)) ∧ τ.st (sIn x) = frame w ∧
      (∀ i, i ≠ sIn x → i ≠ oOut x hx → (τ.st i).length ≤ cap) ∧ (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) ∧
      τ.cell = false := by
  -- the capacity
  obtain ⟨Z, hZ⟩ : ∃ v, v = 3 * (Bnd + 2) := ⟨_, rfl⟩
  obtain ⟨Qp, hQp⟩ : ∃ v, v = Z ^ (Et + 3) := ⟨_, rfl⟩
  have hcap' : 100 * (Kt + 8) * Qp ≤ cap := by rw [hQp, hZ]; exact hcap
  have hZ1 : 1 ≤ Z := by omega
  have hQ1 : 1 ≤ Qp := by rw [hQp]; exact Nat.one_le_pow _ _ (by omega)
  have hZQ : Z ≤ Qp := by
    rw [hQp]
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ _ := Nat.pow_le_pow_right hZ1 (by omega)
  have hZ3 : Z ^ 3 ≤ Qp := by rw [hQp]; exact Nat.pow_le_pow_right hZ1 (by omega)
  have hZE : Z ^ Et ≤ Qp := by rw [hQp]; exact Nat.pow_le_pow_right hZ1 (by omega)
  have hcQ : 100 * (Kt + 8) * Qp = 100 * (Kt * Qp) + 800 * Qp := by ring
  obtain ⟨V, hVd⟩ : ∃ v, v = (Kt + 1) * Qp := ⟨_, rfl⟩
  have hVe : V = Kt * Qp + Qp := by rw [hVd]; ring
  have hVc : 18 * (V + 1) ≤ cap := by omega
  have hBQ : Bnd ≤ Qp := by omega
  have hBV : Bnd ≤ V := by omega
  have hBc : 2 * Bnd + 1 ≤ cap := by omega
  have hZc : 400 * Z ^ 3 ≤ cap := by omega
  -- the front's facts
  have vle := hF.vle
  have hLj : ∀ j : Fin 4, τ0.val (rL j) = (PrimT.S3.gatesJ k j).length := fun j => by
    by_cases h : j.val < k.a
    · have := hF.vL j h
      unfold PrimT.S3.gatesJ
      rw [dif_pos h]
      exact this
    · have := hF.vL0 j (by omega)
      unfold PrimT.S3.gatesJ
      rw [dif_neg h]
      exact this
  have hslot : ∀ j : Fin 4, τ0.st (slotT x hx j) = FinalPass.Corner.gatesW (PrimT.tabH (PrimT.S3.gatesJ k j))
      (PrimT.S3.gatesJ k j) ∨ (τ0.st (slotT x hx j) = [] ∧ PrimT.S3.gatesJ k j = []) := fun j => by
    by_cases h : j.val < k.a
    · left
      unfold PrimT.S3.gatesJ
      rw [dif_pos h]
      exact hF.gates j h
    · right
      unfold PrimT.S3.gatesJ
      rw [dif_neg h]
      exact ⟨hF.gates0 j (by omega), rfl⟩
  have hsIn : ∀ j : Fin 4, slotT x hx j ≠ sIn x := fun j e => by
    have e0 : sIn x = tmapA x (dt3 hx) DataDock.iIN := by unfold tmapA DataDock.nwTmap; rw [if_pos rfl]
    rw [e0] at e
    have := congrArg Fin.val (tmapA_inj x (dt3 hx) e)
    revert this
    fin_cases j <;> decide
  have hH : ∀ j : Fin 4, PrimT.tabH (PrimT.S3.gatesJ k j) ≤ Bnd := fun j => by
    rcases hslot j with h | ⟨_, h⟩
    · have := hF.resid _ (hsIn j)
      rw [h] at this
      exact le_trans (tabH_le_tape _) this
    · rw [h]
      exact Nat.zero_le _
  have hLb : ∀ j : Fin 4, (PrimT.S3.gatesJ k j).length ≤ Bnd := fun j => by rw [← hLj j]; exact vle _
  have hJb : k.Pl.base.J ≤ Bnd := by rw [← hF.vJ]; exact vle _
  have hWb : k.Pl.walkLen ≤ Bnd := by rw [← hF.vW]; exact vle _
  have hMb : k.Pl.M ≤ Bnd := by rw [← hF.vM]; exact vle _
  have hBb : k.Pl.B ≤ Bnd := by rw [← hF.vB]; exact vle _
  have hAb : k.a ≤ Bnd := by rw [← hF.vA]; exact vle _
  have hKb : Fintype.card k.Pl.FlatSeed ≤ Bnd := by rw [← hF.vK]; exact vle _
  have hTab : ∀ j : Fin 4, ((2 * (PrimT.S3.gatesJ k j).length + 1) * (k.Pl.base.J + 1) + 1) * (k.Pl.walkLen + 1) +
      (PrimT.S3.gatesJ k j).length + k.Pl.base.J + 2 ≤ Z ^ 3 := fun j => by
    rw [hZ]; exact tab_arith _ _ _ _ (hLb j) hJb hWb
  have hMBL : ∀ j : Fin 4, k.Pl.M + k.Pl.B + (PrimT.S3.gatesJ k j).length + 2 ≤ Z := fun j => by
    have := hLb j; omega
  have hTp : ∀ j : Fin 4, Kt * (k.Pl.M + k.Pl.B + (PrimT.S3.gatesJ k j).length + 2) ^ Et ≤ Kt * Qp := fun j =>
    Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_left (hMBL j) _) hZE)
  -- 1: the scratch block cleared
  have hv0 : ∀ r, τ0.val r ≤ cap := fun r => le_trans (vle r) (by omega)
  obtain ⟨σ1, e1, s1, sh1, ce1, z1, k1⟩ := FinalPass.S5T.clearL_spec cap scrL τ0 hv0
  have hz1 : ∀ q : Fin LNR, 100 ≤ q.val → q.val < 160 → σ1.val q = 0 := fun q a b => z1 q ((scr_mem q).2 ⟨a, b⟩)
  have hk1 : ∀ q : Fin LNR, (q.val < 100 ∨ 160 ≤ q.val) → σ1.val q = τ0.val q := fun q h =>
    k1 q (fun hm => by have := (scr_mem q).1 hm; omega)
  -- 2: phase H
  obtain ⟨σ2, cH, e2, hcH, IH⟩ := tabHs_run (slotT x hx) cap (fun j => PrimT.S3.gatesJ k j) σ1
    (fun j => by rw [sh1]; exact hF.heads _)
    (fun j => hz1 _ (by rw [rH_val]; omega) (by rw [rH_val]; have := j.isLt; omega))
    (hz1 _ (by rw [rP_val]; omega) (by rw [rP_val]; omega)) (fun j => by rw [s1]; exact hslot j)
    (fun j => by have := hH j; omega)
  obtain ⟨IH1, IH2, IH3, IH4, IH5⟩ := IH
  have keepH : ∀ q : Fin LNR, (q.val < 100 ∨ 104 ≤ q.val) → σ2.val q = σ1.val q := fun q h =>
    IH2 q (fun j _ e => by have := congrArg Fin.val e; rw [rH_val] at this; have := j.isLt; omega)
  have v2 : ∀ q : Fin LNR, (q.val < 100 ∨ 160 ≤ q.val) → σ2.val q = τ0.val q := fun q h => by
    rw [keepH q (by omega), hk1 q h]
  have z2 : ∀ q : Fin LNR, 104 ≤ q.val → q.val < 160 → σ2.val q = 0 := fun q a b => by
    rw [keepH q (by omega)]; exact hz1 q (by omega) b
  -- 3: phase T
  obtain ⟨σ3, cT, e3, hcT, IT⟩ := tabLens_run cap (fun j => (PrimT.S3.gatesJ k j).length) k.Pl.base.J k.Pl.walkLen
    (400 * Z ^ 3) σ2 (fun j => by rw [v2 _ (by rw [rL_val]; omega)]; exact hLj j)
    (by rw [v2 _ (by rw [G35_val]; omega)]; exact hF.vJ) (by rw [v2 _ (by rw [G39_val]; omega)]; exact hF.vW)
    (fun q a b => z2 q (by omega) (by omega))
    (fun j => z2 _ (by rw [rT_val]; omega) (by rw [rT_val]; have := j.isLt; omega))
    (fun j => by have := hTab j; omega)
    (fun j => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hLb j; omega) _))
  obtain ⟨IT1, IT2, IT3, IT4, IT5⟩ := IT
  have keepT : ∀ q : Fin LNR, (q.val < 108 ∨ 112 ≤ q.val) → σ3.val q = σ2.val q := fun q h =>
    IT2 q (fun j _ e => by have := congrArg Fin.val e; rw [rT_val] at this; have := j.isLt; omega)
  have v3 : ∀ q : Fin LNR, (q.val < 100 ∨ 160 ≤ q.val) → σ3.val q = τ0.val q := fun q h => by
    rw [keepT q (by omega), v2 q h]
  have z3 : ∀ q : Fin LNR, 112 ≤ q.val → q.val < 160 → σ3.val q = 0 := fun q a b => by
    rw [keepT q (by omega)]; exact z2 q (by omega) b
  -- 4: phase Q
  obtain ⟨σ4, cQ, e4, hcQ4, IQ⟩ := tpls_run Kt Et tp (oT x hx) htp (oT_inj x hx) cap k.Pl.M k.Pl.B
    (fun j => (PrimT.S3.gatesJ k j).length) σ3
    (by rw [v3 _ (by rw [G32_val]; omega)]; exact hF.vM) (by rw [v3 _ (by rw [G33_val]; omega)]; exact hF.vB)
    (by rw [v3 _ (by rw [G35_val]; omega)]; exact hF.vJ) (fun j => by rw [v3 _ (by rw [rL_val]; omega)]; exact hLj j)
    (fun j => z3 _ (by rw [rQ_val]; omega) (by rw [rQ_val]; have := j.isLt; omega))
    (fun i => z3 _ (by rw [wB_val]; omega) (by rw [wB_val]; have := i.isLt; omega))
    (fun j => by
      rw [IT3, IH3, s1]
      exact hF.hi ⟨DataDock.DT + 3 + j.val, by have := j.isLt; omega⟩ (by show DataDock.DT + 3 ≤ DataDock.DT + 3 + j.val; omega))
    (fun j => by rw [IT4, IH4, sh1]; exact hF.heads _)
    (fun j => le_trans (hTp j) (by omega))
  obtain ⟨IQ1, IQ2, IQ3, IQ4, IQ5, IQ6⟩ := IQ
  have keepQ : ∀ q : Fin LNR, (q.val < 112 ∨ 116 ≤ q.val) → σ4.val q = σ3.val q := fun q h =>
    IQ2 q (fun j _ e => by have := congrArg Fin.val e; rw [rQ_val] at this; have := j.isLt; omega)
  have v4 : ∀ q : Fin LNR, (q.val < 100 ∨ 160 ≤ q.val) → σ4.val q = τ0.val q := fun q h => by
    rw [keepQ q (by omega), v3 q h]
  have hOT : ∀ j : Fin 4, oOut x hx ≠ oT x hx j := fun j e => by
    have := congrArg Fin.val e; rw [oOut_val, oT_val] at this; have := j.isLt; omega
  have hIT : ∀ j : Fin 4, sIn x ≠ oT x hx j := fun j e => by
    have := congrArg Fin.val e; rw [oT_val] at this; have : (sIn x).val = 150 := rfl; omega
  have hIO : sIn x ≠ oOut x hx := fun e => by
    have := congrArg Fin.val e; rw [oOut_val] at this; have : (sIn x).val = 150 := rfl; omega
  -- the eighteen values
  have bA : k.a ≤ V := by omega
  have bK : Fintype.card k.Pl.FlatSeed ≤ V := by omega
  have bL : ∀ j : Fin 4, (PrimT.S3.gatesJ k j).length ≤ V := fun j => by have := hLb j; omega
  have bH : ∀ j : Fin 4, PrimT.tabH (PrimT.S3.gatesJ k j) ≤ V := fun j => by have := hH j; omega
  have bT : ∀ j : Fin 4, PrimT.S3.tabLen k j ≤ V := fun j => by
    rw [tabLen_regs]
    have h1 := tvOf_le (PrimT.S3.gatesJ k j).length k.Pl.base.J k.Pl.walkLen
    have h2 := hTab j
    unfold tvOf at h1
    omega
  have bQ : ∀ j : Fin 4, (PrimT.S3.templJ k j).length ≤ V := fun j => by
    have h1 := tplNum_le Kt Et tp htp k.Pl.M k.Pl.B (PrimT.S3.gatesJ k j).length
    have h2 := hTp j
    have e : (PrimT.S3.templJ k j).length = tplNum k.Pl.M k.Pl.B (PrimT.S3.gatesJ k j).length := rfl
    rw [e]
    have : Kt * Qp ≤ V := by omega
    omega
  have hvsV : ∀ v ∈ List.ofFn (PrimT.S3.symNums k), v ≤ V := by
    intro v hv
    rw [ofFn_symNums] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      first | exact bA | exact bK | exact bL _ | exact bH _ | exact bT _ | exact bQ _
  have hvals : l18.map σ4.val = List.ofFn (PrimT.S3.symNums k) := by
    rw [ofFn_symNums]
    have a0 : σ4.val SymDec.dA = k.a := by rw [v4 _ (by rw [dA_val]; omega)]; exact hF.vA
    have a1 : σ4.val (SymDec.G 41) = Fintype.card k.Pl.FlatSeed := by
      rw [v4 _ (by rw [G41_val]; omega)]; exact hF.vK
    have aL : ∀ j : Fin 4, σ4.val (rL j) = (PrimT.S3.gatesJ k j).length := fun j => by
      rw [v4 _ (by rw [rL_val]; omega)]; exact hLj j
    have aH : ∀ j : Fin 4, σ4.val (rH j) = PrimT.tabH (PrimT.S3.gatesJ k j) := fun j => by
      rw [keepQ _ (by rw [rH_val]; omega), keepT _ (by rw [rH_val]; have := j.isLt; omega)]
      exact IH1 j j.isLt
    have aT : ∀ j : Fin 4, σ4.val (rT j) = PrimT.S3.tabLen k j := fun j => by
      rw [keepQ _ (by rw [rT_val]; have := j.isLt; omega), IT1 j j.isLt, tabLen_regs]
      rfl
    have aQ : ∀ j : Fin 4, σ4.val (rQ j) = (PrimT.S3.templJ k j).length := fun j => by
      rw [IQ1 j j.isLt]
      rfl
    simp only [l18, List.map_cons, List.map_nil, a0, a1, aL, aH, aT, aQ]
  -- 5: the unary list
  have hOP4 : σ4.val rOP = 0 := by
    rw [keepQ _ (by rw [rOP_val]; omega), keepT _ (by rw [rOP_val]; omega)]
    exact z2 _ (by rw [rOP_val]; omega) (by rw [rOP_val]; omega)
  have hO4 : σ4.st (oOut x hx) = [] := by
    rw [IQ3 _ (fun j _ => hOT j), IT3, IH3, s1]
    exact hF.hi ⟨DataDock.DT + 7, by omega⟩ (by show DataDock.DT + 3 ≤ DataDock.DT + 7; omega)
  have hsh4 : σ4.sh = τ0.sh := by rw [IQ5, IT4, IH4, sh1]
  have hlen := unaryList_len_le V _ hvsV
  rw [List.length_ofFn] at hlen
  obtain ⟨τ5, e5, st5, sh5, op5, z5, keep5, sto5, sho5, ce5⟩ := SBEmit.emitList_spec cap (oOut x hx) rOP l18
    (List.ofFn (PrimT.S3.symNums k)) σ4 (by rw [List.length_ofFn]; rfl)
    (List.Nodup.of_map Fin.val (by
      change [321, 449, 330, 331, 332, 333, 100, 101, 102, 103, 108, 109, 110, 111, 112, 113, 114, 115].Nodup
      decide))
    (fun R hR e => by subst e; exact absurd hR (by decide))
    (get_of_map l18 σ4.val _ hvals) (by rw [hsh4, hO4, hF.heads]; rfl) (by rw [hOP4]; omega)
  -- 6: the rewind
  obtain ⟨n5, hn5⟩ : ∃ v, v = (Data.unaryList (List.ofFn (PrimT.S3.symNums k))).length := ⟨_, rfl⟩
  have op5' : τ5.val rOP = n5 := by rw [op5, hOP4, hn5, Nat.zero_add]
  have e6 := wrewind_spec cap (oOut x hx) rOP n5 τ5 op5' (by rw [op5']; omega)
  -- 7: every register cleared
  have hv5 : ∀ r, τ5.val r ≤ cap :=
    FinalPass.S5T.WExec.val_le cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) hv0
  obtain ⟨τ7, e7, s7, sh7, ce7, z7⟩ := FinalPass.S5T.clearAll_spec cap
    ((τ5.setv rOP 0).seth (oOut x hx) (τ5.sh (oOut x hx) - n5)) (fun r => by
      simp only [WState.seth_val, WState.setv_val, Function.update_apply]
      split_ifs
      · exact Nat.zero_le _
      · exact hv5 r)
  have hO5 : τ5.st (oOut x hx) = Data.unaryList (List.ofFn (PrimT.S3.symNums k)) := by rw [st5, hO4, List.nil_append]
  refine ⟨τ7, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))), ?_,
    ?_, ?_, fun i hi ho => ?_, fun i => ?_, z7, ?_⟩
  · -- the steps
    have c1 : scrL.length * (3 * cap + 2) ≤ 512 * (3 * cap + 2) := Nat.mul_le_mul_right _ scrL_len
    have c5 := emitListCost_le V _ hvsV
    rw [List.length_ofFn] at c5
    have c7 : LNR * (3 * cap + 2) = 512 * (3 * cap + 2) := rfl
    have hn : n5 ≤ cap := by omega
    omega
  · rw [s7]
    show τ5.st (oOut x hx) = _
    exact hO5
  · rw [s7]
    show τ5.st (sIn x) = _
    rw [sto5 _ hIO, IQ3 _ (fun j _ => hIT j), IT3, IH3, s1]
    exact hF.hin
  · rw [s7]
    show (τ5.st i).length ≤ cap
    rw [sto5 _ ho]
    by_cases hj : ∃ j : Fin 4, i = oT x hx j
    · obtain ⟨j, rfl⟩ := hj
      exact le_trans (IQ4 j j.isLt) (le_trans (hTp j) (by omega))
    · rw [IQ3 _ (fun j _ e => hj ⟨j, e⟩), IT3, IH3, s1]
      exact le_trans (hF.resid i hi) (by omega)
  · rw [sh7]
    simp only [WState.seth_sh, WState.setv_sh, Function.update_apply]
    split_ifs with h
    · rw [sh5, hO5, ← hn5]; exact Nat.sub_self _
    · rw [sho5 _ h, hsh4]; exact hF.heads i
  · rw [ce7]
    show τ5.cell = false
    rw [ce5, IQ6, IT5, IH5, ce1]
    exact hF.cell

end Post

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
