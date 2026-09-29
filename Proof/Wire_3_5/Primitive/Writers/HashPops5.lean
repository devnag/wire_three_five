import Proof.Wire_3_5.Primitive.Writers.HashPops4

/-! # HASH setup (C), P2a part 5: the loops' invariants and one row `(g, p)`

* **`ws_loop`** (a stream loop `whs S body` under an invariant, one body run per step), **`cd_loop`** (a counted loop
  `countW C body` under an invariant): the loop lemmas with existential exit states (the digit stream's blank length
  varies with the rows);
* `digL` (row `(g, p)`'s digit populations, `ofFn thrDigGis`), `rowW`, **`row_spec`**: C1's digit program
  `Digs.DigsW` on the blanked digit stream (transported by `ThrPt.wexec_pad`), every digit's two records appended to
  the output, the digit word erased back to blanks.

Paper quantities of the main type: row `(g, p)`'s digit populations `v_{i,d}` (P3:2596-2599) and their records
(P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.HbM (elemW popRec)

section Loops
variable {ns nr : ℕ} (cap : ℕ)

/-- **A stream loop under an invariant.** -/
theorem ws_loop (S : Fin (ns + 1)) (body : WM ns nr) (c : ℕ) (Inv : ℕ → WState ns nr → Prop) (m : ℕ)
    (hT : ∀ k < m, ∀ σ, Inv k σ → wbit σ S = true) (hF : ∀ σ, Inv m σ → wbit σ S = false)
    (hstep : ∀ k < m, ∀ σ, Inv k σ → ∃ τ, WExec cap body σ τ c ∧ Inv (k + 1) τ) :
    ∀ j ≤ m, ∀ σ, Inv (m - j) σ → ∃ τ, WExec cap (.whs S body) σ τ (j * (c + 2) + 1) ∧ Inv m τ
  | 0, _, σ, hσ => by
    rw [Nat.sub_zero] at hσ
    exact ⟨σ, WExec.cast cap (WExec.whsF (hF σ hσ)) rfl (by omega), hσ⟩
  | j + 1, hj, σ, hσ => by
    obtain ⟨τ1, e1, i1⟩ := hstep (m - (j + 1)) (by omega) σ hσ
    rw [show m - (j + 1) + 1 = m - j by omega] at i1
    obtain ⟨τ, e2, i2⟩ := ws_loop S body c Inv m hT hF hstep j (by omega) τ1 i1
    exact ⟨τ, WExec.cast cap (WExec.whsT (hT (m - (j + 1)) (by omega) σ hσ) e1 e2) rfl (by ring_nf; omega), i2⟩

/-- **A counted loop under an invariant.** -/
theorem cd_loop (C : Fin nr) (body : WM ns nr) (c : ℕ) (Inv : ℕ → WState ns nr → Prop) (n : ℕ) (hn : n ≤ cap)
    (hC : ∀ k ≤ n, ∀ σ, Inv k σ → σ.val C = n - k)
    (hstep : ∀ k < n, ∀ σ, Inv k σ → ∃ τ, WExec cap body (σ.setv C (n - k - 1)) τ c ∧ Inv (k + 1) τ) :
    ∀ j ≤ n, ∀ σ, Inv (n - j) σ →
      ∃ τ, WExec cap (FinalPass.ThrArith.countW C body) σ τ (j * (c + 4) + 1) ∧ Inv n τ
  | 0, _, σ, hσ => by
    rw [Nat.sub_zero] at hσ
    have h0 := hC n le_rfl σ hσ
    rw [Nat.sub_self] at h0
    exact ⟨σ, WExec.cast cap (WExec.whrF h0) rfl (by omega), hσ⟩
  | j + 1, hj, σ, hσ => by
    have hv := hC (n - (j + 1)) (by omega) σ hσ
    obtain ⟨τ1, e1, i1⟩ := hstep (n - (j + 1)) (by omega) σ hσ
    rw [show n - (j + 1) + 1 = n - j by omega] at i1
    obtain ⟨τ, e2, i2⟩ := cd_loop C body c Inv n hn hC hstep j (by omega) τ1 i1
    have d := WExec.dec (cap := cap) C σ (by rw [hv]; omega)
    rw [hv, show n - (n - (j + 1)) - 1 = n - (n - (j + 1)) - 1 from rfl] at d
    have d' : WExec cap (.dec C) σ (σ.setv C (n - (n - (j + 1)) - 1)) 1 := d
    exact ⟨τ, WExec.cast cap (WExec.whrT (by rw [hv]; omega) (WExec.seq d' e1) e2) rfl (by ring_nf; omega), i2⟩

end Loops

/-- **Row `(g, p)`'s digit populations**: the pool gates of digit `d`'s population, `d < τ₀`. -/
def digL (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) :
    List (List ℕ) :=
  List.ofFn fun d => Records.thrDigGis P Cs carriers alg den g pr d

theorem digsWord_eq (ls : List (List ℕ)) : FinalPass.Digs.digsWord ls = ls.flatMap segW := rfl

section Row
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (h : L.Ok) (σB : WState ns nr)
include h

theorem padAll_w (t : LS) (l : List Bool) (kD : ℕ) :
    FinalPass.ThrPt.padAll (({ t with dg := l }).w L σB) (fun s => if s = L.Dg then kD else 0) =
      ({ t with dg := FinalPass.ThrPt.pad l kD }).w L σB := by
  apply WState.eq
  · rfl
  · funext s
    simp only [FinalPass.ThrPt.padAll_st, LS.w]
    by_cases h1 : s = L.O
    · subst h1; simp [(O_Dg h), FinalPass.ThrPt.pad_zero]
    · by_cases h2 : s = L.Dg
      · subst h2; simp [h1]
      · simp [h1, h2, FinalPass.ThrPt.pad_zero]
  · rfl
  · rfl

/-- **One row `(g, p)`**: C1's digit program, every digit's two records, the digit word erased. -/
def rowW (DW : FinalPass.Digs.DigsW) : WM ns nr := .seq (DW.prog L.Pay L.Dg L.R) (.seq (fmtW L) (eraseW L))

/-- The row's entry for C1's digit program: the tracked state with the digit stream empty. -/
theorem row_in (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ)
    (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (t : LS)
    (hdh : t.dh = 0) (hgi : t.gi = (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)) (hp : t.p = pr.val)
    (hpay : ∀ i : Fin 4, σB.st (L.Pay i) = if hi : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, hi⟩) else [])
    (hpayH : ∀ i : Fin 4, σB.sh (L.Pay i) = 0) (h0 : σB.val (L.R 0) = a')
    (h3 : σB.val (L.R 3) = Primitive.thrDigits P Cs alg den) (h4 : σB.val (L.R 4) = Records.thrOff P Cs carriers)
    (hz : ∀ j : Fin FinalPass.Digs.digsK, 5 ≤ j.val → σB.val (L.R j) = 0) :
    FinalPass.Digs.DigsIn L.Pay L.Dg L.R P Cs carriers alg den g pr (({ t with dg := [] }).w L σB) := by
  have oth0 : ∀ j : Fin FinalPass.Digs.digsK, j.val ≠ 1 → j.val ≠ 2 →
      (({ t with dg := [] } : LS).w L σB).val (L.R j) = σB.val (L.R j) :=
    fun j a b => w_val_other L h σB _ (L.R j) (h.rOut j a b 0) (h.rOut j a b 1) (h.rOut j a b 2)
      (h.rOut j a b 3) (h.rOut j a b 4) (h.rOut j a b 5) (h.rOut j a b 6) (h.rOut j a b 7)
  exact
    { pay := fun i => by
        rw [w_st_other L h σB _ _ (h.payNe i).1 (h.payNe i).2.1]; exact hpay i
      payH := fun i => by
        rw [w_sh_other L h σB _ _ (h.payNe i).1 (h.payNe i).2.1 (h.payNe i).2.2]; exact hpayH i
      dg := by rw [w_st_Dg L h]
      dgH := by rw [w_sh_Dg L h]; exact hdh
      vA := by rw [oth0 0 (by decide) (by decide)]; exact h0
      vG := by rw [w_1 L h]; exact hgi
      vP := by rw [w_2 L h]; exact hp
      vTau := by rw [oth0 3 (by decide) (by decide)]; exact h3
      vOff := by rw [oth0 4 (by decide) (by decide)]; exact h4
      zero := fun j hj => by rw [oth0 j (by omega) (by omega)]; exact hz j hj }

theorem row_spec (DW : FinalPass.Digs.DigsW) (P : Shared.StarParams) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Stars.Carrier P.n))
    (alg : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (g : Primitive.ThrEq P Cs alg)
    (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den)) (t : LS) (kD : ℕ)
    (hdg : t.dg = List.replicate kD false) (hdh : t.dh = 0) (hk : t.k = 0) (hdl : t.dl = 0) (hdc : t.dc = 0)
    (hgi : t.gi = (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)) (hp : t.p = pr.val)
    (hpay : ∀ i : Fin 4, σB.st (L.Pay i) = if hi : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, hi⟩) else [])
    (hpayH : ∀ i : Fin 4, σB.sh (L.Pay i) = 0) (h0 : σB.val (L.R 0) = a')
    (h3 : σB.val (L.R 3) = Primitive.thrDigits P Cs alg den) (h4 : σB.val (L.R 4) = Records.thrOff P Cs carriers)
    (hz : ∀ j : Fin FinalPass.Digs.digsK, 5 ≤ j.val → σB.val (L.R j) = 0) (hT : σB.val L.T = 0)
    (hneed : DW.need (FinalPass.Digs.digsN P Cs carriers alg den pr.val) ≤ cap)
    (hn : Primitive.thrDigits P Cs alg den ≤ cap)
    (hc1 : t.out.length + ((digL P Cs carriers alg den g pr).flatMap recsOf).length +
      2 * ((digL P Cs carriers alg den g pr).flatMap segW).length + 4 ≤ cap)
    (hc2 : ((digL P Cs carriers alg den g pr).flatMap segW).length ≤ cap) :
    WExec cap (rowW L DW) (t.w L σB)
      ({ t with
          out := t.out ++ (digL P Cs carriers alg den g pr).flatMap recsOf
          dg := List.replicate (((digL P Cs carriers alg den g pr).flatMap segW).length +
            (kD - ((digL P Cs carriers alg den g pr).flatMap segW).length)) false }.w L σB)
      (DW.bound (FinalPass.Digs.digsN P Cs carriers alg den pr.val) + 1 +
        (18 * Primitive.thrDigits P Cs alg den + 3 + 1 + (Primitive.thrDigits P Cs alg den *
          (46 * ((digL P Cs carriers alg den g pr).flatMap segW).length + 69 + 4) + 1)) + 1 +
        (7 * ((digL P Cs carriers alg den g pr).flatMap segW).length + 1)) := by
  have hlen : (digL P Cs carriers alg den g pr).length = Primitive.thrDigits P Cs alg den := by simp [digL]
  have hIn := row_in L h σB P Cs carriers alg den g pr t hdh hgi hp hpay hpayH h0 h3 h4 hz
  set t0 : LS := { t with dg := [] } with ht0
  have e1 := DW.run L.Pay L.Dg L.R h.payInj (fun i => (h.payNe i).2.1) P ha' Cs carriers alg den g pr cap
    (t0.w L σB) hIn hneed
  rw [sets_Dg_w L h] at e1
  have e1' := FinalPass.ThrPt.wexec_pad e1 (fun s => if s = L.Dg then kD else 0)
  rw [padAll_w L h σB t0 [] kD, padAll_w L h σB t0 _ kD, FinalPass.ThrPt.pad_nil] at e1'
  have ht0' : ({ t0 with dg := List.replicate kD false } : LS) = t := by
    apply LS.ext <;> simp [ht0, hdg]
  rw [ht0', show (List.ofFn fun d => Records.thrDigGis P Cs carriers alg den g pr d) =
    digL P Cs carriers alg den g pr from rfl] at e1'
  generalize digL P Cs carriers alg den g pr = ls at e1' hc1 hc2 hlen ⊢
  set t1 : LS := { t0 with dg := FinalPass.ThrPt.pad (FinalPass.Digs.digsWord ls) kD } with ht1
  have e2 := fmt_spec cap L h σB ls (List.replicate (kD - (ls.flatMap segW).length) false) t1
    (by simp only [ht1, ht0, digsWord_eq, FinalPass.ThrPt.pad]) (by simp only [ht1, ht0, hdh])
    (by simp only [ht1, ht0, hk]) (by simp only [ht1, ht0, hdc]) hT (by rw [hlen]; exact h3) (by rw [hlen]; exact hn)
    (by simp only [ht1, ht0]; omega) (by simp only [ht1, ht0, hdl]; omega)
  have e3 := erase_spec cap L h σB (ls.flatMap segW).length
    ({ t1 with out := t1.out ++ ls.flatMap recsOf, dh := (ls.flatMap segW).length, dl := t1.dl + (ls.flatMap segW).length })
    (by simp only [ht1, ht0, hdl, Nat.zero_add]) rfl
    (by simp only [ht1, ht0, FinalPass.ThrPt.pad, digsWord_eq, List.length_append]; omega) (by omega)
  refine WExec.cast cap (WExec.seq e1' (WExec.seq e2 e3)) ?_ (by rw [hlen]; omega)
  congr 1
  apply LS.ext <;> simp only [ht1, ht0, hdl, hdh, FinalPass.ThrPt.pad, digsWord_eq]
  rw [List.drop_left' rfl, List.replicate_add]

end Row

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
