import Proof.Wire_3_5.UnionMachine.NumsN4

/-! # SWn, part 5: the numbers' writer `swN x hx Kt Et tp htp l : SWParts.SWnT l` (x ≥ DT + 8)

P3:3170-3178 (`symNums`: the SYM call's eighteen numbers, as a unary list, the SYM slot `32`): at a SYM request,
from the core's blank entry, on NW's bank `x ≥ DT + 8`:

1. The SYM front (`SymFront.frontM`, `front_runB`: the flat list's numbers, `J`, the walk length, the population
   lengths and the gate tables);
2. The post program `postN x hx tp` (`postRun`: the gate tables' widths, the tables' lengths, the templates'
   lengths `tp` (with `TplIface Kt Et tp`), the unary list on the output stream `oOut`, every register cleared).

The capacity `Kn5 F·(|fpIn|+1)^{Dn5 fe}` (above the front's need and the post program's `capP Kt Et (C_F·X^{D_Fs})`),
the steps and the residues `Cs5 F·(|fpIn|+1)^{Ds5 fe}` (degrees on `l`, `Et` and `fe` only; coefficients on `l`, `Kt`,
`Et` and the gate).

* `cap5_arith`, `cost5_arith` (pure bounds); `Kn5`, `Dn5`, `Cs5`, `Ds5`; `sO5`; `swnM`; **`swnRun`**, **`swN`**.

Paper quantity of the main type: the SYM call numbers `symNums k` (the unary list of the eighteen numbers, P3:3170-3178)
at every SYM request, on the writer's output stream, in time polynomial in the input. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

/-! ## Arithmetic -/

/-- The front's need and the post program's capacity below `(K + 100(Kt+8)(3(C+2))^{Et+3})·X^{D + S(Et+3)}`. -/
theorem cap5_arith (Kt Et K C X D S : ℕ) (hX : 1 ≤ X) :
    K * X ^ D ≤ (K + 100 * (Kt + 8) * (3 * (C + 2)) ^ (Et + 3)) * X ^ (D + S * (Et + 3)) ∧
    capP Kt Et (C * X ^ S) ≤ (K + 100 * (Kt + 8) * (3 * (C + 2)) ^ (Et + 3)) * X ^ (D + S * (Et + 3)) := by
  have hS : 1 ≤ X ^ S := Nat.one_le_pow _ _ hX
  have hD : 1 ≤ X ^ D := Nat.one_le_pow _ _ hX
  have e1 : X ^ (D + S * (Et + 3)) = X ^ D * (X ^ S) ^ (Et + 3) := by rw [pow_add, pow_mul]
  have hb : 3 * (C * X ^ S + 2) ≤ 3 * (C + 2) * X ^ S := by
    have e : 3 * (C + 2) * X ^ S = 3 * (C * X ^ S) + 6 * X ^ S := by ring
    omega
  have hp : (3 * (C * X ^ S + 2)) ^ (Et + 3) ≤ (3 * (C + 2)) ^ (Et + 3) * (X ^ S) ^ (Et + 3) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hb _
  have hY : 1 ≤ (X ^ S) ^ (Et + 3) := Nat.one_le_pow _ _ hS
  rw [e1]
  unfold capP
  generalize (3 * (C * X ^ S + 2)) ^ (Et + 3) = Aw at hp ⊢
  generalize (3 * (C + 2)) ^ (Et + 3) = P at hp ⊢
  generalize (X ^ S) ^ (Et + 3) = Y at hp hY ⊢
  generalize X ^ D = Z at hD ⊢
  constructor
  · have h1 : K * Z ≤ K * (Z * Y) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hY)
    have e : (K + 100 * (Kt + 8) * P) * (Z * Y) = K * (Z * Y) + 100 * (Kt + 8) * P * Z * Y := by ring
    omega
  · have h2 : 100 * (Kt + 8) * Aw ≤ 100 * (Kt + 8) * (P * Y) := Nat.mul_le_mul_left _ hp
    have h3 : P * Y ≤ P * Y * Z := Nat.le_mul_of_pos_right _ hD
    have h4 : 100 * (Kt + 8) * (P * Y) ≤ 100 * (Kt + 8) * (P * Y * Z) := Nat.mul_le_mul_left _ h3
    have e : (K + 100 * (Kt + 8) * P) * (Z * Y) = K * (Z * Y) + 100 * (Kt + 8) * (P * Y * Z) := by ring
    omega

/-- The steps (the front's `≤ C·X^S`, one seam, the post program's `≤ 4000·cap + 4000`) and the capacity below
`(C + 4000K + 4001)·X^{D + S}` at `cap = K·X^D`. -/
theorem cost5_arith (C K X S D m c : ℕ) (hX : 1 ≤ X) (hm : m ≤ C * X ^ S) (hc : c ≤ 4000 * (K * X ^ D) + 4000) :
    m + 1 + c ≤ (C + 4000 * K + 4001) * X ^ (D + S) ∧ K * X ^ D ≤ (C + 4000 * K + 4001) * X ^ (D + S) := by
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ (D + S) := ⟨_, rfl⟩
  rw [← hY]
  have p1 : X ^ S ≤ Y := by rw [hY]; exact Nat.pow_le_pow_right hX (by omega)
  have p2 : X ^ D ≤ Y := by rw [hY]; exact Nat.pow_le_pow_right hX (by omega)
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.one_le_pow _ _ hX
  have q1 : C * X ^ S ≤ C * Y := Nat.mul_le_mul_left _ p1
  have q2 : K * X ^ D ≤ K * Y := Nat.mul_le_mul_left _ p2
  have e : (C + 4000 * K + 4001) * Y = C * Y + 4000 * (K * Y) + 4001 * Y := by ring
  rw [e]
  exact ⟨by omega, by omega⟩

/-! ## The constants -/

section Consts
variable (l : Literals)

/-- **The register capacity's coefficient** (on the gate, `Kt`, `Et`). -/
noncomputable def Kn5 (Kt Et : ℕ) (F : GateFree l) : ℕ :=
  FinalPass.SymFront.KF l F + 100 * (Kt + 8) * (3 * (FinalPass.SymFront.CF l F + 2)) ^ (Et + 3)

/-- **The register capacity's degree** (on the filter degree and `Et`). -/
noncomputable def Dn5 (Et fe : ℕ) : ℕ := FinalPass.SymFront.DF l fe + FinalPass.SymFront.DFs l fe * (Et + 3)

/-- The steps' and the residues' coefficient. -/
noncomputable def Cs5 (Kt Et : ℕ) (F : GateFree l) : ℕ := FinalPass.SymFront.CF l F + 4000 * Kn5 l Kt Et F + 4001

/-- The steps' and the residues' degree. -/
noncomputable def Ds5 (Et fe : ℕ) : ℕ := Dn5 l Et fe + FinalPass.SymFront.DFs l fe

end Consts

/-! ## The machine and its run -/

section Gate
variable (x : ℕ) (hx : DataDock.DT + 8 ≤ x) (l : Literals) (Kt Et : ℕ)
  (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr)

/-- The output stream, as `SWnT`'s one slot. -/
def sO5 : Fin 1 ↪ Fin (LNS x + 1) := ⟨fun _ => oOut x hx, fun a b _ => Subsingleton.elim a b⟩

theorem sO5_ne (k : Fin 1) : sO5 x hx k ≠ sIn x := fun e => by
  have h1 := congrArg Fin.val e
  have h2 : (sO5 x hx k).val = 161 + (DataDock.DT + 7) := oOut_val x hx
  have h3 : (sIn x).val = 150 := rfl
  omega

/-- **SWn's machine** at a gate: the SYM front, then the post program. -/
noncomputable def swnM (F : GateFree l) :=
  Composition.machine (FinalPass.SymFront.frontM x (dt3 hx) l F) (postN x hx tp).toProg.compile

/-- **SWn's run at a SYM request**: the unary list of the eighteen call numbers on the output stream. -/
theorem swnRun (htp : TplIface Kt Et tp) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ}
    (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (σ : St x)
    (hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩))
    (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ sIn x → σ.st i = []) (hv : ∀ q, σ.val q = 0) (hc : σ.cell = false) :
    ∃ (τ : St x) (m : ℕ),
      m ≤ Cs5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length
        + 1) ^ Ds5 l Et F.filterErrDeg ∧
      Step (swnM x hx l tp F) m
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) σ).H
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) σ).A
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) τ).H
        (wenc (Kn5 l Kt Et F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
          hcall⟩).length + 1) ^ Dn5 l Et F.filterErrDeg) τ).A ∧
      (∀ k : Fin 1, τ.st (sO5 x hx k) = FinalPass.SWParts.swWs l 16 1 (by norm_num) F kclk coef A a ha
        ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ k) ∧
      τ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) ∧
      (∀ i, i ≠ sIn x → (∀ k, i ≠ sO5 x hx k) →
        (τ.st i).length ≤ Cs5 l Kt Et F * ((fpIn l F kclk coef A a ha
          ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Ds5 l Et F.filterErrDeg) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩,
    hcall⟩).length + 1 := ⟨_, rfl⟩
  rw [← hXd]
  have hX : 1 ≤ X := by omega
  obtain ⟨hcF, hcP⟩ := cap5_arith Kt Et (FinalPass.SymFront.KF l F) (FinalPass.SymFront.CF l F) X
    (FinalPass.SymFront.DF l F.filterErrDeg) (FinalPass.SymFront.DFs l F.filterErrDeg) hX
  obtain ⟨τ0, m, hm, sF, hF⟩ := FinalPass.SymFront.front_runB x (dt3 hx) l F kclk coef A a ha ha' Cs carriers
    translation hcall (Kn5 l Kt Et F * X ^ Dn5 l Et F.filterErrDeg) (by rw [← hXd]; exact hcF) σ
    ⟨hin, hsh, hbl, hv, hc⟩
  rw [← hXd] at hm hF
  obtain ⟨τ, c, eP, hc', hout, hin', hres, hsh', hv', -⟩ := postRun x hx Kt Et tp htp
    (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers)
    (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
    (FinalPass.SymFront.CF l F * X ^ FinalPass.SymFront.DFs l F.filterErrDeg)
    (Kn5 l Kt Et F * X ^ Dn5 l Et F.filterErrDeg) τ0 hF hcP
  obtain ⟨hM, hK⟩ := cost5_arith (FinalPass.SymFront.CF l F) (Kn5 l Kt Et F) X
    (FinalPass.SymFront.DFs l F.filterErrDeg) (Dn5 l Et F.filterErrDeg) m c hX hm hc'
  refine ⟨τ, m + 1 + c, hM, Step.seq sF (Exec.step (WExec.exec _ eP)), fun k => ?_, hin',
    fun i h1 h2 => (hres i h1 (h2 0)).trans hK, hsh', hv'⟩
  exact hout.trans (by rw [Subsingleton.elim k 0]; exact
    (swn_word l F kclk coef A a ha ha' Cs carriers translation hcall hs).symm)

/-- **SWn** (`SWParts.SWnT l`) on NW's bank `x ≥ DT + 8`, the template length program `tp` with its interface. -/
noncomputable def swN (htp : TplIface Kt Et tp) : FinalPass.SWParts.SWnT l :=
  ⟨LNS x, LNR, _, fun F => swnM x hx l tp F, sIn x, sO5 x hx, sO5_ne x hx,
    Kn5 l Kt Et, Dn5 l Et, Cs5 l Kt Et, Ds5 l Et,
    fun F kclk coef A a ha r hm σ hin hsh hbl hv hc => by
      obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
      have hm' : mode = .sym := hm
      subst hm'
      exact swnRun x hx l Kt Et tp htp F kclk coef A a ha ha' Cs carriers translation hcall σ hin hsh hbl hv hc⟩

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
