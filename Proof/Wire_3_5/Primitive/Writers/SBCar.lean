import Proof.Wire_3_5.Foundations.OutMachineCarGen

/-! # SB, part 17: the carrier pipeline for SB (counts only), at any capacity

SB (S4's words `4 … 7`) needs the carriers' atom counts (`carLen = 2·carCnt`, `s4Small2`) and their number, not the
tables. The pipeline (`CarPipe.carPipe`) at the keep list `keepLS` (the request, the two counts and
`1^{|carriers|}`) erases every other stream, the tables included, and runs at any capacity above its needs:

* `pipe_le_cap` (`pipeCost` within `(57600(D+1) + 10^6)·cap²`, `pipe_le` at a general capacity);
* **`carRunS`**: at a request of the family, at every capacity `≥ 2^{D}·(|fpIn|+1)^{D}` (`D = DtC`): the counts on
  `sCar k 5`, `1^{|carriers|}` on `s6`, the request kept, the erased streams and the log at `0^{(N+2)^D}`, heads,
  registers and the cell back at `0`/`false`.

Paper quantity of the main type: the carriers' atom counts (`|X_k|`, P3:3071-3086). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBCar
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarS NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

theorem pipe_le_cap (cap Dt N n : ℕ) (hDt : 1 ≤ Dt) (codes : List ℕ) {n' : ℕ} (carriers : List (Stars.Carrier n'))
    (hT1 : m1Cost (c1Of n) n ≤ (N + 2) ^ Dt)
    (hT2 : Lof n + Out.CarM2.m2Bnd (c2Of N n) n (Lof n) codes carriers ≤ (N + 2) ^ Dt) (hTC : (N + 2) ^ Dt ≤ cap) :
    pipeCost cap Dt N n codes carriers ≤ (57600 * (Dt + 1) + 10 ^ 6) * cap ^ 2 := by
  have hN2 : N + 2 ≤ (N + 2) ^ Dt := Nat.le_self_pow (by omega) _
  have hsq := sq_le cap cap (by omega)
  have hCC : cap ≤ cap ^ 2 := Nat.le_self_pow (by norm_num) _
  have hmk : mkTCost cap Dt N ≤ (Dt + 1) * (4 * PrimAsm.UnaryPow.sq cap) + 27 * N + 12 := by unfold mkTCost; omega
  have hmk2 : (Dt + 1) * (4 * PrimAsm.UnaryPow.sq cap) ≤ (Dt + 1) * (28800 * cap ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have hr : (Dt + 1) * (28800 * cap ^ 2) = 28800 * ((Dt + 1) * cap ^ 2) := by ring
  have hr2 : (57600 * (Dt + 1) + 10 ^ 6) * cap ^ 2 = 57600 * ((Dt + 1) * cap ^ 2) + 10 ^ 6 * cap ^ 2 := by ring
  rw [hr2]
  unfold pipeCost s1Cost s3Cost
  omega

theorem carRunS (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) (σ : OSt) (hin : σ.st (oS sIN) = frame (fpIn l F kclk coef A a ha r))
    (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ oS sIN → σ.st i = []) (hv : ∀ q, σ.val q = 0)
    (hc : σ.cell = false) (cap : ℕ) (hcap : 2 ^ DtC * ((fpIn l F kclk coef A a ha r).length + 1) ^ DtC ≤ cap) :
    ∃ (τ : OSt) (m : ℕ), m ≤ (57600 * (DtC + 1) + 10 ^ 6) * cap ^ 2 ∧
      Step (carM DtC (eraseOf keepLS)) m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      (∀ k : Fin 2, τ.st (oS (sCar k 5)) = List.replicate (carCnt r.1.carriers k.val) true) ∧
      τ.st (oS Out.CarM2.s6) = List.replicate r.1.carriers.length true ∧
      τ.st (oS sIN) = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ∈ eraseOf keepLS ∨ i = oLog →
        τ.st i = List.replicate (((fpIn l F kclk coef A a ha r).length + 2) ^ DtC) false) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) ∧ τ.cell = false := by
  obtain ⟨_, hcar, _, hcount, _, _, _⟩ := r.2
  have hk : r.1.carriers.length ≤ 2 := hcount
  have henv : ∀ X ∈ r.1.carriers, X.WithinEnvelope 26 := hcar
  have ha4 : (PrimAsm.Codec.codeList r.1).length ≤ 4 := by rw [PrimAsm.Codec.codeList_length]; exact r.1.ha
  have hLX : ∀ X ∈ r.1.carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ Lof r.1.n := by
    intro X hX g hg
    have := (henv X hX).2 g hg
    unfold Lof; omega
  obtain ⟨tl, hw⟩ : ∃ tl, reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl = fpIn l F kclk coef A a ha r :=
    ⟨_, PrimAsm.ReqBridge.reqW_word r.1 _⟩
  have hnN : r.1.n ≤ (reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl).length := by rw [hw]; exact FpInLen.n_le_fpIn r
  rw [← hw] at hin hcap ⊢
  obtain ⟨hxN, hyN⟩ := S5T.natWord_le_reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
    (r.1.carriers.map Stars.Carrier.code) tl
  obtain ⟨hT1, hT2⟩ := T_bounds _ r.1.n (PrimAsm.Codec.codeList r.1) r.1.carriers hnN ha4 hk hxN hyN
  obtain ⟨hc1, hc2, hNc⟩ := caps DtC _ r.1.n (PrimAsm.Codec.codeList r.1) r.1.carriers hT1 hT2
  have hTc := (T_le_cap DtC (reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl).length).trans hcap
  obtain ⟨τ, m, hm, hstep, h5, -, h6, hkeep, hres, hτs, hτv, hτc⟩ :=
    carPipe DtC keepLS (by simp [keepLS]) (by simp [keepLS]) r.1.n (PrimAsm.Codec.modeBit r.1.mode)
      (PrimAsm.Codec.codeList r.1) r.1.carriers tl ha4 hk hLX σ hin hbl hsh hv hc cap hnN hxN hyN hT1 hT2
      (hc1.trans hTc) (hc2.trans hTc) hTc (hNc.trans hTc)
  refine ⟨τ, m, le_trans hm (pipe_le_cap cap DtC _ r.1.n one_le_DtC _ r.1.carriers hT1 hT2 hTc), hstep,
    fun k => h5 k (by fin_cases k <;> simp [keepLS]), h6, hkeep.trans hin, hres, hτs, hτv, hτc⟩

end NearCubicWires.WireExponent3_5.PrimAsm.SBCar
