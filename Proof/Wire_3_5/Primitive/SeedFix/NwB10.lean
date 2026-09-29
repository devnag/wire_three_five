import Proof.Wire_3_5.Primitive.SeedFix.NwB9

/-! # NW phase (b), part 10: the register program after the docks

**`wbW`** (`wb_spec`): W6's four numbers read from their ports (`ports4W`), `2^{sb}` (`gapW`), the value
(`vArithW`), the final clear and restore (`finW`): `rN, rM, rE, rT` hold the saves, `rV` holds
`V = vVal |𝒢| cut Σp 2^{sb} #primes n k_h`, every other register `0`; streams, heads and cell kept.

Paper quantity of the main type: phase (b)'s value `V = |PrimeIndex(cut)|·|E|·Q` in `rV` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

variable (cap : ℕ) (x : ℕ)

/-- Register bookkeeping: `setv` chains at the literal registers. -/
local macro "vsimp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := {decide := true}) [WState.setv_val, Function.update_apply, $hs,*])

/-- **The register program after the docks.** -/
def wbW (p1 p2 p3 p4 : Fin (LNS x + 1)) : WM (LNS x) LNR :=
  .seq (ports4W x p1 p2 p3 p4) (.seq (gapW x) (.seq (vArithW x) (finW x)))

theorem wb_spec (p1 p2 p3 p4 : Fin (LNS x + 1)) (g c ps np capT n feL kh vN vM vE vT : ℕ)
    (σ : WState (LNS x) LNR)
    (h1 : σ.st p1 = List.replicate g true) (h2 : σ.st p2 = List.replicate c true)
    (h3 : σ.st p3 = List.replicate np true) (h4 : σ.st p4 = List.replicate ps true)
    (k1 : σ.sh p1 = 0) (k2 : σ.sh p2 = 0) (k3 : σ.sh p3 = 0) (k4 : σ.sh p4 = 0)
    (hZ : ∀ r : Fin LNR, 400 ≤ r.val → r.val < 492 → (r.val < 450 ∨ 456 ≤ r.val) → σ.val r = 0)
    (hC : σ.val (Hb 13) = capT) (hN : σ.val dN = n) (hF : σ.val sFL = feL) (hK : σ.val sKH = kh)
    (hs0 : σ.val s0 = vN) (hs1 : σ.val s1 = vM) (hs2 : σ.val s2 = vE) (hs3 : σ.val s3 = vT)
    (hb : ∀ r, σ.val r ≤ cap)
    (cg : g ≤ cap) (cc : c ≤ cap) (cnp : np ≤ cap) (cps : ps ≤ cap) (hB1 : 1 ≤ capT)
    (hcT : capT * 32 + 2 ≤ cap) (hcN : 2 * (n + 1) ^ 26 + 8 ≤ cap) (hcF : feL + 4 ≤ cap)
    (hsc : 2 ^ ((SymDec.gP n capT feL).seedBits + 1) ≤ cap)
    (hlc : (SymDec.gP n capT feL).labelBits + (SymDec.gP n capT feL).fieldBits + (SymDec.gP n capT feL).walkLen + 512
      ≤ cap)
    (hqc : 2 * (g * c) + 1 ≤ cap) (hnp1 : 1 ≤ np) (hn1 : 1 ≤ n)
    (hV : vVal g c ps (2 ^ (SymDec.gP n capT feL).seedBits) np n kh ≤ cap) :
    ∃ τ k, WExec cap (wbW x p1 p2 p3 p4) σ τ k ∧
      k ≤ 4 * UnaryPow.sq cap + 48 * cap + 20 + 1 + (250 * UnaryPow.sq cap + 1 + (50 * UnaryPow.sq cap + 40000 + 1 +
        (512 * (3 * cap + 2) + 7 * (vN + vM + vE + vT + vVal g c ps (2 ^ (SymDec.gP n capT feL).seedBits) np n kh) +
          10))) ∧
      τ.val NumsPh2.rN = vN ∧ τ.val NumsPh2.rM = vM ∧ τ.val NumsPh2.rE = vE ∧ τ.val NumsPh2.rT = vT ∧
      τ.val NumsPh2.rV = vVal g c ps (2 ^ (SymDec.gP n capT feL).seedBits) np n kh ∧
      (∀ q, q ≠ NumsPh2.rN → q ≠ NumsPh2.rM → q ≠ NumsPh2.rE → q ≠ NumsPh2.rT → q ≠ NumsPh2.rV → τ.val q = 0) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have z0 : ∀ r : Fin LNR, 400 ≤ r.val → r.val < 440 → σ.val r = 0 := fun r a b => hZ r a (by omega) (Or.inl (by omega))
  obtain ⟨c1, e1, c1le⟩ := ports4_spec cap x p1 p2 p3 p4 g c np ps σ h1 h2 h3 h4 k1 k2 k3 k4
    (hZ rG (by decide) (by decide) (Or.inl (by decide))) (hZ rCU (by decide) (by decide) (Or.inl (by decide)))
    (hZ rNP (by decide) (by decide) (Or.inl (by decide))) (hZ rPS (by decide) (by decide) (Or.inl (by decide)))
    (hZ rR (by decide) (by decide) (Or.inr (by decide))) (hZ rTm (by decide) (by decide) (Or.inr (by decide)))
    cg cc cnp cps
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = (((σ.setv rG g).setv rCU c).setv rNP np).setv rPS ps := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have q1 : ∀ r : Fin LNR, (r.val < 440 ∨ 444 ≤ r.val) → σ1.val r = σ.val r := fun r hr => by
    rw [hσ1]
    simp only [WState.setv_val, Function.update_apply, if_neg (show r ≠ rG from fv (by show r.val ≠ 440; omega)),
      if_neg (show r ≠ rCU from fv (by show r.val ≠ 441; omega)),
      if_neg (show r ≠ rNP from fv (by show r.val ≠ 442; omega)),
      if_neg (show r ≠ rPS from fv (by show r.val ≠ 443; omega))]
  have st1 : σ1.st = σ.st := by rw [hσ1]; rfl
  have sh1 : σ1.sh = σ.sh := by rw [hσ1]; rfl
  have cl1 : σ1.cell = σ.cell := by rw [hσ1]; rfl
  have zK : ∀ i : Fin 32, σ1.val (K32 i) = 0 := fun i => by
    have := i.isLt
    rw [q1 _ (Or.inl (by rw [K32_val]; omega))]
    exact z0 _ (by rw [K32_val]; omega) (by rw [K32_val]; omega)
  have zz : ∀ r : Fin LNR, 444 ≤ r.val → r.val < 492 → (r.val < 450 ∨ 456 ≤ r.val) → σ1.val r = 0 :=
    fun r a b h => by rw [q1 r (Or.inr a)]; exact hZ r (by omega) b h
  obtain ⟨σ2, c2, e2, c2le, v2, fr2, st2, sh2, cl2⟩ := gap_spec cap x σ1 capT n feL
    (by rw [q1 _ (Or.inl (by decide))]; exact hC) (by rw [q1 _ (Or.inl (by decide))]; exact hN)
    (by rw [q1 _ (Or.inr (by decide))]; exact hF) zK (zz rK5 (by decide) (by decide) (Or.inr (by decide)))
    (zz r465 (by decide) (by decide) (Or.inr (by decide))) (zz r466 (by decide) (by decide) (Or.inr (by decide)))
    (zz r467 (by decide) (by decide) (Or.inr (by decide))) (zz rTm (by decide) (by decide) (Or.inr (by decide)))
    hB1 hcT hcN hcF hsc hlc
  have q2 : ∀ r : Fin LNR, 432 ≤ r.val → r ≠ rK5 → σ2.val r = σ1.val r := fun r a b => fr2 r (Or.inr a) b
  have zz2 : ∀ r : Fin LNR, 444 ≤ r.val → r.val < 492 → (r.val < 450 ∨ 456 ≤ r.val) → r ≠ rK5 → σ2.val r = 0 :=
    fun r a b h k => by rw [q2 r (by omega) k]; exact zz r a b h
  have hz0 : Z0 x σ2 := ⟨zz2 rT6 (by decide) (by decide) (Or.inl (by decide)) (by decide),
    zz2 rU6 (by decide) (by decide) (Or.inl (by decide)) (by decide),
    zz2 rW6 (by decide) (by decide) (Or.inl (by decide)) (by decide),
    zz2 rV6 (by decide) (by decide) (Or.inl (by decide)) (by decide),
    zz2 rTm (by decide) (by decide) (Or.inr (by decide)) (by decide),
    fun r a b => zz2 r (by omega) (by omega) (Or.inr (by omega)) (fv (by show r.val ≠ 464; omega))⟩
  have hi := St.init (x := x) (σ := σ2) (zz2 rA (by decide) (by decide) (Or.inl (by decide)) (by decide))
    (zz2 rMm (by decide) (by decide) (Or.inl (by decide)) (by decide))
    (zz2 rQq (by decide) (by decide) (Or.inr (by decide)) (by decide))
    (zz2 rBb (by decide) (by decide) (Or.inr (by decide)) (by decide))
    (zz2 rE2 (by decide) (by decide) (Or.inr (by decide)) (by decide))
    (zz2 rP2 (by decide) (by decide) (Or.inr (by decide)) (by decide))
  have vG : σ2.val rG = g := by rw [q2 rG (by decide) (by decide), hσ1]; vsimp []
  have vC : σ2.val rCU = c := by rw [q2 rCU (by decide) (by decide), hσ1]; vsimp []
  have vP : σ2.val rPS = ps := by rw [q2 rPS (by decide) (by decide), hσ1]; vsimp []
  have vNP : σ2.val rNP = np := by rw [q2 rNP (by decide) (by decide), hσ1]; vsimp []
  have vSB : σ2.val rSB = 2 ^ (SymDec.gP n capT feL).seedBits := v2
  have hvN : σ2.val dN = n := by rw [fr2 dN (Or.inl (by decide)) (by decide), q1 dN (Or.inl (by decide))]; exact hN
  have vK : σ2.val sKH = kh := by rw [q2 sKH (by decide) (by decide), q1 sKH (Or.inr (by decide))]; exact hK
  have hsb1 : 1 ≤ 2 ^ (SymDec.gP n capT feL).seedBits := Nat.one_le_two_pow
  have hq0 : True := trivial
  obtain ⟨σ3, c3, e3, c3le, h3⟩ := vArith_spec cap x σ2 hz0 hi g c ps (2 ^ (SymDec.gP n capT feL).seedBits) np n kh
    vG vC vP vSB vNP hvN vK cg cc cps hqc hsb1 hnp1 hn1 hV
  have hb3 := FinalPass.S5T.WExec.val_le cap e3 (FinalPass.S5T.WExec.val_le cap e2
    (FinalPass.S5T.WExec.val_le cap e1 hb))
  have g3 : ∀ r : Fin LNR, 450 ≤ r.val → r.val < 454 → σ3.val r = σ.val r := fun r a b => by
    rw [h3.get r ⟨fv (by show r.val ≠ 444; omega), fv (by show r.val ≠ 445; omega), fv (by show r.val ≠ 456; omega),
      fv (by show r.val ≠ 457; omega), fv (by show r.val ≠ 458; omega), fv (by show r.val ≠ 459; omega)⟩,
      q2 r (by omega) (fv (by show r.val ≠ 464; omega)), q1 r (Or.inr (by omega))]
  obtain ⟨τ, c4, e4, c4le, tN, tM, tE, tT, tV, tz, tst, tsh, tcl⟩ := fin_spec cap x σ3 vN vM vE vT _
    (by rw [g3 s0 (by decide) (by decide)]; exact hs0) (by rw [g3 s1 (by decide) (by decide)]; exact hs1)
    (by rw [g3 s2 (by decide) (by decide)]; exact hs2) (by rw [g3 s3 (by decide) (by decide)]; exact hs3) h3.hA hb3
  refine ⟨τ, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega, tN, tM, tE, tT, tV, tz, ?_, ?_, ?_⟩
  · rw [tst, h3.st, st2, st1]
  · rw [tsh, h3.sh, sh2, sh1]
  · rw [tcl, h3.cell, cl2, cl1]

end NearCubicWires.WireExponent3_5.PrimT.NwB
