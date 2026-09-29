import Proof.Wire_3_5.Primitive.SeedFix.CtrTrack

/-! # X3, part 4: a block's parity bits (P3:1202-1206, 1216)

"The syndrome `Hx` uniquely specifies `e`" (P3:1204-1206) and the code's systematic encoding (P3:1216): parity bit
`t` of a block is the XOR of the data bits at the positions `q` with bit `t` of `q + 1` set (`CtrMath.parB`). The
first pass of the center writer scans the block's data bits once per `t < s` (the row or column stream `R`, from
the block's start `b0`), accumulates parity `t` in `rgACC`, packs it into `rgPAR` at weight `2^t`, and returns `R`
to the block's start. Here:

* `ctog_spec` (the accumulator toggled on a data bit `1` with bit `t` set), `p1Mid_spec` (one position: a data bit
  read, or a parity position skipped), `P1I` (the scan's invariant), `p1_step`, **`p1Loop_spec`** (the scan's loop:
  `rgACC = parB t`);
* `scan1_spec` (one parity bit packed), **`p1_spec`** (all `s`: `rgPAR = packB (parL P zb)`).

Paper quantity of the main types: the block's parity bits `parB P zb t` (the syndrome's bits, P3:1204-1206). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo

/-- The parity accumulator after the first `N` data bits. -/
def accV (P : StarParams) (zb : ℕ → Bool) (t N : ℕ) : Bool := xr (fun m => zb m && (dpos P m + 1).testBit t) N

/-- A block's parity bits, `t < s`. -/
def parL (P : StarParams) (zb : ℕ → Bool) : List Bool := (List.range P.s).map (parB P zb)

section Pass1
variable (cap : ℕ)

/-- The accumulator toggled when the read bit and the tracked bit are both `1`. -/
def ctog : CM := .ifr rgZ (.ifr rgF (togR rgACC) .skip) .skip

theorem ctog_spec (τ : CS) (z f a : Bool) (hz : τ.val rgZ = z.toNat) (hf : τ.val rgF = f.toNat)
    (ha : τ.val rgACC = a.toNat) (hc : 1 ≤ cap) :
    ∃ τ', WExec cap ctog τ τ' 8 ∧ τ'.val rgACC = (xor a (z && f)).toNat ∧ (∀ r, r ≠ rgACC → τ'.val r = τ.val r) ∧
      τ'.st = τ.st ∧ τ'.sh = τ.sh ∧ τ'.cell = τ.cell := by
  cases z
  · exact ⟨τ, WExec.mono (WExec.ifrF (by simpa using hz) (WExec.skip τ)) (by omega), by simp [ha],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  · cases f
    · exact ⟨τ, WExec.mono (WExec.ifrT (by simp [hz]) (WExec.ifrF (by simpa using hf) (WExec.skip τ))) (by omega),
        by simp [ha], fun _ _ => rfl, rfl, rfl, rfl⟩
    · have e := togR_spec cap rgACC τ (by rw [ha]; exact Bool.toNat_le a) hc
      refine ⟨_, WExec.mono (WExec.ifrT (by simp [hz]) (WExec.ifrT (by simp [hf]) e)) (by omega), ?_,
        fun r hr => by simp [Function.update_apply, hr], rfl, rfl, rfl⟩
      simp [ha]
      cases a <;> rfl

/-- One position of the scan: a data bit read and accumulated, or a parity position skipped. -/
def p1Mid (R : Fin 4) : CM := .ifr rgE (.seq (readB R rgRWC) (.seq ctog (WM.clear rgZ))) .skip

theorem p1Mid_spec (P : StarParams) (zb : ℕ → Bool) (t : ℕ) (R : Fin 4) (σ0 : CS) (b0 : ℕ)
    (hzb : ∀ m < dB P, readTapeBit (σ0.st R) (b0 + 2 * m + 1) = zb m) (q : ℕ) (hq : q < P.b) (τ : CS)
    (hP : PowT q (τ.val rgNP) (τ.val rgE)) (hB : BitT t (q + 1) (τ.val rgCD) (τ.val rgF))
    (hA : τ.val rgACC = (accV P zb t (nd P q)).toNat) (hZ : τ.val rgZ = 0) (hW : τ.val rgRWC = 2 * nd P q)
    (hR : τ.sh R = b0 + 2 * nd P q) (hst : τ.st = σ0.st) (hcap : 2 * P.b + 4 ≤ cap) :
    ∃ τ', WExec cap (p1Mid R) τ τ' 60 ∧ τ'.val rgACC = (accV P zb t (nd P (q + 1))).toNat ∧ τ'.val rgZ = 0 ∧
      τ'.val rgRWC = 2 * nd P (q + 1) ∧ τ'.sh R = b0 + 2 * nd P (q + 1) ∧ τ'.st = τ.st ∧
      (∀ i, i ≠ R → τ'.sh i = τ.sh i) ∧ (∀ r, r ≠ rgACC → r ≠ rgZ → r ≠ rgRWC → τ'.val r = τ.val r) ∧
      τ'.cell = τ.cell := by
  by_cases hE : τ.val rgE = 0
  · have hp : isPar P q = true := (powT_par P hq hP).2 hE
    have hn : nd P (q + 1) = nd P q := by rw [nd_succ, if_pos hp]; rfl
    refine ⟨τ, WExec.mono (WExec.ifrF hE (WExec.skip τ)) (by omega), ?_, hZ, ?_, ?_, rfl, fun _ _ => rfl,
      fun _ _ _ _ => rfl, rfl⟩
    · rw [hn, hA]
    · rw [hn, hW]
    · rw [hn, hR]
  · have hd : isPar P q = false := by
      cases h : isPar P q
      · rfl
      · exact absurd ((powT_par P hq hP).1 h) hE
    have hn : nd P (q + 1) = nd P q + 1 := by rw [nd_succ, if_neg (by simp [hd])]
    have hlt : nd P q < dB P := by
      have h1 := nd_mono P (show q + 1 ≤ P.b by omega)
      rw [hn, nd_b] at h1
      omega
    have hdb : dB P ≤ P.b := by unfold dB; omega
    obtain ⟨τ1, e1, a1, z1, w1, s1, o1, v1, c1⟩ := readB_spec cap R rgRWC (by decide) τ hZ (by omega) (by omega)
    have hbit : readTapeBit (τ.st R) (τ.sh R + 1) = zb (nd P q) := by
      rw [hst, hR]
      exact hzb _ hlt
    rw [hbit] at z1
    obtain ⟨τ2, e2, a2, v2, s2, h2, c2⟩ := ctog_spec cap τ1 (zb (nd P q)) ((q + 1).testBit t)
      (accV P zb t (nd P q)) z1 (by rw [v1 rgF (by decide) (by decide), hB.1]) (by rw [v1 rgACC (by decide) (by decide), hA])
      (by omega)
    have e3 := wclear_spec cap rgZ (τ2.val rgZ) τ2 rfl (by rw [v2 rgZ (by decide), z1]; have := Bool.toNat_le (zb (nd P q)); omega)
    have hacc : accV P zb t (nd P (q + 1)) = xor (accV P zb t (nd P q)) (zb (nd P q) && (q + 1).testBit t) := by
      rw [hn]
      simp only [accV, xr]
      rw [dpos_nd P q hq hd]
    have hz2 : τ2.val rgZ ≤ 1 := by rw [v2 rgZ (by decide), z1]; exact Bool.toNat_le _
    refine ⟨_, WExec.mono (WExec.ifrT hE (WExec.seq e1 (WExec.seq e2 e3))) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [a2, hacc]
    · simp
    · simp [v2 rgRWC (by decide), w1, hW, hn]; ring
    · simp [h2, a1, hR, hn]; ring
    · simp [s2, s1]
    · intro i hi
      simp [h2, o1 i hi]
    · intro r r1 r2 r3
      simp [Function.update_apply, r2, v2 r r1, v1 r r2 r3]
    · simp [c2, c1]

/-- One position of the scan with its trackers. -/
def p1Body (R : Fin 4) : CM := .seq (p1Mid R) (.seq powStep bitStep)

/-- The scan's loop over the block's `b` positions. -/
def p1Loop (R : Fin 4) : CM := .whr rgKQ (.seq (.dec rgKQ) (p1Body R))

/-- **The scan's invariant** at position `q`. -/
structure P1I (P : StarParams) (zb : ℕ → Bool) (t : ℕ) (R : Fin 4) (σ0 : CS) (b0 q : ℕ) (τ : CS) : Prop where
  kq : τ.val rgKQ = P.b - q
  pw : PowT q (τ.val rgNP) (τ.val rgE)
  bt : BitT t (q + 1) (τ.val rgCD) (τ.val rgF)
  pwr : τ.val rgPW = 2 ^ t
  acc : τ.val rgACC = (accV P zb t (nd P q)).toNat
  z : τ.val rgZ = 0
  tt : τ.val rgT = 0
  t2 : τ.val rgT2 = 0
  rwc : τ.val rgRWC = 2 * nd P q
  shR : τ.sh R = b0 + 2 * nd P q
  st : τ.st = σ0.st
  sh : ∀ i, i ≠ R → τ.sh i = σ0.sh i
  oth : ∀ r, r ∉ [rgKQ, rgNP, rgE, rgCD, rgF, rgACC, rgZ, rgT, rgT2, rgRWC] → τ.val r = σ0.val r
  cell : τ.cell = σ0.cell

theorem pow_lt_b (P : StarParams) (t : ℕ) (ht : t < P.s) : 2 ^ t ≤ P.b := by
  have h1 : 2 ^ t < 2 ^ P.s := Nat.pow_lt_pow_right (by norm_num) ht
  have h2 := P.b_succ
  omega

theorem p1_step (P : StarParams) (zb : ℕ → Bool) (t : ℕ) (ht : t < P.s) (R : Fin 4) (σ0 : CS) (b0 : ℕ)
    (hzb : ∀ m < dB P, readTapeBit (σ0.st R) (b0 + 2 * m + 1) = zb m) (q : ℕ) (hq : q < P.b) (τ : CS)
    (hI : P1I P zb t R σ0 b0 q τ) (hcap : 8 * (P.b + 2) ≤ cap) :
    ∃ τ', WExec cap (.seq (.dec rgKQ) (p1Body R)) τ τ' (200 * (P.b + 2)) ∧ P1I P zb t R σ0 b0 (q + 1) τ' := by
  have hpt := pow_lt_b P t ht
  have e0 := WExec.dec (cap := cap) rgKQ τ (by rw [hI.kq]; omega)
  set τ0 := τ.setv rgKQ (τ.val rgKQ - 1) with hτ0
  have g : ∀ r, r ≠ rgKQ → τ0.val r = τ.val r := fun r hr => by simp [hτ0, Function.update_apply, hr]
  obtain ⟨τ1, e1, a1, z1, w1, r1, s1, o1, v1, c1⟩ := p1Mid_spec cap P zb t R σ0 b0 hzb q hq τ0
    (by rw [g rgNP (by decide), g rgE (by decide)]; exact hI.pw)
    (by rw [g rgCD (by decide), g rgF (by decide)]; exact hI.bt)
    (by rw [g rgACC (by decide)]; exact hI.acc) (by rw [g rgZ (by decide)]; exact hI.z)
    (by rw [g rgRWC (by decide)]; exact hI.rwc) (by simpa [hτ0] using hI.shR) (by simpa [hτ0] using hI.st) (by omega)
  obtain ⟨τ2, e2, p2, t2, u2, s2, h2, v2, c2⟩ := powStep_spec cap τ1 q
    (by rw [v1 rgNP (by decide) (by decide) (by decide), v1 rgE (by decide) (by decide) (by decide),
      g rgNP (by decide), g rgE (by decide)]; exact hI.pw)
    (by rw [v1 rgT (by decide) (by decide) (by decide), g rgT (by decide)]; exact hI.tt)
    (by rw [v1 rgT2 (by decide) (by decide) (by decide), g rgT2 (by decide)]; exact hI.t2) (by omega)
  obtain ⟨τ3, e3, b3, t3, s3, h3, v3, c3⟩ := bitStep_spec cap τ2 t (q + 1)
    (by rw [v2 rgCD (by decide) (by decide), v2 rgF (by decide) (by decide), v1 rgCD (by decide) (by decide) (by decide),
      v1 rgF (by decide) (by decide) (by decide), g rgCD (by decide), g rgF (by decide)]; exact hI.bt)
    (by rw [v2 rgPW (by decide) (by decide), v1 rgPW (by decide) (by decide) (by decide), g rgPW (by decide)]; exact hI.pwr)
    t2 (by omega)
  refine ⟨τ3, WExec.mono (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3))) (by omega), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, t3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v3 rgKQ (by decide) (by decide), v2 rgKQ (by decide) (by decide), v1 rgKQ (by decide) (by decide) (by decide)]
    simp [hτ0, hI.kq]
    omega
  · rw [v3 rgNP (by decide) (by decide), v3 rgE (by decide) (by decide)]; exact p2
  · exact b3
  · rw [v3 rgPW (by decide) (by decide), v2 rgPW (by decide) (by decide), v1 rgPW (by decide) (by decide) (by decide),
      g rgPW (by decide)]; exact hI.pwr
  · rw [v3 rgACC (by decide) (by decide), v2 rgACC (by decide) (by decide)]; exact a1
  · rw [v3 rgZ (by decide) (by decide), v2 rgZ (by decide) (by decide)]; exact z1
  · rw [v3 rgT2 (by decide) (by decide)]; exact u2
  · rw [v3 rgRWC (by decide) (by decide), v2 rgRWC (by decide) (by decide)]; exact w1
  · rw [h3, h2]; exact r1
  · rw [s3, s2, s1]; simpa [hτ0] using hI.st
  · intro i hi
    rw [h3, h2, o1 i hi]; simpa [hτ0] using hI.sh i hi
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hr
    rw [v3 r n4 n5, v2 r n2 n3, v1 r n6 n7 n10, g r n1]
    exact hI.oth r (by simp [n1, n2, n3, n4, n5, n6, n7, n8, n9, n10])
  · rw [c3, c2, c1]; simpa [hτ0] using hI.cell

theorem p1Loop_spec (P : StarParams) (zb : ℕ → Bool) (t : ℕ) (ht : t < P.s) (R : Fin 4) (σ0 : CS) (b0 : ℕ)
    (hzb : ∀ m < dB P, readTapeBit (σ0.st R) (b0 + 2 * m + 1) = zb m) (hcap : 8 * (P.b + 2) ≤ cap) :
    ∀ (m q : ℕ) (τ : CS), q + m = P.b → P1I P zb t R σ0 b0 q τ →
      ∃ τ', WExec cap (p1Loop R) τ τ' (m * (200 * (P.b + 2) + 2) + 1) ∧ P1I P zb t R σ0 b0 P.b τ' := by
  intro m
  induction m with
  | zero =>
    intro q τ hqm hI
    have hq : q = P.b := by omega
    subst hq
    exact ⟨τ, WExec.mono (WExec.whrF (by rw [hI.kq]; omega)) (by omega), hI⟩
  | succ m ih =>
    intro q τ hqm hI
    obtain ⟨τ1, e1, h1⟩ := p1_step cap P zb t ht R σ0 b0 hzb q (by omega) τ hI hcap
    obtain ⟨τ2, e2, h2⟩ := ih (q + 1) τ1 (by omega) h1
    exact ⟨τ2, WExec.mono (WExec.whrT (by rw [hI.kq]; omega) e1 e2) (by ring_nf; omega), h2⟩

end Pass1

end NearCubicWires.WireExponent3_5.PrimT.Ctr
