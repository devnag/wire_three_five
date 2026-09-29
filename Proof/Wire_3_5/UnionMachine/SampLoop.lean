import Proof.Wire_3_5.UnionMachine.SampSeed
import Proof.Wire_3_5.FinalPass.HashTable
import Proof.Wire_3_5.FinalPass.LiftR

/-! # C6 tail, item 2 (part 4): one sample's value, its pair words and the next label

On the sample expansion's streams (`SampSeed`), one sample `j` is:
* **`horn_spec`**: C5's Horner program `hornerW` (`FinalPass.Hash4`, the machine field's shift-and-XOR product) lifted
  to the streams by `fs` (`WExec.liftW`): `ACC := Σ a_i j^i`, the generator's value at the label `j`;
* **`out_spec`**: the pair words of the value on the output: its bits `[kh, 2kh)` framed, then its bits `[0, kh)` framed
  (`SampMath.pairW`), read from `ACC` along the ruler `1^{kh}`;
* **`inc_spec`**: C5's label increment `incX`, lifted: `X := frame (binary ℓ (j + 1))`.

Paper quantity of the main types: the sample's printed position `pairW ℓ kh (Σ a_i j^i)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SampLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (Same emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.TailAsm (Cp Cp.tr cp_emit rbW fp_app fp_cons fpl)
open NearCubicWires.WireExponent3_5.UnionMachine.SampKit
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (seedWord hornerW incX HReady hornerCost hornerStep)

variable (cap : ℕ)

/-! ## Horner's streams inside the expansion's streams -/

/-- Horner's streams `O, WIN, SEED, P, X, ACC, NEW, ST` as the expansion's `5, 0, 6, 4, 7, 8, 9, 10`. -/
def fs : Fin 8 → Fin 11 := ![5, 0, 6, 4, 7, 8, 9, 10]

theorem fs_inj : Function.Injective fs := by decide

/-- Horner's view of the expansion's state. -/
def proj (ω : WState 10 16) : WState 7 16 := ⟨fun i => ω.sh (fs i), fun i => ω.st (fs i), ω.val, ω.cell⟩

theorem lift_proj (ω : WState 10 16) : LiftW fs id ω (proj ω) := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

theorem proj_of_lift {ω : WState 10 16} {τ : WState 7 16} (h : LiftW fs id ω τ) : proj ω = τ :=
  WState.eq (funext h.sh) (funext h.st) (funext h.val) h.cell

theorem lift_same {ω ω' : WState 10 16} {τ : WState 7 16} (hL : LiftW fs id ω' τ) (hO : OutsideW fs id ω ω')
    (j : Fin 11) (hj : ∀ i, fs i = j → τ.st i = (proj ω).st i ∧ τ.sh i = (proj ω).sh i) :
    ω'.st j = ω.st j ∧ ω'.sh j = ω.sh j := by
  by_cases h : ∃ i, fs i = j
  · obtain ⟨i, rfl⟩ := h
    obtain ⟨h1, h2⟩ := hj i rfl
    exact ⟨(hL.st i).trans h1, (hL.sh i).trans h2⟩
  · obtain ⟨e1, e2⟩ := hO.1 j (fun i hi => h ⟨i, hi⟩)
    exact ⟨e2, e1⟩

/-- Horner's rule on the expansion's streams. -/
def hornL : WM 10 16 := hornerW.liftW fs id

/-- The label increment on the expansion's streams. -/
def incL : WM 10 16 := incX.liftW fs id

/-- **The value at the label**: `ACC := Σ a_i x^i`; the records, `NEW`, `ST` rewritten, all else kept. -/
theorem horn_spec (p ℓ x : ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ) (hcap : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap)
    (ω : WState 10 16) (hR : HReady p ℓ x all (proj ω)) :
    ∃ ω', WExec cap hornL ω ω' (hornerCost ℓ all.length) ∧ HReady p ℓ x all (proj ω') ∧
      ω'.st 8 = frame (binary ℓ (all.foldl (hornerStep p ℓ x) 0)) ∧
      (∀ j : Fin 11, j ≠ 6 → j ≠ 8 → j ≠ 9 → j ≠ 10 → ω'.st j = ω.st j ∧ ω'.sh j = ω.sh j) ∧
      (∀ r, ω'.val r = ω.val r) ∧ ω'.cell = ω.cell := by
  obtain ⟨τ, h, hR', hA, hF⟩ := FinalPass.Hash4.hornerW_spec cap p ℓ x all hℓ hcap (proj ω) hR
  obtain ⟨ω', e, hL, hO⟩ := WExec.liftW cap cap le_rfl fs fs_inj id Function.injective_id h ω (lift_proj ω)
  have hp : proj ω' = τ := proj_of_lift hL
  obtain ⟨-, -, a3, -, -, -, -, -, -, -, -, -, -, a14, a15, a16, a17⟩ := id hR'
  obtain ⟨-, -, b3, -, -, -, -, -, -, -, -, -, -, b14, b15, b16, b17⟩ := hR
  refine ⟨ω', e, by rw [hp]; exact hR', (hL.st 5).trans hA, fun j h6 h8 h9 h10 => lift_same hL hO j ?_, fun r => ?_,
    hL.cell.trans hF.2.2⟩
  · intro i hi
    refine hF.1 i ?_
    intro hs
    unfold FinalPass.Hash4.hornS at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact h6 (hi.symm.trans rfl)
    · exact h8 (hi.symm.trans rfl)
    · exact h9 (hi.symm.trans rfl)
    · exact h10 (hi.symm.trans rfl)
  · refine (hL.val r).trans ?_
    by_cases hr : FinalPass.Hash4.hornR r
    · unfold FinalPass.Hash4.hornR at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact a3.trans b3.symm
      · exact a14.trans b14.symm
      · exact a15.trans b15.symm
      · exact a16.trans b16.symm
      · exact a17.trans b17.symm
    · exact hF.2.1 r hr

/-- **The next label**: `X := frame (binary ℓ (i + 1))`, all else kept. -/
theorem inc_spec (p ℓ i : ℕ) (hc1 : 1 ≤ cap) (hl : 2 * ℓ ≤ cap) (ω : WState 10 16)
    (hX : ω.st 7 = frame (binary ℓ i)) (hhX : ω.sh 7 = 0) (hP : ω.st 4 = frame (binary ℓ p)) (hhP : ω.sh 4 = 0)
    (hF : ω.val 4 = 0) (hR : ω.val 6 = 0) :
    ∃ ω', WExec cap incL ω ω' (ℓ * 41 + 15) ∧ ω'.st 7 = frame (binary ℓ (i + 1)) ∧ ω'.sh 7 = ω.sh 7 ∧
      (∀ j : Fin 11, j ≠ 7 → ω'.st j = ω.st j ∧ ω'.sh j = ω.sh j) ∧ (∀ r, ω'.val r = ω.val r) ∧
      ω'.cell = ω.cell := by
  have h := FinalPass.Hash4.incX_spec cap ℓ p i (proj ω) hc1 hl hX hhX hP hhP hF hR
  obtain ⟨ω', e, hL, hO⟩ := WExec.liftW cap cap le_rfl fs fs_inj id Function.injective_id h ω (lift_proj ω)
  refine ⟨ω', e, (hL.st 4).trans (by simp), hL.sh 4, fun j hj => lift_same hL hO j ?_, fun r => hL.val r, hL.cell⟩
  intro k hk
  have hk4 : k ≠ 4 := by
    rintro rfl
    exact hj (hk.symm.trans rfl)
  exact ⟨by simp [Function.update_of_ne hk4], rfl⟩

/-! ## The pair words of a value -/

/-- The pair words of `ACC`'s value on the output: bits `[kh, 2kh)`, then `[0, kh)`; `ACC`'s head back at `0`. -/
def outW : WM 10 16 :=
  .seq (rulerW 1 0 (.seq (.fwd 8) (.fwd 8))) (.seq (rulerW 1 0 (.seq (rbW 8 5) (rbW 8 5))) (.seq (emitW 5 false)
    (.seq (rulerW 1 0 (.seq (.bwd 8) (.bwd 8))) (.seq (rulerW 1 0 (.seq (.bwd 8) (.bwd 8)))
    (.seq (rulerW 1 0 (.seq (rbW 8 5) (rbW 8 5))) (.seq (emitW 5 false) (rulerW 1 0 (.seq (.bwd 8) (.bwd 8)))))))))

def outCost (kh : ℕ) : ℕ :=
  kh * 16 + 3 + 1 + (kh * 26 + 3 + 1 + (3 + 1 + (kh * 16 + 3 + 1 + (kh * 16 + 3 + 1 + (kh * 26 + 3 + 1 +
    (3 + 1 + (kh * 16 + 3)))))))

theorem frame_of_cp {X D : Fin 11} {σ τ : WState 10 16} {u v : List Bool} (h : Cp X D σ τ u v) :
    WFrame (fun i => i = D ∨ i = X) (fun _ => False) σ τ :=
  ⟨fun i hi => h.same i (fun e => hi (Or.inr e)) (fun e => hi (Or.inl e)), fun r _ => by rw [h.val], h.cell⟩

/-- **The pair words**: the output gains `pairW ℓ kh v`; `ACC` kept, its head back at `0`; all else kept. -/
theorem out_spec (ℓ kh v : ℕ) (hk : 2 * kh ≤ ℓ) (hkc : kh ≤ cap) (ω : WState 10 16)
    (hA : ω.st 8 = frame (binary ℓ v)) (hhA : ω.sh 8 = 0) (hO : ω.sh 5 = (ω.st 5).length)
    (hK : ω.st 1 = List.replicate kh true) (hhK : ω.sh 1 = 0) (hc : ω.val 0 = 0) :
    ∃ τ, WExec cap outW ω τ (outCost kh) ∧ τ.st 5 = ω.st 5 ++ SampMath.pairW ℓ kh v ∧
      τ.sh 5 = (τ.st 5).length ∧ τ.st 8 = ω.st 8 ∧ τ.sh 8 = 0 ∧
      WFrame (fun i => i = 5 ∨ i = 8) (fun _ => False) ω τ := by
  have hbl : (binary ℓ v).length = ℓ := binary_length ℓ v
  have hl0 : ((binary ℓ v).take kh).length = kh := by rw [List.length_take, hbl]; omega
  have hl1 : (((binary ℓ v).drop kh).take kh).length = kh := by
    rw [List.length_take, List.length_drop, hbl]; omega
  have hsplit : binary ℓ v =
      (binary ℓ v).take kh ++ (((binary ℓ v).drop kh).take kh ++ ((binary ℓ v).drop kh).drop kh) := by
    rw [List.take_append_drop, List.take_append_drop]
  have hA' : ω.st 8 = frameP ((binary ℓ v).take kh) ++ (frameP (((binary ℓ v).drop kh).take kh) ++
      (frameP (((binary ℓ v).drop kh).drop kh) ++ [false])) := by
    rw [hA, frame_eq_frameP]; conv_lhs => rw [hsplit]
    simp only [fp_app, List.append_assoc]
  have s1 := skipP_spec cap 1 8 0 (by decide) kh hkc ω hK hhK hc
  obtain ⟨ω2, s2, c2⟩ := copyP_spec cap 1 8 5 0 (by decide) (by decide) (by decide) (((binary ℓ v).drop kh).take kh)
    (frameP ((binary ℓ v).take kh)) (frameP (((binary ℓ v).drop kh).drop kh) ++ [false]) (by rw [hl1]; exact hkc)
    (ω.seth 8 (ω.sh 8 + 2 * kh)) (by simpa using hA') (by simp only [WState.seth_sh, Function.update_self, hhA, fpl, hl0]; omega)
    (by simpa using hO) (by rw [hl1]; simpa using hK) (by simpa using hhK) (by simpa using hc)
  obtain ⟨ω3, s3, c3⟩ := cp_emit cap 8 5 (by decide) false ω2 c2.endO
  have c23 := c2.tr c3 rfl rfl
  have hK3 : ω3.st 1 = List.replicate kh true := by
    rw [(c23.same 1 (by decide) (by decide)).1]; simpa using hK
  have hhK3 : ω3.sh 1 = 0 := by rw [(c23.same 1 (by decide) (by decide)).2]; simpa using hhK
  have hc3 : ω3.val 0 = 0 := by rw [c23.val]; simpa using hc
  have hh3 : ω3.sh 8 = 4 * kh := by
    rw [c23.sh]; simp only [WState.seth_sh, Function.update_self, hhA, List.append_nil, fpl, hl1]; omega
  have s4 := backP_spec cap 1 8 0 (by decide) kh hkc ω3 hK3 hhK3 hc3
  have s5 := backP_spec cap 1 8 0 (by decide) kh hkc (ω3.seth 8 (ω3.sh 8 - 2 * kh)) (by simpa using hK3)
    (by simpa using hhK3) (by simpa using hc3)
  have hω5 : (ω3.seth 8 (ω3.sh 8 - 2 * kh)).seth 8 ((ω3.seth 8 (ω3.sh 8 - 2 * kh)).sh 8 - 2 * kh) =
      ω3.seth 8 0 := by
    rw [wseth_seth]; congr 1; simp only [WState.seth_sh, Function.update_self, hh3]; omega
  rw [hω5] at s5
  obtain ⟨ω6, s6, c6⟩ := copyP_spec cap 1 8 5 0 (by decide) (by decide) (by decide) ((binary ℓ v).take kh) []
    (frameP (((binary ℓ v).drop kh).take kh) ++ (frameP (((binary ℓ v).drop kh).drop kh) ++ [false]))
    (by rw [hl0]; exact hkc) (ω3.seth 8 0)
    (by simp only [WState.seth_st]; rw [c23.st]; simp only [WState.seth_st]; rw [hA']; simp) (by simp)
    (by simpa using c23.endO) (by rw [hl0]; simpa using hK3) (by simpa using hhK3) (by simpa using hc3)
  obtain ⟨ω7, s7, c7⟩ := cp_emit cap 8 5 (by decide) false ω6 c6.endO
  have c67 := c6.tr c7 rfl rfl
  have hK7 : ω7.st 1 = List.replicate kh true := by
    rw [(c67.same 1 (by decide) (by decide)).1]; simpa using hK3
  have hhK7 : ω7.sh 1 = 0 := by rw [(c67.same 1 (by decide) (by decide)).2]; simpa using hhK3
  have hc7 : ω7.val 0 = 0 := by rw [c67.val]; simpa using hc3
  have hh7 : ω7.sh 8 = 2 * kh := by
    rw [c67.sh]; simp only [WState.seth_sh, Function.update_self, List.append_nil, fpl, hl0]; omega
  have s8 := backP_spec cap 1 8 0 (by decide) kh hkc ω7 hK7 hhK7 hc7
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8))))))) (by rw [hl0, hl1]; unfold outCost; omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; rw [c67.out]; simp only [WState.seth_st]; rw [c23.out]
    simp only [WState.seth_st]; unfold SampMath.pairW; rw [frame_eq_frameP, frame_eq_frameP]; simp
  · simp only [WState.seth_sh, WState.seth_st, Function.update_of_ne (show (5 : Fin 11) ≠ 8 by decide)]
    exact c67.endO
  · simp only [WState.seth_st]; rw [c67.st]; simp only [WState.seth_st]; rw [c23.st]; rfl
  · simp only [WState.seth_sh, Function.update_self, hh7]; omega
  · exact (frame_seth _ _ ω 8 _ (Or.inr rfl)).trans ((frame_of_cp c23).trans ((frame_seth _ _ ω3 8 0 (Or.inr rfl)).trans
      ((frame_of_cp c67).trans (frame_seth _ _ ω7 8 _ (Or.inr rfl)))))

/-! ## The samples -/

theorem allC_length (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) : (SampMath.allC P s).length = 8 := by
  simp [SampMath.allC, FinalPass.Hash4.coefsRev]

/-- The state before sample `j`: the output holds the first `j` pair words, the label is `j`, Horner is ready. -/
structure LInv (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (j : ℕ) (ω : WState 10 16) : Prop where
  qs : ω.st 2 = List.replicate P.Q true
  hq : ω.sh 2 = j
  out : ω.st 5 = (List.range j).flatMap fun i => SampMath.pairW P.ell P.kh (SampMath.hv P s i)
  ho : ω.sh 5 = (ω.st 5).length
  seed : ω.st 6 = seedWord P.ell (SampMath.allC P s)
  hs : ω.sh 6 = 0
  acc : ∃ v, ω.st 8 = frame (binary P.ell v)
  ha : ω.sh 8 = 0
  nw : ∃ v, ω.st 9 = frame (binary P.ell v)
  hn : ω.sh 9 = 0
  stw : ∃ v, ω.st 10 = frame (binary P.ell v)
  ht : ω.sh 10 = 0
  x : ω.st 7 = frame (binary P.ell j)
  hx : ω.sh 7 = 0
  md : ω.st 4 = frame (binary P.ell P.modulus)
  hm : ω.sh 4 = 0
  kk : ω.st 1 = List.replicate P.kh true
  hk : ω.sh 1 = 0
  regs : ∀ r, ω.val r = 0

theorem hready_of {P : Sampler.SeedParams} {s : Fin (8 * P.ell) → Bool} {j : ℕ} {ω : WState 10 16}
    (h : LInv P s j ω) : HReady P.modulus P.ell j (SampMath.allC P s) (proj ω) :=
  ⟨h.seed, h.hs, h.regs _, h.acc, h.ha, h.nw, h.hn, h.stw, h.ht, h.x, h.hx, h.md, h.hm, h.regs _, h.regs _, h.regs _,
    h.regs _⟩

/-- One sample: the value, its pair words, the next label. -/
def sampW : WM 10 16 := .seq hornL (.seq outW incL)

def stepCost (ℓ kh : ℕ) : ℕ := hornerCost ℓ 8 + 1 + (outCost kh + 1 + (ℓ * 41 + 15))

theorem step_spec (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hcap : 18 * P.ell + 20 ≤ cap) (j : ℕ)
    (ω : WState 10 16) (h : LInv P s j ω) :
    ∃ ω', WExec cap sampW ω ω' (stepCost P.ell P.kh) ∧ LInv P s (j + 1) (ω'.seth 2 (j + 1)) ∧ ω'.sh 2 = j := by
  have hℓ : 1 ≤ P.ell := P.one_le_ell
  have hk := P.k_le
  have hcapH : (seedWord P.ell (SampMath.allC P s)).length + 2 * P.ell + 2 ≤ cap := by
    rw [FinalPass.Hash4.seedWord_length, allC_length]; omega
  obtain ⟨ω1, s1, hR1, hA1, same1, val1, cell1⟩ :=
    horn_spec cap P.modulus P.ell j (SampMath.allC P s) hℓ hcapH ω (hready_of h)
  obtain ⟨e6, eh6, -, -, eh8, enw, ehnw, est, ehst, ex, ehx, ep, ehp, -, -, -, -⟩ := hR1
  have e6' : ω1.st 6 = seedWord P.ell (SampMath.allC P s) := e6
  have eh6' : ω1.sh 6 = 0 := eh6
  have eh8' : ω1.sh 8 = 0 := eh8
  have enw' : ∃ v, ω1.st 9 = frame (binary P.ell v) := enw
  have ehnw' : ω1.sh 9 = 0 := ehnw
  have est' : ∃ v, ω1.st 10 = frame (binary P.ell v) := est
  have ehst' : ω1.sh 10 = 0 := ehst
  have ex' : ω1.st 7 = frame (binary P.ell j) := ex
  have ehx' : ω1.sh 7 = 0 := ehx
  have ep' : ω1.st 4 = frame (binary P.ell P.modulus) := ep
  have ehp' : ω1.sh 4 = 0 := ehp
  have s15 := same1 5 (by decide) (by decide) (by decide) (by decide)
  have s11 := same1 1 (by decide) (by decide) (by decide) (by decide)
  have s12 := same1 2 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ω2, s2, o5, oh5, o8, oh8, f2⟩ := out_spec cap P.ell P.kh (SampMath.hv P s j) hk (by omega) ω1 hA1 eh8'
    (by rw [s15.1, s15.2]; exact h.ho) (by rw [s11.1]; exact h.kk) (by rw [s11.2]; exact h.hk)
    (by rw [val1]; exact h.regs 0)
  have g : ∀ i : Fin 11, i ≠ 5 → i ≠ 8 → ω2.st i = ω1.st i ∧ ω2.sh i = ω1.sh i :=
    fun i h5 h8 => f2.1 i (fun hi => hi.elim h5 h8)
  have gv : ∀ r, ω2.val r = ω1.val r := fun r => f2.2.1 r (fun hr => hr)
  obtain ⟨ω3, s3, x3, xh3, same3, val3, cell3⟩ := inc_spec cap P.modulus P.ell j (by omega) (by omega) ω2
    (by rw [(g 7 (by decide) (by decide)).1]; exact ex') (by rw [(g 7 (by decide) (by decide)).2]; exact ehx')
    (by rw [(g 4 (by decide) (by decide)).1]; exact ep') (by rw [(g 4 (by decide) (by decide)).2]; exact ehp')
    (by rw [gv, val1]; exact h.regs 4) (by rw [gv, val1]; exact h.regs 6)
  have k : ∀ i : Fin 11, i ≠ 5 → i ≠ 7 → i ≠ 8 → ω3.st i = ω1.st i ∧ ω3.sh i = ω1.sh i := fun i h5 h7 h8 =>
    ⟨((same3 i h7).1).trans (g i h5 h8).1, ((same3 i h7).2).trans (g i h5 h8).2⟩
  have kv : ∀ r, ω3.val r = 0 := fun r => by rw [val3, gv, val1]; exact h.regs r
  refine ⟨ω3, WExec.seq s1 (WExec.seq s2 s3), ?_, ?_⟩
  · refine ⟨?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r => kv r⟩
    · simp only [WState.seth_st]; rw [(k 2 (by decide) (by decide) (by decide)).1, s12.1]; exact h.qs
    · simp only [WState.seth_st]
      rw [(same3 5 (by decide)).1, o5, s15.1, h.out, List.range_succ, List.flatMap_append]; simp
    · simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne (show (5 : Fin 11) ≠ 2 by decide)]
      rw [(same3 5 (by decide)).1, (same3 5 (by decide)).2]; exact oh5
    · simp only [WState.seth_st]; rw [(k 6 (by decide) (by decide) (by decide)).1]; exact e6'
    · simp only [WState.seth_sh, Function.update_of_ne (show (6 : Fin 11) ≠ 2 by decide)]
      rw [(k 6 (by decide) (by decide) (by decide)).2]; exact eh6'
    · simp only [WState.seth_st]; rw [(same3 8 (by decide)).1, o8]; exact ⟨_, hA1⟩
    · simp only [WState.seth_sh, Function.update_of_ne (show (8 : Fin 11) ≠ 2 by decide)]
      rw [(same3 8 (by decide)).2]; exact oh8
    · simp only [WState.seth_st]; rw [(k 9 (by decide) (by decide) (by decide)).1]; exact enw'
    · simp only [WState.seth_sh, Function.update_of_ne (show (9 : Fin 11) ≠ 2 by decide)]
      rw [(k 9 (by decide) (by decide) (by decide)).2]; exact ehnw'
    · simp only [WState.seth_st]; rw [(k 10 (by decide) (by decide) (by decide)).1]; exact est'
    · simp only [WState.seth_sh, Function.update_of_ne (show (10 : Fin 11) ≠ 2 by decide)]
      rw [(k 10 (by decide) (by decide) (by decide)).2]; exact ehst'
    · simp only [WState.seth_st]; exact x3
    · simp only [WState.seth_sh, Function.update_of_ne (show (7 : Fin 11) ≠ 2 by decide)]
      rw [xh3, (g 7 (by decide) (by decide)).2]; exact ehx'
    · simp only [WState.seth_st]; rw [(k 4 (by decide) (by decide) (by decide)).1]; exact ep'
    · simp only [WState.seth_sh, Function.update_of_ne (show (4 : Fin 11) ≠ 2 by decide)]
      rw [(k 4 (by decide) (by decide) (by decide)).2]; exact ehp'
    · simp only [WState.seth_st]; rw [(k 1 (by decide) (by decide) (by decide)).1, s11.1]; exact h.kk
    · simp only [WState.seth_sh, Function.update_of_ne (show (1 : Fin 11) ≠ 2 by decide)]
      rw [(k 1 (by decide) (by decide) (by decide)).2, s11.2]; exact h.hk
  · rw [(k 2 (by decide) (by decide) (by decide)).2, s12.2]; exact h.hq

/-- All samples: one per cell of the ruler `1^Q`. -/
def loopW : WM 10 16 := .whs 2 (.seq sampW (.fwd 2))

theorem loop_spec (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hcap : 18 * P.ell + 20 ≤ cap) :
    ∀ (m j : ℕ) (ω : WState 10 16), j + m = P.Q → LInv P s j ω →
      ∃ τ, WExec cap loopW ω τ (m * (stepCost P.ell P.kh + 4) + 1) ∧ LInv P s P.Q τ
  | 0, j, ω, hj, h => by
    have hz : wbit ω 2 = false := by
      unfold wbit; rw [h.qs, h.hq, show j = P.Q by omega]; exact rd_rep_end P.Q
    exact ⟨ω, WExec.mono (WExec.whsF hz) (by omega), by rw [show P.Q = j by omega]; exact h⟩
  | m + 1, j, ω, hj, h => by
    have hw : wbit ω 2 = true := by
      unfold wbit; rw [h.qs, h.hq]; exact rd_rep P.Q j (by omega)
    obtain ⟨ω', s1, h', e2⟩ := step_spec cap P s hcap j ω h
    have s2 := WExec.fwd (cap := cap) 2 ω'
    rw [e2] at s2
    obtain ⟨τ, s3, hτ⟩ := loop_spec P s hcap m (j + 1) (ω'.seth 2 (j + 1)) (by omega) h'
    exact ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) (by rw [Nat.add_mul, Nat.one_mul]; omega), hτ⟩

end NearCubicWires.WireExponent3_5.UnionMachine.SampLoop
