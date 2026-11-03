import Lean
import Proof.Wire_3_5.Foundations.OutMachineJoin
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineJoinWBase


noncomputable section
set_option maxRecDepth 4096


/-! # Writer combinators, part 2: `join`, `reindex`, `congrWs`, `sub`

* the joint layout of two writers `W`, `W'`: streams `e1` (`W`'s), `e2` (`W'`'s), `W'`'s input read on `W`'s
  (`f2`); registers `g1`, `g2`; the outputs `sOutJ` (`W`'s, then `W'`'s);
* **`join_run`**: `W` runs on its block, the cell is reset, `W'` runs on its block reading the kept input;
* **`CoreWordsMJ.join`**, **`CoreWordsMJ.reindex`**, **`CoreWordsMJ.congrWs`**, **`CoreWordsMJ.sub`**.

Paper quantity of the main type: the front's words at a request (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Join
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW

section JoinLay
variable {l : Literals} {m m' : ℕ}
  {ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
  {ws' : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m' → List Bool}
  (W : Finish.CoreWordsMJ l m ws) (W' : Finish.CoreWordsMJ l m' ws')

/-- The joint stream count: `W`'s streams, then `W'`'s. -/
def jns : ℕ := W.ns + 1 + W'.ns

/-- The joint register count. -/
def jnr : ℕ := W.nr + W'.nr

def e1 (i : Fin (W.ns + 1)) : Fin (jns W W' + 1) := ⟨i.val, by have := i.isLt; unfold jns; omega⟩

def e2 (j : Fin (W'.ns + 1)) : Fin (jns W W' + 1) := ⟨W.ns + 1 + j.val, by have := j.isLt; unfold jns; omega⟩

/-- `W'`'s streams in the joint layout: its input on `W`'s input. -/
def f2 (j : Fin (W'.ns + 1)) : Fin (jns W W' + 1) := if j = W'.sIn then e1 W W' W.sIn else e2 W W' j

def g1 (q : Fin W.nr) : Fin (jnr W W') := ⟨q.val, by have := q.isLt; unfold jnr; omega⟩

def g2 (q : Fin W'.nr) : Fin (jnr W W') := ⟨W.nr + q.val, by have := q.isLt; unfold jnr; omega⟩

theorem e1_inj : Function.Injective (e1 W W') := fun a b h => by
  have h2 := congrArg Fin.val h
  exact Fin.ext h2

theorem e2_inj : Function.Injective (e2 W W') := fun a b h => by
  have h2 : W.ns + 1 + a.val = W.ns + 1 + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

theorem e1_ne_e2 (i : Fin (W.ns + 1)) (j : Fin (W'.ns + 1)) : e1 W W' i ≠ e2 W W' j := fun h => by
  have h2 : i.val = W.ns + 1 + j.val := congrArg Fin.val h
  have := i.isLt
  omega

theorem f2_in : f2 W W' W'.sIn = e1 W W' W.sIn := if_pos rfl

theorem f2_ne (j : Fin (W'.ns + 1)) (hj : j ≠ W'.sIn) : f2 W W' j = e2 W W' j := if_neg hj

theorem f2_inj : Function.Injective (f2 W W') := by
  intro a b h
  by_cases ha : a = W'.sIn <;> by_cases hb : b = W'.sIn
  · rw [ha, hb]
  · rw [ha, f2_in, f2_ne W W' b hb] at h; exact absurd h (e1_ne_e2 W W' _ _)
  · rw [hb, f2_in, f2_ne W W' a ha] at h; exact absurd h.symm (e1_ne_e2 W W' _ _)
  · rw [f2_ne W W' a ha, f2_ne W W' b hb] at h; exact e2_inj W W' h

theorem g1_inj : Function.Injective (g1 W W') := fun a b h => by
  have h2 := congrArg Fin.val h
  exact Fin.ext h2

theorem g2_inj : Function.Injective (g2 W W') := fun a b h => by
  have h2 : W.nr + a.val = W.nr + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The joint outputs: `W`'s, then `W'`'s. -/
def sOutJ : Fin (m + m') → Fin (jns W W' + 1) :=
  Fin.append (fun k => e1 W W' (W.sOut k)) (fun k => e2 W W' (W'.sOut k))

theorem sOutJ_inj : Function.Injective (sOutJ W W') := by
  intro a b h
  induction a using Fin.addCases with
  | left a1 =>
    induction b using Fin.addCases with
    | left b1 =>
      simp only [sOutJ, Fin.append_left] at h
      rw [W.sOut.injective (e1_inj W W' h)]
    | right b2 =>
      simp only [sOutJ, Fin.append_left, Fin.append_right] at h
      exact absurd h (e1_ne_e2 W W' _ _)
  | right a2 =>
    induction b using Fin.addCases with
    | left b1 =>
      simp only [sOutJ, Fin.append_left, Fin.append_right] at h
      exact absurd h.symm (e1_ne_e2 W W' _ _)
    | right b2 =>
      simp only [sOutJ, Fin.append_right] at h
      rw [W'.sOut.injective (e2_inj W W' h)]

theorem sOutJ_ne (k : Fin (m + m')) : sOutJ W W' k ≠ e1 W W' W.sIn := by
  induction k using Fin.addCases with
  | left k1 =>
    simp only [sOutJ, Fin.append_left]
    exact fun h => W.out_ne k1 (e1_inj W W' h)
  | right k2 =>
    simp only [sOutJ, Fin.append_right]
    exact fun h => e1_ne_e2 W W' _ _ h.symm

/-- The joint machine: `W` on its block ; the cell reset ; `W'` on its block. -/
noncomputable def jMach (F : GateFree l) : (s : ℕ) × Machine (jns W W' + 2 + jnr W W') s :=
  ⟨_, Composition.machine (RecoveryFocus.machine (tmap (e1 W W') (g1 W W')) (W.M F))
    (Composition.machine (WM.setc (ns := jns W W') (nr := jnr W W') false).toProg.compile
      (RecoveryFocus.machine (tmap (f2 W W') (g2 W W')) (W'.M F)))⟩

/-- **The joint run.** -/
theorem join_run (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (σ : WState (jns W W') (jnr W W')) (hin : σ.st (e1 W W' W.sIn) = frame (fpIn l F kclk coef A a ha r))
    (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ e1 W W' W.sIn → σ.st i = []) (hv : ∀ q, σ.val q = 0)
    (hc : σ.cell = false) :
    ∃ (τ : WState (jns W W') (jnr W W')) (n : ℕ),
      n ≤ (W.Cs F + W'.Cs F + 4) *
        ((fpIn l F kclk coef A a ha r).length + 1) ^ (W.Ds F.filterErrDeg + W'.Ds F.filterErrDeg) ∧
      Step (jMach W W' F).2 n
        (wenc ((W.Kc F + W'.Kc F) * ((fpIn l F kclk coef A a ha r).length + 1) ^
          (W.Dk F.filterErrDeg + W'.Dk F.filterErrDeg)) σ).H
        (wenc ((W.Kc F + W'.Kc F) * ((fpIn l F kclk coef A a ha r).length + 1) ^
          (W.Dk F.filterErrDeg + W'.Dk F.filterErrDeg)) σ).A
        (wenc ((W.Kc F + W'.Kc F) * ((fpIn l F kclk coef A a ha r).length + 1) ^
          (W.Dk F.filterErrDeg + W'.Dk F.filterErrDeg)) τ).H
        (wenc ((W.Kc F + W'.Kc F) * ((fpIn l F kclk coef A a ha r).length + 1) ^
          (W.Dk F.filterErrDeg + W'.Dk F.filterErrDeg)) τ).A ∧
      (∀ k, τ.st (sOutJ W W' k) = Fin.append (ws F kclk coef A a ha r) (ws' F kclk coef A a ha r) k) ∧
      τ.st (e1 W W' W.sIn) = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ≠ e1 W W' W.sIn → (∀ k, i ≠ sOutJ W W' k) →
        (τ.st i).length ≤ (W.Cs F + W'.Cs F + 4) *
          ((fpIn l F kclk coef A a ha r).length + 1) ^ (W.Ds F.filterErrDeg + W'.Ds F.filterErrDeg)) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  generalize hN : (fpIn l F kclk coef A a ha r).length = N
  have hK1 : W.Kc F * (N + 1) ^ W.Dk F.filterErrDeg ≤
      (W.Kc F + W'.Kc F) * (N + 1) ^ (W.Dk F.filterErrDeg + W'.Dk F.filterErrDeg) :=
    Nat.mul_le_mul (Nat.le_add_right _ _) (pow_mono_add N _ _)
  have hK2 : W'.Kc F * (N + 1) ^ W'.Dk F.filterErrDeg ≤
      (W.Kc F + W'.Kc F) * (N + 1) ^ (W.Dk F.filterErrDeg + W'.Dk F.filterErrDeg) :=
    Nat.mul_le_mul (Nat.le_add_left _ _) (pow_mono_add' N _ _)
  have hQ : 1 ≤ (N + 1) ^ (W.Ds F.filterErrDeg + W'.Ds F.filterErrDeg) := Nat.one_le_pow _ _ (Nat.succ_pos N)
  generalize hc0 : (W.Kc F + W'.Kc F) * (N + 1) ^ (W.Dk F.filterErrDeg + W'.Dk F.filterErrDeg) = c at hK1 hK2 ⊢
  -- stage 1: `W` on its block
  obtain ⟨τ1, n1, hn1, hs1, ho1, hk1, hr1, hτs1, hτv1⟩ := W.run F kclk coef A a ha r (restrict (e1 W W') (g1 W W') σ)
    hin (fun i => hsh _) (fun i hi => hbl _ (fun h => hi (e1_inj W W' h))) (fun q => hv _) hc
  rw [hN] at hn1 hs1 hr1
  have d1 := embed_run (e1 W W') (g1 W W') (W.M F) (e1_inj W W') (g1_inj W W') c n1 σ τ1 hsh hv hτs1 hτv1
    (stepUp (W.M F) n1 _ c hK1 _ τ1 (fun q => hv _) hτv1 hs1)
  -- stage 2: the cell reset
  have d2 : Step (WM.setc (ns := jns W W') (nr := jnr W W') false).toProg.compile 1
      (wenc c (overlay (e1 W W') (g1 W W') σ τ1)).H (wenc c (overlay (e1 W W') (g1 W W') σ τ1)).A
      (wenc c ((overlay (e1 W W') (g1 W W') σ τ1).setc false)).H
      (wenc c ((overlay (e1 W W') (g1 W W') σ τ1).setc false)).A :=
    Exec.step (WExec.exec c (WExec.setc false _))
  -- the state `W'` starts from
  have h2sh : ∀ i, ((overlay (e1 W W') (g1 W W') σ τ1).setc false).sh i = 0 :=
    overlay_sh0 (es := e1 W W') (er := g1 W W') σ τ1 hsh hτs1
  have h2v : ∀ q, ((overlay (e1 W W') (g1 W W') σ τ1).setc false).val q = 0 :=
    overlay_val0 (es := e1 W W') (er := g1 W W') σ τ1 hv hτv1
  have h2in : ((overlay (e1 W W') (g1 W W') σ τ1).setc false).st (e1 W W' W.sIn) =
      frame (fpIn l F kclk coef A a ha r) := (overlay_st_in (er := g1 W W') (e1_inj W W') σ τ1 W.sIn).trans hk1
  have h2e2 : ∀ j, ((overlay (e1 W W') (g1 W W') σ τ1).setc false).st (e2 W W' j) = [] := fun j =>
    (overlay_st_off (er := g1 W W') σ τ1 _ (fun i => e1_ne_e2 W W' i j)).trans (hbl _ (fun h => e1_ne_e2 W W' _ _ h.symm))
  -- stage 3: `W'` on its block, reading the kept input
  obtain ⟨τ2, n2, hn2, hs2, ho2, hk2, hr2, hτs2, hτv2⟩ := W'.run F kclk coef A a ha r
    (restrict (f2 W W') (g2 W W') ((overlay (e1 W W') (g1 W W') σ τ1).setc false))
    (by show ((overlay (e1 W W') (g1 W W') σ τ1).setc false).st (f2 W W' W'.sIn) = _
        rw [f2_in]; exact h2in)
    (fun i => h2sh _)
    (fun j hj => by
      show ((overlay (e1 W W') (g1 W W') σ τ1).setc false).st (f2 W W' j) = []
      rw [f2_ne W W' j hj]; exact h2e2 j)
    (fun q => h2v _) rfl
  rw [hN] at hn2 hs2 hr2
  have d3 := embed_run (f2 W W') (g2 W W') (W'.M F) (f2_inj W W') (g2_inj W W') c n2 _ τ2 h2sh h2v hτs2 hτv2
    (stepUp (W'.M F) n2 _ c hK2 _ τ2 (fun q => h2v _) hτv2 hs2)
  refine ⟨overlay (f2 W W') (g2 W W') ((overlay (e1 W W') (g1 W W') σ τ1).setc false) τ2, n1 + 1 + (1 + 1 + n2),
    bnd_sum _ _ _ _ _ n1 n2 (pow_mono_add N _ _) (pow_mono_add' N _ _) hQ hn1 hn2, Step.seq d1 (Step.seq d2 d3),
    ?_, ?_, ?_, overlay_sh0 (es := f2 W W') (er := g2 W W') _ τ2 h2sh hτs2,
    overlay_val0 (es := f2 W W') (er := g2 W W') _ τ2 h2v hτv2⟩
  · -- the outputs
    intro k
    induction k using Fin.addCases with
    | left k1 =>
      simp only [sOutJ, Fin.append_left]
      have hf : ∀ j, f2 W W' j ≠ e1 W W' (W.sOut k1) := by
        intro j hj
        by_cases hjs : j = W'.sIn
        · rw [hjs, f2_in] at hj; exact W.out_ne k1 (e1_inj W W' hj).symm
        · rw [f2_ne W W' j hjs] at hj; exact e1_ne_e2 W W' _ _ hj.symm
      rw [overlay_st_off (er := g2 W W') _ τ2 _ hf, WState.setc_st, overlay_st_in (er := g1 W W') (e1_inj W W') σ τ1]
      exact ho1 k1
    | right k2 =>
      simp only [sOutJ, Fin.append_right]
      rw [← f2_ne W W' _ (W'.out_ne k2), overlay_st_in (er := g2 W W') (f2_inj W W')]
      exact ho2 k2
  · -- the input kept
    rw [← f2_in W W', overlay_st_in (er := g2 W W') (f2_inj W W')]
    exact hk2
  · -- the residues
    intro i h1 h2
    by_cases hi : i.val < W.ns + 1
    · have hi1 : i = e1 W W' ⟨i.val, hi⟩ := Fin.ext rfl
      have hf : ∀ j, f2 W W' j ≠ i := by
        intro j hj
        by_cases hjs : j = W'.sIn
        · rw [hjs, f2_in] at hj; exact h1 hj.symm
        · rw [f2_ne W W' j hjs, hi1] at hj; exact e1_ne_e2 W W' _ _ hj.symm
      have hres := hr1 ⟨i.val, hi⟩ (fun h => h1 (by rw [hi1, h]))
        (fun k h => h2 (Fin.castAdd m' k) (by rw [hi1, h]; simp only [sOutJ, Fin.append_left]))
      rw [overlay_st_off (er := g2 W W') _ τ2 i hf, WState.setc_st, hi1,
        overlay_st_in (er := g1 W W') (e1_inj W W') σ τ1]
      exact bnd_le _ _ _ _ _ (pow_mono_add N _ _) hres
    · have hj0 : i.val - (W.ns + 1) < W'.ns + 1 := by
        have := i.isLt; unfold jns at this; omega
      have hij : i = e2 W W' ⟨i.val - (W.ns + 1), hj0⟩ := Fin.ext (by show i.val = W.ns + 1 + (i.val - (W.ns + 1)); omega)
      by_cases hjs : (⟨i.val - (W.ns + 1), hj0⟩ : Fin (W'.ns + 1)) = W'.sIn
      · have hf : ∀ j, f2 W W' j ≠ i := by
          intro j hj
          by_cases hj's : j = W'.sIn
          · rw [hj's, f2_in, hij] at hj; exact e1_ne_e2 W W' _ _ hj
          · rw [f2_ne W W' j hj's, hij, hjs] at hj; exact hj's (e2_inj W W' hj)
        have hg : ∀ i', e1 W W' i' ≠ i := fun i' h => by rw [hij] at h; exact e1_ne_e2 W W' _ _ h
        rw [overlay_st_off (er := g2 W W') _ τ2 i hf, WState.setc_st, overlay_st_off (er := g1 W W') σ τ1 i hg,
          hbl i h1]
        simp
      · have hres := hr2 ⟨i.val - (W.ns + 1), hj0⟩ hjs
          (fun k h => h2 (Fin.natAdd m k) (by rw [hij, h]; simp only [sOutJ, Fin.append_right]))
        rw [hij, ← f2_ne W W' _ hjs, overlay_st_in (er := g2 W W') (f2_inj W W')]
        exact bnd_le' _ _ _ _ _ (pow_mono_add' N _ _) hres

end JoinLay

end NearCubicWires.WireExponent3_5.FinalPass.Out.Join

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Out.Join

variable {l : Literals} {m m' : ℕ}
  {ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
  {ws' : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m' → List Bool}

/-- **Two writers as one**: `W`'s words, then `W'`'s, on the disjoint union of their layouts sharing the
input; capacity `(Kc + Kc')·(N+1)^{Dk + Dk'}`, steps and residues within `(Cs + Cs' + 4)·(N+1)^{Ds + Ds'}`. -/
noncomputable def CoreWordsMJ.join (W : CoreWordsMJ l m ws) (W' : CoreWordsMJ l m' ws') :
    CoreWordsMJ l (m + m') fun F kclk coef A a ha r => Fin.append (ws F kclk coef A a ha r) (ws' F kclk coef A a ha r)
    where
  ns := jns W W'
  nr := jnr W W'
  s := fun F => (jMach W W' F).1
  M := fun F => (jMach W W' F).2
  sIn := e1 W W' W.sIn
  sOut := ⟨sOutJ W W', sOutJ_inj W W'⟩
  out_ne := sOutJ_ne W W'
  Kc := fun F => W.Kc F + W'.Kc F
  Dk := fun e => W.Dk e + W'.Dk e
  Cs := fun F => W.Cs F + W'.Cs F + 4
  Ds := fun e => W.Ds e + W'.Ds e
  run := fun F kclk coef A a ha r σ hin hsh hbl hv hc => join_run W W' F kclk coef A a ha r σ hin hsh hbl hv hc

/-- **A writer at an equal word family.** -/
noncomputable def CoreWordsMJ.congrWs
    {ws2 : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
    (W : CoreWordsMJ l m ws)
    (h : ∀ F kclk coef A a ha r k, ws F kclk coef A a ha r k = ws2 F kclk coef A a ha r k) : CoreWordsMJ l m ws2 where
  ns := W.ns
  nr := W.nr
  s := W.s
  M := W.M
  sIn := W.sIn
  sOut := W.sOut
  out_ne := W.out_ne
  Kc := W.Kc
  Dk := W.Dk
  Cs := W.Cs
  Ds := W.Ds
  run := fun F kclk coef A a ha r σ hin hsh hbl hv hc => by
    obtain ⟨τ, n, hn, hs, ho, hk, hr, hτs, hτv⟩ := W.run F kclk coef A a ha r σ hin hsh hbl hv hc
    exact ⟨τ, n, hn, hs, fun k => (ho k).trans (h F kclk coef A a ha r k), hk, hr, hτs, hτv⟩

/-- **A subset of a writer's words** (`f : Fin m' ↪ Fin m`): the dropped words become residues, within the step
count (they start blank). -/
noncomputable def CoreWordsMJ.sub (W : CoreWordsMJ l m ws) (f : Fin m' ↪ Fin m) :
    CoreWordsMJ l m' fun F kclk coef A a ha r k => ws F kclk coef A a ha r (f k) where
  ns := W.ns
  nr := W.nr
  s := W.s
  M := W.M
  sIn := W.sIn
  sOut := f.trans W.sOut
  out_ne := fun k => W.out_ne (f k)
  Kc := W.Kc
  Dk := W.Dk
  Cs := W.Cs
  Ds := W.Ds
  run := fun F kclk coef A a ha r σ hin hsh hbl hv hc => by
    obtain ⟨τ, n, hn, hs, ho, hk, hr, hτs, hτv⟩ := W.run F kclk coef A a ha r σ hin hsh hbl hv hc
    refine ⟨τ, n, hn, hs, fun k => ho (f k), hk, fun i h1 h2 => ?_, hτs, hτv⟩
    by_cases hio : ∃ k, i = W.sOut k
    · obtain ⟨k, rfl⟩ := hio
      have hl := stepLen hs (sTape (W.sOut k)) 0 (by rw [wenc_H_s, hsh]) (by rw [wenc_A_s, hbl _ (W.out_ne k)]; simp)
      rw [wenc_A_s] at hl
      omega
    · exact hr i h1 (fun k hk' => hio ⟨k, hk'⟩)

end NearCubicWires.WireExponent3_5.FinalPass.Finish

end
