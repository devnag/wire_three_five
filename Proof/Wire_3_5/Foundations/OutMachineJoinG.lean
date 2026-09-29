import Proof.Wire_3_5.Foundations.OutMachineJoinW

/-! # Writer combinators with a guard

Some writers run only at some requests (the SYM parts: `r.1.mode = .sym`). A **guarded** writer
`Finish.GuardedWordsMJ l G m ws` is `CoreWordsMJ` whose run assumes `G r`. Here:

* the raw joint layout (`jnsR`, `e1R`, `e2R`, `f2R`, `g1R`, `g2R`, `sOutR`, `jMachR`), `RunAt` (a writer's run at one
  request, abstractly), **`join_core`** (two runs at one request are the joint machine's run), `RunAt.mono`;
* **`GuardedWordsMJ.join`** (the guard shared), **`.reindex`**, **`.congrWs`**, **`.sub`**;
* **`CoreWordsMJ.toG`** (any guard), **`SymWordsMJ.ofG`** (at `G := r.1.mode = .sym` and the SYM slots' words).

Paper quantity of the main type: the front's words at a request (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.JoinG
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Out.Join

section Raw
variable {ns nr ns' nr' : ℕ}

def jnsR (ns ns' : ℕ) : ℕ := ns + 1 + ns'

def jnrR (nr nr' : ℕ) : ℕ := nr + nr'

def e1R (ns ns' : ℕ) (i : Fin (ns + 1)) : Fin (jnsR ns ns' + 1) := ⟨i.val, by have := i.isLt; unfold jnsR; omega⟩

def e2R (ns ns' : ℕ) (j : Fin (ns' + 1)) : Fin (jnsR ns ns' + 1) :=
  ⟨ns + 1 + j.val, by have := j.isLt; unfold jnsR; omega⟩

def f2R (sIn : Fin (ns + 1)) (sIn' : Fin (ns' + 1)) (j : Fin (ns' + 1)) : Fin (jnsR ns ns' + 1) :=
  if j = sIn' then e1R ns ns' sIn else e2R ns ns' j

def g1R (nr nr' : ℕ) (q : Fin nr) : Fin (jnrR nr nr') := ⟨q.val, by have := q.isLt; unfold jnrR; omega⟩

def g2R (nr nr' : ℕ) (q : Fin nr') : Fin (jnrR nr nr') := ⟨nr + q.val, by have := q.isLt; unfold jnrR; omega⟩

theorem e1R_inj : Function.Injective (e1R ns ns') := fun a b h => by
  have h2 := congrArg Fin.val h
  exact Fin.ext h2

theorem e2R_inj : Function.Injective (e2R ns ns') := fun a b h => by
  have h2 : ns + 1 + a.val = ns + 1 + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

theorem e1R_ne_e2R (i : Fin (ns + 1)) (j : Fin (ns' + 1)) : e1R ns ns' i ≠ e2R ns ns' j := fun h => by
  have h2 : i.val = ns + 1 + j.val := congrArg Fin.val h
  have := i.isLt
  omega

theorem f2R_in (sIn : Fin (ns + 1)) (sIn' : Fin (ns' + 1)) : f2R sIn sIn' sIn' = e1R ns ns' sIn := if_pos rfl

theorem f2R_ne (sIn : Fin (ns + 1)) (sIn' : Fin (ns' + 1)) (j : Fin (ns' + 1)) (hj : j ≠ sIn') :
    f2R sIn sIn' j = e2R ns ns' j := if_neg hj

theorem f2R_inj (sIn : Fin (ns + 1)) (sIn' : Fin (ns' + 1)) : Function.Injective (f2R sIn sIn') := by
  intro a b h
  by_cases ha : a = sIn' <;> by_cases hb : b = sIn'
  · rw [ha, hb]
  · rw [ha, f2R_in, f2R_ne sIn sIn' b hb] at h; exact absurd h (e1R_ne_e2R _ _)
  · rw [hb, f2R_in, f2R_ne sIn sIn' a ha] at h; exact absurd h.symm (e1R_ne_e2R _ _)
  · rw [f2R_ne sIn sIn' a ha, f2R_ne sIn sIn' b hb] at h; exact e2R_inj h

theorem g1R_inj : Function.Injective (g1R nr nr') := fun a b h => by
  have h2 := congrArg Fin.val h
  exact Fin.ext h2

theorem g2R_inj : Function.Injective (g2R nr nr') := fun a b h => by
  have h2 : nr + a.val = nr + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- The joint outputs: the first writer's, then the second's. -/
def sOutR {m m' : ℕ} (sOut : Fin m → Fin (ns + 1)) (sOut' : Fin m' → Fin (ns' + 1)) :
    Fin (m + m') → Fin (jnsR ns ns' + 1) :=
  Fin.append (fun k => e1R ns ns' (sOut k)) (fun k => e2R ns ns' (sOut' k))

theorem sOutR_inj {m m' : ℕ} (sOut : Fin m → Fin (ns + 1)) (sOut' : Fin m' → Fin (ns' + 1))
    (h1 : Function.Injective sOut) (h2 : Function.Injective sOut') : Function.Injective (sOutR sOut sOut') := by
  intro a b h
  induction a using Fin.addCases with
  | left a1 =>
    induction b using Fin.addCases with
    | left b1 =>
      simp only [sOutR, Fin.append_left] at h
      rw [h1 (e1R_inj h)]
    | right b2 =>
      simp only [sOutR, Fin.append_left, Fin.append_right] at h
      exact absurd h (e1R_ne_e2R _ _)
  | right a2 =>
    induction b using Fin.addCases with
    | left b1 =>
      simp only [sOutR, Fin.append_left, Fin.append_right] at h
      exact absurd h.symm (e1R_ne_e2R _ _)
    | right b2 =>
      simp only [sOutR, Fin.append_right] at h
      rw [h2 (e2R_inj h)]

theorem sOutR_ne {m m' : ℕ} (sIn : Fin (ns + 1)) (sOut : Fin m → Fin (ns + 1)) (sOut' : Fin m' → Fin (ns' + 1))
    (hne : ∀ k, sOut k ≠ sIn) (k : Fin (m + m')) : sOutR sOut sOut' k ≠ e1R ns ns' sIn := by
  induction k using Fin.addCases with
  | left k1 =>
    simp only [sOutR, Fin.append_left]
    exact fun h => hne k1 (e1R_inj h)
  | right k2 =>
    simp only [sOutR, Fin.append_right]
    exact fun h => e1R_ne_e2R _ _ h.symm

/-- The joint machine. -/
noncomputable def jMachR {s s' : ℕ} (M : Machine (ns + 2 + nr) s) (M' : Machine (ns' + 2 + nr') s')
    (sIn : Fin (ns + 1)) (sIn' : Fin (ns' + 1)) : (t : ℕ) × Machine (jnsR ns ns' + 2 + jnrR nr nr') t :=
  ⟨_, Composition.machine (RecoveryFocus.machine (tmap (e1R ns ns') (g1R nr nr')) M)
    (Composition.machine (WM.setc (ns := jnsR ns ns') (nr := jnrR nr nr') false).toProg.compile
      (RecoveryFocus.machine (tmap (f2R sIn sIn') (g2R nr nr')) M'))⟩

/-- **A writer's run at one request**: from the input `x` (everything else blank, heads and registers `0`), within
`S` steps, the words `ws` on `sOut`, the input kept, the residues within `S`, heads and registers `0`. -/
def RunAt {s m : ℕ} (M : Machine (ns + 2 + nr) s) (sIn : Fin (ns + 1)) (sOut : Fin m → Fin (ns + 1)) (K S : ℕ)
    (x : List Bool) (ws : Fin m → List Bool) : Prop :=
  ∀ σ : WState ns nr, σ.st sIn = x → (∀ i, σ.sh i = 0) → (∀ i, i ≠ sIn → σ.st i = []) → (∀ q, σ.val q = 0) →
    σ.cell = false →
    ∃ (τ : WState ns nr) (n : ℕ), n ≤ S ∧ Step M n (wenc K σ).H (wenc K σ).A (wenc K τ).H (wenc K τ).A ∧
      (∀ k, τ.st (sOut k) = ws k) ∧ τ.st sIn = x ∧ (∀ i, i ≠ sIn → (∀ k, i ≠ sOut k) → (τ.st i).length ≤ S) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0)

theorem RunAt.mono {s m : ℕ} {M : Machine (ns + 2 + nr) s} {sIn : Fin (ns + 1)} {sOut : Fin m → Fin (ns + 1)}
    {K S S' : ℕ} {x : List Bool} {ws : Fin m → List Bool} (h : RunAt M sIn sOut K S x ws) (hS : S ≤ S') :
    RunAt M sIn sOut K S' x ws := by
  intro σ h1 h2 h3 h4 h5
  obtain ⟨τ, n, hn, hs, ho, hk, hr, hτs, hτv⟩ := h σ h1 h2 h3 h4 h5
  exact ⟨τ, n, le_trans hn hS, hs, ho, hk, fun i a b => le_trans (hr i a b) hS, hτs, hτv⟩

/-- **Two runs at one request are the joint machine's run** (the first writer, the cell reset, the second writer
reading the kept input). -/
theorem join_core {s s' m m' : ℕ} (M : Machine (ns + 2 + nr) s) (M' : Machine (ns' + 2 + nr') s')
    (sIn : Fin (ns + 1)) (sOut : Fin m → Fin (ns + 1)) (sIn' : Fin (ns' + 1)) (sOut' : Fin m' → Fin (ns' + 1))
    (hne : ∀ k, sOut k ≠ sIn) (hne' : ∀ k, sOut' k ≠ sIn') (K1 K2 c S1 S2 : ℕ) (hK1 : K1 ≤ c) (hK2 : K2 ≤ c)
    (x : List Bool) (ws : Fin m → List Bool) (ws' : Fin m' → List Bool)
    (h1 : RunAt M sIn sOut K1 S1 x ws) (h2 : RunAt M' sIn' sOut' K2 S2 x ws') :
    RunAt (jMachR M M' sIn sIn').2 (e1R ns ns' sIn) (sOutR sOut sOut') c (S1 + S2 + 3) x (Fin.append ws ws') := by
  intro σ hin hsh hbl hv hc
  -- stage 1
  obtain ⟨τ1, n1, hn1, hs1, ho1, hk1, hr1, hτs1, hτv1⟩ := h1 (restrict (e1R ns ns') (g1R nr nr') σ)
    hin (fun i => hsh _) (fun i hi => hbl _ (fun h => hi (e1R_inj h))) (fun q => hv _) hc
  have d1 := embed_run (e1R ns ns') (g1R nr nr') M e1R_inj g1R_inj c n1 σ τ1 hsh hv hτs1 hτv1
    (stepUp M n1 _ c hK1 _ τ1 (fun q => hv _) hτv1 hs1)
  -- stage 2
  have d2 : Step (WM.setc (ns := jnsR ns ns') (nr := jnrR nr nr') false).toProg.compile 1
      (wenc c (overlay (e1R ns ns') (g1R nr nr') σ τ1)).H (wenc c (overlay (e1R ns ns') (g1R nr nr') σ τ1)).A
      (wenc c ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false)).H
      (wenc c ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false)).A :=
    Exec.step (WExec.exec c (WExec.setc false _))
  have h2sh : ∀ i, ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false).sh i = 0 :=
    overlay_sh0 (es := e1R ns ns') (er := g1R nr nr') σ τ1 hsh hτs1
  have h2v : ∀ q, ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false).val q = 0 :=
    overlay_val0 (es := e1R ns ns') (er := g1R nr nr') σ τ1 hv hτv1
  have h2in : ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false).st (e1R ns ns' sIn) = x :=
    (overlay_st_in (er := g1R nr nr') e1R_inj σ τ1 sIn).trans hk1
  have h2e2 : ∀ j, ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false).st (e2R ns ns' j) = [] := fun j =>
    (overlay_st_off (er := g1R nr nr') σ τ1 _ (fun i => e1R_ne_e2R i j)).trans
      (hbl _ (fun h => e1R_ne_e2R _ _ h.symm))
  -- stage 3
  obtain ⟨τ2, n2, hn2, hs2, ho2, hk2, hr2, hτs2, hτv2⟩ := h2
    (restrict (f2R sIn sIn') (g2R nr nr') ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false))
    (by show ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false).st (f2R sIn sIn' sIn') = _
        rw [f2R_in]; exact h2in)
    (fun i => h2sh _)
    (fun j hj => by
      show ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false).st (f2R sIn sIn' j) = []
      rw [f2R_ne sIn sIn' j hj]; exact h2e2 j)
    (fun q => h2v _) rfl
  have d3 := embed_run (f2R sIn sIn') (g2R nr nr') M' (f2R_inj sIn sIn') g2R_inj c n2 _ τ2 h2sh h2v hτs2 hτv2
    (stepUp M' n2 _ c hK2 _ τ2 (fun q => h2v _) hτv2 hs2)
  refine ⟨overlay (f2R sIn sIn') (g2R nr nr') ((overlay (e1R ns ns') (g1R nr nr') σ τ1).setc false) τ2,
    n1 + 1 + (1 + 1 + n2), by omega, Step.seq d1 (Step.seq d2 d3), ?_, ?_, ?_,
    overlay_sh0 (es := f2R sIn sIn') (er := g2R nr nr') _ τ2 h2sh hτs2,
    overlay_val0 (es := f2R sIn sIn') (er := g2R nr nr') _ τ2 h2v hτv2⟩
  · intro k
    induction k using Fin.addCases with
    | left k1 =>
      simp only [sOutR, Fin.append_left]
      have hf : ∀ j, f2R sIn sIn' j ≠ e1R ns ns' (sOut k1) := by
        intro j hj
        by_cases hjs : j = sIn'
        · rw [hjs, f2R_in] at hj; exact hne k1 (e1R_inj hj).symm
        · rw [f2R_ne sIn sIn' j hjs] at hj; exact e1R_ne_e2R _ _ hj.symm
      rw [overlay_st_off (er := g2R nr nr') _ τ2 _ hf, WState.setc_st,
        overlay_st_in (er := g1R nr nr') e1R_inj σ τ1]
      exact ho1 k1
    | right k2 =>
      simp only [sOutR, Fin.append_right]
      rw [← f2R_ne sIn sIn' _ (hne' k2), overlay_st_in (er := g2R nr nr') (f2R_inj sIn sIn')]
      exact ho2 k2
  · rw [← f2R_in sIn sIn', overlay_st_in (er := g2R nr nr') (f2R_inj sIn sIn')]
    exact hk2
  · intro i h1 h2
    by_cases hi : i.val < ns + 1
    · have hi1 : i = e1R ns ns' ⟨i.val, hi⟩ := Fin.ext rfl
      have hf : ∀ j, f2R sIn sIn' j ≠ i := by
        intro j hj
        by_cases hjs : j = sIn'
        · rw [hjs, f2R_in] at hj; exact h1 hj.symm
        · rw [f2R_ne sIn sIn' j hjs, hi1] at hj; exact e1R_ne_e2R _ _ hj.symm
      have hres := hr1 ⟨i.val, hi⟩ (fun h => h1 (by rw [hi1, h]))
        (fun k h => h2 (Fin.castAdd m' k) (by rw [hi1, h]; simp only [sOutR, Fin.append_left]))
      rw [overlay_st_off (er := g2R nr nr') _ τ2 i hf, WState.setc_st, hi1,
        overlay_st_in (er := g1R nr nr') e1R_inj σ τ1]
      omega
    · have hj0 : i.val - (ns + 1) < ns' + 1 := by
        have := i.isLt; unfold jnsR at this; omega
      have hij : i = e2R ns ns' ⟨i.val - (ns + 1), hj0⟩ :=
        Fin.ext (by show i.val = ns + 1 + (i.val - (ns + 1)); omega)
      by_cases hjs : (⟨i.val - (ns + 1), hj0⟩ : Fin (ns' + 1)) = sIn'
      · have hf : ∀ j, f2R sIn sIn' j ≠ i := by
          intro j hj
          by_cases hj's : j = sIn'
          · rw [hj's, f2R_in, hij] at hj; exact e1R_ne_e2R _ _ hj
          · rw [f2R_ne sIn sIn' j hj's, hij, hjs] at hj; exact hj's (e2R_inj hj)
        have hg : ∀ i', e1R ns ns' i' ≠ i := fun i' h => by rw [hij] at h; exact e1R_ne_e2R _ _ h
        rw [overlay_st_off (er := g2R nr nr') _ τ2 i hf, WState.setc_st,
          overlay_st_off (er := g1R nr nr') σ τ1 i hg, hbl i h1]
        simp
      · have hres := hr2 ⟨i.val - (ns + 1), hj0⟩ hjs
          (fun k h => h2 (Fin.natAdd m k) (by rw [hij, h]; simp only [sOutR, Fin.append_right]))
        rw [hij, ← f2R_ne sIn sIn' _ hjs, overlay_st_in (er := g2R nr nr') (f2R_inj sIn sIn')]
        omega

end Raw

theorem bndG (C C' : ℕ) (N : ℕ) (x y : ℕ) (hQ : (N + 1) ^ x ≤ (N + 1) ^ (x + y))
    (hQ' : (N + 1) ^ y ≤ (N + 1) ^ (x + y)) :
    C * (N + 1) ^ x + C' * (N + 1) ^ y + 3 ≤ (C + C' + 4) * (N + 1) ^ (x + y) := by
  have a1 := Nat.mul_le_mul_left C hQ
  have a2 := Nat.mul_le_mul_left C' hQ'
  have h1 : 1 ≤ (N + 1) ^ (x + y) := Nat.one_le_pow _ _ (Nat.succ_pos N)
  have e : (C + C' + 4) * (N + 1) ^ (x + y) = C * (N + 1) ^ (x + y) + (C' * (N + 1) ^ (x + y) +
      4 * (N + 1) ^ (x + y)) := by ring
  rw [e]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.Out.JoinG

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Out.Join NearCubicWires.WireExponent3_5.FinalPass.Out.JoinG

/-- **A guarded word writer**: `CoreWordsMJ` whose run assumes the guard `G r`. -/
structure GuardedWordsMJ (l : Literals)
    (G : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Prop) (m : ℕ)
    (ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool)
    where
  ns : ℕ
  nr : ℕ
  s : GateFree l → ℕ
  M : (F : GateFree l) → Machine (ns + 2 + nr) (s F)
  sIn : Fin (ns + 1)
  sOut : Fin m ↪ Fin (ns + 1)
  out_ne : ∀ k, sOut k ≠ sIn
  Kc : GateFree l → ℕ
  Dk : ℕ → ℕ
  Cs : GateFree l → ℕ
  Ds : ℕ → ℕ
  run : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
    G F kclk coef A a ha r → ∀ σ : WState ns nr, σ.st sIn = frame (fpIn l F kclk coef A a ha r) → (∀ i, σ.sh i = 0) →
      (∀ i, i ≠ sIn → σ.st i = []) → (∀ q, σ.val q = 0) → σ.cell = false →
      ∃ (τ : WState ns nr) (n : ℕ), n ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg ∧
        Step (M F) n (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).A
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).A ∧
        (∀ k : Fin m, τ.st (sOut k) = ws F kclk coef A a ha r k) ∧
        τ.st sIn = frame (fpIn l F kclk coef A a ha r) ∧
        (∀ i, i ≠ sIn → (∀ k, i ≠ sOut k) →
          (τ.st i).length ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0)

variable {l : Literals}
  {G : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Prop} {m m' : ℕ}
  {ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
  {ws' : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m' → List Bool}

/-- **Two guarded writers as one** (the guard shared). -/
noncomputable def GuardedWordsMJ.join (W : GuardedWordsMJ l G m ws) (W' : GuardedWordsMJ l G m' ws') :
    GuardedWordsMJ l G (m + m') fun F kclk coef A a ha r =>
      Fin.append (ws F kclk coef A a ha r) (ws' F kclk coef A a ha r) where
  ns := jnsR W.ns W'.ns
  nr := jnrR W.nr W'.nr
  s := fun F => (jMachR (W.M F) (W'.M F) W.sIn W'.sIn).1
  M := fun F => (jMachR (W.M F) (W'.M F) W.sIn W'.sIn).2
  sIn := e1R W.ns W'.ns W.sIn
  sOut := ⟨sOutR W.sOut W'.sOut, sOutR_inj _ _ W.sOut.injective W'.sOut.injective⟩
  out_ne := sOutR_ne W.sIn W.sOut W'.sOut W.out_ne
  Kc := fun F => W.Kc F + W'.Kc F
  Dk := fun e => W.Dk e + W'.Dk e
  Cs := fun F => W.Cs F + W'.Cs F + 4
  Ds := fun e => W.Ds e + W'.Ds e
  run := fun F kclk coef A a ha r hG =>
    RunAt.mono (join_core (W.M F) (W'.M F) W.sIn W.sOut W'.sIn W'.sOut W.out_ne W'.out_ne _ _ _ _ _
      (Nat.mul_le_mul (Nat.le_add_right _ _) (pow_mono_add _ _ _))
      (Nat.mul_le_mul (Nat.le_add_left _ _) (pow_mono_add' _ _ _)) _ _ _
      (W.run F kclk coef A a ha r hG) (W'.run F kclk coef A a ha r hG))
      (bndG _ _ _ _ _ (pow_mono_add _ _ _) (pow_mono_add' _ _ _))

/-- **A guarded writer at an equal word family** (on the guard). -/
noncomputable def GuardedWordsMJ.congrWs
    {ws2 : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
    (W : GuardedWordsMJ l G m ws)
    (h : ∀ F kclk coef A a ha r, G F kclk coef A a ha r → ∀ k, ws F kclk coef A a ha r k = ws2 F kclk coef A a ha r k) :
    GuardedWordsMJ l G m ws2 where
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
  run := fun F kclk coef A a ha r hG σ hin hsh hbl hv hc => by
    obtain ⟨τ, n, hn, hs, ho, hk, hr, hτs, hτv⟩ := W.run F kclk coef A a ha r hG σ hin hsh hbl hv hc
    exact ⟨τ, n, hn, hs, fun k => (ho k).trans (h F kclk coef A a ha r hG k), hk, hr, hτs, hτv⟩

/-- **The SYM words writer from a guarded one** at `G := r.1.mode = .sym` and the SYM slots' words. -/
noncomputable def SymWordsMJ.ofG
    (W : GuardedWordsMJ l (fun _ _ _ _ _ _ r => r.1.mode = .sym) 17
      (fun F kclk coef A a ha r k => frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot k))) : SymWordsMJ l where
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
  run := fun F kclk coef A a ha r hm => W.run F kclk coef A a ha r hm

end NearCubicWires.WireExponent3_5.FinalPass.Finish
