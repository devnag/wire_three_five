import Proof.Packets.SrcMetaRegs
import Proof.MachineModel.BlockUnaryCalc
import Proof.Packets.PacketsMetaSeedCount
import Proof.Packets.PacketsMetaMaps
import Proof.PCP.PCPPNativeArithmetic

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.MetaPipe
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceStart.Regs
noncomputable section

/-! ## 1. Local entries, operations -/

/-- One unary input on local tape `i`, every other local tape empty. -/
def in1 (n : ℕ) (i : Fin n) (x : ℕ) : Fin n → List Bool :=
  fun j => if j = i then List.replicate x true else []

/-- Two unary inputs on local tapes `i1`, `i2`, every other local tape empty. -/
def in2 (n : ℕ) (i1 i2 : Fin n) (x y : ℕ) : Fin n → List Bool :=
  fun j => if j = i1 then List.replicate x true else if j = i2 then List.replicate y true else []

/-- A unary operation: a fixed heads-`0` machine, input returned, `1^(f x)` on the output tape. -/
structure UOp (f : ℕ → ℕ) where
  n : ℕ
  st : ℕ
  M : Machine n st
  i : Fin n
  o : Fin n
  hio : i ≠ o
  cost : ℕ → ℕ
  run : ∀ x, ∃ tout : Fin n → List Bool, Step M (cost x) (fun _ => 0) (in1 n i x) (fun _ => 0) tout ∧
    tout i = List.replicate x true ∧ tout o = List.replicate (f x) true

/-- A binary operation (under a precondition `pre`). -/
structure BOp (f : ℕ → ℕ → ℕ) (pre : ℕ → ℕ → Prop) where
  n : ℕ
  st : ℕ
  M : Machine n st
  i1 : Fin n
  i2 : Fin n
  o : Fin n
  h12 : i1 ≠ i2
  h1o : i1 ≠ o
  h2o : i2 ≠ o
  cost : ℕ → ℕ → ℕ
  run : ∀ x y, pre x y → ∃ tout : Fin n → List Bool,
    Step M (cost x y) (fun _ => 0) (in2 n i1 i2 x y) (fun _ => 0) tout ∧
    tout i1 = List.replicate x true ∧ tout i2 = List.replicate y true ∧ tout o = List.replicate (f x y) true

/-! ## 2. The register file -/

/-- **The register-file invariant.** -/
def Inv {NL : ℕ} (R nR : ℕ) (vs : List ℕ) (S : ℕ) (E : Fin NL → List Bool) : Prop :=
  (∀ x : Fin NL, x.val < nR → E x = ZeroPadding.pad R (List.replicate (vs.getD x.val 0) true)) ∧
  (∀ x : Fin NL, S ≤ x.val → E x = List.replicate R false)

theorem getD_snoc (vs : List ℕ) (y r : ℕ) (hr : r ≠ vs.length) : (vs ++ [y]).getD r 0 = vs.getD r 0 := by
  rcases Nat.lt_or_gt_of_ne hr with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_self (vs : List ℕ) (y : ℕ) : (vs ++ [y]).getD vs.length 0 = y := by
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

theorem getD_len (vs : List ℕ) : vs.getD vs.length 0 = 0 :=
  List.getD_eq_default _ _ (le_refl _)

/-- The naming of a unary stage. -/
def nm1 {n NL : ℕ} (i o : Fin n) (ra ro : Fin NL) (j : Fin n) : Option (Fin NL) :=
  if j = i then some ra else if j = o then some ro else none

/-- The naming of a binary stage. -/
def nm2 {n NL : ℕ} (i1 i2 o : Fin n) (ra rb ro : Fin NL) (j : Fin n) : Option (Fin NL) :=
  if j = i1 then some ra else if j = i2 then some rb else if j = o then some ro else none

/-- A unary stage docked into the register file (input register `a`, output register `m`, scratch from `S`). -/
def uM {NL : ℕ} {f : ℕ → ℕ} (U : UOp f) (a m S : ℕ) (ha : a < NL) (hm : m < NL) (hs : S + U.n ≤ NL) :
    Machine NL U.st :=
  RecoveryFocus.machine (nslot (nm1 U.i U.o ⟨a, ha⟩ ⟨m, hm⟩) S hs) U.M

/-- A binary stage docked into the register file. -/
def bM {NL : ℕ} {f : ℕ → ℕ → ℕ} {pre : ℕ → ℕ → Prop} (B : BOp f pre) (a b m S : ℕ) (ha : a < NL) (hb : b < NL)
    (hm : m < NL) (hs : S + B.n ≤ NL) : Machine NL B.st :=
  RecoveryFocus.machine (nslot (nm2 B.i1 B.i2 B.o ⟨a, ha⟩ ⟨b, hb⟩ ⟨m, hm⟩) S hs) B.M

theorem fin_ne {NL : ℕ} (a b : ℕ) (ha : a < NL) (hb : b < NL) (h : a ≠ b) : (⟨a, ha⟩ : Fin NL) ≠ ⟨b, hb⟩ :=
  fun e => h (congrArg Fin.val e)

/-- **One unary stage.** -/
theorem ustage {NL : ℕ} {f : ℕ → ℕ} (U : UOp f) {R nR S : ℕ} {vs : List ℕ} {E : Fin NL → List Bool}
    (hE : Inv R nR vs S E) (a m x : ℕ) (vs' : List ℕ)
    (hlen : vs.length = m) (ham : a < m) (hx : vs.getD a 0 = x) (hvs : vs' = vs ++ [f x]) (hm : m < nR) (hS : nR ≤ S)
    (ha' : a < NL) (hm' : m < NL) (hs : S + U.n ≤ NL) :
    ∃ E', Step (uM U a m S ha' hm' hs) (U.cost x) (fun _ => 0) E (fun _ => 0) E' ∧ Inv R nR vs' (S + U.n) E' := by
  subst hvs hlen
  obtain ⟨tout, hrun, hti, hto⟩ := U.run x
  have hne := fin_ne a vs.length ha' hm' (Nat.ne_of_lt ham)
  have haS : a < S := by omega
  have hmS : vs.length < S := by omega
  have hinj : ∀ i j r, nm1 U.i U.o ⟨a, ha'⟩ ⟨vs.length, hm'⟩ i = some r →
      nm1 U.i U.o ⟨a, ha'⟩ ⟨vs.length, hm'⟩ j = some r → i = j := by
    intro i j r hi hj
    unfold nm1 at hi hj
    by_cases c1 : i = U.i
    · by_cases c2 : j = U.i
      · rw [c1, c2]
      · rw [if_pos c1] at hi
        rw [if_neg c2] at hj
        by_cases c3 : j = U.o
        · rw [if_pos c3] at hj
          exact absurd ((Option.some.inj hi).trans (Option.some.inj hj).symm) hne
        · rw [if_neg c3] at hj
          exact absurd hj (by simp)
    · rw [if_neg c1] at hi
      by_cases c3 : i = U.o
      · rw [if_pos c3] at hi
        by_cases c2 : j = U.i
        · rw [if_pos c2] at hj
          exact absurd ((Option.some.inj hj).trans (Option.some.inj hi).symm) hne
        · rw [if_neg c2] at hj
          by_cases c4 : j = U.o
          · rw [c3, c4]
          · rw [if_neg c4] at hj
            exact absurd hj (by simp)
      · rw [if_neg c3] at hi
        exact absurd hi (by simp)
  have hlow : ∀ j r, nm1 U.i U.o ⟨a, ha'⟩ ⟨vs.length, hm'⟩ j = some r → r.val < S := by
    intro j r h
    unfold nm1 at h
    by_cases c1 : j = U.i
    · rw [if_pos c1] at h
      rw [← Option.some.inj h]
      exact haS
    · rw [if_neg c1] at h
      by_cases c2 : j = U.o
      · rw [if_pos c2] at h
        rw [← Option.some.inj h]
        exact hmS
      · rw [if_neg c2] at h
        exact absurd h (by simp)
  have hEa : E ⟨a, ha'⟩ = ZeroPadding.pad R (List.replicate x true) := by
    rw [hE.1 ⟨a, ha'⟩ (by show a < nR; omega), hx]
  have hEm : E ⟨vs.length, hm'⟩ = ZeroPadding.pad R [] := by
    rw [hE.1 ⟨vs.length, hm'⟩ hm]
    show ZeroPadding.pad R (List.replicate (vs.getD vs.length 0) true) = _
    rw [getD_len]
    rfl
  obtain ⟨E', hstep, hnamed, hother, hbeyond⟩ := nstage hrun (nm1 U.i U.o ⟨a, ha'⟩ ⟨vs.length, hm'⟩) S hs hinj hlow E
    (by
      intro j r h
      unfold nm1 at h
      by_cases c1 : j = U.i
      · rw [if_pos c1] at h
        rw [← Option.some.inj h, hEa]
        unfold in1
        rw [if_pos c1]
      · rw [if_neg c1] at h
        by_cases c2 : j = U.o
        · rw [if_pos c2] at h
          rw [← Option.some.inj h, hEm]
          unfold in1
          rw [if_neg c1]
        · rw [if_neg c2] at h
          exact absurd h (by simp))
    (by
      intro j h
      have c1 : j ≠ U.i := by
        intro c
        unfold nm1 at h
        rw [if_pos c] at h
        exact absurd h (by simp)
      unfold in1
      rw [if_neg c1]
      exact NearCubicWires.SourceStart.Stages.pad_nil R)
    hE.2
  have hA : E' ⟨a, ha'⟩ = ZeroPadding.pad R (tout U.i) :=
    hnamed U.i ⟨a, ha'⟩ (by unfold nm1; rw [if_pos rfl])
  have hM : E' ⟨vs.length, hm'⟩ = ZeroPadding.pad R (tout U.o) :=
    hnamed U.o ⟨vs.length, hm'⟩ (by unfold nm1; rw [if_neg U.hio.symm, if_pos rfl])
  refine ⟨E', hstep, ?_, hbeyond⟩
  intro y hy
  by_cases c1 : y = ⟨a, ha'⟩
  · subst c1
    rw [hA, hti]
    show _ = ZeroPadding.pad R (List.replicate ((vs ++ [f x]).getD a 0) true)
    rw [getD_snoc vs (f x) a (Nat.ne_of_lt ham), hx]
  · by_cases c2 : y = ⟨vs.length, hm'⟩
    · subst c2
      rw [hM, hto]
      show _ = ZeroPadding.pad R (List.replicate ((vs ++ [f x]).getD vs.length 0) true)
      rw [getD_snoc_self]
    · have hyv : y.val ≠ vs.length := fun e => c2 (Fin.ext e)
      have hn : ∀ j, nm1 U.i U.o ⟨a, ha'⟩ ⟨vs.length, hm'⟩ j ≠ some y := by
        intro j h
        unfold nm1 at h
        by_cases d1 : j = U.i
        · rw [if_pos d1] at h
          exact c1 (Option.some.inj h).symm
        · rw [if_neg d1] at h
          by_cases d2 : j = U.o
          · rw [if_pos d2] at h
            exact c2 (Option.some.inj h).symm
          · rw [if_neg d2] at h
            exact absurd h (by simp)
      rw [hother y (by omega) hn, hE.1 y hy, getD_snoc vs (f x) y.val hyv]

/-- **One binary stage.** -/
theorem bstage {NL : ℕ} {f : ℕ → ℕ → ℕ} {pre : ℕ → ℕ → Prop} (B : BOp f pre) {R nR S : ℕ} {vs : List ℕ}
    {E : Fin NL → List Bool} (hE : Inv R nR vs S E) (a b m x y : ℕ) (vs' : List ℕ)
    (hlen : vs.length = m) (ham : a < m) (hbm : b < m) (hab : a ≠ b) (hx : vs.getD a 0 = x) (hy : vs.getD b 0 = y)
    (hpre : pre x y) (hvs : vs' = vs ++ [f x y]) (hm : m < nR) (hS : nR ≤ S)
    (ha' : a < NL) (hb' : b < NL) (hm' : m < NL) (hs : S + B.n ≤ NL) :
    ∃ E', Step (bM B a b m S ha' hb' hm' hs) (B.cost x y) (fun _ => 0) E (fun _ => 0) E' ∧
      Inv R nR vs' (S + B.n) E' := by
  subst hvs hlen
  obtain ⟨tout, hrun, hti, htj, hto⟩ := B.run x y hpre
  have nab := fin_ne a b ha' hb' hab
  have nam := fin_ne a vs.length ha' hm' (Nat.ne_of_lt ham)
  have nbm := fin_ne b vs.length hb' hm' (Nat.ne_of_lt hbm)
  have haS : a < S := by omega
  have hbS : b < S := by omega
  have hmS : vs.length < S := by omega
  -- the named local tapes, one lemma per register
  have k1 : ∀ j r, nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ j = some r →
      (j = B.i1 ∧ r = ⟨a, ha'⟩) ∨ (j = B.i2 ∧ r = ⟨b, hb'⟩) ∨ (j = B.o ∧ r = ⟨vs.length, hm'⟩) := by
    intro j r h
    unfold nm2 at h
    by_cases c1 : j = B.i1
    · rw [if_pos c1] at h
      exact Or.inl ⟨c1, (Option.some.inj h).symm⟩
    · rw [if_neg c1] at h
      by_cases c2 : j = B.i2
      · rw [if_pos c2] at h
        exact Or.inr (Or.inl ⟨c2, (Option.some.inj h).symm⟩)
      · rw [if_neg c2] at h
        by_cases c3 : j = B.o
        · rw [if_pos c3] at h
          exact Or.inr (Or.inr ⟨c3, (Option.some.inj h).symm⟩)
        · rw [if_neg c3] at h
          exact absurd h (by simp)
  have e1 : nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ B.i1 = some ⟨a, ha'⟩ := by
    unfold nm2; rw [if_pos rfl]
  have e2 : nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ B.i2 = some ⟨b, hb'⟩ := by
    unfold nm2; rw [if_neg B.h12.symm, if_pos rfl]
  have e3 : nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ B.o = some ⟨vs.length, hm'⟩ := by
    unfold nm2; rw [if_neg B.h1o.symm, if_neg B.h2o.symm, if_pos rfl]
  have hinj : ∀ i j r, nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ i = some r →
      nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ j = some r → i = j := by
    intro i j r hi hj
    rcases k1 i r hi with ⟨i1, r1⟩ | ⟨i1, r1⟩ | ⟨i1, r1⟩ <;>
      rcases k1 j r hj with ⟨j1, s1⟩ | ⟨j1, s1⟩ | ⟨j1, s1⟩
    · exact i1.trans j1.symm
    · exact absurd (r1.symm.trans s1) nab
    · exact absurd (r1.symm.trans s1) nam
    · exact absurd (s1.symm.trans r1) nab
    · exact i1.trans j1.symm
    · exact absurd (r1.symm.trans s1) nbm
    · exact absurd (s1.symm.trans r1) nam
    · exact absurd (s1.symm.trans r1) nbm
    · exact i1.trans j1.symm
  have hlow : ∀ j r, nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ j = some r → r.val < S := by
    intro j r h
    rcases k1 j r h with ⟨_, r1⟩ | ⟨_, r1⟩ | ⟨_, r1⟩
    · rw [r1]; exact haS
    · rw [r1]; exact hbS
    · rw [r1]; exact hmS
  have hEa : E ⟨a, ha'⟩ = ZeroPadding.pad R (List.replicate x true) := by
    rw [hE.1 ⟨a, ha'⟩ (by show a < nR; omega), hx]
  have hEb : E ⟨b, hb'⟩ = ZeroPadding.pad R (List.replicate y true) := by
    rw [hE.1 ⟨b, hb'⟩ (by show b < nR; omega), hy]
  have hEm : E ⟨vs.length, hm'⟩ = ZeroPadding.pad R [] := by
    rw [hE.1 ⟨vs.length, hm'⟩ hm]
    show ZeroPadding.pad R (List.replicate (vs.getD vs.length 0) true) = _
    rw [getD_len]
    rfl
  obtain ⟨E', hstep, hnamed, hother, hbeyond⟩ :=
    nstage hrun (nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩) S hs hinj hlow E
    (by
      intro j r h
      rcases k1 j r h with ⟨j1, r1⟩ | ⟨j1, r1⟩ | ⟨j1, r1⟩
      · rw [r1, hEa, j1]
        unfold in2
        rw [if_pos rfl]
      · rw [r1, hEb, j1]
        unfold in2
        rw [if_neg B.h12.symm, if_pos rfl]
      · rw [r1, hEm, j1]
        unfold in2
        rw [if_neg B.h1o.symm, if_neg B.h2o.symm])
    (by
      intro j h
      have c1 : j ≠ B.i1 := by
        intro c; rw [c, e1] at h; exact absurd h (by simp)
      have c2 : j ≠ B.i2 := by
        intro c; rw [c, e2] at h; exact absurd h (by simp)
      unfold in2
      rw [if_neg c1, if_neg c2]
      exact NearCubicWires.SourceStart.Stages.pad_nil R)
    hE.2
  refine ⟨E', hstep, ?_, hbeyond⟩
  intro z hz
  by_cases c1 : z = ⟨a, ha'⟩
  · subst c1
    rw [hnamed B.i1 _ e1, hti]
    show _ = ZeroPadding.pad R (List.replicate ((vs ++ [f x y]).getD a 0) true)
    rw [getD_snoc vs (f x y) a (Nat.ne_of_lt ham), hx]
  · by_cases c2 : z = ⟨b, hb'⟩
    · subst c2
      rw [hnamed B.i2 _ e2, htj]
      show _ = ZeroPadding.pad R (List.replicate ((vs ++ [f x y]).getD b 0) true)
      rw [getD_snoc vs (f x y) b (Nat.ne_of_lt hbm), hy]
    · by_cases c3 : z = ⟨vs.length, hm'⟩
      · subst c3
        rw [hnamed B.o _ e3, hto]
        show _ = ZeroPadding.pad R (List.replicate ((vs ++ [f x y]).getD vs.length 0) true)
        rw [getD_snoc_self]
      · have hzv : z.val ≠ vs.length := fun e => c3 (Fin.ext e)
        have hn : ∀ j, nm2 B.i1 B.i2 B.o ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨vs.length, hm'⟩ j ≠ some z := by
          intro j h
          rcases k1 j z h with ⟨_, r1⟩ | ⟨_, r1⟩ | ⟨_, r1⟩
          · exact c1 r1
          · exact c2 r1
          · exact c3 r1
        rw [hother z (by omega) hn, hE.1 z hz, getD_snoc vs (f x y) z.val hzv]

/-! ## 3. The operations -/

/-- `x ↦ ⌊x/2⌋` (PG's `Halve`, masked). -/
def halfOp : UOp (fun x => x / 2) where
  n := 2 + 1
  st := _
  M := MaskedReset.machine NearCubicWires.PacketsMeta.Seed.Halve.machine (fun _ => true)
  i := 0
  o := 1
  hio := by decide
  cost := fun x => 2 * (x + 1) + 2
  run := fun x => by
    obtain ⟨k, hm⟩ := NearCubicWires.SourceStart.Stages.mask0 (NearCubicWires.PacketsMeta.Seed.Halve.run x)
    have e : (Fin.addCases (![List.replicate x true, []] : Fin 2 → List Bool) (fun _ : Fin 1 => ([] : List Bool))) =
        in1 (2 + 1) 0 x := by
      funext j
      fin_cases j <;> rfl
    rw [e] at hm
    exact ⟨_, hm, rfl, rfl⟩

/-- `x ↦ x + c` (PG's `CopyPlus c`, masked). -/
def plusOp (c : ℕ) : UOp (fun x => x + c) where
  n := 2 + 1
  st := _
  M := MaskedReset.machine (NearCubicWires.PacketsGlue.RequestMeta.CopyPlus.machine c) (fun _ => true)
  i := 0
  o := 1
  hio := by decide
  cost := fun x => 2 * (x + 1 + c) + 2
  run := fun x => by
    have h := NearCubicWires.PacketsGlue.RequestMeta.CopyPlus.run c x
    rw [NearCubicWires.SourceStart.Stages.vec2_zero] at h
    obtain ⟨k, hm⟩ := NearCubicWires.SourceStart.Stages.mask0 h
    have e : (Fin.addCases (![List.replicate x true, []] : Fin 2 → List Bool) (fun _ : Fin 1 => ([] : List Bool))) =
        in1 (2 + 1) 0 x := by
      funext j
      fin_cases j <;> rfl
    rw [e] at hm
    exact ⟨_, hm, rfl, rfl⟩

def polyOp (D C : ℕ) : UOp (fun x => NearCubicWires.BlockPlatform.UnaryCalc.value D C x) where
  n := NearCubicWires.BlockPlatform.UnaryCalc.tapes D
  st := _
  M := PCPSerializerCapacity.Power.machine D C
  i := NearCubicWires.BlockPlatform.UnaryCalc.inputTape D
  o := NearCubicWires.BlockPlatform.UnaryCalc.outputTape D
  hio := (NearCubicWires.BlockPlatform.UnaryCalc.output_ne_input D).symm
  cost := PCPSerializerCapacity.Power.budget D C
  run := fun x => by
    obtain ⟨out, h, h0, h1⟩ := NearCubicWires.BlockPlatform.UnaryCalc.poly_step D C x
    have e : RepairSource.ProjectionNormalization.DimensionPolynomial.input D x =
        in1 _ (NearCubicWires.BlockPlatform.UnaryCalc.inputTape D) x := by
      funext j
      unfold in1 RepairSource.ProjectionNormalization.DimensionPolynomial.input
      simp [NearCubicWires.BlockPlatform.UnaryCalc.inputTape, Fin.ext_iff]
    rw [e] at h
    exact ⟨out, h, h0, h1⟩

def sumOp : BOp (fun x y => x + y) (fun _ _ => True) where
  n := 4
  st := _
  M := ClockUnarySum.machine
  i1 := 0
  i2 := 1
  o := 2
  h12 := by decide
  h1o := by decide
  h2o := by decide
  cost := fun x y => 2 * (x + y) + 6
  run := fun x y _ => by
    have h := NearCubicWires.BlockPlatform.UnaryCalc.sum_step x y
    have e : (![List.replicate x true, List.replicate y true, [], []] : Fin 4 → List Bool) = in2 4 0 1 x y := by
      funext j
      fin_cases j <;> rfl
    rw [e] at h
    exact ⟨_, h, rfl, rfl, rfl⟩

theorem cold_in (x y : ℕ) : PCPPNativeColdArithmetic.input x y = in2 5 0 1 x y := by
  funext j
  fin_cases j <;> rfl

def subOp : BOp (fun x y => x - y) (fun _ _ => True) where
  n := 5
  st := _
  M := PCPPNativeColdArithmetic.machine
  i1 := 0
  i2 := 1
  o := 3
  h12 := by decide
  h1o := by decide
  h2o := by decide
  cost := PCPPNativeColdArithmetic.budget
  run := fun x y _ => by
    have h := Step.of_ready (PCPPNativeColdArithmetic.ready x y)
    rw [cold_in] at h
    exact ⟨_, h, rfl, rfl, rfl⟩

def maxOp : BOp (fun x y => max x y) (fun _ _ => True) where
  n := 5
  st := _
  M := PCPPNativeColdArithmetic.machine
  i1 := 0
  i2 := 1
  o := 2
  h12 := by decide
  h1o := by decide
  h2o := by decide
  cost := PCPPNativeColdArithmetic.budget
  run := fun x y _ => by
    have h := Step.of_ready (PCPPNativeColdArithmetic.ready x y)
    rw [cold_in] at h
    exact ⟨_, h, rfl, rfl, rfl⟩

end
end NearCubicWires.SourceFactorSel.MetaPipe

