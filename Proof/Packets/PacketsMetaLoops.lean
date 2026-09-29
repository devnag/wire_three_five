import Proof.Packets.PacketsMetaLevelRun

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.PacketsMeta.CutoffMath
noncomputable section

namespace Lev

/-! ## The body at its global slots -/

def sBody : Fin 24 → Fin 60 :=
  ![3, 4, 5, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]

theorem sBody_inj : Function.Injective sBody := by decide

def bodyG := RecoveryFocus.machine sBody Body.machine

def bodyS (g : GS) : GS :=
  { g with f := g.f + selMag [rec g 0, rec g 1, rec g 2, rec g 3], cnt := g.cnt + 1, fl := false }

theorem ofFn_rec (g : GS) : List.ofFn (rec g) = [rec g 0, rec g 1, rec g 2, rec g 3] := by
  simp [List.ofFn_succ]

theorem take4_rec (g : GS) : (List.ofFn (rec g)).take 4 = [rec g 0, rec g 1, rec g 2, rec g 3] := by
  rw [ofFn_rec]
  rfl

theorem horner_lt (A B a0 a1 a2 a3 b : ℕ) (h0 : a0 < A) (h1 : a1 < A) (h2 : a2 < A) (h3 : a3 < A)
    (hb : b ≤ B) (hB : 1 ≤ B) : a0 + b * (a1 + b * (a2 + b * a3)) < 4 * A * B ^ 3 := by
  have e3 : b * a3 ≤ B * A := Nat.mul_le_mul hb h3.le
  have e2 : b * (a2 + b * a3) ≤ B * (A + B * A) := Nat.mul_le_mul hb (by omega)
  have e1 : b * (a1 + b * (a2 + b * a3)) ≤ B * (A + B * (A + B * A)) := Nat.mul_le_mul hb (by omega)
  have hA : 1 ≤ A := by omega
  have p1 : B ≤ B ^ 3 := by
    calc B = B ^ 1 := (pow_one B).symm
      _ ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  have p2 : B * B ≤ B ^ 3 := by
    calc B * B = B ^ 2 := (sq B).symm
      _ ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  have p0 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB
  have e : A + B * (A + B * (A + B * A)) = A * 1 + A * B + A * (B * B) + A * B ^ 3 := by ring
  have q1 : A * 1 ≤ A * B ^ 3 := Nat.mul_le_mul_left _ p0
  have q2 : A * B ≤ A * B ^ 3 := Nat.mul_le_mul_left _ p1
  have q3 : A * (B * B) ≤ A * B ^ 3 := Nat.mul_le_mul_left _ p2
  have e4 : 4 * A * B ^ 3 = A * B ^ 3 + A * B ^ 3 + A * B ^ 3 + A * B ^ 3 := by ring
  omega

section Body
variable {W : ℕ} (fx : Fin 60 → TS) (d : Fin 4 → CD)

/-- The body's cost. -/
def nB (W : ℕ) : ℕ := 130 * W * W + 700 * W + 900

theorem body_run (hfx3 : fx 3 = .ruler) (hfx5 : fx 5 = .reg 0) (hW : 1 ≤ W) (R Fmax Cmax : ℕ)
    (hR : 4 * R + 11 ≤ W) (hrec : ∀ (j : Fin 4) (x : Rec), x ∈ tab (d j) → recMag x < 2 ^ R)
    (hFm : Fmax < 2 ^ W) (hCm : Cmax < 2 ^ W) (g : GS) (hg : InvAt d Fmax Cmax 4 selMag 1 g) :
    LRuns W bodyG (nB W) (Gv fx d g) (Gv fx d (bodyS g)) := by
  obtain ⟨_, hgrec, hgf, hgc⟩ := hg
  rw [take4_rec] at hgf
  have r0 := hrec 0 _ (hgrec 0 (by decide))
  have r1 := hrec 1 _ (hgrec 1 (by decide))
  have r2 := hrec 2 _ (hgrec 2 (by decide))
  have r3 := hrec 3 _ (hgrec 3 (by decide))
  simp only [rec, recMag] at r0 r1 r2 r3
  have hRW : 2 ^ (4 * R + 11) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hR
  have hbase : Body.base (g.ra 0) (g.ra 1) (g.ra 2) (g.ra 3) (g.ru 0) (g.ru 1) (g.ru 2) (g.ru 3)
      (g.rv 0) (g.rv 1) (g.rv 2) (g.rv 3) < 2 ^ (R + 2) := by
    have e : 2 ^ (R + 2) = 4 * 2 ^ R := by rw [pow_add]; ring
    simp only [Body.base]
    omega
  have hB1 : 1 ≤ 2 ^ (R + 2) := Nat.one_le_two_pow
  have hbig : 4 * 2 ^ R * (2 ^ (R + 2)) ^ 3 ≤ 2 ^ W := by
    have e : 4 * 2 ^ R * (2 ^ (R + 2)) ^ 3 = 2 ^ (4 * R + 8) := by
      rw [← pow_mul, show 4 * 2 ^ R = 2 ^ 2 * 2 ^ R by norm_num, ← pow_add, ← pow_add]
      ring_nf
    rw [e]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hRW
  have hR2 : 2 ^ (R + 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA := horner_lt (2 ^ R) (2 ^ (R + 2)) (g.ra 0) (g.ra 1) (g.ra 2) (g.ra 3) _ (by omega) (by omega)
    (by omega) (by omega) hbase.le hB1
  have hP := horner_lt (2 ^ R) (2 ^ (R + 2)) (g.ru 0) (g.ru 1) (g.ru 2) (g.ru 3) _ (by omega) (by omega)
    (by omega) (by omega) hbase.le hB1
  have hQ := horner_lt (2 ^ R) (2 ^ (R + 2)) (g.rv 0) (g.rv 1) (g.rv 2) (g.rv 3) _ (by omega) (by omega)
    (by omega) (by omega) hbase.le hB1
  have h := Body.at_run (W := W) (Gv fx d g) sBody sBody_inj (g.ra 0) (g.ra 1) (g.ra 2) (g.ra 3)
    (g.ru 0) (g.ru 1) (g.ru 2) (g.ru 3) (g.rv 0) (g.rv 1) (g.rv 2) (g.rv 3) g.f g.cnt g.fl
    (by
      intro j
      fin_cases j
      · exact hfx3
      · rfl
      · exact hfx5
      all_goals rfl)
    hW (by omega) (by omega) (by omega) (by omega) (by simp only [rec] at hgf; omega) (by omega)
  have e1 : sBody 1 = 4 := rfl
  have e22 : sBody 22 = 48 := rfl
  have e23 : sBody 23 = 49 := rfl
  rw [e1, e22, e23, up_fl, up_F, up_C] at h
  exact h

theorem bodyS_keeps : Keeps 4 bodyS := by
  intro g j _
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem bodyS_inR (g : GS) (hg : InR d g) : InR d (bodyS g) := hg

theorem bodyS_f (g : GS) : (bodyS g).f = g.f + selMag ((List.ofFn (rec g)).take ((3 : Fin 4).val + 1)) := by
  show g.f + selMag [rec g 0, rec g 1, rec g 2, rec g 3] = g.f + selMag ((List.ofFn (rec g)).take 4)
  rw [take4_rec]

theorem bodyS_cnt (g : GS) : (bodyS g).cnt = g.cnt + 1 := rfl

end Body

/-! ## The four levels -/

def loops := lev 0 (lev 1 (lev 2 (lev 3 bodyG)))

def S3 (d : Fin 4 → CD) : GS → GS := levS d 3 bodyS
def S2 (d : Fin 4 → CD) : GS → GS := levS d 2 (S3 d)
def S1 (d : Fin 4 → CD) : GS → GS := levS d 1 (S2 d)
def loopS (d : Fin 4 → CD) : GS → GS := levS d 0 (S1 d)

def Φ3 (d : Fin 4 → CD) : List Rec → ℕ := up selMag (tab (d 3))
def Φ2 (d : Fin 4 → CD) : List Rec → ℕ := up (Φ3 d) (tab (d 2))
def Φ1 (d : Fin 4 → CD) : List Rec → ℕ := up (Φ2 d) (tab (d 1))

def Ψ3 (d : Fin 4 → CD) : ℕ := (tab (d 3)).length * 1
def Ψ2 (d : Fin 4 → CD) : ℕ := (tab (d 2)).length * Ψ3 d
def Ψ1 (d : Fin 4 → CD) : ℕ := (tab (d 1)).length * Ψ2 d

def loopsCost (W : ℕ) (d : Fin 4 → CD) : ℕ :=
  levCost W (d 0) (levCost W (d 1) (levCost W (d 2) (levCost W (d 3) (nB W))))

section Levels
variable (d : Fin 4 → CD)

theorem S3_keeps : Keeps ((2 : Fin 4).val + 1) (S3 d) := levS_keeps d 3 bodyS bodyS_keeps
theorem S2_keeps : Keeps ((1 : Fin 4).val + 1) (S2 d) := levS_keeps d 2 (S3 d) (S3_keeps d)
theorem S1_keeps : Keeps ((0 : Fin 4).val + 1) (S1 d) := levS_keeps d 1 (S2 d) (S2_keeps d)

theorem S3_inR (g : GS) (hg : InR d g) : InR d (S3 d g) :=
  levS_inR d 3 bodyS bodyS_keeps (bodyS_inR d) g hg
theorem S2_inR (g : GS) (hg : InR d g) : InR d (S2 d g) :=
  levS_inR d 2 (S3 d) (S3_keeps d) (S3_inR d) g hg
theorem S1_inR (g : GS) (hg : InR d g) : InR d (S1 d g) :=
  levS_inR d 1 (S2 d) (S2_keeps d) (S2_inR d) g hg

theorem S3_f (g : GS) : (S3 d g).f = g.f + Φ3 d ((List.ofFn (rec g)).take ((2 : Fin 4).val + 1)) :=
  levS_f d 3 bodyS bodyS_keeps selMag 1 bodyS_f bodyS_cnt g
theorem S3_cnt (g : GS) : (S3 d g).cnt = g.cnt + Ψ3 d :=
  levS_cnt d 3 bodyS bodyS_keeps selMag 1 bodyS_f bodyS_cnt g
theorem S2_f (g : GS) : (S2 d g).f = g.f + Φ2 d ((List.ofFn (rec g)).take ((1 : Fin 4).val + 1)) :=
  levS_f d 2 (S3 d) (S3_keeps d) (Φ3 d) (Ψ3 d) (S3_f d) (S3_cnt d) g
theorem S2_cnt (g : GS) : (S2 d g).cnt = g.cnt + Ψ2 d :=
  levS_cnt d 2 (S3 d) (S3_keeps d) (Φ3 d) (Ψ3 d) (S3_f d) (S3_cnt d) g
theorem S1_f (g : GS) : (S1 d g).f = g.f + Φ1 d ((List.ofFn (rec g)).take ((0 : Fin 4).val + 1)) :=
  levS_f d 1 (S2 d) (S2_keeps d) (Φ2 d) (Ψ2 d) (S2_f d) (S2_cnt d) g
theorem S1_cnt (g : GS) : (S1 d g).cnt = g.cnt + Ψ1 d :=
  levS_cnt d 1 (S2 d) (S2_keeps d) (Φ2 d) (Ψ2 d) (S2_f d) (S2_cnt d) g

theorem up4 (T0 T1 T2 T3 : List Rec) :
    up (up (up (up selMag T3) T2) T1) T0 [] = nestedSum T0 T1 T2 T3 selMag := by
  simp only [up, nestedSum, List.nil_append, List.cons_append, List.singleton_append]

/-- **The loops' `F`.** -/
theorem loopS_f (g : GS) :
    (loopS d g).f = g.f + nestedSum (tab (d 0)) (tab (d 1)) (tab (d 2)) (tab (d 3)) selMag := by
  have h := levS_f d 0 (S1 d) (S1_keeps d) (Φ1 d) (Ψ1 d) (S1_f d) (S1_cnt d) g
  rw [show loopS d g = levS d 0 (S1 d) g from rfl, h, ← up4]
  rfl

/-- **The loops' `CNT`.** -/
theorem loopS_cnt (g : GS) :
    (loopS d g).cnt = g.cnt + (tab (d 0)).length * ((tab (d 1)).length * ((tab (d 2)).length *
      ((tab (d 3)).length * 1))) :=
  levS_cnt d 0 (S1 d) (S1_keeps d) (Φ1 d) (Ψ1 d) (S1_f d) (S1_cnt d) g

end Levels

/-! ## The run -/

section Run
variable {W : ℕ} (fx : Fin 60 → TS) (d : Fin 4 → CD)

theorem loops_run (hfx3 : fx 3 = .ruler) (hfx5 : fx 5 = .reg 0) (hW : 1 ≤ W) (R : ℕ) (hR : 4 * R + 11 ≤ W)
    (hfit : ∀ j, Fits W (d j)) (hrec : ∀ (j : Fin 4) (x : Rec), x ∈ tab (d j) → recMag x < 2 ^ R)
    (Fmax Cmax : ℕ) (hF : Fmax < 2 ^ W) (hC : Cmax < 2 ^ W) (g : GS) (hg : InR d g)
    (hFg : g.f + nestedSum (tab (d 0)) (tab (d 1)) (tab (d 2)) (tab (d 3)) selMag ≤ Fmax)
    (hCg : g.cnt + (tab (d 0)).length * ((tab (d 1)).length * ((tab (d 2)).length *
      ((tab (d 3)).length * 1))) ≤ Cmax) :
    LRuns W loops (loopsCost W d) (Gv fx d g) (Gv fx d (loopS d g)) := by
  have h3 : ∀ g', InvAt d Fmax Cmax ((2 : Fin 4).val + 1) (Φ3 d) (Ψ3 d) g' →
      LRuns W (lev 3 bodyG) (levCost W (d 3) (nB W)) (Gv fx d g') (Gv fx d (S3 d g')) := by
    intro g' hg'
    exact lev_run fx d 3 hfx3 hfx5 bodyG bodyS (nB W) Fmax Cmax selMag 1 (hfit 3)
      (body_run fx d hfx3 hfx5 hW R Fmax Cmax hR hrec hF hC) bodyS_f bodyS_cnt bodyS_keeps (bodyS_inR d) g' hg'
  have h2 : ∀ g', InvAt d Fmax Cmax ((1 : Fin 4).val + 1) (Φ2 d) (Ψ2 d) g' →
      LRuns W (lev 2 (lev 3 bodyG)) (levCost W (d 2) (levCost W (d 3) (nB W))) (Gv fx d g') (Gv fx d (S2 d g')) := by
    intro g' hg'
    exact lev_run fx d 2 hfx3 hfx5 (lev 3 bodyG) (S3 d) _ Fmax Cmax (Φ3 d) (Ψ3 d) (hfit 2) h3 (S3_f d) (S3_cnt d)
      (S3_keeps d) (S3_inR d) g' hg'
  have h1 : ∀ g', InvAt d Fmax Cmax ((0 : Fin 4).val + 1) (Φ1 d) (Ψ1 d) g' →
      LRuns W (lev 1 (lev 2 (lev 3 bodyG))) (levCost W (d 1) (levCost W (d 2) (levCost W (d 3) (nB W))))
        (Gv fx d g') (Gv fx d (S1 d g')) := by
    intro g' hg'
    exact lev_run fx d 1 hfx3 hfx5 (lev 2 (lev 3 bodyG)) (S2 d) _ Fmax Cmax (Φ2 d) (Ψ2 d) (hfit 1) h2 (S2_f d)
      (S2_cnt d) (S2_keeps d) (S2_inR d) g' hg'
  have e : up (Φ1 d) (tab (d 0)) ((List.ofFn (rec g)).take (0 : Fin 4).val) =
      nestedSum (tab (d 0)) (tab (d 1)) (tab (d 2)) (tab (d 3)) selMag := by
    rw [← up4]
    rfl
  refine lev_run fx d 0 hfx3 hfx5 (lev 1 (lev 2 (lev 3 bodyG))) (S1 d) _ Fmax Cmax (Φ1 d) (Ψ1 d) (hfit 0) h1
    (S1_f d) (S1_cnt d) (S1_keeps d) (S1_inR d) g ⟨hg, fun j hj => absurd hj (by simp), ?_, hCg⟩
  rw [e]
  exact hFg

end Run

end Lev

end
end NearCubicWires.PacketsMeta

