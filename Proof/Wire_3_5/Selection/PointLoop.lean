import Proof.Wire_3_5.Selection.PointBody

/-! # C1.4: the enumeration of a half's points (P3:1339-1345)

Paper: "Enumerate its `2^k` error rows [...] Enumerate each half's score vectors" (P3:1339-1345). The machine's order
(`enumL`, `enumR`, in C1.4's interface): the errors counter `u` outer (word `U`, `2^(s·h)` values), the half
counter `x` inner (word `X`, `2^(bits)` values), each a width-`w` word stepped by C6's `incB` (partners `XP`, `UP`),
counted by C6's `cloop` on the counts in `Q 16`, `Q 18`. Each point runs `body`, which appends the point's keys
`keys u x` to the key stream `K`. Main declarations: `PS` (the loop's state), `enumP`, **`enum_spec`** (the key stream
gains `(range nu).flatMap (fun u => (range nx).flatMap (keys u)))`). Paper quantity: the enumeration of one half's
points, in the machine's order. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)

variable {ns nr : ℕ}

/-- **The enumeration's state** at `(u, x)`: the words `U := u`, `X := x`, the key stream holding `out`, the routine's
words at `0`. -/
def PS (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) (s W : ℕ) (σ : WState ns nr) (K : Fin (ns + 1)) (CK : Fin nr)
    (L : List Bool) (wx wu u x : ℕ) (out : List Bool) : WState ns nr :=
  mkP S Q s W (kst ((σ.sets (S 1) (frame (binary wu u))).sets (S 0) (frame (binary wx x))) K CK L out) 0 0 0 0 0 0 0 0 0 0 0 0

/-- **The enumeration**: `u` outer, `x` inner, `body` at each point. -/
def enumP (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) (body : WM ns nr) : WM ns nr :=
  .seq (cloop (Q 18) (Q 19) (.seq (cloop (Q 16) (Q 17) (.seq body (incB (S 0) (S 10) (Q 0) (Q 1))))
    (.seq (zeroB (S 0) (S 10) (Q 0) (Q 1)) (incB (S 1) (S 11) (Q 0) (Q 1))))) (zeroB (S 1) (S 11) (Q 0) (Q 1))

section Loop
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr) {K : Fin (ns + 1)} {CK : Fin nr} (L : List Bool)
variable (hK : ∀ k : Fin 12, K ≠ S k) (hCK : ∀ i : Fin 20, CK ≠ Q i)
include hS hQ hK hCK

theorem PS_setv (σ : WState ns nr) (i : Fin 20) (hi : 9 ≤ i.val) (v wx wu u x : ℕ) (out : List Bool) :
    (PS S Q s W σ K CK L wx wu u x out).setv (Q i) v = PS S Q s W (σ.setv (Q i) v) K CK L wx wu u x out := by
  unfold PS
  rw [mkP_setv hS hQ s W _ (Q i) v (fun j hj => hQ.ne (by intro h; rw [h] at hi; omega))]
  congr 1
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [kst, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
    by_cases h1 : j = CK
    · subst h1; simp [hCK i]
    · simp only [h1, if_false]
  · rfl

theorem PS_setv2 (σ : WState ns nr) (i k : Fin 20) (hi : 9 ≤ i.val) (hk : 9 ≤ k.val) (v w wx wu u x : ℕ)
    (out : List Bool) :
    ((PS S Q s W σ K CK L wx wu u x out).setv (Q i) v).setv (Q k) w =
      PS S Q s W ((σ.setv (Q i) v).setv (Q k) w) K CK L wx wu u x out := by
  rw [PS_setv hS hQ s W L hK hCK σ i hi, PS_setv hS hQ s W L hK hCK _ k hk]

variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
  (h0XP : σ0.sh (S 10) = 0) (h0UP : σ0.sh (S 11) = 0)
include h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP

theorem PS_numX (σ : WState ns nr) (wx wu u x : ℕ) (out : List Bool) :
    NumOn (PS S Q s W σ K CK L wx wu u x out) (S 0) wx x := by
  have hk := fun k => Ne.symm (hK k)
  constructor
  · simp [PS, mkP, kst, hS.eq_iff, hk]
  · simp [PS, mkP, kst, hS.eq_iff, hk]

theorem PS_numU (σ : WState ns nr) (wx wu u x : ℕ) (out : List Bool) :
    NumOn (PS S Q s W σ K CK L wx wu u x out) (S 1) wu u := by
  have hk := fun k => Ne.symm (hK k)
  constructor
  · simp [PS, mkP, kst, hS.eq_iff, hk]
  · simp [PS, mkP, kst, hS.eq_iff, hk]

theorem PS_numP (σ : WState ns nr) (hσ : σ.sh = σ0.sh) (p : Fin 12) (hp : p = 10 ∨ p = 11) (w v : ℕ)
    (hP : σ.st (S p) = frame (binary w v)) (wx wu u x : ℕ) (out : List Bool) :
    NumOn (PS S Q s W σ K CK L wx wu u x out) (S p) w v := by
  have hk := fun k => Ne.symm (hK k)
  constructor
  · rcases hp with rfl | rfl <;> simp [PS, mkP, kst, hS.eq_iff, hk, hP]
  · rcases hp with rfl | rfl <;> simp [PS, mkP, kst, hS.eq_iff, hk, hσ, h0XP, h0UP]

theorem PS_FR (σ : WState ns nr) (hF : σ.val (Q 0) = 0) (hR : σ.val (Q 1) = 0) (wx wu u x : ℕ) (out : List Bool) :
    (PS S Q s W σ K CK L wx wu u x out).val (Q 0) = 0 ∧ (PS S Q s W σ K CK L wx wu u x out).val (Q 1) = 0 := by
  have hc := fun i => Ne.symm (hCK i)
  exact ⟨by simp [PS, mkP, kst, hQ.eq_iff, hc, hF], by simp [PS, mkP, kst, hQ.eq_iff, hc, hR]⟩

theorem PS_setX (σ : WState ns nr) (wx wu u x x' : ℕ) (out : List Bool) :
    (PS S Q s W σ K CK L wx wu u x out).sets (S 0) (frame (binary wx x')) = PS S Q s W σ K CK L wx wu u x' out := by
  have hk := fun k => Ne.symm (hK k)
  unfold PS
  apply WState.eq
  · rfl
  · funext j
    simp only [mkP, kst, WState.sets_st, WState.seth_st, WState.setv_st, Function.update_apply]
    by_cases hj : j = S 0
    · subst hj; simp [hS.eq_iff, hk]
    · simp only [hj, if_false]
  · rfl
  · rfl

theorem PS_setU (σ : WState ns nr) (wx wu u u' x : ℕ) (out : List Bool) :
    (PS S Q s W σ K CK L wx wu u x out).sets (S 1) (frame (binary wu u')) = PS S Q s W σ K CK L wx wu u' x out := by
  have hk := fun k => Ne.symm (hK k)
  unfold PS
  apply WState.eq
  · rfl
  · funext j
    simp only [mkP, kst, WState.sets_st, WState.seth_st, WState.setv_st, Function.update_apply]
    by_cases hj : j = S 1
    · subst hj; simp [hS.eq_iff, hk]
    · by_cases hj0 : j = S 0
      · subst hj0; simp [hS.eq_iff, hk]
      · simp only [hj, hj0, if_false]
  · rfl
  · rfl

/-- The enumeration's cost. -/
def enumCost (nu nx c wx wu : ℕ) : ℕ :=
  nu * ((nx * ((c + 1 + (41 * wx + 7)) + 8) + 1 + 1 + (7 * nx + 1)) + 1 + (41 * wx + 7) + 1 + (41 * wu + 7) + 8) +
    1 + 1 + (7 * nu + 1) + 1 + (41 * wu + 7)

/-- **The enumeration of a half's points**: the key stream gains every point's keys, `u` outer and `x` inner; the
words `U`, `X` end at `0`. -/
theorem enum_spec (body : WM ns nr) (keys : ℕ → ℕ → List Bool) (c nu nx wx wu xp up : ℕ) (o0 : List Bool)
    (hnu : σ0.val (Q 18) = nu) (hnx : σ0.val (Q 16) = nx) (h17 : σ0.val (Q 17) = 0) (h19 : σ0.val (Q 19) = 0)
    (hXP : σ0.st (S 10) = frame (binary wx xp)) (hUP : σ0.st (S 11) = frame (binary wu up))
    (hnxw : nx < 2 ^ wx) (hnuw : nu < 2 ^ wu) (hcu : nu ≤ cap) (hcx : nx ≤ cap) (hcwx : 2 * wx + 1 ≤ cap)
    (hcwu : 2 * wu + 1 ≤ cap)
    (hbody : ∀ v1 w1 v2 w2 u x, u < nu → x < nx →
      WExec cap body (PS S Q s W ((((σ0.setv (Q 18) v1).setv (Q 19) w1).setv (Q 16) v2).setv (Q 17) w2) K CK L wx wu u x
          (o0 ++ ((List.range u).flatMap (fun u' => (List.range nx).flatMap (keys u')) ++
            (List.range x).flatMap (keys u))))
        (PS S Q s W ((((σ0.setv (Q 18) v1).setv (Q 19) w1).setv (Q 16) v2).setv (Q 17) w2) K CK L wx wu u x
          (o0 ++ ((List.range u).flatMap (fun u' => (List.range nx).flatMap (keys u')) ++
            (List.range x).flatMap (keys u)) ++ keys u x)) c) :
    WExec cap (enumP S Q body) (PS S Q s W σ0 K CK L wx wu 0 0 o0)
      (PS S Q s W σ0 K CK L wx wu 0 0 (o0 ++ (List.range nu).flatMap (fun u => (List.range nx).flatMap (keys u))))
      (enumCost nu nx c wx wu) := by
  have hq : ∀ i j : Fin 20, i ≠ j → Q i ≠ Q j := fun i j h => hQ.ne h
  -- the outer loop
  let N : WState ns nr → ℕ → WState ns nr := fun σ u =>
    PS S Q s W σ K CK L wx wu u 0 (o0 ++ (List.range u).flatMap (fun u' => (List.range nx).flatMap (keys u')))
  have hl := cloopM cap (Q 18) (Q 19) (hQ.ne (by decide)) _ N
    (fun σ j v w => PS_setv2 hS hQ s W L hK hCK σ 18 19 (by decide) (by decide) v w _ _ _ _ _) σ0 nu
    ((nx * ((c + 1 + (41 * wx + 7)) + 8) + 1 + 1 + (7 * nx + 1)) + 1 + (41 * wx + 7) + 1 + (41 * wu + 7)) hnu h19 hcu (by
      intro u hu v1 w1
      set σ1 := (σ0.setv (Q 18) v1).setv (Q 19) w1 with hσ1
      set O := o0 ++ (List.range u).flatMap (fun u' => (List.range nx).flatMap (keys u')) with hO
      have hsh1 : σ1.sh = σ0.sh := rfl
      -- the inner loop
      let M : WState ns nr → ℕ → WState ns nr := fun σ x =>
        PS S Q s W σ K CK L wx wu u x (O ++ (List.range x).flatMap (keys u))
      have hin := cloopM cap (Q 16) (Q 17) (hQ.ne (by decide)) _ M
        (fun σ j v w => PS_setv2 hS hQ s W L hK hCK σ 16 17 (by decide) (by decide) v w _ _ _ _ _) σ1 nx
        (c + 1 + (41 * wx + 7)) (by simp [hσ1, Function.update_apply, hq 16 18 (by decide), hq 16 19 (by decide), hnx])
        (by simp [hσ1, Function.update_apply, hq 17 18 (by decide), hq 17 19 (by decide), h17]) hcx (by
          intro x hx v2 w2
          set σ2 := (σ1.setv (Q 16) v2).setv (Q 17) w2 with hσ2
          have hb := hbody v1 w1 v2 w2 u x hu hx
          rw [← List.append_assoc] at hb
          have hFR := PS_FR hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ2
            (by simp [hσ2, hσ1, Function.update_apply, hq 0 16 (by decide), hq 0 17 (by decide), hq 0 18 (by decide),
              hq 0 19 (by decide), h0F])
            (by simp [hσ2, hσ1, Function.update_apply, hq 1 16 (by decide), hq 1 17 (by decide), hq 1 18 (by decide),
              hq 1 19 (by decide), h0R]) wx wu u x (O ++ (List.range x).flatMap (keys u) ++ keys u x)
          have hi := incB_spec cap wx (A := S 0) (B := S 10) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide))
            _ x xp (PS_numX hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ2 wx wu u x _)
            (PS_numP hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ2 rfl 10 (Or.inl rfl) wx xp
              (by simp [hσ2, hσ1, hXP]) wx wu u x _) hFR.1 hFR.2 (by omega) hcwx
          rw [PS_setX hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP] at hi
          have e : O ++ (List.range (x + 1)).flatMap (keys u) = O ++ (List.range x).flatMap (keys u) ++ keys u x := by
            rw [List.range_succ, List.flatMap_append]; simp
          refine WExec.cast cap (WExec.seq hb hi) ?_ le_rfl
          simp only [M, e])
      simp only [M, List.range_zero, List.flatMap_nil, List.append_nil] at hin
      have hFR1 := PS_FR hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ1
        (by simp [hσ1, Function.update_apply, hq 0 18 (by decide), hq 0 19 (by decide), h0F])
        (by simp [hσ1, Function.update_apply, hq 1 18 (by decide), hq 1 19 (by decide), h0R])
      set Rn := O ++ (List.range nx).flatMap (keys u) with hRn
      -- X := 0
      have hz := zeroB_spec cap wx (A := S 0) (B := S 10) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide))
        _ nx xp (PS_numX hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ1 wx wu u nx Rn)
        (PS_numP hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ1 hsh1 10 (Or.inl rfl) wx xp
          (by simp [hσ1, hXP]) wx wu u nx Rn) (hFR1 wx wu u nx Rn).1 (hFR1 wx wu u nx Rn).2 hcwx
      rw [PS_setX hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP] at hz
      -- U := u + 1
      have hu' := incB_spec cap wu (A := S 1) (B := S 11) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide))
        _ u up (PS_numU hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ1 wx wu u 0 Rn)
        (PS_numP hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ1 hsh1 11 (Or.inr rfl) wu up
          (by simp [hσ1, hUP]) wx wu u 0 Rn) (hFR1 wx wu u 0 Rn).1 (hFR1 wx wu u 0 Rn).2 (by omega) hcwu
      rw [PS_setU hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP] at hu'
      have e : o0 ++ (List.range (u + 1)).flatMap (fun u' => (List.range nx).flatMap (keys u')) =
          O ++ (List.range nx).flatMap (keys u) := by
        rw [hO, List.range_succ, List.flatMap_append]; simp
      refine WExec.cast cap (WExec.seq hin (WExec.seq hz hu')) ?_ (by omega)
      simp only [N, e, hRn])
  simp only [N, List.range_zero, List.flatMap_nil, List.append_nil] at hl
  set All := o0 ++ (List.range nu).flatMap (fun u => (List.range nx).flatMap (keys u)) with hAll
  -- U := 0
  have hFR0 := PS_FR hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ0 h0F h0R
  have hz := zeroB_spec cap wu (A := S 1) (B := S 11) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide))
    _ nu up (PS_numU hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ0 wx wu nu 0 All)
    (PS_numP hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP σ0 rfl 11 (Or.inr rfl) wu up hUP wx wu nu 0 All)
    (hFR0 wx wu nu 0 All).1 (hFR0 wx wu nu 0 All).2 hcwu
  rw [PS_setU hS hQ s W σ0 L hK hCK h0C h0Y h0A h0A' h0V h0F h0R h0XP h0UP] at hz
  unfold enumP enumCost
  exact WExec.cast cap (WExec.seq hl hz) rfl (by ring_nf; omega)

end Loop

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
