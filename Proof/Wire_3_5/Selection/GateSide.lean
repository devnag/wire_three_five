import Proof.Wire_3_5.Selection.GateLayout

/-! # C1.4: one half's keys for one join (P3:1339-1346)

Paper: "Enumerate each half's score vectors" (P3:1344-1345). One half's contribution to a join's key stream: the
enumeration (`enumP`) of the point bodies (`ptBody`) with the join's emitter. This module states it on a ready
state (`SideReady`: the words at `0`, the weight table, the counts, the emitters' environment) as a `kst` step: the key
stream gains `(range nu).flatMap (u ↦ (range nx).flatMap (x ↦ f (min a a') (max a a')))`, the routine's words
`a = aW …`, `a' = aW' …`. Main declarations: `EmitHyp` (what the join's emitter must do), `SideReady`, `aW`, `aW'`,
**`side_spec`**. Paper quantity: one half's tagged keys for a join. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.SelectionMachine.Gate (hh)

variable {ns nr : ℕ}

/-- The routine's left/right word of a point `(u, x)`: the running sum over the half if the point passes the coset
test, else `init`. -/
def aW (P : StarParams) (recs : List (Bool × ℕ)) (ini o fr N x : ℕ) : ℕ :=
  if okB x.testBit P.b P.s o N (hh P) then (accC ini (zAt recs) x.testBit (hh P * P.b + fr)).toNat else ini

/-- The flipped word. -/
def aW' (P : StarParams) (recs : List (Bool × ℕ)) (ini o fr N u x : ℕ) : ℕ :=
  if okB x.testBit P.b P.s o N (hh P) then
    (accC ini (zAt recs) (fun p => xor (x.testBit p) (Gate.flipL P u p)) (hh P * P.b + fr)).toNat else ini

/-- **What a join's emitter must do**: from either order of the two key words (`S 6`/`S 7`, counters `CA`/`CA'`), on
any state meeting `cond`, append `f lo hi` to the key stream. -/
def EmitHyp (cap W V : ℕ) (S : Fin 12 → Fin (ns + 1)) (K : Fin (ns + 1)) (CK CA CA' : Fin nr)
    (EM : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (cond : WState ns nr → Prop)
    (f : ℕ → ℕ → List Bool) (c : ℕ) : Prop :=
  ∀ (σ : WState ns nr) (L out : List Bool) (vlo vhi : ℕ) (lo hi : Fin (ns + 1)) (Clo Chi : Fin nr),
    ((lo = S 6 ∧ hi = S 7 ∧ Clo = CA ∧ Chi = CA') ∨ (lo = S 7 ∧ hi = S 6 ∧ Clo = CA' ∧ Chi = CA)) →
    cond σ → NumOn σ lo W vlo → NumOn σ hi W vhi → σ.val Clo = 0 → σ.val Chi = 0 → vlo ≤ vhi →
    vhi < 2 ^ (V + 1) → out.length + 4 * W + 8 ≤ cap →
    WExec cap (EM lo hi Clo Chi) (kst σ K CK L out) (kst σ K CK L (out ++ f vlo vhi)) c

theorem flatMap_len_le {α : Type} (g : ℕ → List α) (B : ℕ) (hg : ∀ i, (g i).length ≤ B) :
    ∀ n, ((List.range n).flatMap g).length ≤ n * B
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append]
    have := flatMap_len_le g B hg n
    have h2 := hg n
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    nlinarith

theorem prefix_bound (u nu x nx B : ℕ) (hu : u < nu) (hx : x < nx) :
    u * (nx * B) + x * B + B ≤ nu * nx * B := by
  have h1 : u * nx + x + 1 ≤ nu * nx := by
    have := Nat.mul_le_mul_right nx (show u + 1 ≤ nu by omega)
    rw [add_one_mul] at this; omega
  have h2 := Nat.mul_le_mul_right B h1
  have e : (u * nx + x + 1) * B = u * (nx * B) + x * B + B := by ring
  omega

theorem wsets_same (σ : WState ns nr) (i : Fin (ns + 1)) : σ.sets i (σ.st i) = σ := by
  apply WState.eq
  · rfl
  · funext j; simp only [WState.sets_st, Function.update_apply]; split_ifs with h
    · subst h; rfl
    · rfl
  · rfl
  · rfl

section Side
variable (P : StarParams) {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr}
  (hQ : Function.Injective Q)
variable (cap W V : ℕ) (σ : WState ns nr) {K : Fin (ns + 1)} {CK CA CA' : Fin nr} (L : List Bool)
variable (hK : ∀ k : Fin 12, K ≠ S k) (hCK : ∀ i : Fin 20, CK ≠ Q i) (hCA : ∀ i : Fin 20, CA ≠ Q i)
  (hCA' : ∀ i : Fin 20, CA' ≠ Q i)
include hS hQ hK hCK hCA hCA'

/-- The routine's zero state is the state itself. -/
theorem mkP_self (s : ℕ) (hsh : ∀ k : Fin 12, k.val < 4 → σ.sh (S k) = 0)
    (hw4 : σ.st (S 4) = frame (binary s 0)) (hw5 : σ.st (S 5) = frame (binary s 0))
    (hw6 : σ.st (S 6) = frame (binary W 0)) (hw7 : σ.st (S 7) = frame (binary W 0))
    (hw8 : σ.st (S 8) = frame (binary W 0)) (hq : ∀ i : Fin 20, 2 ≤ i.val → i.val < 9 → σ.val (Q i) = 0) :
    mkP S Q s W σ 0 0 0 0 0 0 0 0 0 0 0 0 = σ := by
  apply WState.eq
  · funext j; simp only [mkP]
    split_ifs with h0 h3 h1 h2 <;> (try subst_vars) <;> first | rfl | (symm; exact hsh _ (by decide))
  · funext j; simp only [mkP]
    split_ifs <;> subst_vars <;> first | rfl | (symm; assumption)
  · funext j; simp only [mkP]
    split_ifs <;> subst_vars <;> first | rfl | (symm; exact hq _ (by decide) (by decide))
  · rfl

/-- **One half's keys for a join**: on a ready state, the enumeration of the point bodies appends, `u` outer and `x`
inner, `f (min a a') (max a a')` for the routine's words of each point. -/
theorem side_spec (EM : Fin (ns + 1) → Fin (ns + 1) → Fin nr → Fin nr → WM ns nr) (cond : WState ns nr → Prop)
    (f : ℕ → ℕ → List Bool) (cE : ℕ) (hEm : EmitHyp cap W V S K CK CA CA' EM cond f cE)
    (hf : ∀ a b, (f a b).length ≤ 4 * W + 2)
    (recs : List (Bool × ℕ)) (ini o fr N wx wu wn xp up nx nu : ℕ) (out : List Bool)
    (hX0 : σ.st (S 0) = frame (binary wx 0)) (hU0 : σ.st (S 1) = frame (binary wu 0))
    (hsh : ∀ k : Fin 12, k.val < 12 → σ.sh (S k) = 0)
    (hw4 : σ.st (S 4) = frame (binary P.s 0)) (hw5 : σ.st (S 5) = frame (binary P.s 0))
    (hw6 : σ.st (S 6) = frame (binary W 0)) (hw7 : σ.st (S 7) = frame (binary W 0))
    (hw8 : σ.st (S 8) = frame (binary W 0)) (hq : ∀ i : Fin 20, i.val < 9 → σ.val (Q i) = 0)
    (hN : σ.st (S 2) = frame (binary wn N)) (hT : σ.st (S 3) = tbl W recs) (hI : NumOn σ (S 9) W ini)
    (hK9 : σ.val (Q 9) = P.b) (hK10 : σ.val (Q 10) = hh P) (hK11 : σ.val (Q 11) = P.s) (hK12 : σ.val (Q 12) = fr)
    (hK13 : σ.val (Q 13) = o) (hT14 : σ.val (Q 14) = 0) (hT15 : σ.val (Q 15) = 0) (hK16 : σ.val (Q 16) = nx)
    (hT17 : σ.val (Q 17) = 0) (hK18 : σ.val (Q 18) = nu) (hT19 : σ.val (Q 19) = 0)
    (hXP : σ.st (S 10) = frame (binary wx xp)) (hUP : σ.st (S 11) = frame (binary wu up))
    (hCA0 : σ.val CA = 0) (hCA'0 : σ.val CA' = 0)
    (hcond : ∀ v1 w1 v2 w2 u x a a' wv, cond (mkP S Q P.s W ((((((σ.setv (Q 18) v1).setv (Q 19) w1).setv (Q 16) v2).setv
      (Q 17) w2).sets (S 1) (frame (binary wu u))).sets (S 0) (frame (binary wx x))) 0 0 0 0 0 0 a a' 0 0 0 wv))
    (hL : hh P * P.b + fr ≤ recs.length) (hLx : hh P * P.b + fr ≤ wx) (hLu : P.s * hh P ≤ wu)
    (hLn : P.s * (o + hh P) ≤ wn) (hnx : nx < 2 ^ wx) (hnu : nu < 2 ^ wu)
    (hR : ∀ (c : ℕ → Bool) (Pp : ℕ), Pp ≤ hh P * P.b + fr → 0 ≤ accC ini (zAt recs) c Pp ∧
      accC ini (zAt recs) c Pp < 2 ^ W)
    (hkey : ∀ u x, aW P recs ini o fr N x < 2 ^ (V + 1) ∧ aW' P recs ini o fr N u x < 2 ^ (V + 1))
    (hini : ini < 2 ^ W)
    (hcap : 2 * P.s + 1 ≤ cap) (hcapW : 2 * W + 1 ≤ cap) (hcapT : (hh P * P.b + fr) * (2 * W + 2) ≤ cap)
    (hcapX : 2 * (hh P * P.b + fr) ≤ cap) (hcapb : P.b ≤ cap) (hcaph : hh P ≤ cap) (hcapf : fr ≤ cap)
    (hcapo : o ≤ cap) (hcapU : 2 * (P.s * hh P) ≤ cap) (hcapN : 2 * (P.s * (o + hh P)) ≤ cap) (hcu : nu ≤ cap)
    (hcx : nx ≤ cap) (hcwx : 2 * wx + 1 ≤ cap) (hcwu : 2 * wu + 1 ≤ cap)
    (hcapK : out.length + nu * nx * (4 * W + 2) + 4 * W + 8 ≤ cap) :
    WExec cap (enumP S Q (ptBody S Q EM CA CA')) (kst σ K CK L out)
      (kst σ K CK L (out ++ (List.range nu).flatMap (fun u => (List.range nx).flatMap (fun x =>
        f (min (aW P recs ini o fr N x) (aW' P recs ini o fr N u x))
          (max (aW P recs ini o fr N x) (aW' P recs ini o fr N u x))))))
      (enumCost nu nx (pointCost (hh P) P.b fr o P.s W + cE + 200 * W + 30) wx wu) := by
  have hKn : ∀ k : Fin 12, S k ≠ K := fun k => Ne.symm (hK k)
  have hq' : ∀ i j : Fin 20, i ≠ j → Q i ≠ Q j := fun i j h => hQ.ne h
  -- the ready state is the enumeration's state at `(0, 0)`
  have hself : ∀ o' : List Bool, PS S Q P.s W σ K CK L wx wu 0 0 o' = kst σ K CK L o' := by
    intro o'
    unfold PS
    rw [← hU0, ← hX0, wsets_same, wsets_same]
    rw [mkP_kst hS hQ P.s W σ K CK L o' (fun k _ => hK k) (fun i _ _ => hCK i)]
    rw [mkP_self hS hQ W σ hK hCK hCA hCA' P.s (fun k hk => hsh k (by omega)) hw4 hw5 hw6 hw7 hw8
      (fun i _ hi => hq i hi)]
  set keys : ℕ → ℕ → List Bool := fun u x => f (min (aW P recs ini o fr N x) (aW' P recs ini o fr N u x))
    (max (aW P recs ini o fr N x) (aW' P recs ini o fr N u x)) with hkeys
  have hl := enum_spec hS hQ cap P.s W σ L hK hCK (by rw [hsh 4 (by decide)]) (by rw [hsh 5 (by decide)])
    (by rw [hsh 6 (by decide)]) (by rw [hsh 7 (by decide)]) (by rw [hsh 8 (by decide)]) (hq 0 (by decide))
    (hq 1 (by decide)) (hsh 10 (by decide)) (hsh 11 (by decide)) (ptBody S Q EM CA CA') keys
    (pointCost (hh P) P.b fr o P.s W + cE + 200 * W + 30) nu nx wx wu xp up out hK18 hK16 hT17 hT19 hXP hUP hnx hnu
    hcu hcx hcwx hcwu (by
      intro v1 w1 v2 w2 u x hu hx
      set σ' := (((σ.setv (Q 18) v1).setv (Q 19) w1).setv (Q 16) v2).setv (Q 17) w2 with hσ'
      set σb := (σ'.sets (S 1) (frame (binary wu u))).sets (S 0) (frame (binary wx x)) with hσb
      set o' := out ++ ((List.range u).flatMap (fun u' => (List.range nx).flatMap (keys u')) ++
        (List.range x).flatMap (keys u)) with ho'
      have hvq : ∀ i : Fin 20, i.val < 16 → σb.val (Q i) = σ.val (Q i) := by
        intro i hi
        simp only [hσb, hσ', WState.sets_val, WState.setv_val, Function.update_apply]
        rw [if_neg (hq' i 17 (by intro h; rw [h] at hi; simp at hi)), if_neg (hq' i 16 (by intro h; rw [h] at hi; simp at hi)),
          if_neg (hq' i 19 (by intro h; rw [h] at hi; simp at hi)), if_neg (hq' i 18 (by intro h; rw [h] at hi; simp at hi))]
      have hvr : ∀ r : Fin nr, (∀ i : Fin 20, r ≠ Q i) → σb.val r = σ.val r := by
        intro r hr
        simp only [hσb, hσ', WState.sets_val, WState.setv_val, Function.update_apply]
        rw [if_neg (hr 17), if_neg (hr 16), if_neg (hr 19), if_neg (hr 18)]
      have hshb : σb.sh = σ.sh := rfl
      have hstb : ∀ k : Fin 12, 2 ≤ k.val → σb.st (S k) = σ.st (S k) := by
        intro k hk
        simp only [hσb, hσ', WState.sets_st, WState.setv_st, Function.update_apply]
        rw [if_neg (hS.ne (by intro h; rw [h] at hk; simp at hk)), if_neg (hS.ne (by intro h; rw [h] at hk; simp at hk))]
      have hpre : o'.length + 4 * W + 8 ≤ cap := by
        have h1 := flatMap_len_le (fun u' => (List.range nx).flatMap (keys u')) (nx * (4 * W + 2))
          (fun u' => flatMap_len_le (keys u') (4 * W + 2) (fun x' => hf _ _) nx) u
        have h2 := flatMap_len_le (keys u) (4 * W + 2) (fun x' => hf _ _) x
        have h3 := prefix_bound u nu x nx (4 * W + 2) hu hx
        simp only [ho', List.length_append]
        omega
      have hb : P.b < 2 ^ P.s := by have := P.b_succ; omega
      have hx0 := hsh 0 (by decide)
      have hmain := ptBody_spec hS hQ cap P.s W σb L (fun k _ => hK k) (fun i _ => hCK i)
        (by rw [hshb]; exact hsh 4 (by decide)) (by rw [hshb]; exact hsh 5 (by decide))
        (by rw [hshb]; exact hsh 6 (by decide)) (by rw [hshb]; exact hsh 7 (by decide))
        (by rw [hshb]; exact hsh 8 (by decide)) (by rw [hvq 0 (by decide)]; exact hq 0 (by decide))
        (by rw [hvq 1 (by decide)]; exact hq 1 (by decide)) EM CA CA' f cE o' recs x wx u wu N wn (hh P) P.b fr o ini
        (Gate.flipL P u) (by simp [hσb]) (by simp [hσb, hσ', hS.ne (show (1 : Fin 12) ≠ 0 by decide)])
        (by rw [hstb 2 (by decide)]; exact hN) (by rw [hstb 3 (by decide)]; exact hT)
        ⟨by rw [hstb 9 (by decide)]; exact hI.1, by rw [hshb]; exact hI.2⟩ hb hL hLx hLu hLn
        (fun t ht j hj => flip_eq P u t j ht hj) (fun p hp => flip_free P u p hp) (fun Pp hPp => ⟨hR _ Pp hPp, hR _ Pp hPp⟩)
        hini (by rw [hvq 9 (by decide)]; exact hK9) (by rw [hvq 10 (by decide)]; exact hK10)
        (by rw [hvq 11 (by decide)]; exact hK11) (by rw [hvq 12 (by decide)]; exact hK12)
        (by rw [hvq 13 (by decide)]; exact hK13) (by rw [hvq 14 (by decide)]; exact hT14)
        (by rw [hvq 15 (by decide)]; exact hT15) hcap hcapW hcapT hcapX hcapb hcaph hcapf hcapo hcapU hcapN
        (by
          intro aF aF' hlt
          refine hEm _ L o' aF' aF (S 7) (S 6) CA' CA (Or.inr ⟨rfl, rfl, rfl, rfl⟩) (hcond _ _ _ _ _ _ _ _ _)
            ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, hshb, hsh 7 (by decide)]⟩
            ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, hshb, hsh 6 (by decide)]⟩
            (by simp [mkP, hCA', hvr CA' hCA', hCA'0]) (by simp [mkP, hCA, hvr CA hCA, hCA0]) (le_of_lt hlt)
            (hkey u x).1 hpre)
        (by
          intro aF aF' hle
          refine hEm _ L o' aF aF' (S 6) (S 7) CA CA' (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (hcond _ _ _ _ _ _ _ _ _)
            ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, hshb, hsh 6 (by decide)]⟩
            ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, hshb, hsh 7 (by decide)]⟩
            (by simp [mkP, hCA, hvr CA hCA, hCA0]) (by simp [mkP, hCA', hvr CA' hCA', hCA'0]) hle (hkey u x).2 hpre)
      exact hmain)
  rw [hself, hself] at hl
  exact hl

end Side

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
