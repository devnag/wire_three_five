import Proof.Wire_3_5.Primitive.SeedFix.C4HfA

/-! # The HASH child family, part 2: unframing a list of kept words

`filt:soft`, P3:2253-2290: the child's working Hb bank, word by word: `copiesW ks ws js` unframes each kept stream
`ks j` onto its working stream `ws j`, `j ∈ js` (**`copies_spec`**; the other streams' words and heads unchanged).

Paper quantity of the main type: the Hb bank's words at a child. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

theorem uSt_st_other (σ : WState ns nr) (s d : Fin (ns + 1)) (u : List Bool) (i : Fin (ns + 1)) (hi : i ≠ d) :
    (uSt σ s d u).st i = σ.st i := by
  show Function.update σ.st d u i = _
  rw [Function.update_of_ne hi]

theorem uSt_sh_other (σ : WState ns nr) (s d : Fin (ns + 1)) (u : List Bool) (i : Fin (ns + 1)) (hs : i ≠ s)
    (hd : i ≠ d) : (uSt σ s d u).sh i = σ.sh i := by
  show Function.update (Function.update σ.sh s (2 * u.length)) d u.length i = _
  rw [Function.update_of_ne hd, Function.update_of_ne hs]

/-- Unframe each kept stream `ks j` onto its working stream `ws j`, `j ∈ js`. -/
def copiesW (ks ws : Fin 94 → Fin (ns + 1)) : List (Fin 94) → WM ns nr
  | [] => .skip
  | j :: js => .seq (unfW (ks j) (ws j)) (copiesW ks ws js)

/-- Its step bound. -/
def copiesCost (w : Fin 94 → List Bool) : List (Fin 94) → ℕ
  | [] => 0
  | j :: js => 10 * (w j).length + 1 + 1 + copiesCost w js

/-- **The copies**: each working stream `ws j` gets the unframed `w j`; other words, other heads, the registers and
the cell unchanged. -/
theorem copies_spec (cap : ℕ) (ks ws : Fin 94 → Fin (ns + 1)) (w : Fin 94 → List Bool)
    (hks : Function.Injective ks) (hws : Function.Injective ws) (hkw : ∀ i j, ks i ≠ ws j) :
    ∀ (js : List (Fin 94)) (σ : WState ns nr), js.Nodup →
      (∀ j ∈ js, σ.st (ks j) = frame (w j) ∧ σ.sh (ks j) = 0 ∧ σ.st (ws j) = [] ∧ σ.sh (ws j) = 0) →
      ∃ τ : WState ns nr, WExec cap (copiesW ks ws js) σ τ (copiesCost w js) ∧ (∀ j ∈ js, τ.st (ws j) = w j) ∧
        (∀ i, (∀ j ∈ js, i ≠ ws j) → τ.st i = σ.st i) ∧
        (∀ i, (∀ j ∈ js, i ≠ ws j ∧ i ≠ ks j) → τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], σ, _, _ => ⟨σ, WExec.skip (cap := cap) σ, fun j hj => absurd hj List.not_mem_nil, fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl⟩
  | j :: js, σ, hnd, hin => by
    obtain ⟨hj1, hj2, hj3, hj4⟩ := hin j (List.mem_cons_self)
    have hsd : ks j ≠ ws j := hkw j j
    have t1 := unf_spec cap σ (ks j) (ws j) hsd (w j) hj1 hj2 hj3 hj4
    set σ1 := uSt σ (ks j) (ws j) (w j) with hσ1
    have hnd' := (List.nodup_cons.mp hnd)
    have hin' : ∀ j' ∈ js, σ1.st (ks j') = frame (w j') ∧ σ1.sh (ks j') = 0 ∧ σ1.st (ws j') = [] ∧
        σ1.sh (ws j') = 0 := by
      intro j' hj'
      have hne : j' ≠ j := fun e => hnd'.1 (e ▸ hj')
      obtain ⟨a1, a2, a3, a4⟩ := hin j' (List.mem_cons_of_mem _ hj')
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hσ1, uSt_st_other _ _ _ _ _ (hkw j' j)]; exact a1
      · rw [hσ1, uSt_sh_other _ _ _ _ _ (fun e => hne (hks e)) (hkw j' j)]; exact a2
      · rw [hσ1, uSt_st_other _ _ _ _ _ (fun e => hne (hws e))]; exact a3
      · rw [hσ1, uSt_sh_other _ _ _ _ _ (fun e => hkw j j' e.symm) (fun e => hne (hws e))]; exact a4
    obtain ⟨τ, t2, h1, h2, h3, h4, h5⟩ := copies_spec cap ks ws w hks hws hkw js σ1 hnd'.2 hin'
    refine ⟨τ, WExec.cast cap (WExec.seq t1 t2) rfl (by simp only [copiesCost]; omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro j' hj'
      rcases List.mem_cons.mp hj' with e | hj'
      · subst e
        have : τ.st (ws j') = σ1.st (ws j') := h2 _ (fun j'' hj'' e => hnd'.1 (by
          have := hws e; rw [← this] at hj''; exact hj''))
        rw [this, hσ1, uSt_st_d]
      · exact h1 j' hj'
    · intro i hi
      rw [h2 i (fun j' hj' => hi j' (List.mem_cons_of_mem _ hj')), hσ1,
        uSt_st_other _ _ _ _ _ (hi j List.mem_cons_self)]
    · intro i hi
      rw [h3 i (fun j' hj' => hi j' (List.mem_cons_of_mem _ hj')), hσ1,
        uSt_sh_other _ _ _ _ _ (hi j List.mem_cons_self).2 (hi j List.mem_cons_self).1]
    · rw [h4]; rfl
    · rw [h5]; rfl

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
