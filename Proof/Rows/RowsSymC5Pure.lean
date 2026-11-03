import Proof.Rows.RowsKeyTop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymC5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc
open RowsConstruction.BaseLayout RowsConstruction.KeyStep
noncomputable section

/-! ## 1. Generic facts about the carry cascade `next` -/

section Generic
variable {ι : Type} [DecidableEq ι]

theorem zeroS_zero : ∀ (ls : List (Level ι)), zero ls (fun _ => 0) = fun _ => 0
  | [] => rfl
  | l :: ls => by
    simp only [zero]
    have e : Function.update (fun _ : ι => (0 : ℕ)) l.field 0 = fun _ => 0 := by
      funext x; by_cases hx : x = l.field <;> simp [hx]
    rw [e]
    exact zeroS_zero ls

end Generic

/-! ## 2. The physical five-level cascade (seed, then offsets 0..3; offset 3 innermost) -/

def o8 (c : Fin 4) : Fin 8 := ⟨c.val, by omega⟩

/-! ## 3. The SYM request's cascade is `cascS` on the padded bounds -/

/-- Generic padded bounds: `g c` below `n`, `1` from `n` to `3`. -/
def sbndN (n : ℕ) (g : Fin n → ℕ) (c : Fin 4) : ℕ := if h : c.val < n then g ⟨c.val, h⟩ else 1

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

abbrev skeys := RCFive.RowKeys.symKeys r L target
abbrev sdig := symDigitsOf r L target
abbrev sspec := cursorSpec a (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target)
/-- The seed count of the SYM family. -/
abbrev sNS : ℕ := (symSeeds r L target).length

/-- The four offset bounds: `bottomCount+1` for the request's circuits, `1` past them (radix-1 padding). -/
def sbnd (c : Fin 4) : ℕ := sbndN r.circuits.length (fun i => (r.circuits.get i).bottomCount + 1) c

/-- A key's offsets, padded by `0` to four slots (the words `RowsBaseLayout.symOffWords` frame). -/
def offN (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) : ℕ :=
  if h : c.val < r.circuits.length then k.offset ⟨c.val, h⟩ else 0

theorem sdig_off (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) :
    sdig r L target k (o8 c) = offN r L target k c := by
  unfold sdig symDigitsOf offN
  by_cases hc : c.val < r.circuits.length
  · rw [dif_pos (by simpa [o8] using hc), dif_pos hc]
    rfl
  · rw [dif_neg (by simpa [o8] using hc), dif_neg hc]
    have h5 : ¬ (o8 c).val = 5 := by simp [o8]; omega
    rw [if_neg h5]

theorem keyAt_eq (j : Nat) (hj : j < (skeys r L target).length) :
    symKeyAt r L target j = some (skeys r L target)[j] := by
  simp only [symKeyAt, Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj]

theorem skeys_ne (j : Nat) (hj : j < (skeys r L target).length) :
    PacketFamilyParent.rcKeys a (PCJd4d1d9d7d1fa4313_Production.Request.sym r four L target) ≠ [] := by
  change skeys r L target ≠ []
  intro h
  rw [h] at hj
  simp at hj

theorem sdigits : (skeys r L target).map (sdig r L target) = enum (sspec a r four L target) (fun _ => 0) :=
  sym_digits a r four L target

include a four in

theorem sym_key0 (h0 : 0 < (skeys r L target).length) :
    sdig r L target (skeys r L target)[0] = fun _ => 0 := by
  have hh := (enum_next (sspec a r four L target) (cursorSpec_wf a _)
    (cursorSpec_pos a _ (skeys_ne a r four L target 0 h0)) (fun _ => 0)).2.2
  rw [← sdigits a r four L target, zeroS_zero, List.head?_map, List.head?_eq_getElem?,
    List.getElem?_eq_getElem h0] at hh
  exact Option.some.inj hh

end Sym

/-! ## 4. The cumulative targets as a function of the padded offsets -/

/-- The four cumulative targets of padded offsets `o` for `n` circuits (`0` past the circuits). -/
def tgv (n : ℕ) (o : Fin 4 → ℕ) : Fin 4 → ℕ :=
  ![if 0 < n then o 0 else 0, if 1 < n then o 0 + o 1 + 1 else 0,
    if 2 < n then o 0 + o 1 + o 2 + 2 else 0, if 3 < n then o 0 + o 1 + o 2 + o 3 + 3 else 0]

theorem tgv_ge (n : ℕ) (o : Fin 4 → ℕ) (c : Fin 4) (hc : ¬ c.val < n) : tgv n o c = 0 := by
  fin_cases c <;> simp_all [tgv]

theorem tgv_zero (n : ℕ) (o : Fin 4 → ℕ) (h : 0 < n) : tgv n o 0 = o 0 + 0 := by
  simp [tgv, h]

theorem tgv_succ (n : ℕ) (o : Fin 4 → ℕ) (c : Fin 4) (h0 : 0 < c.val) (hc : c.val < n) :
    tgv n o c = tgv n o ⟨c.val - 1, by omega⟩ + o c + 1 := by
  fin_cases c
  · simp at h0
  all_goals (simp at hc; simp [tgv]; split_ifs <;> omega)

section Sym
variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : Nat)

include four in
/-- **The resident target of slot `c` is `tgv` of the padded offsets.** -/
theorem tg_eq (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) :
    SymVerdict.Tg r k.offset c = tgv r.circuits.length (offN r L target k) c := by
  have hN : ∀ i : ℕ, SymMeaning.offsetN r k.offset i =
      if h : i < r.circuits.length then k.offset ⟨i, h⟩ else 0 := fun i => rfl
  unfold SymVerdict.Tg SymMeaning.targetCount
  fin_cases c <;>
    simp [tgv, offN, hN, Finset.sum_range_succ] <;> split_ifs <;> omega

end Sym

/-! ## 5. The SYM master bank: two keys differ exactly at the target ports 140–143 -/

/-- Target port of slot `c` (`SymVerdict.auxP (tIdx c)`). -/
def tgtP (c : Fin 4) : Fin 254 := ⟨140 + c.val, by omega⟩

theorem tgtP_eq (c : Fin 4) : tgtP c = SymVerdict.auxP (SymVerdict.tIdx c) := by
  apply Fin.ext
  rw [SymVerdict.auxP_val]
  simp [tgtP, SymVerdict.tIdx]
  omega

theorem tgtP_ne109 (c : Fin 4) : tgtP c ≠ 109 := by
  intro h
  have := congrArg Fin.val h
  simp [tgtP] at this
  omega

section Sym
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The SYM counter width `T+3`. -/
abbrev sw : Nat := symT a r four L target + 3

/-- The four target updates of a master bank. -/
def tupd (M : Fin 254 → List Bool) (w : Nat) (t : Fin 4 → Nat) : Fin 254 → List Bool :=
  Function.update (Function.update (Function.update (Function.update M (tgtP 0) (fb w (t 0))) (tgtP 1) (fb w (t 1)))
    (tgtP 2) (fb w (t 2))) (tgtP 3) (fb w (t 3))

theorem tgtP_key (c : Fin 4) : tgtP c ∈ symKeySet := by
  fin_cases c <;> decide

/-- The master at a target port. -/
theorem masters_tgt (R : Nat) (k : RCFive.RowKeys.SymKey r L target) (c : Fin 4) :
    symMasters a r four L target R k (tgtP c) = fb (sw a r four L target) (SymVerdict.Tg r k.offset c) := by
  simp only [symMasters, if_neg (tgtP_ne109 c)]
  rw [keyPad_key R (tgtP_key c), tgtP_eq]
  unfold SymVerdict.input
  rw [SymVerdict.layout_aux]
  fin_cases c <;> rfl

/-! ## 6. Numeric side conditions -/

theorem tg_lt (k : RCFive.RowKeys.SymKey r L target) (hk : k ∈ skeys r L target) (c : Fin 4) :
    SymVerdict.Tg r k.offset c < 2^(sw a r four L target) :=
  (sym_spec a r four L target k.offset (sym_offset_le r L target k hk)).2.2.2.1 c

theorem sw_fits (k : RCFive.RowKeys.SymKey r L target) :
    2 * sw a r four L target + 1 ≤ symRes r.q (symT a r four L target) := by
  have h := sym_hml a r four L target (symRes r.q (symT a r four L target)) (symR_le_res _ _) k (tgtP 0)
  rw [masters_tgt, fb, frame_length, SignedSortKey.binary_length] at h
  exact h

end Sym

end
end RowsConstruction.SymC5
