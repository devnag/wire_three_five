import Proof.Wire_3_5.Primitive.SeedFix.C4HfE

/-! # The HASH child family, part 6: the prep program on the Hb unit's streams

`filt:soft`, P3:2255-2262: the Hb unit's prep (C5's word programs on 189 streams: the 94 kept framed words, the prefix,
the 94 working tapes; two registers): unframe the kept words onto the working tapes but `80` and `93`, write the prefix
word `frame (p ++ [b])` on `80` (counting `plen = |p| + 1`), and the free-bit ruler on `93` (**`prep_spec`**: the working
tapes hold the Hb bank `hb0` at the child prefix `(plen, listNum (p ++ [b]))`).

Paper quantity of the main type: the Hb printer's bank at the child prefix `p ++ [b]`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- The kept word `j`'s stream. -/
def kS (j : Fin 94) : Fin (188 + 1) := ⟨j.val, by omega⟩
/-- The prefix stream. -/
def pS : Fin (188 + 1) := ⟨94, by omega⟩
/-- The working tape `j`'s stream. -/
def wS (j : Fin 94) : Fin (188 + 1) := ⟨95 + j.val, by omega⟩
def r0 : Fin 2 := 0
def r1 : Fin 2 := 1

theorem kS_inj : Function.Injective kS := fun i j h => Fin.ext (by have := congrArg Fin.val h; simpa [kS] using this)
theorem wS_inj : Function.Injective wS := fun i j h => Fin.ext (by have := congrArg Fin.val h; simp [wS] at this; omega)
theorem kS_ne_wS (i j : Fin 94) : kS i ≠ wS j := fun h => by
  have := congrArg Fin.val h; simp [kS, wS] at this; have := i.isLt; omega

/-- The copied tapes: all but `80` and `93`. -/
def jsC : List (Fin 94) := (List.finRange 94).filter fun j => j.val ≠ 80 ∧ j.val ≠ 93

theorem jsC_nodup : jsC.Nodup := (List.nodup_finRange 94).filter _

theorem mem_jsC (j : Fin 94) : j ∈ jsC ↔ j.val ≠ 80 ∧ j.val ≠ 93 := by
  simp [jsC]

/-- **The prep program** of the child bit `b`. -/
def prepW (b : Bool) : WM 188 2 :=
  .seq (copiesW kS wS jsC) (.seq (pfxW pS (wS ⟨80, by omega⟩) r0 b) (skipW (kS ⟨93, by omega⟩) (wS ⟨93, by omega⟩) r0 r1))

/-- The unit's entry streams: the framed kept words, the framed prefix, blank working tapes. -/
def prepIn (KW : Fin 94 → List Bool) (p : List Bool) : WState 188 2 :=
  ⟨fun _ => 0, fun i => if h : i.val < 94 then frame (KW ⟨i.val, h⟩) else if i.val = 94 then frame p else [],
    fun _ => 0, false⟩

theorem pad_drop (cC T k : ℕ) (hk : k ≤ T) (hT : T ≤ cC) :
    (ZeroPadding.pad cC (List.replicate T true)).drop k ++ List.replicate k false =
      ZeroPadding.pad cC (List.replicate (T - k) true) := by
  unfold ZeroPadding.pad
  rw [List.drop_append_of_le_length (by simp; omega), List.drop_replicate]
  simp only [List.length_replicate, List.append_assoc, List.replicate_append_replicate]
  congr 2
  omega

section Acc
variable {ns nr : ℕ} (σ : WState ns nr)

theorem pfxOut_st_ne (P d : Fin (ns + 1)) (r : Fin nr) (p : List Bool) (b : Bool) (i : Fin (ns + 1)) (h : i ≠ d) :
    (pfxOut σ P d r p b).st i = σ.st i := Function.update_of_ne h _ _
theorem pfxOut_st_d (P d : Fin (ns + 1)) (r : Fin nr) (p : List Bool) (b : Bool) :
    (pfxOut σ P d r p b).st d = frame (p ++ [b]) := Function.update_self _ _ _
theorem pfxOut_sh_ne (P d : Fin (ns + 1)) (r : Fin nr) (p : List Bool) (b : Bool) (i : Fin (ns + 1)) (h1 : i ≠ P)
    (h2 : i ≠ d) : (pfxOut σ P d r p b).sh i = σ.sh i := by
  show Function.update (Function.update σ.sh P _) d _ i = _
  rw [Function.update_of_ne h2, Function.update_of_ne h1]
theorem pfxOut_val_r (P d : Fin (ns + 1)) (r : Fin nr) (p : List Bool) (b : Bool) :
    (pfxOut σ P d r p b).val r = p.length + 1 := Function.update_self _ _ _
theorem pfxOut_val_ne (P d : Fin (ns + 1)) (r : Fin nr) (p : List Bool) (b : Bool) (r' : Fin nr) (h : r' ≠ r) :
    (pfxOut σ P d r p b).val r' = σ.val r' := Function.update_of_ne h _ _
theorem skipOut_st_d (s d : Fin (ns + 1)) (r0 r1 : Fin nr) (k : ℕ) (w : List Bool) :
    (skipOut σ s d r0 r1 k w).st d = w.drop k ++ List.replicate k false := Function.update_self _ _ _
theorem skipOut_st_ne (s d : Fin (ns + 1)) (r0 r1 : Fin nr) (k : ℕ) (w : List Bool) (i : Fin (ns + 1)) (h : i ≠ d) :
    (skipOut σ s d r0 r1 k w).st i = σ.st i := Function.update_of_ne h _ _

end Acc

/-- The prep's step count. -/
def prepCost (KW : Fin 94 → List Bool) (p : List Bool) : ℕ :=
  copiesCost KW jsC + 1 + ((18 * p.length + 20) + 1 + (19 * (KW ⟨93, by omega⟩).length + 3))

/-- **The prep**: the working tapes hold the Hb bank at the child prefix `p ++ [b]`; the kept words and the prefix
stay. -/
theorem prep_spec (cap : ℕ) (D : HashData) (c : HbCaps) (p : List Bool) (b : Bool)
    (hplen : p.length + 1 ≤ 2 * D.MP.t * D.MP.ell0) (hcC : 2 * D.MP.t * D.MP.ell0 ≤ c.cC) (hcap : p.length + 2 < cap) :
    ∃ τ : WState 188 2, WExec cap (prepW b) (prepIn (hb0 (hbX D c 0 0)) p) τ
        (prepCost (hb0 (hbX D c 0 0)) p) ∧
      (∀ j, τ.st (wS j) = hb0 (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))) j) ∧
      (∀ i : Fin (188 + 1), i.val < 95 → τ.st i = (prepIn (hb0 (hbX D c 0 0)) p).st i) := by
  set KW := hb0 (hbX D c 0 0) with hKW
  set σ0 := prepIn KW p with hσ0
  have hwSv : ∀ i j, wS i = wS j → i.val = j.val := fun i j e => congrArg Fin.val (wS_inj e)
  have hwS80 : ∀ j ∈ jsC, wS ⟨80, by omega⟩ ≠ wS j := fun j hj e => by
    have h1 := (mem_jsC j).mp hj; have := hwSv _ _ e; simp at this; omega
  have hwS93 : ∀ j ∈ jsC, wS ⟨93, by omega⟩ ≠ wS j := fun j hj e => by
    have h1 := (mem_jsC j).mp hj; have := hwSv _ _ e; simp at this; omega
  have hkS93 : ∀ j ∈ jsC, kS ⟨93, by omega⟩ ≠ kS j := fun j hj e => by
    have h1 := (mem_jsC j).mp hj; have := congrArg Fin.val (kS_inj e); simp at this; omega
  have hpS_w : ∀ j, pS ≠ wS j := fun j e => by have := congrArg Fin.val e; simp [pS, wS] at this; omega
  have hpS_k : ∀ j, pS ≠ kS j := fun j e => by
    have := congrArg Fin.val e; simp [pS, kS] at this; have := j.isLt; omega
  -- 1: the copies
  have hin : ∀ j ∈ jsC, σ0.st (kS j) = frame (KW j) ∧ σ0.sh (kS j) = 0 ∧ σ0.st (wS j) = [] ∧ σ0.sh (wS j) = 0 := by
    intro j _
    refine ⟨?_, rfl, ?_, rfl⟩
    · show (if h : (kS j).val < 94 then frame (KW ⟨(kS j).val, h⟩) else _) = _
      rw [dif_pos (by simp [kS])]; rfl
    · show (if h : (wS j).val < 94 then _ else if (wS j).val = 94 then _ else []) = []
      rw [dif_neg (by simp only [wS]; omega), if_neg (by simp only [wS]; omega)]
  obtain ⟨τ1, t1, g1, g2, g3, g4, g5⟩ := copies_spec cap kS wS KW kS_inj wS_inj kS_ne_wS jsC σ0 jsC_nodup hin
  -- 2: the prefix word
  have p1 : τ1.st pS = frame p := by
    rw [g2 pS (fun j _ => hpS_w j)]
    simp [hσ0, prepIn, pS]
  have p2 : τ1.sh pS = 0 := by rw [g3 pS (fun j _ => ⟨hpS_w j, hpS_k j⟩)]; rfl
  have p3 : τ1.st (wS ⟨80, by omega⟩) = [] := by
    rw [g2 _ hwS80]
    simp [hσ0, prepIn, wS]
  have p4 : τ1.sh (wS ⟨80, by omega⟩) = 0 := by
    rw [g3 _ (fun j hj => ⟨hwS80 j hj, fun e => kS_ne_wS j _ e.symm⟩)]; rfl
  have p5 : τ1.val r0 = 0 := by rw [g4]; rfl
  have hPd : pS ≠ wS ⟨80, by omega⟩ := hpS_w _
  have t2 := pfx_spec cap τ1 pS (wS ⟨80, by omega⟩) hPd r0 p b p1 p2 p3 p4 p5 (by omega)
  -- 3: the free-bit ruler
  have hk93 : kS ⟨93, by omega⟩ ≠ wS ⟨80, by omega⟩ := kS_ne_wS _ _
  have hw9380 : wS ⟨93, by omega⟩ ≠ wS ⟨80, by omega⟩ := fun e => by have := hwSv _ _ e; simp at this
  have q1 : (pfxOut τ1 pS (wS ⟨80, by omega⟩) r0 p b).st (kS ⟨93, by omega⟩) = frame (KW ⟨93, by omega⟩) := by
    rw [pfxOut_st_ne _ _ _ _ _ _ _ hk93, g2 _ (fun j _ => kS_ne_wS _ _)]
    simp [hσ0, prepIn, kS]
  have q2 : (pfxOut τ1 pS (wS ⟨80, by omega⟩) r0 p b).sh (kS ⟨93, by omega⟩) = 0 := by
    rw [pfxOut_sh_ne _ _ _ _ _ _ _ (fun e => hpS_k _ e.symm) hk93,
      g3 _ (fun j hj => ⟨kS_ne_wS _ _, hkS93 j hj⟩)]
    rfl
  have q3 : (pfxOut τ1 pS (wS ⟨80, by omega⟩) r0 p b).st (wS ⟨93, by omega⟩) = [] := by
    rw [pfxOut_st_ne _ _ _ _ _ _ _ hw9380, g2 _ hwS93]
    simp [hσ0, prepIn, wS]
  have q4 : (pfxOut τ1 pS (wS ⟨80, by omega⟩) r0 p b).sh (wS ⟨93, by omega⟩) = 0 := by
    rw [pfxOut_sh_ne _ _ _ _ _ _ _ (fun e => hpS_w _ e.symm) hw9380,
      g3 _ (fun j hj => ⟨hwS93 j hj, fun e => kS_ne_wS j _ e.symm⟩)]
    rfl
  have q5 := pfxOut_val_r τ1 pS (wS ⟨80, by omega⟩) r0 p b
  have q6 : (pfxOut τ1 pS (wS ⟨80, by omega⟩) r0 p b).val r1 = 0 := by
    rw [pfxOut_val_ne _ _ _ _ _ _ _ (by decide), g4]; rfl
  have hKW93 : KW ⟨93, by omega⟩ = ZeroPadding.pad c.cC (List.replicate (2 * D.MP.t * D.MP.ell0) true) := by
    rw [hKW, hb0_93]; simp
  have hlen93 : p.length + 1 ≤ (KW ⟨93, by omega⟩).length := by
    rw [hKW93]; unfold ZeroPadding.pad; simp; omega
  have t3 := skip_spec cap _ (kS ⟨93, by omega⟩) (wS ⟨93, by omega⟩) (kS_ne_wS _ _) r0 r1 (by decide)
    (p.length + 1) (KW ⟨93, by omega⟩) q1 q2 q3 q4 q5 q6 hlen93 (by omega)
  refine ⟨_, WExec.seq t1 (WExec.seq t2 t3), ?_, ?_⟩
  · intro j
    by_cases h93 : j.val = 93
    · have e : j = ⟨93, by omega⟩ := Fin.ext h93
      rw [e, skipOut_st_d, hKW93, pad_drop _ _ _ hplen hcC, List.length_append, List.length_singleton, hb0_93]
    · rw [skipOut_st_ne _ _ _ _ _ _ _ _ (fun e => h93 (by have := hwSv _ _ e; simpa using this))]
      by_cases h80 : j.val = 80
      · have e : j = ⟨80, by omega⟩ := Fin.ext h80
        rw [e, pfxOut_st_d, hb0_80, C4Enum.binary_listNum]
      · rw [pfxOut_st_ne _ _ _ _ _ _ _ (fun e => h80 (by have := hwSv _ _ e; simpa using this)),
          g1 j ((mem_jsC j).mpr ⟨h80, h93⟩), hKW]
        exact (hb0_other D c _ _ j h80 h93).symm
  · intro i hi
    have hn93 : i ≠ wS ⟨93, by omega⟩ := fun e => by rw [e] at hi; simp [wS] at hi
    have hn80 : i ≠ wS ⟨80, by omega⟩ := fun e => by rw [e] at hi; simp [wS] at hi
    rw [skipOut_st_ne _ _ _ _ _ _ _ _ hn93, pfxOut_st_ne _ _ _ _ _ _ _ hn80,
      g2 i (fun j _ e => by rw [e] at hi; simp [wS] at hi)]

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
