import Proof.Wire_3_5.UnionMachine.FrontTWPass
import Proof.Wire_3_5.UnionMachine.FrontTWFrame

/-! # C6 front, U5: the clause loop over the PCPP output's literal pairs (P3:3685-3691)

The literal list of the PCPP output word (`natListWord`, after the header and the systematic supports) is read one
pair per clause: `L₀ := literalIndex (left)`, `L₁ := literalIndex (right)` (PA's `readNatM`), then the pass's clause
body. **`clLoopT`**: from the list's start, `M` rounds append each clause's body output in clause order and conjoin
its admissibility; the literal cursor ends past the list. Paper quantity: the calls of `(tr:tests)`, clause by clause. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit NearCubicWires.WireExponent3_5.UnionMachine.FrontTWFrame
open NearCubicWires.RepairRepresentation (natWord)

variable (cap : ℕ) (src : Fin 11 → List Bool)

/-- The clause loop: `M` rounds (counter `CL`) of two literal reads and the body. -/
def clLoop (body : WM 10 NR) : WM 10 NR :=
  .whr rCL (.seq (.dec rCL) (.seq (readNatM false sPO rF rC rL0 rP rTT)
    (.seq (readNatM false sPO rF rC rL1 rP rTT) body)))

/-- The cost of reading one literal. -/
def rdCost (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)

/-- The literal pair of clause `i`. -/
def litA (lits : List ℕ) (i : ℕ) : ℕ := lits.getD (2 * i) 0
def litB (lits : List ℕ) (i : ℕ) : ℕ := lits.getD (2 * i + 1) 0

/-- The body outputs of the first `i` clauses. -/
def accW (lits : List ℕ) (Wc : ℕ → ℕ → List Bool) (i : ℕ) : List Bool :=
  (List.range i).flatMap fun j => Wc (litA lits j) (litB lits j)

/-- The admissibility of the first `i` clauses. -/
def accB (lits : List ℕ) (bc : ℕ → ℕ → Bool) (i : ℕ) : Bool :=
  (List.range i).all fun j => bc (litA lits j) (litB lits j)

theorem accW_succ (lits : List ℕ) (Wc : ℕ → ℕ → List Bool) (i : ℕ) :
    accW lits Wc (i + 1) = accW lits Wc i ++ Wc (litA lits i) (litB lits i) := by
  simp [accW, List.range_succ, List.flatMap_append]

theorem accB_succ (lits : List ℕ) (bc : ℕ → ℕ → Bool) (i : ℕ) :
    accB lits bc (i + 1) = (accB lits bc i && bc (litA lits i) (litB lits i)) := by
  simp [accB, List.range_succ, List.all_append]

theorem natWords_take_succ (lits : List ℕ) (k : ℕ) (hk : k < lits.length) :
    (lits.take (k + 1)).flatMap natWord = (lits.take k).flatMap natWord ++ natWord (lits.getD k 0) := by
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.getD_eq_getElem _ _ hk]
  simp

theorem natWords_split (lits : List ℕ) (k : ℕ) (hk : k < lits.length) :
    lits.flatMap natWord = (lits.take k).flatMap natWord ++ natWord (lits.getD k 0) ++
      (lits.drop (k + 1)).flatMap natWord := by
  rw [List.getD_eq_getElem _ _ hk]
  conv_lhs => rw [← List.take_append_drop k lits]
  rw [List.flatMap_append, List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]

/-- The registers the reads use are plain and clear. -/
structure RdOK (v0 : Fin NR → ℕ) : Prop where
  f : v0 rF = 0
  c : v0 rC = 0
  p : v0 rP = 0
  tt : v0 rTT = 0
  l0 : v0 rL0 = 0
  l1 : v0 rL1 = 0
  cl : v0 rCL = 0

theorem pCL : Plain rCL := ⟨by decide, by decide⟩

/-- **One literal read** into `R` (`L₀` or `L₁`), the cursor past its field. -/
theorem readLitT (h : ℕ) (o : List Bool) (cl : Bool) (w : Fin NR → ℕ) (ok : ℕ) (R : Fin NR) (hR : R = rL0 ∨ R = rL1)
    (hf : w rF = 0) (hc : w rC = 0) (hp : w rP = 0) (ht : w rTT = 0) (hR0 : w R = 0) (x : ℕ) (pre rest : List Bool)
    (hsrc : src sPO = pre ++ natWord x ++ rest) (hh : h = pre.length) (hcap : 2 ^ (natBitLength x + 1) ≤ cap) :
    WExec cap (readNatM false sPO rF rC R rP rTT) (ts src h o (regsOf w Z4 Z4 Z4 ok) cl)
      (ts src (h + (natWord x).length) o (regsOf (Function.update w R x) Z4 Z4 Z4 ok) cl) (rdCost x) := by
  have pR : Plain R := by rcases hR with e | e <;> subst e <;> exact ⟨by decide, by decide⟩
  have oR : R ≠ rOP := by rcases hR with e | e <;> subst e <;> decide
  have d1 : rF ≠ R := by rcases hR with e | e <;> subst e <;> decide
  have d2 : rC ≠ R := by rcases hR with e | e <;> subst e <;> decide
  have d3 : rP ≠ R := by rcases hR with e | e <;> subst e <;> decide
  have d4 : R ≠ rTT := by rcases hR with e | e <;> subst e <;> decide
  have e := readNatM_spec cap false sPO rF rC R rP rTT (by decide) d1 (by decide) (by decide) d2 (by decide) (by decide)
    d3 (by decide) d4 x pre rest (ts src h o (regsOf w Z4 Z4 Z4 ok) cl)
    (by rw [ts_st _ _ _ _ _ _ (by decide), hsrc]; simp [PrimAsm.ParseNat.enc])
    (by rw [ts_sh_PO]; exact hh)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hf)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hc)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hp)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact ht)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ pR oR, hR0]; omega)
  rw [tsR_val _ _ _ _ _ _ _ _ _ _ pR oR, hR0, Nat.zero_add, ts_seth_PO, tsR_setv _ _ _ _ _ _ _ _ _ _ pR oR] at e
  simp only [stp, Bool.false_eq_true, if_false, one_mul] at e
  rw [← hh] at e
  exact e

theorem getD_mem (lits : List ℕ) (k : ℕ) (hk : k < lits.length) : lits.getD k 0 ∈ lits := by
  rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-- **The clause loop**: `M` clauses from the list's start; each body output appended in clause order. -/
theorem clLoopT (body : WM 10 NR) (hR : usesR rCL body = false) (cl : Bool) (v0 : Fin NR → ℕ) (hv : RdOK v0)
    (lits : List ℕ) (M : ℕ) (hM : lits.length = 2 * M) (pre rest : List Bool)
    (hsrc : src sPO = pre ++ lits.flatMap natWord ++ rest) (Wc : ℕ → ℕ → List Bool) (bc : ℕ → ℕ → Bool) (L cc Rb : ℕ)
    (hbody : ∀ i < M, ∀ (h : ℕ) (o : List Bool) (ok : ℕ), ok ≤ 1 →
      o.length + (Wc (litA lits i) (litB lits i)).length + L ≤ cap →
      WExec cap body (ts src h o (regsOf (Function.update (Function.update v0 rL0 (litA lits i)) rL1 (litB lits i))
        Z4 Z4 Z4 ok) cl) (ts src h (o ++ Wc (litA lits i) (litB lits i))
          (regsOf v0 Z4 Z4 Z4 (if bc (litA lits i) (litB lits i) then ok else 0)) cl) cc)
    (hrd : ∀ x ∈ lits, rdCost x ≤ Rb ∧ 2 ^ (natBitLength x + 1) ≤ cap) (hMc : M ≤ cap)
    (o : List Bool) (ok : ℕ) (hok : ok ≤ 1) (hlen : o.length + (accW lits Wc M).length + L ≤ cap) :
    WExec cap (clLoop body) (ts src pre.length o (regsOf (Function.update v0 rCL M) Z4 Z4 Z4 ok) cl)
      (ts src (pre.length + (lits.flatMap natWord).length) (o ++ accW lits Wc M)
        (regsOf v0 Z4 Z4 Z4 (if accB lits bc M then ok else 0)) cl) (M * (2 * Rb + cc + 8) + 1) := by
  set S : ℕ → TS := fun i => ts src (pre.length + ((lits.take (2 * i)).flatMap natWord).length) (o ++ accW lits Wc i)
    (regsOf (Function.update v0 rCL (M - i)) Z4 Z4 Z4 (if accB lits bc i then ok else 0)) cl with hS
  have hSK : ∀ i ≤ M, (S i).val rCL = M - i := fun i _ => by
    simp only [S]; rw [tsR_val _ _ _ _ _ _ _ _ _ _ pCL (by decide), Function.update_self]
  have hmono : ∀ i, i ≤ M → (accW lits Wc i).length ≤ (accW lits Wc M).length := by
    intro i hi
    induction hk : M - i generalizing i with
    | zero => rw [show i = M by omega]
    | succ m ih =>
      have := ih (i + 1) (by omega) (by omega)
      rw [accW_succ] at this; simp only [List.length_append] at this; omega
  have hbody' : ∀ i < M, WExec cap (.seq (readNatM false sPO rF rC rL0 rP rTT)
      (.seq (readNatM false sPO rF rC rL1 rP rTT) body)) ((S i).setv rCL (M - i - 1)) (S (i + 1))
      (2 * Rb + cc + 4) := by
    intro i hi
    have h2i : 2 * i < lits.length := by omega
    have h2i1 : 2 * i + 1 < lits.length := by omega
    set okp := if accB lits bc i then ok else 0 with hokp
    have hokp1 : okp ≤ 1 := by simp only [okp]; split_ifs <;> omega
    set w := Function.update v0 rCL (M - i - 1) with hw
    have wv : ∀ r, r ≠ rCL → w r = v0 r := fun r hr => Function.update_of_ne hr _ _
    set p0 := pre.length + ((lits.take (2 * i)).flatMap natWord).length with hp0
    have e0 : (S i).setv rCL (M - i - 1) = ts src p0 (o ++ accW lits Wc i) (regsOf w Z4 Z4 Z4 okp) cl := by
      simp only [S]; rw [tsR_setv _ _ _ _ _ _ _ _ _ _ pCL (by decide), Function.update_idem]
    rw [e0]
    have hsA := natWords_split lits (2 * i) h2i
    have r1 := readLitT cap src p0 (o ++ accW lits Wc i) cl w okp rL0 (Or.inl rfl)
      (by rw [wv _ (by decide)]; exact hv.f) (by rw [wv _ (by decide)]; exact hv.c)
      (by rw [wv _ (by decide)]; exact hv.p) (by rw [wv _ (by decide)]; exact hv.tt)
      (by rw [wv _ (by decide)]; exact hv.l0) (litA lits i) (pre ++ (lits.take (2 * i)).flatMap natWord)
      ((lits.drop (2 * i + 1)).flatMap natWord ++ rest) (by rw [hsrc, hsA]; simp [litA, List.append_assoc])
      (by simp [p0]) (hrd _ (getD_mem lits _ h2i)).2
    have hsB := natWords_split lits (2 * i + 1) h2i1
    have htake1 := natWords_take_succ lits (2 * i) h2i
    set w1 := Function.update w rL0 (litA lits i) with hw1
    have r2 := readLitT cap src (p0 + (natWord (litA lits i)).length) (o ++ accW lits Wc i) cl w1 okp rL1 (Or.inr rfl)
      (by rw [hw1, Function.update_of_ne (by decide), wv _ (by decide)]; exact hv.f)
      (by rw [hw1, Function.update_of_ne (by decide), wv _ (by decide)]; exact hv.c)
      (by rw [hw1, Function.update_of_ne (by decide), wv _ (by decide)]; exact hv.p)
      (by rw [hw1, Function.update_of_ne (by decide), wv _ (by decide)]; exact hv.tt)
      (by rw [hw1, Function.update_of_ne (by decide), wv _ (by decide)]; exact hv.l1) (litB lits i)
      (pre ++ (lits.take (2 * i + 1)).flatMap natWord) ((lits.drop (2 * i + 1 + 1)).flatMap natWord ++ rest)
      (by rw [hsrc, hsB]; simp [litB, List.append_assoc])
      (by rw [htake1]; simp [p0, litA]; omega) (hrd _ (getD_mem lits _ h2i1)).2
    -- the body, framed over the loop counter
    have hb := hbody i hi (p0 + (natWord (litA lits i)).length + (natWord (litB lits i)).length)
      (o ++ accW lits Wc i) okp hokp1 (by
        have := hmono (i + 1) (by omega)
        rw [accW_succ] at this
        simp only [List.length_append] at this ⊢; omega)
    have hbf := WExec.frame_reg cap hb rCL hR (M - i - 1)
    have e1 : (ts src (p0 + (natWord (litA lits i)).length + (natWord (litB lits i)).length) (o ++ accW lits Wc i)
        (regsOf (Function.update (Function.update v0 rL0 (litA lits i)) rL1 (litB lits i)) Z4 Z4 Z4 okp) cl).setv rCL
          (M - i - 1) = ts src (p0 + (natWord (litA lits i)).length + (natWord (litB lits i)).length) (o ++ accW lits Wc i)
        (regsOf (Function.update w1 rL1 (litB lits i)) Z4 Z4 Z4 okp) cl := by
      rw [tsR_setv _ _ _ _ _ _ _ _ _ _ pCL (by decide)]
      congr 2
      simp only [w1, w]
      rw [Function.update_comm (show rL1 ≠ rCL by decide), Function.update_comm (show rL0 ≠ rCL by decide)]
    rw [e1] at hbf
    have e2 : (ts src (p0 + (natWord (litA lits i)).length + (natWord (litB lits i)).length)
        (o ++ accW lits Wc i ++ Wc (litA lits i) (litB lits i))
        (regsOf v0 Z4 Z4 Z4 (if bc (litA lits i) (litB lits i) then okp else 0)) cl).setv rCL (M - i - 1) = S (i + 1) := by
      rw [tsR_setv _ _ _ _ _ _ _ _ _ _ pCL (by decide)]
      simp only [S]
      have htake2 := natWords_take_succ lits (2 * i + 1) h2i1
      have hq : (if bc (litA lits i) (litB lits i) then okp else 0) =
          (if (accB lits bc i && bc (litA lits i) (litB lits i)) then ok else 0) := by
        simp only [okp]; cases accB lits bc i <;> cases bc (litA lits i) (litB lits i) <;> simp
      have hcur : p0 + (natWord (litA lits i)).length + (natWord (litB lits i)).length =
          pre.length + ((lits.take (2 * (i + 1))).flatMap natWord).length := by
        rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, htake2, htake1]
        simp [p0, litA, litB]; omega
      rw [hq, hcur, accW_succ, accB_succ, List.append_assoc, show M - (i + 1) = M - i - 1 by omega]
    rw [e2] at hbf
    have hr1 := (hrd _ (getD_mem lits _ h2i)).1
    have hr2 := (hrd _ (getD_mem lits _ h2i1)).1
    exact WExec.mono (WExec.seq r1 (WExec.seq r2 hbf)) (by simp only [litA, litB] at *; omega)
  have hl := Round.wloop cap rCL _ (2 * Rb + cc + 4) M S hSK hMc hbody'
  have e0 : S 0 = ts src pre.length o (regsOf (Function.update v0 rCL M) Z4 Z4 Z4 ok) cl := by
    simp [S, accW, accB]
  have eM : S M = ts src (pre.length + (lits.flatMap natWord).length) (o ++ accW lits Wc M)
      (regsOf v0 Z4 Z4 Z4 (if accB lits bc M then ok else 0)) cl := by
    simp only [S]
    rw [Nat.sub_self, show Function.update v0 rCL 0 = v0 from Function.update_eq_self_iff.2 hv.cl.symm,
      show lits.take (2 * M) = lits by rw [← hM]; exact List.take_length]
  rw [e0, eM] at hl
  exact WExec.mono hl (by nlinarith)

/-! ## Seeking the literal list -/

abbrev rSQ : Fin NR := 50
abbrev rMM : Fin NR := 51

/-- Skip the PCPP output's header (four fields), the supports' bits (`SQ` of them) and the literal count. -/
def seekLits : WM 10 NR :=
  .seq (skipNatM false sPO rF rC) (.seq (skipNatM false sPO rF rC) (.seq (skipNatM false sPO rF rC)
    (.seq (skipNatM false sPO rF rC) (.seq (fwdK sPO rSQ rT) (skipNatM false sPO rF rC)))))

/-- One field skipped on the PCPP stream. -/
theorem skipPO (h : ℕ) (o : List Bool) (cl : Bool) (w : Fin NR → ℕ) (ok : ℕ) (hf : w rF = 0) (hc : w rC = 0)
    (x : ℕ) (pre rest : List Bool) (hsrc : src sPO = pre ++ natWord x ++ rest) (hh : h = pre.length)
    (hcap : natBitLength x + 1 ≤ cap) :
    WExec cap (skipNatM false sPO rF rC) (ts src h o (regsOf w Z4 Z4 Z4 ok) cl)
      (ts src (h + (natWord x).length) o (regsOf w Z4 Z4 Z4 ok) cl) (20 * natBitLength x + 20) := by
  have e := skipNatM_spec cap false sPO rF rC (by decide) x pre rest (ts src h o (regsOf w Z4 Z4 Z4 ok) cl)
    (by rw [ts_st _ _ _ _ _ _ (by decide), hsrc]; simp [PrimAsm.ParseNat.enc]) (by rw [ts_sh_PO]; exact hh)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hf)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hc) hcap
  rw [ts_seth_PO] at e
  simp only [stp, Bool.false_eq_true, if_false, one_mul] at e
  rw [← hh] at e
  exact e

/-- **Seeking the literal list**: from the PCPP output word's start to its literal list's first field. -/
theorem seekLitsT (o : List Bool) (cl : Bool) (w : Fin NR → ℕ) (ok : ℕ) (hf : w rF = 0) (hc : w rC = 0)
    (hT : w rT = 0) (x1 x2 x3 x4 n : ℕ) (bits rest : List Bool)
    (hsrc : src sPO = natWord x1 ++ natWord x2 ++ natWord x3 ++ natWord x4 ++ bits ++ natWord n ++ rest)
    (hSQ : w rSQ = bits.length) (hcap : natBitLength x1 + natBitLength x2 + natBitLength x3 + natBitLength x4 +
      natBitLength n + bits.length + 1 ≤ cap) :
    WExec cap seekLits (ts src 0 o (regsOf w Z4 Z4 Z4 ok) cl)
      (ts src (natWord x1 ++ natWord x2 ++ natWord x3 ++ natWord x4 ++ bits ++ natWord n).length o
        (regsOf w Z4 Z4 Z4 ok) cl)
      (20 * (natBitLength x1 + natBitLength x2 + natBitLength x3 + natBitLength x4 + natBitLength n) + 16 * bits.length +
        110) := by
  have s1 := skipPO cap src 0 o cl w ok hf hc x1 [] (natWord x2 ++ natWord x3 ++ natWord x4 ++ bits ++ natWord n ++ rest)
    (by rw [hsrc]; simp [List.append_assoc]) rfl (by omega)
  have s2 := skipPO cap src (0 + (natWord x1).length) o cl w ok hf hc x2 (natWord x1) (natWord x3 ++ natWord x4 ++ bits ++ natWord n ++ rest)
    (by rw [hsrc]; simp [List.append_assoc]) (by simp) (by omega)
  have s3 := skipPO cap src (0 + (natWord x1).length + (natWord x2).length) o cl w ok hf hc x3
    (natWord x1 ++ natWord x2) (natWord x4 ++ bits ++ natWord n ++ rest)
    (by rw [hsrc]; simp [List.append_assoc]) (by simp) (by omega)
  have s4 := skipPO cap src (0 + (natWord x1).length + (natWord x2).length + (natWord x3).length) o cl w ok hf hc x4
    (natWord x1 ++ natWord x2 ++ natWord x3) (bits ++ natWord n ++ rest)
    (by rw [hsrc]; simp [List.append_assoc]) (by simp; omega) (by omega)
  set h4 := 0 + (natWord x1).length + (natWord x2).length + (natWord x3).length + (natWord x4).length with hh4
  have f5 := fwdK_spec cap sPO rSQ rT (by decide) (ts src h4 o (regsOf w Z4 Z4 Z4 ok) cl)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hT)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide), hSQ]; omega)
  rw [ts_sh_PO, tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide), hSQ, ts_seth_PO] at f5
  have s6 := skipPO cap src (h4 + bits.length) o cl w ok hf hc n
    (natWord x1 ++ natWord x2 ++ natWord x3 ++ natWord x4 ++ bits) rest
    (by rw [hsrc]) (by simp [h4]; omega) (by omega)
  have e : h4 + bits.length + (natWord n).length =
      (natWord x1 ++ natWord x2 ++ natWord x3 ++ natWord x4 ++ bits ++ natWord n).length := by
    simp [h4]; omega
  rw [e] at s6
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq f5 s6))))) ?_
  omega

/-! ## One pass -/

/-- One pass: seek the literal list, `CL := M`, the clause loop, return the literal cursor. -/
def passP (body : WM 10 NR) : WM 10 NR :=
  .seq seekLits (.seq (cloop rMM rT (.inc rCL)) (.seq (clLoop body) (rewB sPO rBIG rT)))

/-- The PCPP output word's layout on the PCPP stream. -/
structure POLayout (src : Fin 11 → List Bool) (w : Fin NR → ℕ) (lits : List ℕ) (M : ℕ) : Prop where
  hdr : ∃ x1 x2 x3 x4 : ℕ, ∃ bits rest : List Bool,
    src sPO = natWord x1 ++ natWord x2 ++ natWord x3 ++ natWord x4 ++ bits ++ natWord lits.length ++
      lits.flatMap natWord ++ rest ∧ w rSQ = bits.length ∧
      natBitLength x1 + natBitLength x2 + natBitLength x3 + natBitLength x4 + natBitLength lits.length + bits.length + 1
        ≤ cap ∧
      (natWord x1 ++ natWord x2 ++ natWord x3 ++ natWord x4 ++ bits ++ natWord lits.length ++ lits.flatMap natWord).length
        ≤ w rBIG ∧
      20 * (natBitLength x1 + natBitLength x2 + natBitLength x3 + natBitLength x4 + natBitLength lits.length) +
        16 * bits.length + 110 ≤ w rBIG * 40 + 200
  len : lits.length = 2 * M
  mm : w rMM = M

/-- **One pass** over the clauses (the literal cursor starts and ends at `0`). -/
theorem passT (body : WM 10 NR) (hR : usesR rCL body = false) (cl : Bool) (v0 : Fin NR → ℕ) (hv : RdOK v0)
    (hT : v0 rT = 0) (hBc : v0 rBIG ≤ cap) (lits : List ℕ) (M : ℕ) (hPO : POLayout cap src v0 lits M)
    (Wc : ℕ → ℕ → List Bool) (bc : ℕ → ℕ → Bool) (L cc Rb : ℕ)
    (hbody : ∀ i < M, ∀ (h : ℕ) (o : List Bool) (ok : ℕ), ok ≤ 1 →
      o.length + (Wc (litA lits i) (litB lits i)).length + L ≤ cap →
      WExec cap body (ts src h o (regsOf (Function.update (Function.update v0 rL0 (litA lits i)) rL1 (litB lits i))
        Z4 Z4 Z4 ok) cl) (ts src h (o ++ Wc (litA lits i) (litB lits i))
          (regsOf v0 Z4 Z4 Z4 (if bc (litA lits i) (litB lits i) then ok else 0)) cl) cc)
    (hrd : ∀ x ∈ lits, rdCost x ≤ Rb ∧ 2 ^ (natBitLength x + 1) ≤ cap) (hMc : M + 1 ≤ cap)
    (o : List Bool) (ok : ℕ) (hok : ok ≤ 1) (hlen : o.length + (accW lits Wc M).length + L ≤ cap) :
    WExec cap (passP body) (ts src 0 o (regsOf v0 Z4 Z4 Z4 ok) cl)
      (ts src 0 (o ++ accW lits Wc M) (regsOf v0 Z4 Z4 Z4 (if accB lits bc M then ok else 0)) cl)
      (40 * v0 rBIG + 200 + 1 + (18 * M + 3 + 1 + (M * (2 * Rb + cc + 8) + 1 + 1 + (16 * v0 rBIG + 3)))) := by
  obtain ⟨⟨x1, x2, x3, x4, bits, rest, hsrc, hSQ, hcap, hbig, hsk⟩, hlenM, hMM⟩ := hPO
  have s1 := seekLitsT cap src o cl v0 ok hv.f hv.c hT x1 x2 x3 x4 lits.length bits (lits.flatMap natWord ++ rest)
    (by rw [hsrc]; simp [List.append_assoc]) hSQ hcap
  set pre := natWord x1 ++ natWord x2 ++ natWord x3 ++ natWord x4 ++ bits ++ natWord lits.length with hpre
  -- CL := M
  have s2 := cloopIncT cap src pre.length o cl rMM rCL (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun j => regsOf (Function.update v0 rCL j) Z4 Z4 Z4 ok)
    (fun j => by beta_reduce; rw [regsOf_updPlain _ _ _ _ _ _ pCL, Function.update_idem])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ pCL, Function.update_self])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩,
      regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide)]
                 exact hT)
    (by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide), hMM]; omega)
  beta_reduce at s2
  rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide), hMM,
    show Function.update v0 rCL 0 = v0 from Function.update_eq_self_iff.2 hv.cl.symm] at s2
  -- the loop
  have s3 := clLoopT cap src body hR cl v0 hv lits M hlenM pre rest (by rw [hsrc]) Wc bc L cc Rb hbody hrd (by omega)
    o ok hok hlen
  -- rewind the literal cursor
  set okM := if accB lits bc M then ok else 0 with hokM
  have s4 := rewB_spec cap sPO rBIG rT (by decide)
    (ts src (pre.length + (lits.flatMap natWord).length) (o ++ accW lits Wc M) (regsOf v0 Z4 Z4 Z4 okM) cl)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hT)
    (by rw [ts_sh_PO, tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]
        have : pre.length + (lits.flatMap natWord).length = (pre ++ lits.flatMap natWord).length := by simp
        rw [this]; exact hbig)
    (by rw [tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; exact hBc)
  rw [ts_seth_PO, tsR_val _ _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at s4
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
