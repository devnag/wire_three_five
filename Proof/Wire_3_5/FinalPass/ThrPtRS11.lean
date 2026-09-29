import Proof.Wire_3_5.FinalPass.ThrPtRS10

/-! # S2 (THR per point), part 25: the primes loop (P3:2587-2630)

Stream `8` holds the primes up to the cutoff as unary words `1^p 0` (the call's word 5). `readP_spec`: one prime read
into register `7` (its position counted in `110`). `primeLoop`: while stream `8`'s cell is `1` — read `p`, the row
`(g, p)` (any program meeting the row's contract `RowStep`), `p` cleared. **`primeLoop_spec`**: over the primes list
`L`, the accumulator gains `Σ_{p ∈ L} F p` and the working state stays `RowReady`. Paper quantity:
`Σ_p R̂_{g,p}(c, u, v)` for one `g`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem rdMid (pre tail : List Bool) (b : Bool) : readTapeBit (pre ++ b :: tail) pre.length = b := by
  simp [readTapeBit]

theorem rdEnd (U : List Bool) : readTapeBit U U.length = false := by
  simp [readTapeBit]

theorem rdOnes (U V : List Bool) (q k : ℕ) (hk : k < q) :
    readTapeBit (U ++ (List.replicate q true ++ V)) (U.length + k) = true := by
  have hq : List.replicate q true = List.replicate k true ++ true :: List.replicate (q - k - 1) true := by
    rw [← List.replicate_succ, ← List.replicate_add]
    congr 1
    omega
  have := rdMid (U ++ List.replicate k true) (List.replicate (q - k - 1) true ++ V) true
  rw [hq]
  simpa [List.append_assoc] using this

theorem rdZero (U V : List Bool) (q : ℕ) :
    readTapeBit (U ++ (List.replicate q true ++ false :: V)) (U.length + q) = false := by
  have := rdMid (U ++ List.replicate q true) V false
  simpa [List.append_assoc] using this

theorem unaryList_cons (q : ℕ) (L : List ℕ) :
    PrimAsm.Data.unaryList (q :: L) = List.replicate q true ++ false :: PrimAsm.Data.unaryList L := by
  simp [PrimAsm.Data.unaryList]

theorem unaryList_length : ∀ L : List ℕ, (PrimAsm.Data.unaryList L).length = (L.map (· + 1)).sum
  | [] => by simp [PrimAsm.Data.unaryList]
  | q :: L => by
    rw [unaryList_cons, List.length_append, List.length_replicate, List.length_cons, unaryList_length L]
    simp only [List.map_cons, List.sum_cons]
    omega

variable (cap : ℕ) (σB : WState 16 118)

theorem readP_spec (t : TSt) (U V : List Bool) (q : ℕ) (hst : σB.st 8 = U ++ (List.replicate q true ++ false :: V))
    (hh : t.hPr = U.length) (hc : t.prH + q + 1 ≤ cap) (hr : t.p + q ≤ cap) :
    WExec cap (WM.readU 8 110 7) (t.w σB)
      ({ t with hPr := t.hPr + q + 1, prH := t.prH + q + 1, p := t.p + q }.w σB) (11 * q + 7) := by
  have e := wreadU_spec cap (8 : Fin 17) (110 : Fin 118) 7 (by decide) q (t.w σB)
    (fun k hk => by rw [tw_st_other σB t 8 (by decide), tw_sh_hPr, hst, hh]; exact rdOnes U (false :: V) q k hk)
    (by rw [tw_st_other σB t 8 (by decide), tw_sh_hPr, hst, hh]; exact rdZero U V q)
    (by rw [tw_val_prH]; exact hc) (by rw [tw_val_p]; exact hr)
  rw [tw_sh_hPr, tw_seth_hPr, tw_val_prH, tw_setv_prH, tw_val_p, tw_setv_p] at e
  exact e

theorem clearP_spec (t : TSt) (q : ℕ) (hp : t.p = q) (hc : q ≤ cap) :
    WExec cap (WM.clear 7) (t.w σB) ({ t with p := 0 }.w σB) (3 * q + 1) := by
  have e := wclear_spec cap (7 : Fin 118) q (t.w σB) (by rw [tw_val_p, hp]) (by rw [tw_val_p, hp]; exact hc)
  rwa [tw_setv_p] at e

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
