import Proof.Wire_3_5.FinalPass.SymF10
import Proof.Wire_3_5.FinalPass.SymF12
import Proof.Wire_3_5.FinalPass.SymFront3

/-! # SWf (the SYM words writer's flat tables), part 13: the flat part's machine and its run at a SYM request

The flat part runs on NW's bank past the front's data region: **`swfM l W F`** = the SYM front (`SymFront.frontM`: the
flat list's numbers in registers) then the four docked flat tables writers (`tailM`, part 10, the writer
`tabMP W c_r (9E₀) (CWP K₀) E₀ K₀` of part 12 on four blocks of `twW` tapes past `DT + 3`). **`swf_run`**: at a SYM
request, at a capacity above the front's need, the front's register bound and the requests, the part steps to a
state with the four circuits' flat tables words `flatWord (symListParams …) L_c` on the blocks' output tapes, the
input kept, every head and register `0`, every other stream within the bound.

Paper quantity of the main type: the call words `4·2 + c` (the list seeds' flat tables of circuit `c`, list:flatten
P3:1508-1520) at the request, on the part's output streams. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.WalkBank NearCubicWires.SupplierPipeline NearCubicWires.BlockPlatform

/-- The front's region. -/
abbrev xFw : ℕ := DataDock.DT + 3

section Layout
variable (l : Literals) (W : WalkBankProducer)

/-- The flat tables writer's tape count (on `l` alone). -/
noncomputable abbrev twW : ℕ := ShellX.STx W.x (9 * E0P l) 1 1 (E0P l) + 1

/-- The part's extra streams. -/
noncomputable abbrev xW : ℕ := xP xFw (twW l W)

theorem hxW : DataDock.DT + 3 ≤ xW l W := by unfold xW xP xFw; omega

/-- The writer's ports. -/
noncomputable def winW : Fin (twW l W) := ShellX.shellInX W.x (9 * E0P l) 1 1 (E0P l)
noncomputable def woutW : Fin (twW l W) := ShellX.shellOutX W.x (9 * E0P l) 1 1 (E0P l)

theorem winW_ne : winW l W ≠ woutW l W := ShellX.shellInX_ne_out

/-- The flat tables writer at a gate. -/
noncomputable def MwF (F : GateFree l) := tabMP W F.cr (9 * E0P l) (CWP (K0P F.cr)) (E0P l) (K0P F.cr)

/-- **The flat part's machine** at a gate. -/
noncomputable def swfM (F : GateFree l) :=
  Composition.machine (SymFront.frontM (xW l W) (hxW l W) l F) (tailM xFw (twW l W) (MwF l W F) (winW l W))

/-- The requests' length bound at a call (`n + 2` and the flat list's numbers below `K0P c_r·(n+2)^{E0P}`). -/
noncomputable def lwW (cr n : ℕ) : ℕ := 16 * (K0P cr * (n + 2) ^ E0P l)

end Layout

section Gate
variable (l : Literals) (W : WalkBankProducer) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The flat part's run at a SYM request.** -/
theorem swf_run {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (cap : ℕ)
    (hcapF : SymFront.KF l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length
      + 1) ^ SymFront.DF l F.filterErrDeg ≤ cap)
    (hreg : SymFront.CF l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length
      + 1) ^ SymFront.DFs l F.filterErrDeg ≤ cap)
    (hcapR : n + 4 * lwW l F.cr n + 10 ≤ cap) (σ : WState (LNS (xW l W)) LNR)
    (hE : NumsPh2.Entry (xW l W) l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ σ) :
    ∃ (τ : WState (LNS (xW l W)) LNR) (m : ℕ),
      m ≤ SymFront.CF l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length
        + 1) ^ SymFront.DFs l F.filterErrDeg + 1 + tailCost cap (fun c => budP F.cr (E0P l) (K0P F.cr)
          ((callInputs l F kclk coef A a ha).starParams n hcall.2.2.2.2.2.1)
          (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
          (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ c)) n (lwW l F.cr n) ∧
      Step (swfM l W F) m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      (∀ c : Fin 4, τ.st (tmC xFw (twW l W) c (woutW l W)) =
        flatWord (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
          (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ c)) ∧
      τ.st (NumsPh2.sIn (xW l W)) =
        frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) ∧ τ.cell = false ∧
      (∀ i, i ≠ NumsPh2.sIn (xW l W) → (∀ c, i ≠ tmC xFw (twW l W) c (woutW l W)) →
        (τ.st i).length ≤ SymFront.CF l F * ((fpIn l F kclk coef A a ha
          ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ SymFront.DFs l F.filterErrDeg +
          2 * lwW l F.cr n + 1 + (budP F.cr (E0P l) (K0P F.cr)
            ((callInputs l F kclk coef A a ha).starParams n hcall.2.2.2.2.2.1)
            (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
            (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ 0) +
          budP F.cr (E0P l) (K0P F.cr) ((callInputs l F kclk coef A a ha).starParams n hcall.2.2.2.2.2.1)
            (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
            (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ 1) +
          budP F.cr (E0P l) (K0P F.cr) ((callInputs l F kclk coef A a ha).starParams n hcall.2.2.2.2.2.1)
            (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
            (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ 2) +
          budP F.cr (E0P l) (K0P F.cr) ((callInputs l F kclk coef A a ha).starParams n hcall.2.2.2.2.2.1)
            (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
            (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ 3))) := by
  -- the front
  obtain ⟨τF, mF, hmF, sF, hF⟩ := SymFront.front_run (xW l W) (hxW l W) l F kclk coef A a ha ha' Cs carriers
    translation hcall cap hcapF σ hE
  set r : FReq l F kclk coef A a ha := ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ with hrd
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  set P := (callInputs l F kclk coef A a ha).starParams n hs with hPd
  set Pl := symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers with hPl
  set Ls : Fin 4 → ℕ := fun c => symL l F kclk coef A a ha r c with hLs
  set Bud : Fin 4 → ℕ := fun c => budP F.cr (E0P l) (K0P F.cr) P Pl (Ls c) with hBud
  -- the atoms
  have hK0 : 1 ≤ K0P F.cr := by unfold K0P; omega
  have hE0 : 1 ≤ E0P l := by unfold E0P; omega
  have hat := fun c => atoms_symP l F kclk coef A a ha r rfl c
  have hN2 : n + 2 ≤ K0P F.cr * (n + 2) ^ E0P l := by
    have h1 : n + 2 ≤ (n + 2) ^ E0P l := Nat.le_self_pow (by omega) _
    have h2 : (n + 2) ^ E0P l ≤ K0P F.cr * (n + 2) ^ E0P l := Nat.le_mul_of_pos_left _ hK0
    omega
  have hlw : ∀ c, (TabW.reqT n Pl.M Pl.B Pl.errExp (Ls c) 0 (Fintype.card Pl.FlatSeed)).length ≤ lwW l F.cr n := by
    intro c
    obtain ⟨a1, a2, a3, a4, a5⟩ := hat c
    exact TabW.reqT_le n Pl.M Pl.B Pl.errExp (Ls c) 0 (Fintype.card Pl.FlatSeed) _ hN2 a1 a2 a3 a4 (by omega) a5
  -- the four writers
  have hwr : ∀ c, WriterIfaceJ.WriterRun (MwF l W F) (Bud c) (winW l W) (woutW l W)
      (TabW.reqT n Pl.M Pl.B Pl.errExp (Ls c) 0 (Fintype.card Pl.FlatSeed)) (flatWord Pl (Ls c)) := by
    intro c
    obtain ⟨a1, a2, a3, a4, a5⟩ := hat c
    exact writer_atP W F.cr P rfl Pl (Ls c) (K0P F.cr) (E0P l) hK0 hE0 a1 a2 a3 a4 a5
  -- the tail
  have hLv : ∀ c : Fin 4, τF.val ⟨330 + c.val, by have := c.isLt; show 330 + c.val < 512; omega⟩ = Ls c := by
    intro c
    show _ = (if h : c.val < a' then (Stars.symGates (Cs ⟨c.val, h⟩)).length else 0)
    split
    · rename_i h; exact hF.vL c h
    · rename_i h; exact hF.vL0 c (by omega)
  have hblk : ∀ c j, τF.st (tmC xFw (twW l W) c j) = [] ∧ τF.sh (tmC xFw (twW l W) c j) = 0 := fun c j =>
    ⟨hF.hi _ (by show DataDock.DT + 3 ≤ xFw + (c.val * twW l W + j.val); unfold xFw; omega), hF.heads _⟩
  obtain ⟨τ, sT, hout, hin, hres, hsh, hoth, hval, hcell⟩ := tail_run xFw (twW l W) (MwF l W F) (winW l W) cap
    (woutW l W) (winW_ne l W) Bud n Pl.M Pl.B Pl.errExp (Fintype.card Pl.FlatSeed) (lwW l F.cr n) Ls
    (fun c => flatWord Pl (Ls c)) τF hF.vN hF.vM hF.vB hF.vE hF.vK hLv hblk (fun q => le_trans (hF.vle q) hreg) hlw
    hcapR hwr
  refine ⟨τ, _, ?_, Step.seq sF sT, hout, ?_, ?_, hval, ?_, fun i hi1 hi2 => ?_⟩
  · have := hmF
    omega
  · have hne : ∀ c j, tmC xFw (twW l W) c j ≠ NumsPh2.sIn (xW l W) := fun c j e => by
      have := congrArg Fin.val e
      rw [tmC_val] at this
      exact absurd this (by show ¬ (161 + (xFw + (c.val * twW l W + j.val)) = 150); omega)
    rw [(hoth _ hne).1]
    exact hF.hin
  · intro i
    by_cases hb : ∃ c j, tmC xFw (twW l W) c j = i
    · obtain ⟨c, j, rfl⟩ := hb
      exact hsh c j
    · have hne : ∀ c j, tmC xFw (twW l W) c j ≠ i := fun c j e => hb ⟨c, j, e⟩
      rw [(hoth i hne).2]
      exact hF.heads i
  · rw [hcell]; exact hF.cell
  · show (τ.st i).length ≤ SymFront.CF l F * ((fpIn l F kclk coef A a ha r).length + 1) ^
      SymFront.DFs l F.filterErrDeg + 2 * lwW l F.cr n + 1 + (Bud 0 + Bud 1 + Bud 2 + Bud 3)
    by_cases hb : ∃ c j, tmC xFw (twW l W) c j = i
    · obtain ⟨c, j, rfl⟩ := hb
      have hjo : j ≠ woutW l W := fun e => hi2 c (by rw [e])
      by_cases hji : j = winW l W
      · subst hji
        rw [hin c, frame_length]
        have := hlw c
        omega
      · have h1 := hres c j hji hjo
        have hB : Bud c ≤ Bud 0 + Bud 1 + Bud 2 + Bud 3 := by
          fin_cases c <;> simp <;> omega
        omega
    · have hne : ∀ c j, tmC xFw (twW l W) c j ≠ i := fun c j e => hb ⟨c, j, e⟩
      rw [(hoth i hne).1]
      have := hF.resid i hi1
      omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymF
