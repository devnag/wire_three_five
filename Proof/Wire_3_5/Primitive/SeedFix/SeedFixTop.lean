import Lean
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Primitive.Writers.ComposeEnvBase
import Proof.Wire_3_5.MachineModel.BlockBranch
import Proof.Wire_3_5.MachineModel.BlockJoin
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJ
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTopBase


noncomputable section
set_option maxRecDepth 4096


/-! # SEEDFIX: the enclosing term 

Paper: "There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact printer calls. Under the
displayed allowances the printer applies, and the explicit descriptions and their construction give the middle term in
`prim:runtime`" (P3:3170-3173).

`SeedFixAt` is assembled from PA's writers (`WritersAtJ`, verified interface v2) and the C4 part (`C4At`,
`WireExponent3_5PrimTSeedFixTypes`) on one bank:
* tapes `0` the request (framed), `1` the seed word, `2` the mode flag, `3` the THR writer's input, `4` blank;
  then the four stages' scratch and the three writers' tapes (`Dims`, the slot maps `frontSl`, …, `thrWSl`);
* the machine: `front`, then a branch on the flag (S5's `Block.branchM`): THR runs `hashW ; hash ; thrW ; thr`,
  SYM runs `symW ; sym` (`topM`);
* **`seedFixAt_of`**: the word blocks (`WordBlocks.toRewound`) within `(3c₄ + 2c_W + 6)·seedClasses E` for any `E`
  above both floors; **`seedFixLeaf_of`**: `WriterLeafJ l → C4Leaf l → SeedFixLeaf l` with `E₄ := envMax E_W E₄'`.

Paper quantity of the main type: the fixed seeds `seedWord` (`SeedFixAt`, `SeedFixLeaf`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.SeedFixTop
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Slot maps by tape number -/

/-! ## Bank facts -/

/-! ## The layout -/

namespace Dims
end Dims

section Layout

end Layout

/-! ## The banks along the two paths -/

section Banks

section Thr

end Thr

section Sym

end Sym

end Banks

/-! ## The machine -/

/-- The machine's time bound at length `n`: three stages and two writers (the THR path), and the paid links. -/
noncomputable def topCost (l : Literals) (F : GateFree l) (EW E₄ : Envelope) (cW c₄ kclk coef A a : ℕ)
    (ha : a ≤ kclk + 1) (n : ℕ) : ℕ :=
  3 * seedBudget l F E₄ c₄ kclk coef A a ha n +
    2 * (cW * classBound EW .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
      (((gate0 l F).budget kclk coef A a ha).psiOf n)) + 6

section Machine
variable {l : Literals} {F : GateFree l} {EW E₄ : Envelope} {cW c₄ kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
variable (W : WritersAtJ l F EW cW kclk coef A a ha) (C : C4At l F E₄ c₄ kclk coef A a ha)

/-- The bank's dimensions from the stages and the writers. -/
def dimsOf : Dims := ⟨C.front.x, C.sym.x, C.hash.x, C.thr.x, W.sym.t, W.hash.t, W.thr.t⟩

theorem two_lt : 2 < (dimsOf W C).T := by have := (dimsOf W C).five_le; omega

/-- The mode flag's tape. -/
def flagT : Fin (dimsOf W C).T := ⟨2, two_lt W C⟩

noncomputable def frontM := RecoveryFocus.machine (frontSl (dimsOf W C)) C.front.M
noncomputable def symWM := RecoveryFocus.machine (symWSl (dimsOf W C) W.sym.inS) W.sym.M
noncomputable def symSM := RecoveryFocus.machine (symSl (dimsOf W C) W.sym.outS.val W.sym.outS.isLt) C.sym.M
noncomputable def hashWM := RecoveryFocus.machine (hashWSl (dimsOf W C) W.hash.inS) W.hash.M
noncomputable def hashSM := RecoveryFocus.machine (hashSl (dimsOf W C) W.hash.outS.val W.hash.outS.isLt) C.hash.M
noncomputable def thrWM := RecoveryFocus.machine (thrWSl (dimsOf W C) W.thr.inS) W.thr.M
noncomputable def thrSM := RecoveryFocus.machine (thrSl (dimsOf W C) W.thr.outS.val W.thr.outS.isLt) C.thr.M
/-- The THR path: the hash writer, the hash stage, the THR writer, the THR stage. -/
noncomputable def thrPathM :=
  Composition.machine (hashWM W C) (Composition.machine (hashSM W C) (Composition.machine (thrWM W C) (thrSM W C)))
/-- The SYM path: the SYM writer, the SYM stage. -/
noncomputable def symPathM := Composition.machine (symWM W C) (symSM W C)
/-- **The seed-fixing machine**: the front stage, then the branch on the mode flag. -/
noncomputable def topM := Composition.machine (frontM W C) (Block.branchM (flagT W C) (thrPathM W C) (symPathM W C))

theorem thr_step (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) :
    ∃ A' : Fin (dimsOf W C).T → List Bool,
      Step (topM W C) (topCost l F EW E₄ cW c₄ kclk coef A a ha n) (fun _ => 0)
        (entryBank (dimsOf W C).T (thrReq n a' ha' Cs carriers translation).word) (fun _ => 0) A' ∧
      ∀ i : Fin (dimsOf W C).T, i.val = 1 →
        A' i = seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (thrReq n a' ha' Cs carriers translation) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hc.2.2.2.2.2.1
  set D := dimsOf W C with hD
  set w := (thrReq n a' ha' Cs carriers translation).word with hw
  obtain ⟨Jf, -, hf⟩ := C.front_run (thrReq n a' ha' Cs carriers translation) hc
  have s1 := Block.dockKeep (readyStep hf) (frontSl D) (frontSl_inj D) (fun _ => 0) (entryBank D.T w)
    (fun _ => rfl) (front_in D w)
  obtain ⟨Jh, -, hh⟩ := W.hash.ready n a' ha' Cs carriers translation hc hs
  have s2 := Block.dockKeep (readyStep hh) (hashWSl D W.hash.inS) (hashWSl_inj D W.hash.inS) (fun _ => 0)
    (A1 D w true Jf) (fun _ => rfl) (hashW_in D w true Jf W.hash.inS)
  obtain ⟨Jhs, -, h3⟩ := C.hash_run n a' ha' Cs carriers translation hc hs
  have s3 := Block.dockKeep (readyStep h3) (hashSl D W.hash.outS.val W.hash.outS.isLt)
    (hashSl_inj D W.hash.outS.val W.hash.outS.isLt) (fun _ => 0)
    (A2 D w true Jf W.hash.inS W.hash.outS (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) Jh) (fun _ => rfl)
    (hashS_in D w true Jf W.hash.inS W.hash.outS (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) Jh W.hash.hio)
  obtain ⟨Jt, -, h4⟩ := W.thr.ready n a' ha' Cs carriers translation hc hs
  have s4 := Block.dockKeep (readyStep h4) (thrWSl D W.thr.inS) (thrWSl_inj D W.thr.inS) (fun _ => 0)
    (A3 D w true Jf W.hash.inS W.hash.outS (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) Jh (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs) Jhs) (fun _ => rfl)
    (thrW_in D w true Jf W.hash.inS W.hash.outS (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) Jh (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs) Jhs W.thr.inS)
  obtain ⟨Jts, -, h5⟩ := C.thr_run n a' ha' Cs carriers translation hc hs
  have s5 := Block.dockKeep (readyStep h5) (thrSl D W.thr.outS.val W.thr.outS.isLt)
    (thrSl_inj D W.thr.outS.val W.thr.outS.isLt) (fun _ => 0)
    (A4 D w true Jf W.hash.inS W.hash.outS (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) Jh (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs) Jhs W.thr.inS W.thr.outS (thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) Jt) (fun _ => rfl)
    (thrS_in D w true Jf W.hash.inS W.hash.outS (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) Jh (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs) Jhs W.thr.inS W.thr.outS (thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) Jt W.thr.hio)
  have path := s2.seq (s3.seq (s4.seq s5))
  have hbit : Block.entryBit (BlockPlatform.ofStep path).entryH (BlockPlatform.ofStep path).entryA (flagT W C) = true := by
    show readTapeBit (A1 D w true Jf (flagT W C)) 0 = true
    rw [A1_at2 D w true Jf _ rfl]
    rfl
  have blk := (Block.branchT (flagT W C) (BlockPlatform.ofStep path) (symPathM W C) hbit).run
  have all := s1.seq blk
  refine ⟨_, all.enlarge ?_, fun i hi => A5_at1 D w true Jf W.hash.inS W.hash.outS (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers) Jh (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs) Jhs W.thr.inS W.thr.outS (thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation) Jt (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (thrReq n a' ha' Cs carriers translation)) Jts i hi⟩
  simp only [Block.branchT_cost]
  unfold topCost
  simp only [BlockPlatform.ofStep]
  omega

theorem sym_step (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation)) :
    ∃ A' : Fin (dimsOf W C).T → List Bool,
      Step (topM W C) (topCost l F EW E₄ cW c₄ kclk coef A a ha n) (fun _ => 0)
        (entryBank (dimsOf W C).T (symReq n a' ha' Cs carriers translation).word) (fun _ => 0) A' ∧
      ∀ i : Fin (dimsOf W C).T, i.val = 1 →
        A' i = seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (symReq n a' ha' Cs carriers translation) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hc.2.2.2.2.2.1
  set D := dimsOf W C with hD
  set w := (symReq n a' ha' Cs carriers translation).word with hw
  obtain ⟨Jf, -, hf⟩ := C.front_run (symReq n a' ha' Cs carriers translation) hc
  have s1 := Block.dockKeep (readyStep hf) (frontSl D) (frontSl_inj D) (fun _ => 0) (entryBank D.T w)
    (fun _ => rfl) (front_in D w)
  obtain ⟨Js, -, h2⟩ := W.sym.ready n a' ha' Cs carriers translation hc hs
  have s2 := Block.dockKeep (readyStep h2) (symWSl D W.sym.inS) (symWSl_inj D W.sym.inS) (fun _ => 0)
    (A1 D w false Jf) (fun _ => rfl) (symW_in D w false Jf W.sym.inS)
  obtain ⟨Jss, -, h3⟩ := C.sym_run n a' ha' Cs carriers translation hc hs
  have s3 := Block.dockKeep (readyStep h3) (symSl D W.sym.outS.val W.sym.outS.isLt)
    (symSl_inj D W.sym.outS.val W.sym.outS.isLt) (fun _ => 0)
    (B2 D w false Jf W.sym.inS W.sym.outS (symTape (callInputs l F kclk coef A a ha) hs Cs carriers) Js) (fun _ => rfl)
    (symS_in D w false Jf W.sym.inS W.sym.outS (symTape (callInputs l F kclk coef A a ha) hs Cs carriers) Js W.sym.hio)
  have path := s2.seq s3
  have hbit : Block.entryBit (BlockPlatform.ofStep path).entryH (BlockPlatform.ofStep path).entryA (flagT W C) = false := by
    show readTapeBit (A1 D w false Jf (flagT W C)) 0 = false
    rw [A1_at2 D w false Jf _ rfl]
    rfl
  have blk := (Block.branchF (flagT W C) (thrPathM W C) (BlockPlatform.ofStep path) hbit).run
  have all := s1.seq blk
  refine ⟨_, all.enlarge ?_, fun i hi => B3_at1 D w false Jf W.sym.inS W.sym.outS (symTape (callInputs l F kclk coef A a ha) hs Cs carriers) Js (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (symReq n a' ha' Cs carriers translation)) Jss i hi⟩
  simp only [Block.branchF_cost]
  unfold topCost
  simp only [BlockPlatform.ofStep]
  omega

/-- Every request of the call family: its run and its seed word on tape `1`. -/
theorem top_step (r : {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req}) :
    ∃ A' : Fin (dimsOf W C).T → List Bool,
      Step (topM W C) (topCost l F EW E₄ cW c₄ kclk coef A a ha r.1.n) (fun _ => 0) (entryBank (dimsOf W C).T r.1.word)
        (fun _ => 0) A' ∧
      ∀ i : Fin (dimsOf W C).T, i.val = 1 → A' i = seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1 := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hc⟩ := r
  cases mode with
  | thr => exact thr_step W C n a' ha' Cs carriers translation hc
  | sym => exact sym_step W C n a' ha' Cs carriers translation hc

end Machine

/-! ## The class inequality and the leaf -/

section Leaf

variable {l : Literals} {F : GateFree l} {EW E₄ : Envelope} {cW c₄ kclk coef A a : ℕ} {ha : a ≤ kclk + 1}

/-- The machine's word blocks at one call family, within `(3c₄ + 2c_W + 6)·seedClasses E`. -/
noncomputable def topBlocks (W : WritersAtJ l F EW cW kclk coef A a ha) (C : C4At l F E₄ c₄ kclk coef A a ha)
    (E : Envelope) (hEW : ClassLE EW E) (hE4 : ClassLE E₄ E) :
    BlockPlatform.WordBlocks {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req} (fun r => r.1.word)
      (fun r => seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)
      (fun r => (3 * c₄ + 2 * cW + 6) * seedClasses E r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n)) where
  tapeCount := (dimsOf W C).T
  stateCount := _
  twoTapes := by have := (dimsOf W C).five_le; omega
  machine := topM W C
  outputTape := ⟨1, by have := (dimsOf W C).five_le; omega⟩
  outputFresh := by simp
  cost := fun r => topCost l F EW E₄ cW c₄ kclk coef A a ha r.1.n
  exitH := fun _ _ => 0
  exitA := fun r => Classical.choose (top_step W C r)
  step := fun r => (Classical.choose_spec (top_step W C r)).1
  exitOut := fun r => (Classical.choose_spec (top_step W C r)).2 _ rfl
  fits := fun r => by
    have hs : (callInputs l F kclk coef A a ha).StarAt r.1.n := r.2.2.2.2.2.2.1
    have hq : 1 ≤ r.1.n := by have := hs.2.1; have := hs.2.2.1; omega
    exact cost_fits hEW hE4 cW c₄ r.1.n _ _ hq

/-- **Seed fixing at one call family** from PA's writers and the C4 part. -/
noncomputable def seedFixAt_of (W : WritersAtJ l F EW cW kclk coef A a ha) (C : C4At l F E₄ c₄ kclk coef A a ha)
    (E : Envelope) (hEW : ClassLE EW E) (hE4 : ClassLE E₄ E) :
    SeedFixAt l F E (3 * c₄ + 2 * cW + 6) kclk coef A a ha :=
  (topBlocks W C E hEW hE4).toRewound (fun _ => rfl)

end Leaf

end NearCubicWires.WireExponent3_5.PrimT.SeedFixTop

end
