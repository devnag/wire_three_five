import Proof.Wire_3_5.Recovery.CaseTwoPadWhole

/-! # One round of the uniform Case-2 XOR fold at the padded request (P3:3729-3733, 3761-3763; D1.6 A1)

Realizes one copy of "`f^{⊕t(q)}`" (P3:3732-3733) for the hybrid Case 2, where "each honest proof bit is computed by
the deterministic PCPP algorithm" (P3:3762-3763) on `S₂`'s padded request, with a copy count that GROWS with `q`
("the least `t` with `e_t ≤ L^{−τ}`", P3:3818-3822): one fixed program must evaluate `t(q)+1` copies for every `q`,
so the copies share ONE reused bank and the block index is DATA, a unary offset `1^{i·w}` on a port (base's fixed-copy
fold `CloseoutCaseTwo.FixedFold` has one bank per copy and the block index in the machine).

One round, on a bank whose ports are the framed hierarchy input, the framed oracle descriptor, the accumulator, the
framed address `frame x`, the offset `1^{i·w}` and the block width `1^w` (both `false`-padded to the bank's capacity),
and the width `1^q`:
* copy `1^q` onto the block's width tape (base `PCPUnaryCopy`);
* crop block `i` of the address, `frame (x[i·w, (i+1)·w))`, onto the block's address tape (base `SliceFrame`);
* run the padded whole block at block `0` with its head reset, and XOR its honest bit into the accumulator (base
  `XorBody`).
The advance adds `w` to the offset in place (base `CaseTwoAdvance`).

Paper quantity of the main type: the unsigned honest proof bit of the padded request at block `i`,
`paddedUnsigned (a.output req) hcb (field x (i·w) w)`, XORed into the accumulator (`round_run`), and the offset's advance
(`advance_run`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

/-! ## The block's address window -/

/-- **One block of the address is the occurrence address word**: `x[o, o+q+cap+1) = u · clause · pad · position`. -/
theorem block_word {N : ℕ} (point : BitInput N) (offset q cb cap : ℕ) (hcb : cb ≤ cap) :
    List.ofFn (AddressWindow.field point offset (q + cap + 1)) =
      AddressFields.word (AddressWindow.field point offset q) (AddressWindow.field point (offset + q) cb)
        (AddressWindow.padding point offset q cb cap) (AddressWindow.read point (offset + q + cap)) := by
  have he : q + cap + 1 = q + (cb + ((cap - cb) + 1)) := by omega
  rw [he, AddressWindow.field_split, AddressWindow.field_split, AddressWindow.field_split,
    AddressWindow.field_one]
  have hp : offset + q + cb + (cap - cb) = offset + q + cap := by omega
  simp only [AddressFields.word, AddressWindow.padding, Nat.add_assoc] at hp ⊢
  rw [hp]

/-- **The address splits at a block** that fits: `x = x[0,o) · x[o,o+w) · x[o+w,N)`. -/
theorem split_at {N : ℕ} (point : BitInput N) (offset width : ℕ) (hfit : offset + width ≤ N) :
    List.ofFn point = List.ofFn (AddressWindow.field point 0 offset) ++
      List.ofFn (AddressWindow.field point offset width) ++ AddressWindow.tail point offset width := by
  have key : ∀ m, m = N → List.ofFn (AddressWindow.field point 0 m) = List.ofFn (AddressWindow.field point 0 N) := by
    intro m hm; subst hm; rfl
  calc List.ofFn point = List.ofFn (AddressWindow.field point 0 N) := (AddressWindow.full_field point).symm
    _ = List.ofFn (AddressWindow.field point 0 (offset + (width + (N - (offset + width))))) :=
        (key _ (by omega)).symm
    _ = _ := by
        rw [AddressWindow.field_split, AddressWindow.field_split]
        simp only [Nat.zero_add, AddressWindow.tail, List.append_assoc]

/-! ## The worker's tapes -/

/-- The accumulator block: base's XOR step around the padded whole block at block `0`, head reset included. -/
def xmachine (k D CH Cpad : ℕ) (code : List Bool) :=
  XorBody.machine (wresetMachine source a k D 0 CH Cpad code) ((woutputSlot source a k D).castAdd 1)

theorem wtapes_ge (k D : ℕ) : 9 ≤ wtapes source a k D := by
  unfold wtapes stapes; omega

/-- The accumulator block's tape count. -/
abbrev xt (k D : ℕ) := wtapes source a k D + 1 + 1
/-- The round's tape count: the accumulator block, then nine tapes (four ports, five scratch). -/
abbrev tw (k D : ℕ) := xt source a k D + 9

/-- The accumulator block's tapes, first in the round. -/
def xe (k D : ℕ) (i : Fin (xt source a k D)) : Fin (tw source a k D) := i.castAdd 9
/-- The nine extra tapes: `0` address, `1` offset, `2` block width, `3` width `1^q`, `4`–`8` scratch. -/
def ee (k D : ℕ) (j : Fin 9) : Fin (tw source a k D) := j.natAdd (xt source a k D)

theorem xe_injective (k D : ℕ) : Function.Injective (xe source a k D) := by
  intro i j h; exact Fin.ext (by simpa [xe] using congrArg Fin.val h)

theorem xe_val (k D : ℕ) (i : Fin (xt source a k D)) : (xe source a k D i).val = i.val := rfl
theorem ee_val (k D : ℕ) (j : Fin 9) : (ee source a k D j).val = xt source a k D + j.val := rfl

/-- The block's width tape `1^q` (`sold 8`). -/
def xq (k D : ℕ) : Fin (xt source a k D) := ⟨8, by have := wtapes_ge source a k D; show 8 < wtapes source a k D + 1 + 1; omega⟩
/-- The block's address tape (`sold 2`). -/
def xa (k D : ℕ) : Fin (xt source a k D) := ⟨2, by have := wtapes_ge source a k D; show 2 < wtapes source a k D + 1 + 1; omega⟩
/-- The accumulator. -/
def xacc (k D : ℕ) : Fin (xt source a k D) := Fin.last _

/-- The copy's slots: `1^q` port, the block's width tape, a scratch log. -/
def copySlots (k D : ℕ) : Fin 3 → Fin (tw source a k D) :=
  ![ee source a k D 3, xe source a k D (xq source a k D), ee source a k D 8]
/-- The crop's slots: address port, raw field (scratch), offset port, width port, two scratch, the block's address
tape, one scratch. -/
def sliceSlots (k D : ℕ) : Fin 8 → Fin (tw source a k D) :=
  ![ee source a k D 0, ee source a k D 4, ee source a k D 1, ee source a k D 2, ee source a k D 5,
    ee source a k D 6, xe source a k D (xa source a k D), ee source a k D 7]

theorem copySlots_val (k D : ℕ) (i : Fin 3) : (copySlots source a k D i).val =
    if i.val = 0 then xt source a k D + 3 else if i.val = 1 then 8 else xt source a k D + 8 := by
  fin_cases i <;> rfl

theorem copySlots_injective (k D : ℕ) : Function.Injective (copySlots source a k D) := by
  have hw := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  intro i j h
  have hv := congrArg Fin.val h
  rw [copySlots_val, copySlots_val] at hv
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at hv <;> omega

theorem sliceSlots_val (k D : ℕ) (i : Fin 8) : (sliceSlots source a k D i).val =
    if i.val = 6 then 2 else xt source a k D + (![0, 4, 1, 2, 5, 6, 0, 7] : Fin 8 → ℕ) i := by
  fin_cases i <;> rfl

theorem sliceSlots_injective (k D : ℕ) : Function.Injective (sliceSlots source a k D) := by
  have hw := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  intro i j h
  have hv := congrArg Fin.val h
  rw [sliceSlots_val, sliceSlots_val] at hv
  apply Fin.ext
  revert hv
  fin_cases i <;> fin_cases j <;> simp <;> omega

/-- **The round's worker**: copy `1^q`, crop the block, then the accumulator block. -/
def worker (k D CH Cpad : ℕ) (code : List Bool) :=
  Composition.machine (RecoveryFocus.machine (copySlots source a k D) PCPUnaryCopy.machine)
    (Composition.machine (RecoveryFocus.machine (sliceSlots source a k D) SliceFrame.machine)
      (RecoveryFocus.machine (xe source a k D) (xmachine source a k D CH Cpad code)))

/-- The round's tapes by position value. -/
def bankN (k D : ℕ) (hier desc : List Bool) (parity : Bool) (addr off width qw : List Bool) (v : ℕ) : List Bool :=
  if v = 0 then hier else if v = 1 then desc
  else if v = wtapes source a k D + 1 then [parity]
  else if v = xt source a k D then addr else if v = xt source a k D + 1 then off
  else if v = xt source a k D + 2 then width else if v = xt source a k D + 3 then qw else []

/-- **The round's tapes**, by position: hierarchy frame, descriptor frame, the accumulator `[parity]`, the address
frame, the offset, the block width, `1^q`; all other tapes empty. -/
def bank (k D : ℕ) (hier desc : List Bool) (parity : Bool) (addr off width qw : List Bool) :
    Fin (tw source a k D) → List Bool := fun t => bankN source a k D hier desc parity addr off width qw t.val

section BankValues
variable (k D : ℕ) (hier desc : List Bool) (parity : Bool) (addr off width qw : List Bool)

theorem bankN_hier : bankN source a k D hier desc parity addr off width qw 0 = hier := by simp [bankN]
theorem bankN_desc : bankN source a k D hier desc parity addr off width qw 1 = desc := by simp [bankN]
theorem bankN_acc : bankN source a k D hier desc parity addr off width qw (wtapes source a k D + 1) = [parity] := by
  have := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  unfold bankN; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_addr : bankN source a k D hier desc parity addr off width qw (xt source a k D) = addr := by
  have := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  unfold bankN; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_off : bankN source a k D hier desc parity addr off width qw (xt source a k D + 1) = off := by
  have := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  unfold bankN; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_width : bankN source a k D hier desc parity addr off width qw (xt source a k D + 2) = width := by
  have := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  unfold bankN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
theorem bankN_q : bankN source a k D hier desc parity addr off width qw (xt source a k D + 3) = qw := by
  have := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  unfold bankN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]
theorem bankN_other (v : ℕ) (h0 : v ≠ 0) (h1 : v ≠ 1) (h2 : v ≠ wtapes source a k D + 1)
    (h3 : v ≠ xt source a k D) (h4 : v ≠ xt source a k D + 1) (h5 : v ≠ xt source a k D + 2)
    (h6 : v ≠ xt source a k D + 3) : bankN source a k D hier desc parity addr off width qw v = [] := by
  unfold bankN
  rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]

end BankValues

theorem copy_slice_disjoint (k D : ℕ) (i : Fin 3) (j : Fin 8) : copySlots source a k D i ≠ sliceSlots source a k D j := by
  have hw := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  intro h
  have hv := congrArg Fin.val h
  rw [copySlots_val, sliceSlots_val] at hv
  revert hv
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem copy_xe (k D : ℕ) (i : Fin 3) (j : Fin (xt source a k D)) (hj : j.val ≠ 8) :
    copySlots source a k D i ≠ xe source a k D j := by
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  have hjl := j.isLt
  intro h
  have hv := congrArg Fin.val h
  rw [copySlots_val, xe_val] at hv
  split_ifs at hv <;> omega

theorem slice_xe (k D : ℕ) (i : Fin 8) (j : Fin (xt source a k D)) (hj : j.val ≠ 2) :
    sliceSlots source a k D i ≠ xe source a k D j := by
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  have hjl := j.isLt
  intro h
  have hv := congrArg Fin.val h
  rw [sliceSlots_val, xe_val] at hv
  revert hv
  fin_cases i <;> simp <;> omega

theorem xe_ee (k D : ℕ) (i : Fin (xt source a k D)) (j : Fin 9) : xe source a k D i ≠ ee source a k D j := by
  intro h
  have hv := congrArg Fin.val h
  rw [xe_val, ee_val] at hv
  have := i.isLt
  omega

/-- The accumulator block's input, by position. -/
theorem xinput_val (k D : ℕ) (hier desc addr : List Bool) (q : ℕ) (parity : Bool) (i : Fin (xt source a k D)) :
    XorBody.input (wresetInput source a k D hier desc addr q) parity i =
      if i.val = 0 then RepairOrdinary.frame hier else if i.val = 1 then RepairOrdinary.frame desc
      else if i.val = 2 then RepairOrdinary.frame addr else if i.val = 8 then List.replicate q true
      else if i.val = wtapes source a k D + 1 then [parity] else [] := by
  have hs : 9 ≤ stapes source a k := by unfold stapes; omega
  have hw : stapes source a k ≤ wtapes source a k D := by unfold wtapes; omega
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  obtain ⟨v, hv⟩ := i
  simp only [XorBody.input, wresetInput, winput, addCases_val, sinput]
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ## One round -/

section Round
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
  (oracle : BooleanCircuit
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
  (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
  (D : ℕ)

/-- The padded request's clause cap `⌈D log₂(arity+2)⌉`. -/
abbrev capOf : ℕ := CloseoutLanguage.clauseWidth D (wrequest source a H Cpad hpad r oracle q hq).arity
/-- The block width `arity + cap + 1`. -/
abbrev widthOf : ℕ := (wrequest source a H Cpad hpad r oracle q hq).arity + capOf source a H Cpad hpad r oracle q hq D + 1

/-- **The cost of round `i`**: the copy, the crop at offset `i·w`, and the accumulator block on block `i`. -/
def roundCost {N : ℕ} (point : BitInput N) (i : ℕ) : ℕ :=
  2 * q + 4 + 1 + (SliceFrame.budget (i * widthOf source a H Cpad hpad r oracle q hq D)
      (widthOf source a H Cpad hpad r oracle q hq D) + 1 +
    (2 * wbudget source a H Cpad hpad r oracle q hq D 0
      (AddressWindow.field point (i * widthOf source a H Cpad hpad r oracle q hq D)
        (wrequest source a H Cpad hpad r oracle q hq).arity)
      (AddressWindow.field point (i * widthOf source a H Cpad hpad r oracle q hq D +
        (wrequest source a H Cpad hpad r oracle q hq).arity)
        (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits)
      (AddressWindow.read point (i * widthOf source a H Cpad hpad r oracle q hq D +
        (wrequest source a H Cpad hpad r oracle q hq).arity + capOf source a H Cpad hpad r oracle q hq D))
      (capOf source a H Cpad hpad r oracle q hq D -
        (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits) + 2 + 2))

/-- The round's input tapes at block `i` with accumulator `parity` and bank capacity `total`. -/
def roundIn {N : ℕ} (point : BitInput N) (i total : ℕ) (parity : Bool) : Fin (tw source a k D) → List Bool :=
  bank source a k D (RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r))
    (RepairOrdinary.frame (PCPPNative.descriptor oracle)) parity (RepairOrdinary.frame (List.ofFn point))
    (ZeroPadding.pad total (List.replicate (i * widthOf source a H Cpad hpad r oracle q hq D) true))
    (ZeroPadding.pad total (List.replicate (widthOf source a H Cpad hpad r oracle q hq D) true))
    (List.replicate q true)

section RoundIn
variable {N : ℕ} (point : BitInput N) (i total : ℕ) (parity : Bool)

theorem roundIn_val (t : Fin (tw source a k D)) : roundIn source a H Cpad hpad r oracle q hq D point i total parity t =
    bankN source a k D (RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r))
      (RepairOrdinary.frame (PCPPNative.descriptor oracle)) parity (RepairOrdinary.frame (List.ofFn point))
      (ZeroPadding.pad total (List.replicate (i * widthOf source a H Cpad hpad r oracle q hq D) true))
      (ZeroPadding.pad total (List.replicate (widthOf source a H Cpad hpad r oracle q hq D) true))
      (List.replicate q true) t.val := rfl
theorem roundIn_e0 : roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 0) =
    RepairOrdinary.frame (List.ofFn point) := by
  rw [roundIn_val]; exact bankN_addr source a k D _ _ _ _ _ _ _
theorem roundIn_e1 : roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 1) =
    ZeroPadding.pad total (List.replicate (i * widthOf source a H Cpad hpad r oracle q hq D) true) :=
  by rw [roundIn_val]; exact bankN_off source a k D _ _ _ _ _ _ _
theorem roundIn_e2 : roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 2) =
    ZeroPadding.pad total (List.replicate (widthOf source a H Cpad hpad r oracle q hq D) true) :=
  by rw [roundIn_val]; exact bankN_width source a k D _ _ _ _ _ _ _
theorem roundIn_e3 : roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 3) =
    List.replicate q true := by
  rw [roundIn_val]; exact bankN_q source a k D _ _ _ _ _ _ _
theorem roundIn_other (t : Fin (tw source a k D)) (h0 : t.val ≠ 0) (h1 : t.val ≠ 1)
    (h2 : t.val ≠ wtapes source a k D + 1) (h3 : t.val ≠ xt source a k D) (h4 : t.val ≠ xt source a k D + 1)
    (h5 : t.val ≠ xt source a k D + 2) (h6 : t.val ≠ xt source a k D + 3) :
    roundIn source a H Cpad hpad r oracle q hq D point i total parity t = [] := by
  rw [roundIn_val]; exact bankN_other source a k D _ _ _ _ _ _ _ t.val h0 h1 h2 h3 h4 h5 h6

end RoundIn

/-- **One round is ready**: block `i`'s honest bit of the padded request is XORed into the accumulator; the address,
offset, width, `1^q`, hierarchy and descriptor ports are kept. -/
theorem round_run (hcoeff : H.coefficient ≤ Cpad) (hD : 1 ≤ D) {N : ℕ} (point : BitInput N)
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    (i total : ℕ) (parity : Bool) (hfit : (i + 1) * widthOf source a H Cpad hpad r oracle q hq D ≤ N) :
    ∃ out, ClockJoin.ReadyRun (worker source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (roundCost source a H Cpad hpad r oracle q hq D point i)
        (roundIn source a H Cpad hpad r oracle q hq D point i total parity) out ∧
      out (xe source a k D (xacc source a k D)) =
        [xor parity (CloseoutLanguage.paddedUnsigned (a.output (wrequest source a H Cpad hpad r oracle q hq)) hcb
          (AddressWindow.field point (i * widthOf source a H Cpad hpad r oracle q hq D)
            (widthOf source a H Cpad hpad r oracle q hq D)))] ∧
      (∀ j : Fin 4, out (ee source a k D (j.castAdd 5)) =
        roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D (j.castAdd 5))) ∧
      (∀ j : Fin (xt source a k D), j.val < 2 → out (xe source a k D j) =
        roundIn source a H Cpad hpad r oracle q hq D point i total parity (xe source a k D j)) := by
  have hw9 := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  set req := wrequest source a H Cpad hpad r oracle q hq with hreq
  set cap := capOf source a H Cpad hpad r oracle q hq D with hcap
  set width := widthOf source a H Cpad hpad r oracle q hq D with hwidth
  set off := i * width with hoff
  have b_e0 := roundIn_e0 source a H Cpad hpad r oracle q hq D point i total parity
  have b_e1 := roundIn_e1 source a H Cpad hpad r oracle q hq D point i total parity
  have b_e2 := roundIn_e2 source a H Cpad hpad r oracle q hq D point i total parity
  have b_e3 := roundIn_e3 source a H Cpad hpad r oracle q hq D point i total parity
  have b_other : ∀ (t : Fin (tw source a k D)) (v : ℕ), t.val = v → v ≠ 0 → v ≠ 1 → v ≠ wtapes source a k D + 1 →
      v ≠ xt source a k D → v ≠ xt source a k D + 1 → v ≠ xt source a k D + 2 → v ≠ xt source a k D + 3 →
      roundIn source a H Cpad hpad r oracle q hq D point i total parity t = [] := by
    intro t v hv h0 h1 h2 h3 h4 h5 h6
    subst hv
    exact roundIn_other source a H Cpad hpad r oracle q hq D point i total parity t h0 h1 h2 h3 h4 h5 h6
  have hoffw : off + width ≤ N := by
    have : off + width = (i + 1) * width := by rw [hoff]; ring
    omega
  -- the copy of `1^q`
  have c1 := ready_of_root (PCPUnaryCopy.copy_ready q 0 0 0)
  have f1 := c1.focus (copySlots source a k D) (copySlots_injective source a k D)
    (roundIn source a H Cpad hpad r oracle q hq D point i total parity) (by
    intro j
    fin_cases j
    · exact b_e3.trans (ZeroPadding.pad_zero _).symm
    · exact b_other _ 8 rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact b_other _ (xt source a k D + 8) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  set o1 : Fin 3 → List Bool := ![ZeroPadding.pad 0 (List.replicate q true), ZeroPadding.pad 0 (List.replicate q true),
    List.replicate (max 0 (q + 1)) false] with ho1
  set B1 := install (copySlots source a k D) (roundIn source a H Cpad hpad r oracle q hq D point i total parity) o1
    with hB1
  -- the crop of block `i`
  set pre := List.ofFn (AddressWindow.field point 0 off) with hpre
  set fld := List.ofFn (AddressWindow.field point off width) with hfld
  set tl := AddressWindow.tail point off width with htl
  have hsplit : List.ofFn point = pre ++ fld ++ tl := split_at point off width hoffw
  have hpre_len : pre.length = off := List.length_ofFn
  have hfld_len : fld.length = width := List.length_ofFn
  obtain ⟨s2, hs2, s26, _, s20, s22, s23⟩ := SliceFrame.slice_run pre fld tl
  set cap2 : Fin 8 → ℕ := ![0, 0, total, total, 0, 0, 0, 0] with hcap2
  have p2 := ready_pad SliceFrame.machine _ _ _ cap2 hs2
  have hB1s : ∀ j, B1 (sliceSlots source a k D j) =
      roundIn source a H Cpad hpad r oracle q hq D point i total parity (sliceSlots source a k D j) :=
    fun j => install_other _ _ _ _ (fun i => copy_slice_disjoint source a k D i j)
  have f2 := p2.focus (sliceSlots source a k D) (sliceSlots_injective source a k D) B1 (by
    intro j
    rw [hB1s]
    fin_cases j
    · show roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 0) =
        ZeroPadding.pad 0 (RepairOrdinary.frame (pre ++ fld ++ tl))
      rw [b_e0, ZeroPadding.pad_zero, hsplit]
    · exact b_other _ (xt source a k D + 4) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · show roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 1) =
        ZeroPadding.pad total (List.replicate pre.length true)
      rw [b_e1, hpre_len]
    · show roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 2) =
        ZeroPadding.pad total (List.replicate fld.length true)
      rw [b_e2, hfld_len]
    · exact b_other _ (xt source a k D + 5) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact b_other _ (xt source a k D + 6) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact b_other _ 2 rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · exact b_other _ (xt source a k D + 7) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  set o2 : Fin 8 → List Bool := fun j => ZeroPadding.pad (cap2 j) (s2 j) with ho2
  set B2 := install (sliceSlots source a k D) B1 o2 with hB2
  -- the accumulator block on block `i`
  set u := AddressWindow.field point off req.arity with hu
  set clause := AddressWindow.field point (off + req.arity) (a.output req).clauseBits with hclause
  set padw := AddressWindow.padding point off req.arity (a.output req).clauseBits cap with hpadw
  set position := AddressWindow.read point (off + req.arity + cap) with hposition
  have hpadw_len : padw.length = cap - (a.output req).clauseBits := List.length_ofFn
  have hcapw : (a.output req).clauseBits + padw.length = CloseoutLanguage.clauseWidth D req.arity := by
    rw [hpadw_len]; show _ = cap; omega
  have hpre0 : ([] : List Bool).length = 0 * (req.arity + CloseoutLanguage.clauseWidth D req.arity + 1) := by simp
  obtain ⟨wout, hw, hbit, hret⟩ := wreset_run source a H Cpad hcoeff hpad r oracle q hq D 0 hD u clause padw [] []
    position hcapw hpre0
  have haddr : [] ++ AddressFields.word u clause padw position ++ [] = fld := by
    rw [List.nil_append, List.append_nil, hfld]
    exact (block_word point off req.arity (a.output req).clauseBits cap hcb).symm
  obtain ⟨xres, hx, hxacc, hxold⟩ := XorBody.ready
    (wresetMachine source a k D 0 H.coefficient Cpad (VerifierEncoding.code H.verifier))
    ((woutputSlot source a k D).castAdd 1) _ _ wout parity _ hw hbit
  have hB2x : ∀ j : Fin (xt source a k D), j.val ≠ 2 → B2 (xe source a k D j) = B1 (xe source a k D j) :=
    fun j hj => install_other _ _ _ _ (fun i => slice_xe source a k D i j hj)
  have hB1x : ∀ j : Fin (xt source a k D), j.val ≠ 8 → B1 (xe source a k D j) =
      roundIn source a H Cpad hpad r oracle q hq D point i total parity (xe source a k D j) :=
    fun j hj => install_other _ _ _ _ (fun i => copy_xe source a k D i j hj)
  have f3 := hx.focus (xe source a k D) (xe_injective source a k D) B2 (by
    intro j
    rw [xinput_val]
    have hjl := j.isLt
    by_cases h2 : j.val = 2
    · have hj : xe source a k D j = sliceSlots source a k D 6 := Fin.ext (by simp [xe, sliceSlots, xa, h2])
      rw [hj, hB2, install_slot _ (sliceSlots_injective source a k D), if_neg (by omega), if_neg (by omega),
        if_pos h2, haddr]
      show ZeroPadding.pad 0 (s2 6) = _
      rw [ZeroPadding.pad_zero, s26]
    by_cases h8 : j.val = 8
    · have hj : xe source a k D j = copySlots source a k D 1 := Fin.ext (by simp [xe, copySlots, xq, h8])
      rw [hB2x j h2, hj, hB1, install_slot _ (copySlots_injective source a k D), if_neg (by omega), if_neg (by omega),
        if_neg h2, if_pos h8]
      show ZeroPadding.pad 0 (List.replicate q true) = _
      rw [ZeroPadding.pad_zero]
    rw [hB2x j h2, hB1x j h8, if_neg h2, if_neg h8]
    by_cases h0 : j.val = 0
    · rw [if_pos h0]
      rw [roundIn_val, show (xe source a k D j).val = 0 from h0, bankN_hier]
    by_cases h1 : j.val = 1
    · rw [if_neg h0, if_pos h1]
      rw [roundIn_val, show (xe source a k D j).val = 1 from h1, bankN_desc]
    rw [if_neg h0, if_neg h1]
    by_cases hacc : j.val = wtapes source a k D + 1
    · rw [if_pos hacc]
      rw [roundIn_val, show (xe source a k D j).val = wtapes source a k D + 1 from hacc, bankN_acc]
    rw [if_neg hacc]
    exact b_other _ j.val rfl h0 h1 hacc (by omega) (by omega) (by omega) (by omega))
  -- the round
  have j23 := ClockJoin.join _ _ _ _ _ _ _ f2 f3
  have j123 := ClockJoin.join _ _ _ _ _ _ _ f1 j23
  refine ⟨_, ClockJoin.enlarge _ _ _ _ _ j123 (le_of_eq ?_), ?_, ?_, ?_⟩
  · unfold roundCost
    rw [hpre_len, hfld_len, hpadw_len]
  · rw [install_slot _ (xe_injective source a k D)]
    show xres (Fin.last _) = _
    rw [hxacc]
    congr 2
    show _ = CloseoutLanguage.paddedUnsigned (a.output req) hcb (AddressWindow.field point off (req.arity + cap + 1))
    rw [AddressWindow.padded_value]
    rfl
  · intro j
    rw [install_other _ _ _ _ (fun i => xe_ee source a k D i _)]
    fin_cases j
    · show B2 (sliceSlots source a k D 0) = _
      rw [hB2, install_slot _ (sliceSlots_injective source a k D)]
      show ZeroPadding.pad 0 (s2 0) = roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 0)
      rw [ZeroPadding.pad_zero, s20, b_e0, hsplit]
    · show B2 (sliceSlots source a k D 2) = _
      rw [hB2, install_slot _ (sliceSlots_injective source a k D)]
      show ZeroPadding.pad total (s2 2) = roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 1)
      rw [s22, b_e1, hpre_len]
    · show B2 (sliceSlots source a k D 3) = _
      rw [hB2, install_slot _ (sliceSlots_injective source a k D)]
      show ZeroPadding.pad total (s2 3) = roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 2)
      rw [s23, b_e2, hfld_len]
    · show B2 (copySlots source a k D 0) = _
      rw [hB2, install_other _ _ _ _ (fun i => (copy_slice_disjoint source a k D 0 i).symm), hB1,
        install_slot _ (copySlots_injective source a k D)]
      show ZeroPadding.pad 0 (List.replicate q true) = roundIn source a H Cpad hpad r oracle q hq D point i total parity (ee source a k D 3)
      rw [ZeroPadding.pad_zero, b_e3]
  · intro j hj
    rw [install_slot _ (xe_injective source a k D)]
    have hjv : j.val = 0 ∨ j.val = 1 := by omega
    rcases hjv with h0 | h1
    · have he : j = XorBody.old ((wold source a k D (sold source a k ((0 : Fin 3).castAdd 6))).castAdd 1) :=
        Fin.ext (by simp [XorBody.old, wold, sold, h0])
      rw [roundIn_val, show (xe source a k D j).val = 0 from h0, bankN_hier, he, hxold, hret 0]
      rfl
    · have he : j = XorBody.old ((wold source a k D (sold source a k ((1 : Fin 3).castAdd 6))).castAdd 1) :=
        Fin.ext (by simp [XorBody.old, wold, sold, h1])
      rw [roundIn_val, show (xe source a k D j).val = 1 from h1, bankN_desc, he, hxold, hret 1]
      rfl

end Round

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
