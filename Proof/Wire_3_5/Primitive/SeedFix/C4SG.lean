import Proof.Wire_3_5.Primitive.SeedFix.C4SF

/-! # C4 per-call setup (item 3), part 7: the SYM numbers machine's program, as one run

P3:2987-2988, 3011-3016, 2929-2941, 1188-1196 (as parts 2–6): the program `bigW F` (the SYM numbers; the seed's
numbers; C4.K's free numbers `F`; the rulers' derived numbers; the thirty-nine words) from the cell's entry (the
request, the counts) leaves the words on the streams `120 … 159` and the request on stream `0`.

* `symO`, `symClean` (the words, clean), `wordCost_le`, `bigW`, **`bigS_spec`**.

Paper quantities of the main type: the enumeration's rulers and constants, the generator's inputs, the compiler
request's numbers, at the call's `ℓ`, `kh`, `Q`, `n_T`, `w`, `dRow`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-- The words' streams. -/
def symO : Fin 39 → Fin 161 := ![120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]

/-- **The words, clean.** -/
def symClean (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) : Fin 39 → List Bool :=
  ![List.replicate ell true,
    List.replicate kh true,
    List.replicate (fr 0) true,
    List.replicate (fr 1) true,
    List.replicate (kh + kh) true,
    List.replicate (dd 0) true,
    List.replicate (dd 1) true,
    List.replicate (dd 2) true,
    List.replicate (dd 3) true,
    List.replicate (dd 4) true,
    [false],
    Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits ell (Q - 1)) ++ [false],
    [true],
    Streaming.marks (List.replicate 8 true) ++ [false],
    List.replicate 8 true ++ [false],
    List.replicate ell true ++ [false],
    List.replicate kh true ++ [false],
    [true, false],
    List.replicate 7 true ++ [false],
    List.replicate (kh + kh) true ++ [false],
    [false],
    [false],
    [true, true] ++ FiltRec.reps (dd 6) [true, false] ++ [false],
    [true, false],
    List.replicate (fr 0) true ++ [false],
    [false] ++ List.replicate cnt true,
    List.replicate (fr 2) true,
    [false] ++ List.replicate (dd 4) true,
    List.replicate kh true,
    List.replicate Q true,
    List.replicate ell true,
    List.replicate ell true,
    List.replicate ell true,
    List.replicate (fr 3) true,
    List.replicate (fr 2) true,
    List.replicate (fr 4) true,
    List.replicate (fr 5) true,
    [true] ++ List.replicate d2 true ++ [false] ++ List.replicate d2 false ++ [true],
    [true] ++ List.replicate (fr 6) true ++ [false] ++ List.replicate (fr 6) false ++ [true]]

/-- A word's step bound from its registers' bounds. -/
theorem wordCost_le (cap : ℕ) (σ : WState (LNS 0) LNR) (e : Emit1)
    (hp : ∀ p ∈ e.ps, ∀ A u, p = .r A u → σ.val A ≤ cap ∧ u.length ≤ 2)
    (hc : ∀ p ∈ e.ps, ∀ u, p = .c u → u.length ≤ 17) (hn : e.ps.length ≤ 5)
    (hh : ∀ R, e.hb = some R → σ.val (R 0) ≤ cap ∧ σ.val (R 4) ≤ cap) :
    wordCost σ e ≤ 8 * UnaryPow.sq cap := by
  have hsq : UnaryPow.sq cap = 200 * (cap + 2) * (cap + 2) := rfl
  have hpc : ∀ p ∈ e.ps, partCost σ p ≤ UnaryPow.sq cap := by
    intro p hp'
    cases p with
    | c u =>
      have := hc _ hp' u rfl
      simp only [partCost]; nlinarith
    | r A u =>
      obtain ⟨h1, h2⟩ := hp _ hp' A u rfl
      simp only [partCost]
      have : σ.val A * (8 * u.length + 4) ≤ cap * 20 := Nat.mul_le_mul h1 (by omega)
      nlinarith
  have hsum : (e.ps.map (partCost σ)).sum ≤ e.ps.length * UnaryPow.sq cap := by
    have := List.sum_le_card_nsmul (e.ps.map (partCost σ)) (UnaryPow.sq cap) (fun x hx => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx; exact hpc p hp')
    simpa using this
  unfold wordCost
  cases hb : e.hb with
  | none =>
    simp only [Nat.zero_add]
    have : e.ps.length * UnaryPow.sq cap ≤ 5 * UnaryPow.sq cap := Nat.mul_le_mul_right _ hn
    have := UnaryPow.sq_ge cap
    omega
  | some R =>
    obtain ⟨h0, h4⟩ := hh R hb
    dsimp only
    have e1 : σ.val (R 4) * (10 * σ.val (R 0) + 40) ≤ cap * (10 * cap + 40) := Nat.mul_le_mul h4 (by omega)
    have : e.ps.length * UnaryPow.sq cap ≤ 5 * UnaryPow.sq cap := Nat.mul_le_mul_right _ hn
    nlinarith

/-- The derived numbers (`der_spec`'s). -/
def derVals (Q kh tw cp' : ℕ) : Fin 7 → ℕ :=
  ![kh + kh + tw, max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp',
    wOf kh Q + 1, wOf kh Q + 1 + tw, max (kh + kh) (Nat.clog 2 Q) * 8, Q - 1, max (kh + kh) (Nat.clog 2 Q) - 1]

/-- **The SYM numbers machine's program.** -/
def bigW (F : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM (LNS 0) LNR :=
  .seq (numsSW cr fe ζ Cδ C) (.seq seedW (.seq F.prog (.seq derW (emitsW symEmits))))

theorem symEmits_short : ∀ e ∈ symEmits, (∀ p ∈ e.ps, ∀ A u, p = Part.r A u → u.length ≤ 2) ∧
    (∀ p ∈ e.ps, ∀ u, p = Part.c u → u.length ≤ 17) ∧ e.ps.length ≤ 5 := by
  intro e he
  simp only [symEmits, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨fun p hp => ?_, fun p hp => ?_, by decide⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp

/-- **The SYM numbers machine's program, run** (C4.K's free numbers `F`): from the cell's entry, the thirty-nine words
on the streams `symO`, every other stream as at entry. -/
theorem bigS_spec (F : FreeProg) (cap cr fe : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w : List Bool) (codes ccs : List ℕ) (tl : List Bool)
    (cx cy : List ℕ) (Kb Cmax capS err L kh : ℕ)
    (hw : w = Data.reqW P.n false codes ccs tl) (hccs : ccs.length = cx.length) (hcx : cx.length ≤ 2)
    (hcy : cy.length ≤ 4) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hC : ∀ c ∈ cx ++ cy, c ≤ Cmax)
    (hN1 : P1Need cap w P.n codes ccs cx cy Kb Cmax)
    (hcapS : capS = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (herr : err = fe * Ledger.Lq P.n) (hL : L = Ledger.Lq P.n) (hkh : kh = P.s * (P.r / 2))
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hN2 : NumsNeed cap P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0))
    (hn : 2 ≤ P.n) (hQ : 2 * (symInOf capS P.n err L kh cx.length codes.length cy).Q ≤ cap)
    (hv : ∀ j : Fin 11, (![capS, P.n, err, L, kh, cx.length, codes.length, cy.getD 0 0, cy.getD 1 0, cy.getD 2 0,
      cy.getD 3 0] : Fin 11 → ℕ) j ≤ cap)
    (Q gs fs pi : ℕ) (hQd : Q = (symInOf capS P.n err L kh cx.length codes.length cy).Q)
    (hgs : gs = 2 ^ (gP P.n capS err).seedBits) (hfs : fs = 2 ^ FlatNums.fbv cy.sum (bV cx.length capS) (L + 5))
    (hpi : pi = stV (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0))
    (hsc : SeedCap cap Q kh gs fs pi P.b P.s (P.r / 2) P.r P.n)
    (x : FreeIn) (hx : x = ⟨P.n, kh, L, capS, codes.length, cx.length, cy.sum, Q, max (kh + kh) (Nat.clog 2 Q),
      gs * fs * pi, wOf kh Q, (P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)⟩)
    (hF : F.ok cap x) (hdc : DerCap cap Q kh (F.val x 0) (F.val x 1))
    (cQl : Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q)) (cQ : Q + 1 ≤ cap)
    (cl : 3 * max (kh + kh) (Nat.clog 2 Q) + Q + 3 ≤ cap) (ck : kh + kh + 1 ≤ cap)
    (cfr : ∀ j, F.val x j + F.val x j + 3 ≤ cap)
    (cdd : ∀ i, derVals Q kh (F.val x 0) (F.val x 1) i + derVals Q kh (F.val x 0) (F.val x 1) i + 3 ≤ cap)
    (ccnt : gs * fs * pi * 2 ^ wOf kh Q + 1 ≤ cap)
    (cd2 : (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2))) +
      (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2))) + 3 ≤ cap)
    (c17 : 17 ≤ cap) :
    ∃ τ c, WExec cap (bigW F cr fe ζ Cδ C) (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (cx ++ cy))) τ c ∧
      c ≤ numsSCost cap P.n cr fe (Ledger.rowBt h0 h1 P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) (Ledger.Lq P.n)
        codes.length cx.length Kb Cmax cy.sum + 1 + (400 * UnaryPow.sq cap + 1 + (F.cost cap x + 1 +
        (200 * UnaryPow.sq cap + 1 + (400 * UnaryPow.sq cap)))) ∧
      (∀ j : Fin 39, τ.st (sk 0 (symO j)) = symClean Q kh (max (kh + kh) (Nat.clog 2 Q)) (gs * fs * pi * 2 ^ wOf kh Q)
        (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)))
        (F.val x) (derVals Q kh (F.val x 0) (F.val x 1)) j) ∧
      (∀ s, (∀ j : Fin 39, s ≠ sk 0 (symO j)) → τ.st s = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (cx ++ cy))).st s) ∧
      τ.cell = false := by
  set ell := max (kh + kh) (Nat.clog 2 Q) with hell
  set cnt := gs * fs * pi * 2 ^ wOf kh Q with hcnt
  set dRv := (P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2) with hdRv
  set d2 := 0 + dRv + dRv with hd2
  set fr := F.val x with hfr
  set dd := derVals Q kh (F.val x 0) (F.val x 1) with hdd
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ1, c1, e1, v1N, v1A, v1NC, v1M0, v1M1, v1M2, v1M3, v1MS, v1L, v1r, v1s, v1b, v1r2, v1kh, v1k, v1err, v1cap,
    v1G, v1Q, v1z, v1st, v1sh, v1cl, c1le⟩ := numsS_spec cap cr fe h0 h1 Cδ C P hrP w codes ccs tl cx cy Kb Cmax capS err L
      kh hw hccs hcx hcy hKb hC hN1 hcapS herr hL hkh hcS hcP hcC hN2 hn hQ hv
  rw [← hQd] at v1Q
  obtain ⟨τ2, c2, e2, c2le, s2X2, s2N0, s2W0, s2P1, s2CC, s2ST, s2D2, s2X0, s2T, s2fr, s2st, s2sh, s2cl⟩ :=
    seed_spec cap τ1 Q kh gs fs pi P.b P.s (P.r / 2) P.r P.n v1Q v1kh
      (by rw [v1G]; exact hgs.symm) (by rw [v1G]; exact hfs.symm) (by rw [v1G, hpi]; rfl) v1b v1s v1r2 v1r v1N
      (fun q h1' h2' => v1z q h1' h2') hsc
  have k2 : ∀ q : Fin LNR, (q.val < 64 ∨ 127 ≤ q.val) → τ2.val q = τ1.val q := s2fr
  have hfreg : FreeRegs τ2 x := by
    rw [hx]
    exact ⟨by rw [k2 _ (by right; decide)]; exact v1N, by rw [k2 _ (by right; decide)]; exact v1kh,
      by rw [k2 _ (by right; decide)]; exact v1L, by rw [k2 _ (by right; decide)]; exact v1cap,
      by rw [k2 _ (by right; decide)]; exact v1A, by rw [k2 _ (by right; decide)]; exact v1NC,
      by rw [k2 _ (by right; decide)]; exact v1MS, by rw [k2 _ (by left; decide)]; exact v1Q, s2X2, s2N0, s2W0, s2ST⟩
  obtain ⟨τ3, e3, s3fb, s3fr, s3st, s3sh, s3cl⟩ := F.run cap τ2 x hfreg
    (fun q h1' h2' => by rw [k2 q (by right; omega)]; exact v1z q (by omega) (by omega))
    (fun q h1' h2' => by rw [k2 q (by right; omega)]; exact v1z q (by omega) (by omega)) hF
  have k3 : ∀ q : Fin LNR, (q.val < 130 ∨ (137 ≤ q.val ∧ q.val < 177) ∨ 200 ≤ q.val) → τ3.val q = τ2.val q := s3fr
  obtain ⟨τ4, c4, e4, c4le, d0, d1, d2', d3, d4, d5, d6, r0, r4, t4, fr4, rb4, st4, sh4, cl4⟩ :=
    der_spec cap τ3 Q kh (F.val x 0) (F.val x 1)
      (by rw [k3 _ (by left; decide)]; exact s2X0) (by rw [k3 _ (by left; decide)]; exact s2X2) (s3fb 0) (s3fb 1)
      (by rw [k3 _ (by left; decide)]; exact s2W0) (by rw [k3 _ (by left; decide), k2 _ (by left; decide)]; exact v1Q)
      (fun q h1' h2' => by rw [k3 q (by right; left; omega), k2 q (by right; omega)]; exact v1z q (by omega) (by omega))
      (by rw [k3 _ (by left; decide)]; exact s2T) hdc
  have k4 : ∀ q : Fin LNR, (q.val < 140 ∨ 177 ≤ q.val) → τ4.val q = τ3.val q := fr4
  have hSR : SymRegs τ4 Q kh ell cnt d2 fr dd := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun j => ?_, fun i => ?_, r0, r4, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2X0
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2X2
    · rw [k4 _ (by right; decide), k3 _ (by right; right; decide), k2 _ (by right; decide)]; exact v1kh
    · rw [k4 _ (by left; decide), k3 _ (by left; decide), k2 _ (by left; decide)]; exact v1Q
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2CC
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2D2
    · rw [k4 _ (by left; simp [FB, blk_val]; omega)]; exact s3fb j
    · fin_cases i
      · exact d0
      · exact d1
      · exact d2'
      · exact d3
      · exact d4
      · exact d5
      · exact d6
    all_goals first
      | (rw [rb4 _ (by decide), k3 _ (by right; left; decide), k2 _ (by right; decide)]
         exact v1z _ (by decide) (by decide))
  have hst4 : τ4.st = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (cx ++ cy))).st := by rw [st4, s3st, s2st, v1st]
  have hsk : ∀ k : Fin 161, 120 ≤ k.val → (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (cx ++ cy))).st (sk 0 k) = [] := by
    intro k hk
    have n0 : sk 0 k ≠ sk 0 0 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n1 : sk 0 k ≠ sk 0 1 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n2 : sk 0 k ≠ sk 0 2 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n3 : sk 0 k ≠ sk 0 113 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n0, n1, n2, n3]
  have hsh4 : ∀ k : Fin 161, 120 ≤ k.val → τ4.sh (sk 0 k) = 0 := by
    intro k hk
    have n3 : sk 0 k ≠ sk 0 113 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n1 : sk 0 k ≠ sk 0 1 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    rw [sh4, s3sh, s2sh, v1sh _ n3]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n1]
  have hok := symEmits_ok cap τ4 Q kh ell cnt d2 fr dd hSR (fun k hk => by rw [hst4]; exact hsk k hk) hsh4
    (fun q h1' h2' => by rw [k4 q (by right; omega), k3 q (by right; right; omega), k2 q (by right; omega)]
                         exact v1z q (by omega) (by omega))
    cQl cQ cl ck cfr cdd ccnt (by rw [hd2]; exact cd2) c17
  obtain ⟨τ5, e5, sE, sO, -, -, -, cl5⟩ := emitsW_spec cap symEmits τ4 hok symEmits_O_nodup symEmits_OP_nodup
    (by rw [k4 _ (by right; decide), k3 _ (by right; right; decide), k2 _ (by right; decide)]; exact v1z _ (by decide) (by decide))
    (by rw [k4 _ (by right; decide), k3 _ (by right; right; decide), k2 _ (by right; decide)]; exact v1z _ (by decide) (by decide))
  have hcost5 : (symEmits.map (wordCost τ4)).sum + symEmits.length ≤ 400 * UnaryPow.sq cap := by
    have hle : ∀ e ∈ symEmits, wordCost τ4 e ≤ 8 * UnaryPow.sq cap := by
      intro e he
      obtain ⟨sh1, sh2, sh3⟩ := symEmits_short e he
      have hw := hok e he
      refine wordCost_le cap τ4 e (fun p hp A u hpA => ⟨(hw.hps p hp A u hpA).2, sh1 p hp A u hpA⟩) sh2 sh3
        (fun R hR => ?_)
      have hhd := hw.hhd
      rw [hR] at hhd
      obtain ⟨-, -, -, -, -, -, -, -, hc⟩ := hhd
      omega
    have := List.sum_le_card_nsmul (symEmits.map (wordCost τ4)) (8 * UnaryPow.sq cap) (fun y hy => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy; exact hle e he)
    simp only [List.length_map, symEmits_length, smul_eq_mul] at this
    rw [symEmits_length]
    omega
  have fin0 : τ5.st (sk 0 120) = symClean Q kh ell cnt d2 fr dd 0 := by
    have hw := symW0 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin1 : τ5.st (sk 0 121) = symClean Q kh ell cnt d2 fr dd 1 := by
    have hw := symW1 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin2 : τ5.st (sk 0 122) = symClean Q kh ell cnt d2 fr dd 2 := by
    have hw := symW2 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin3 : τ5.st (sk 0 123) = symClean Q kh ell cnt d2 fr dd 3 := by
    have hw := symW3 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin4 : τ5.st (sk 0 124) = symClean Q kh ell cnt d2 fr dd 4 := by
    have hw := symW4 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin5 : τ5.st (sk 0 125) = symClean Q kh ell cnt d2 fr dd 5 := by
    have hw := symW5 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin6 : τ5.st (sk 0 126) = symClean Q kh ell cnt d2 fr dd 6 := by
    have hw := symW6 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin7 : τ5.st (sk 0 127) = symClean Q kh ell cnt d2 fr dd 7 := by
    have hw := symW7 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin8 : τ5.st (sk 0 128) = symClean Q kh ell cnt d2 fr dd 8 := by
    have hw := symW8 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin9 : τ5.st (sk 0 129) = symClean Q kh ell cnt d2 fr dd 9 := by
    have hw := symW9 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin10 : τ5.st (sk 0 130) = symClean Q kh ell cnt d2 fr dd 10 := by
    have hw := symW10 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin11 : τ5.st (sk 0 131) = symClean Q kh ell cnt d2 fr dd 11 := by
    have hw := symW11 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin12 : τ5.st (sk 0 132) = symClean Q kh ell cnt d2 fr dd 12 := by
    have hw := symW12 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin13 : τ5.st (sk 0 133) = symClean Q kh ell cnt d2 fr dd 13 := by
    have hw := symW13 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin14 : τ5.st (sk 0 135) = symClean Q kh ell cnt d2 fr dd 14 := by
    have hw := symW14 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin15 : τ5.st (sk 0 136) = symClean Q kh ell cnt d2 fr dd 15 := by
    have hw := symW15 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin16 : τ5.st (sk 0 137) = symClean Q kh ell cnt d2 fr dd 16 := by
    have hw := symW16 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin17 : τ5.st (sk 0 138) = symClean Q kh ell cnt d2 fr dd 17 := by
    have hw := symW17 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin18 : τ5.st (sk 0 139) = symClean Q kh ell cnt d2 fr dd 18 := by
    have hw := symW18 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin19 : τ5.st (sk 0 140) = symClean Q kh ell cnt d2 fr dd 19 := by
    have hw := symW19 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin20 : τ5.st (sk 0 141) = symClean Q kh ell cnt d2 fr dd 20 := by
    have hw := symW20 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin21 : τ5.st (sk 0 142) = symClean Q kh ell cnt d2 fr dd 21 := by
    have hw := symW21 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin22 : τ5.st (sk 0 143) = symClean Q kh ell cnt d2 fr dd 22 := by
    have hw := symW22 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin23 : τ5.st (sk 0 144) = symClean Q kh ell cnt d2 fr dd 23 := by
    have hw := symW23 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin24 : τ5.st (sk 0 145) = symClean Q kh ell cnt d2 fr dd 24 := by
    have hw := symW24 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin25 : τ5.st (sk 0 146) = symClean Q kh ell cnt d2 fr dd 25 := by
    have hw := symW25 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin26 : τ5.st (sk 0 147) = symClean Q kh ell cnt d2 fr dd 26 := by
    have hw := symW26 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin27 : τ5.st (sk 0 148) = symClean Q kh ell cnt d2 fr dd 27 := by
    have hw := symW27 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin28 : τ5.st (sk 0 149) = symClean Q kh ell cnt d2 fr dd 28 := by
    have hw := symW28 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin29 : τ5.st (sk 0 150) = symClean Q kh ell cnt d2 fr dd 29 := by
    have hw := symW29 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin30 : τ5.st (sk 0 151) = symClean Q kh ell cnt d2 fr dd 30 := by
    have hw := symW30 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin31 : τ5.st (sk 0 152) = symClean Q kh ell cnt d2 fr dd 31 := by
    have hw := symW31 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin32 : τ5.st (sk 0 153) = symClean Q kh ell cnt d2 fr dd 32 := by
    have hw := symW32 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin33 : τ5.st (sk 0 154) = symClean Q kh ell cnt d2 fr dd 33 := by
    have hw := symW33 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin34 : τ5.st (sk 0 155) = symClean Q kh ell cnt d2 fr dd 34 := by
    have hw := symW34 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin35 : τ5.st (sk 0 156) = symClean Q kh ell cnt d2 fr dd 35 := by
    have hw := symW35 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin36 : τ5.st (sk 0 157) = symClean Q kh ell cnt d2 fr dd 36 := by
    have hw := symW36 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin37 : τ5.st (sk 0 158) = symClean Q kh ell cnt d2 fr dd 37 := by
    have hw := symW37 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin38 : τ5.st (sk 0 159) = symClean Q kh ell cnt d2 fr dd 38 := by
    have hw := symW38 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  refine ⟨τ5, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), by omega, fun j => ?_, fun s hs => ?_, ?_⟩
  · fin_cases j
    · exact fin0
    · exact fin1
    · exact fin2
    · exact fin3
    · exact fin4
    · exact fin5
    · exact fin6
    · exact fin7
    · exact fin8
    · exact fin9
    · exact fin10
    · exact fin11
    · exact fin12
    · exact fin13
    · exact fin14
    · exact fin15
    · exact fin16
    · exact fin17
    · exact fin18
    · exact fin19
    · exact fin20
    · exact fin21
    · exact fin22
    · exact fin23
    · exact fin24
    · exact fin25
    · exact fin26
    · exact fin27
    · exact fin28
    · exact fin29
    · exact fin30
    · exact fin31
    · exact fin32
    · exact fin33
    · exact fin34
    · exact fin35
    · exact fin36
    · exact fin37
    · exact fin38
  · rw [sO s (fun e he => ?_), hst4]
    obtain ⟨k, hk⟩ := List.get_of_mem he
    rw [← hk]
    have := hs ⟨k.val, by rw [← symEmits_length]; exact k.isLt⟩
    intro e2'
    apply this
    rw [e2']
    fin_cases k <;> rfl
  · rw [cl5, cl4, s3cl, s2cl, v1cl]

end NearCubicWires.WireExponent3_5.PrimT.C4Set
