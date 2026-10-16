import HDLean.Rtl.Blast.Vec

/-!
# Bit-blasting one cell

`blastOp` turns a non-instance cell into gates, reading its operands from a
frame of bits. Every operation checks the widths it relies on and fails
closed. `blastOp_ok`: if it succeeds and the frame's bits denote the cycle's
values, the result denotes exactly `Op.evalBV`.
-/
namespace HDLean.Rtl.Blast
open Std.Sat Std.Sat.AIG Std.Tactic.BVDecide BVExpr.bitblast BVPred

/-- Bits of everything a cell may read. -/
structure BFrame where
  ins : Array Bits
  regs : Array Bits
  mems : Array (Array Bits)
  vals : Array Bits

def BFrame.v (fr : BFrame) (k : Nat) : Bits := fr.vals.getD k #[]

/-- Raw value `n` read at the bits' own width. -/
def RawDen (aig : AIG Nat) (assign : Nat → Bool) (bits : Bits) (n : Nat) : Prop :=
  Denotes aig assign bits (bv bits.size n)

theorem RawDen.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {bits : Bits} {n : Nat}
    (h : RawDen aig assign bits n) (hp : IsPrefix aig.decls aig'.decls) : RawDen aig' assign bits n :=
  Denotes.mono h hp

theorem RawDen.at {aig : AIG Nat} {assign : Nat → Bool} {bits : Bits} {n w : Nat}
    (h : RawDen aig assign bits n) (hs : bits.size = w) : Denotes aig assign bits (bv w n) := by
  subst hs; exact h

/-- The frame's bits denote the frame's values; cell values are reduced to their width. -/
structure FrameOk (aig : AIG Nat) (assign : Nat → Bool) (fr : BFrame) (F : Frame) : Prop where
  vals : ∀ k, RawDen aig assign (fr.v k) (F.val k) ∧ F.val k < 2 ^ (fr.v k).size
  ins : ∀ k, RawDen aig assign (fr.ins.getD k #[]) (F.input k)
  regs : ∀ k, RawDen aig assign (fr.regs.getD k #[]) (F.reg k)
  mems : ∀ mi a, RawDen aig assign ((fr.mems.getD mi #[]).getD a #[]) (F.mem mi a)

theorem FrameOk.mono {aig aig' : AIG Nat} {assign : Nat → Bool} {fr : BFrame} {F : Frame}
    (h : FrameOk aig assign fr F) (hp : IsPrefix aig.decls aig'.decls) : FrameOk aig' assign fr F :=
  ⟨fun k => ⟨(h.vals k).1.mono hp, (h.vals k).2⟩, fun k => (h.ins k).mono hp, fun k => (h.regs k).mono hp,
    fun mi a => (h.mems mi a).mono hp⟩

theorem Yields.get {aig : AIG Nat} {assign : Nat → Bool} {r : Option (Bits × AIG Nat)} {x : BitVec w}
    {bits : Bits} {aig' : AIG Nat} (hy : Yields aig assign r x) (h : r = some (bits, aig')) :
    IsPrefix aig.decls aig'.decls ∧ Denotes aig' assign bits x := by
  obtain ⟨b, a, hr, hp, hd⟩ := hy
  rw [hr] at h; cases h; exact ⟨hp, hd⟩

/-! ## Operators -/

def blastBin (op : BinOp) (a b : Bits) (w : Nat) (aig : AIG Nat) : Option (Bits × AIG Nat) :=
  match op with
  | .and => vzip mkAndCached a b w aig
  | .or => vzip mkOrCached a b w aig
  | .xor => vzip mkXorCached a b w aig
  | .nand => do let (t, aig) ← vzip mkAndCached a b w aig; vop1 blastNot t w aig
  | .nor => do let (t, aig) ← vzip mkOrCached a b w aig; vop1 blastNot t w aig
  | .xnor => do let (t, aig) ← vzip mkXorCached a b w aig; vop1 blastNot t w aig
  | .add => vop2 blastAdd a b w aig
  | .sub => vop2 blastSub a b w aig
  | .mul => vop2 blastMul a b w aig
  | .udiv => vop2 blastUdiv a b w aig
  | .umod => vop2 blastUmod a b w aig
  | .shl => vshift blastShiftLeft a b w b.size aig
  | .lshr => vshift blastShiftRight a b w b.size aig
  | .ashr => vshift blastArithShiftRight a b w b.size aig

def sltBits (a b : Bits) (cw : Nat) (aig : AIG Nat) : Option (Bits × AIG Nat) := do
  let (u, aig) ← bit2 (w := cw) mkUlt a b aig
  let (x1, aig) ← gate2 mkXorCached (bitOr a (cw - 1) false) (bitOr b (cw - 1) false) aig
  let (x2, aig) ← gate2 mkXorCached x1 (u.getD 0 (fconst false)) aig
  pure (bitOf x2, aig)

def blastCmp (op : CmpOp) (a b : Bits) (cw : Nat) (aig : AIG Nat) : Option (Bits × AIG Nat) :=
  match op with
  | .eq => bit2 (w := cw) mkEq a b aig
  | .ne => (bit2 (w := cw) mkEq a b aig).map fun p => (bitNot p.1, p.2)
  | .ult => bit2 (w := cw) mkUlt a b aig
  | .ule => (bit2 (w := cw) mkUlt b a aig).map fun p => (bitNot p.1, p.2)
  | .slt => sltBits a b cw aig
  | .sle => (sltBits b a cw aig).map fun p => (bitNot p.1, p.2)

/-- Read one of `2 ^ n` entries starting at `base`, selected by the low `n` address bits. -/
def muxTree (entries : Nat → Bits) (addr : Bits) (w : Nat) : Nat → Nat → AIG Nat → Option (Bits × AIG Nat)
  | 0, base, aig => some (entries base, aig)
  | n + 1, base, aig => do
    let (hi, aig) ← muxTree entries addr w n (base + 2 ^ n) aig
    let (lo, aig) ← muxTree entries addr w n base aig
    vite (bitOr addr n false) hi lo w aig

def blastOp (fr : BFrame) (w : Nat) (op : Op) (aig : AIG Nat) : Option (Bits × AIG Nat) :=
  match op with
  | .const n => some (constBits w n, aig)
  | .input k => if (fr.ins.getD k #[]).size = w then some (fr.ins.getD k #[], aig) else none
  | .reg k => if (fr.regs.getD k #[]).size = w then some (fr.regs.getD k #[], aig) else none
  | .memRead mi a =>
    let entries := fr.mems.getD mi #[]
    if (List.range (2 ^ (fr.v a).size)).all (fun idx => (entries.getD idx #[]).size == w) then
      muxTree (fun idx => entries.getD idx #[]) (fr.v a) w (fr.v a).size 0 aig
    else none
  | .not a => if (fr.v a).size = w then vop1 blastNot (fr.v a) w aig else none
  | .neg a => if (fr.v a).size = w then vop1 blastNeg (fr.v a) w aig else none
  | .bin op a b =>
    if (fr.v a).size = w ∧ (op.isShift = true ∨ (fr.v b).size = w) then blastBin op (fr.v a) (fr.v b) w aig
    else none
  | .cmp op cw a b =>
    if (fr.v a).size = cw ∧ (fr.v b).size = cw then
      (blastCmp op (fr.v a) (fr.v b) cw aig).map fun p => (zextBits p.1 w, p.2)
    else none
  | .mux s a b =>
    if 0 < (fr.v s).size ∧ (fr.v a).size = w ∧ (fr.v b).size = w then
      vite (bitOr (fr.v s) 0 false) (fr.v a) (fr.v b) w aig
    else none
  | .slice a lo => some (sliceBits (fr.v a) lo w, aig)
  | .concat h l lw =>
    if (fr.v h).size = w - lw ∧ (fr.v l).size = lw then some (zextBits (concatBits (fr.v h) (fr.v l)) w, aig)
    else none
  | .zext a => some (zextBits (fr.v a) w, aig)
  | .sext a fw => if (fr.v a).size = fw then some (sextBits (fr.v a) w, aig) else none
  | .inst .. => none


/-! ## Correctness -/

theorem vshift_ok' (f : {len : Nat} → (aig : AIG Nat) → ArbitraryShiftTarget aig len → RefVecEntry Nat len)
    [LawfulVecOperator Nat ArbitraryShiftTarget f] (op : ∀ {n : Nat}, BitVec w → BitVec n → BitVec w)
    (hf : ∀ (aig : AIG Nat) (target : ArbitraryShiftTarget aig w) (x : BitVec w) (y : BitVec target.n)
      (assign : Nat → Bool),
      (∀ idx (hidx : idx < w), ⟦aig, target.target.get idx hidx, assign⟧ = x.getLsbD idx) →
      (∀ idx (hidx : idx < target.n), ⟦aig, target.distance.get idx hidx, assign⟧ = y.getLsbD idx) →
      ∀ idx (hidx : idx < w), ⟦(f aig target).aig, (f aig target).vec.get idx hidx, assign⟧ = (op x y).getLsbD idx)
    {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x : BitVec w} {y : BitVec v}
    (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) :
    Yields aig assign (vshift f a b w v aig) (op x y) := by
  apply vshift_ok f (fun x y => op x y) _ ha hb
  intro aig' target x' y' assign' hn hl hr
  obtain ⟨n, t, d⟩ := target
  simp only at hn
  subst hn
  exact hf aig' ⟨_, t, d⟩ x' y' assign' hl hr

private theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : x.bind f = some b) : ∃ a, x = some a ∧ f a = some b := Option.bind_eq_some_iff.mp h

theorem blastBin_ok (op : BinOp) {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x : BitVec w}
    (ha : Denotes aig assign a x) (nb : Nat) (hb : RawDen aig assign b nb) (hbn : nb < 2 ^ b.size)
    (hsz : op.isShift = true ∨ b.size = w) {bits : Bits} {aig' : AIG Nat}
    (h : blastBin op a b w aig = some (bits, aig')) :
    IsPrefix aig.decls aig'.decls ∧ Denotes aig' assign bits (op.eval x (bv w nb) nb) := by
  have hbw : op.isShift = false → Denotes aig assign b (bv w nb) := fun hs => by
    rcases hsz with h' | h'
    · simp [hs] at h'
    · exact hb.at h'
  have hnb : (bv b.size nb).toNat = nb := by simp [bv, Nat.mod_eq_of_lt hbn]
  have zipAnd := fun {aig : AIG Nat} {a b : Bits} {x y : BitVec w} (ha : Denotes aig assign a x)
      (hb : Denotes aig assign b y) =>
    vzip_ok mkAndCached (· && ·) (· &&& ·) (fun _ _ _ => denote_mkAndCached)
      (fun x y i => by
        rcases Nat.lt_or_ge i w with hi | hi
        · simp [hi, BitVec.getLsbD_and]
        · simp [Nat.not_lt.mpr hi, BitVec.getLsbD_and, BitVec.getLsbD_of_ge x i hi]) ha hb
  have zipOr := fun {aig : AIG Nat} {a b : Bits} {x y : BitVec w} (ha : Denotes aig assign a x)
      (hb : Denotes aig assign b y) =>
    vzip_ok mkOrCached (· || ·) (· ||| ·) (fun _ _ _ => denote_mkOrCached)
      (fun x y i => by
        rcases Nat.lt_or_ge i w with hi | hi
        · simp [hi, BitVec.getLsbD_or]
        · simp [Nat.not_lt.mpr hi, BitVec.getLsbD_or, BitVec.getLsbD_of_ge x i hi, BitVec.getLsbD_of_ge y i hi]) ha hb
  have zipXor := fun {aig : AIG Nat} {a b : Bits} {x y : BitVec w} (ha : Denotes aig assign a x)
      (hb : Denotes aig assign b y) =>
    vzip_ok mkXorCached (· ^^ ·) (· ^^^ ·) (fun _ _ _ => denote_mkXorCached)
      (fun x y i => by
        rcases Nat.lt_or_ge i w with hi | hi
        · simp [hi, BitVec.getLsbD_xor]
        · simp [Nat.not_lt.mpr hi, BitVec.getLsbD_xor, BitVec.getLsbD_of_ge x i hi, BitVec.getLsbD_of_ge y i hi]) ha hb
  have notOk := fun {aig : AIG Nat} {a : Bits} {x : BitVec w} (ha : Denotes aig assign a x) =>
    vop1_ok blastNot (~~~ ·) (fun aig input x assign hx idx hidx => by
      rw [denote_blastNot, hx, BitVec.getLsbD_not]; simp [hidx]) ha
  cases op with
  | and => exact (zipAnd ha (hbw rfl)).get h
  | or => exact (zipOr ha (hbw rfl)).get h
  | xor => exact (zipXor ha (hbw rfl)).get h
  | nand =>
    obtain ⟨⟨t, a1⟩, h1, h2⟩ := bind_some h
    obtain ⟨p1, d1⟩ := (zipAnd ha (hbw rfl)).get h1
    obtain ⟨p2, d2⟩ := (notOk d1).get h2
    exact ⟨IsPrefix.trans' p1 p2, d2⟩
  | nor =>
    obtain ⟨⟨t, a1⟩, h1, h2⟩ := bind_some h
    obtain ⟨p1, d1⟩ := (zipOr ha (hbw rfl)).get h1
    obtain ⟨p2, d2⟩ := (notOk d1).get h2
    exact ⟨IsPrefix.trans' p1 p2, d2⟩
  | xnor =>
    obtain ⟨⟨t, a1⟩, h1, h2⟩ := bind_some h
    obtain ⟨p1, d1⟩ := (zipXor ha (hbw rfl)).get h1
    obtain ⟨p2, d2⟩ := (notOk d1).get h2
    exact ⟨IsPrefix.trans' p1 p2, d2⟩
  | add => exact (vop2_ok blastAdd (· + ·) (fun aig input x y assign hl hr => denote_blastAdd aig x y assign input hl hr)
      ha (hbw rfl)).get h
  | sub => exact (vop2_ok blastSub (· - ·) (fun aig input x y assign hl hr => denote_blastSub aig x y assign input hl hr)
      ha (hbw rfl)).get h
  | mul => exact (vop2_ok blastMul (· * ·) (fun aig input x y assign hl hr => denote_blastMul aig x y assign input hl hr)
      ha (hbw rfl)).get h
  | udiv => exact (vop2_ok blastUdiv (· / ·) (fun aig input x y assign hl hr => denote_blastUdiv aig x y assign input hl hr)
      ha (hbw rfl)).get h
  | umod => exact (vop2_ok blastUmod (· % ·) (fun aig input x y assign hl hr => denote_blastUmod aig x y assign input hl hr)
      ha (hbw rfl)).get h
  | shl =>
    have := (vshift_ok' blastShiftLeft (fun x y => x <<< y)
      (fun aig target x y assign hl hr => denote_blastShiftLeft aig target x y assign hl hr) ha hb).get h
    simpa [BinOp.eval, hnb] using this
  | lshr =>
    have := (vshift_ok' blastShiftRight (fun x y => x >>> y)
      (fun aig target x y assign hl hr => denote_blastShiftRight aig target x y assign hl hr) ha hb).get h
    simpa [BinOp.eval, hnb] using this
  | ashr =>
    have := (vshift_ok' blastArithShiftRight (fun x y => BitVec.sshiftRight' x y)
      (fun aig target x y assign hl hr => denote_blastArithShiftRight aig target x y assign hl hr) ha hb).get h
    simpa [BinOp.eval, BitVec.sshiftRight', hnb] using this


private theorem map_some {α β : Type} {x : Option α} {f : α → β} {b : β}
    (h : x.map f = some b) : ∃ a, x = some a ∧ f a = b := Option.map_eq_some_iff.mp h

theorem bit_of_denotes {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {x : BitVec w} (h : Denotes aig assign a x)
    (i : Nat) : BitIs aig assign (bitOr a i false) (if i < w then x.getLsbD i else false) := bitOr_ok h i false

theorem msb_bit {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {x : BitVec w} (h : Denotes aig assign a x) :
    BitIs aig assign (bitOr a (w - 1) false) x.msb := by
  have := bit_of_denotes h (w - 1)
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw; simpa [BitVec.msb] using this
  · rwa [if_pos (by omega), ← BitVec.msb_eq_getLsbD_last] at this

theorem single_bit {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {c : Bool}
    (h : Denotes aig assign a (BitVec.ofBool c)) : BitIs aig assign (a.getD 0 (fconst false)) c := by
  have hs := h.size
  obtain ⟨hb, hd⟩ := h.bit 0 (by omega)
  have heq : a.getD 0 (fconst false) = a[0]'(by omega) := by
    simp [Array.getD_eq_getD_getElem?, show 0 < a.size by omega]
  rw [heq]
  exact ⟨hb, by rw [hd]; simp⟩

theorem sltBits_ok {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x y : BitVec cw}
    (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) {bits : Bits} {aig' : AIG Nat}
    (h : sltBits a b cw aig = some (bits, aig')) :
    IsPrefix aig.decls aig'.decls ∧ Denotes aig' assign bits (BitVec.ofBool (x.slt y)) := by
  unfold sltBits at h
  obtain ⟨⟨u, a1⟩, h1, h2⟩ := bind_some h
  obtain ⟨p1, d1⟩ := (bit2_ok (w := cw) mkUlt (fun x y => x.ult y)
    (fun aig input x y assign hl hr => mkUlt_denote_eq aig x y input assign hl hr) ha hb).get h1
  obtain ⟨⟨x1, a2⟩, h3, h4⟩ := bind_some h2
  obtain ⟨r1, a2', e1, p2, d2⟩ := gate2_ok mkXorCached (· ^^ ·) (fun _ _ _ => denote_mkXorCached)
    ((msb_bit ha).mono p1) ((msb_bit hb).mono p1)
  rw [e1] at h3; cases h3
  obtain ⟨⟨x2, a3⟩, h5, h6⟩ := bind_some h4
  obtain ⟨r2, a3', e2, p3, d3⟩ := gate2_ok mkXorCached (· ^^ ·) (fun _ _ _ => denote_mkXorCached) d2
    ((single_bit d1).mono p2)
  rw [e2] at h5; cases h5
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h6
  obtain ⟨rfl, rfl⟩ := h6
  refine ⟨IsPrefix.trans' p1 (IsPrefix.trans' p2 p3), bitOf_ok _ _ ?_⟩
  obtain ⟨hb3, hd3⟩ := d3
  exact ⟨hb3, by rw [hd3, BitVec.slt_eq_ult]⟩

theorem blastCmp_ok (op : CmpOp) {aig : AIG Nat} {assign : Nat → Bool} {a b : Bits} {x y : BitVec cw}
    (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) {bits : Bits} {aig' : AIG Nat}
    (h : blastCmp op a b cw aig = some (bits, aig')) :
    IsPrefix aig.decls aig'.decls ∧ Denotes aig' assign bits (BitVec.ofBool (op.eval x y)) := by
  have eqOk := fun {a b : Bits} {x y : BitVec cw} (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) =>
    bit2_ok (w := cw) mkEq (fun x y => x == y)
      (fun aig input x y assign hl hr => mkEq_denote_eq aig input assign x y hl hr) ha hb
  have ultOk := fun {a b : Bits} {x y : BitVec cw} (ha : Denotes aig assign a x) (hb : Denotes aig assign b y) =>
    bit2_ok (w := cw) mkUlt (fun x y => x.ult y)
      (fun aig input x y assign hl hr => mkUlt_denote_eq aig x y input assign hl hr) ha hb
  cases op with
  | eq => exact (eqOk ha hb).get h
  | ult => exact (ultOk ha hb).get h
  | ne =>
    obtain ⟨⟨t, a1⟩, h1, h2⟩ := map_some h
    cases h2
    obtain ⟨p, d⟩ := (eqOk ha hb).get h1
    have := bitNot_ok d
    exact ⟨p, by simpa [CmpOp.eval, bne] using this⟩
  | ule =>
    obtain ⟨⟨t, a1⟩, h1, h2⟩ := map_some h
    cases h2
    obtain ⟨p, d⟩ := (ultOk hb ha).get h1
    exact ⟨p, by simpa [CmpOp.eval, BitVec.ule_eq_not_ult] using bitNot_ok d⟩
  | slt => exact sltBits_ok ha hb h
  | sle =>
    obtain ⟨⟨t, a1⟩, h1, h2⟩ := map_some h
    cases h2
    obtain ⟨p, d⟩ := sltBits_ok hb ha h1
    exact ⟨p, by simpa [CmpOp.eval, BitVec.sle_eq_not_slt] using bitNot_ok d⟩

theorem muxTree_ok {entries : Nat → Bits} {addr : Bits} {E : Nat → BitVec w} {assign : Nat → Bool} (m : Nat) :
    ∀ (n base : Nat) (aig : AIG Nat) (bits : Bits) (aig' : AIG Nat),
      (∀ j, j < n → BitIs aig assign (bitOr addr j false) (m.testBit j)) →
      (∀ idx, base ≤ idx → idx < base + 2 ^ n → Denotes aig assign (entries idx) (E idx)) →
      muxTree entries addr w n base aig = some (bits, aig') →
      IsPrefix aig.decls aig'.decls ∧ Denotes aig' assign bits (E (base + m % 2 ^ n))
  | 0, base, aig, bits, aig', _, he, h => by
    simp only [muxTree, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨IsPrefix.refl' aig, ?_⟩
    rw [Nat.pow_zero, Nat.mod_one, Nat.add_zero]
    exact he base (Nat.le_refl _) (by simp)
  | n + 1, base, aig, bits, aig', hbits, he, h => by
    simp only [muxTree] at h
    obtain ⟨⟨hi, a1⟩, h1, h2⟩ := bind_some h
    obtain ⟨⟨lo, a2⟩, h3, h4⟩ := bind_some h2
    obtain ⟨p1, d1⟩ := muxTree_ok m n (base + 2 ^ n) aig hi a1 (fun j hj => hbits j (by omega))
      (fun idx h1 h2 => he idx (by omega) (by rw [Nat.pow_succ]; omega)) h1
    obtain ⟨p2, d2⟩ := muxTree_ok m n base a1 lo a2 (fun j hj => (hbits j (by omega)).mono p1)
      (fun idx h1 h2 => (he idx h1 (by rw [Nat.pow_succ]; omega)).mono p1) h3
    obtain ⟨p3, d3⟩ := (vite_ok ((hbits n (by omega)).mono (IsPrefix.trans' p1 p2)) (d1.mono p2) d2).get h4
    refine ⟨IsPrefix.trans' p1 (IsPrefix.trans' p2 p3), ?_⟩
    have hmod : m % 2 ^ (n + 1) = m % 2 ^ n + 2 ^ n * (m / 2 ^ n % 2) := Nat.mod_pow_succ
    rw [hmod]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with hb | hb
    · have : m.testBit n = false := by simp [Nat.testBit_eq_decide_div_mod_eq, hb]
      simpa [this, hb] using d3
    · have : m.testBit n = true := by simp [Nat.testBit_eq_decide_div_mod_eq, hb]
      simp only [this, if_true] at d3
      simpa [hb, Nat.add_assoc, Nat.add_comm (2 ^ n)] using d3


theorem testBit_of_denotes {aig : AIG Nat} {assign : Nat → Bool} {a : Bits} {n : Nat} (h : RawDen aig assign a n)
    (j : Nat) (hj : j < a.size) : BitIs aig assign (bitOr a j false) (n.testBit j) := by
  have := bit_of_denotes h j
  rwa [if_pos hj, bv, BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and] at this

/-- Gates for one cell denote the cell's value. -/
theorem blastOp_ok {aig : AIG Nat} {assign : Nat → Bool} {fr : BFrame} {F : Frame}
    (hf : FrameOk aig assign fr F) (w : Nat) (op : Op) {bits : Bits} {aig' : AIG Nat}
    (h : blastOp fr w op aig = some (bits, aig')) :
    IsPrefix aig.decls aig'.decls ∧ Denotes aig' assign bits (op.evalBV F w) := by
  cases op with
  | const n =>
    simp only [blastOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨IsPrefix.refl' aig, constBits_ok aig assign w n⟩
  | input k =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨IsPrefix.refl' aig, (hf.ins k).at hs⟩
    · cases h
  | reg k =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨IsPrefix.refl' aig, (hf.regs k).at hs⟩
    · cases h
  | memRead mi a =>
    simp only [blastOp] at h
    split at h
    · rename_i hall
      have hsz : ∀ idx, idx < 2 ^ (fr.v a).size → ((fr.mems.getD mi #[]).getD idx #[]).size = w := by
        intro idx hidx
        have := List.all_eq_true.mp hall idx (List.mem_range.mpr hidx)
        simpa using this
      obtain ⟨p, d⟩ := muxTree_ok (E := fun idx => bv w (F.mem mi idx)) (F.val a) (fr.v a).size 0 aig bits aig'
        (fun j hj => testBit_of_denotes (hf.vals a).1 j hj)
        (fun idx _ h2 => (hf.mems mi idx).at (hsz idx (by simpa using h2))) h
      refine ⟨p, ?_⟩
      simpa [Op.evalBV, Nat.mod_eq_of_lt (hf.vals a).2] using d
    · cases h
  | not a =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      exact (vop1_ok blastNot (~~~ ·) (fun aig input x assign hx idx hidx => by
        rw [denote_blastNot, hx, BitVec.getLsbD_not]; simp [hidx]) ((hf.vals a).1.at hs)).get h
    · cases h
  | neg a =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      exact (vop1_ok blastNeg (- ·) (fun aig input x assign hx => denote_blastNeg aig x input assign hx)
        ((hf.vals a).1.at hs)).get h
    · cases h
  | bin o a b =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      exact blastBin_ok o ((hf.vals a).1.at hs.1) (F.val b) (hf.vals b).1 (hf.vals b).2 hs.2 h
    · cases h
  | cmp o cw a b =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      obtain ⟨⟨t, a1⟩, h1, h2⟩ := map_some h
      simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨p, d⟩ := blastCmp_ok o ((hf.vals a).1.at hs.1) ((hf.vals b).1.at hs.2) h1
      refine ⟨p, ?_⟩
      have d' : Denotes a1 assign t (bv 1 (BitVec.ofBool (o.eval (bv cw (F.val a)) (bv cw (F.val b)))).toNat) := by
        rw [bv_ofNat_toNat]; exact d
      have := zextBits_ok _ w d' (BitVec.isLt _)
      rw [bv, BitVec.ofNat_toNat] at this
      exact this
    · cases h
  | mux s a b =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      exact (vite_ok (testBit_of_denotes (hf.vals s).1 0 hs.1) ((hf.vals a).1.at hs.2.1)
        ((hf.vals b).1.at hs.2.2)).get h
    · cases h
  | slice a lo =>
    simp only [blastOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨IsPrefix.refl' aig, sliceBits_ok (F.val a) lo w (hf.vals a).1 (hf.vals a).2⟩
  | concat hh l lw =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc := concatBits_ok ((hf.vals hh).1.at hs.1) ((hf.vals l).1.at hs.2)
      rw [← bv_ofNat_toNat (bv (w - lw) (F.val hh) ++ bv lw (F.val l))] at hc
      have := zextBits_ok _ w hc (BitVec.isLt _)
      rw [bv, BitVec.ofNat_toNat] at this
      exact ⟨IsPrefix.refl' aig, this⟩
    · cases h
  | zext a =>
    simp only [blastOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨IsPrefix.refl' aig, zextBits_ok (F.val a) w (hf.vals a).1 (hf.vals a).2⟩
  | sext a fw =>
    simp only [blastOp] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨IsPrefix.refl' aig, sextBits_ok w ((hf.vals a).1.at hs)⟩
    · cases h
  | inst j args outs => simp [blastOp] at h

end HDLean.Rtl.Blast
