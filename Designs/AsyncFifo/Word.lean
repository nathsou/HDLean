import HDLean.Rtl.MealyDesign
import HDLean.Rtl.Tactic
import HDLean.Rtl.Multi
import Designs.AsyncFifo.Progress

/-!
# The dual-clock FIFO in word-level RTL

Two clock domains of one multi-clock design (`MDesign`):

* domain 0 (write) holds the Gray-coded write pointer `wgray`; its binary value
  is decoded by an XOR network. It drives the shared memory's write port and
  exports `wgray` through crossing 0;
* domain 1 (read) holds the Gray-coded read pointer `rgray` and the memory read
  address `raddr`, the low bits of the binary read pointer. It exports `rgray`
  through crossing 1 and reads the shared memory asynchronously at `raddr`.

Each domain sees the other's pointer only through a two-flop synchronizer. The
design implements the dual-clock model `AsyncFifo.next` exactly, from every
power-up state (`decode_next`); the model's proofs then give the queue
refinement and progress. The read address agrees with the read pointer from the
first read-domain reset on (`AddrOk`).
-/
namespace HDLean.AsyncFifo.Word
open HDLean.Rtl HDLean.Rtl.Build

/-! ## Gray coding in the builder -/

/-- `x ^^^ (x >>> 1)`. -/
def grayB {c : Ctx} (x : Sig n) : M c (Sig n) := do
  let one ← const n 1
  let sh ← lshr x one
  xor x sh

/-- `acc ^^^ (g >>> j)` for every `j` of the list, in order. -/
def ungrayLoop {c : Ctx} (g : Sig n) : Sig n → List Nat → M c (Sig n)
  | acc, [] => pure acc
  | acc, j :: js => do
    let amount ← const n (BitVec.ofNat n j)
    let sh ← lshr g amount
    let acc' ← xor acc sh
    ungrayLoop g acc' js

/-- The XOR decoder of the model (`ungray`). -/
def ungrayB {c : Ctx} (g : Sig n) : M c (Sig n) := do
  let zero ← const n 0
  ungrayLoop g zero (List.range n)

theorem grayB_ensures {c : Ctx} {s : Build.State c} {x : Sig n} {fx} (hx : Build.Refines s x fx) (hn : 0 < n) :
    Ensures s (grayB x) (fun y t => Build.Refines t y (fun e => gray (fx e))) := by
  unfold grayB
  rtl_let one, hone ← const_ensures _ n 1 hn
  rtl_let sh, hsh ← shift_ensures .lshr rfl hx hone hn
  apply ensures_weaken (bin_ensures .xor hx hsh hn)
  intro y t h
  refine ⟨h.1, fun e => ?_⟩
  rw [h.2 e]
  have h1 : (1 : BitVec n).toNat = 1 := by simp [Nat.one_mod_two_pow hn]
  simp only [BinOp.eval, gray, h1]

theorem ungrayLoop_ensures {c : Ctx} {s : Build.State c} {g acc : Sig n} {fg facc} (hg : Build.Refines s g fg)
    (hacc : Build.Refines s acc facc) (hn : 0 < n) (js : List Nat) (hjs : ∀ j ∈ js, j < n) :
    Ensures s (ungrayLoop g acc js)
      (fun y t => Build.Refines t y (fun e => js.foldl (fun a j => a ^^^ (fg e >>> j)) (facc e))) := by
  induction js generalizing s acc facc with
  | nil => exact ensures_pure _ _ hacc
  | cons j js ih =>
    unfold ungrayLoop
    rtl_let amount, hamount ← const_ensures _ n (BitVec.ofNat n j) hn
    rtl_let sh, hsh ← shift_ensures .lshr rfl hg hamount hn
    rtl_let acc', hacc' ← bin_ensures .xor hacc hsh hn
    have hj : j % 2 ^ n = j := Nat.mod_eq_of_lt (Nat.lt_trans (hjs j (by simp)) (Nat.lt_two_pow_self))
    apply ensures_weaken (ih hg hacc' (fun j hj => hjs j (by simp [hj])))
    intro y t h
    refine ⟨h.1, fun e => ?_⟩
    rw [h.2 e]
    simp only [List.foldl_cons, BinOp.eval, BitVec.toNat_ofNat, hj]

theorem ungrayB_ensures {c : Ctx} {s : Build.State c} {g : Sig n} {fg} (hg : Build.Refines s g fg) (hn : 0 < n) :
    Ensures s (ungrayB g) (fun y t => Build.Refines t y (fun e => ungray (fg e))) := by
  unfold ungrayB
  rtl_let zero, hzero ← const_ensures _ n 0 hn
  exact ungrayLoop_ensures hg hzero hn _ (fun j hj => List.mem_range.mp hj)

/-! ## The write domain -/

hdl_record WIn (k w : Nat) where
  rst : 1
  valid : 1
  data : w
  rsync : (k + 1)

hdl_record WOut (k w : Nat) where
  ready : 1
  wgray : (k + 1)
  wen : 1
  waddr : k
  wdata : w

hdl_record WRegs (k : Nat) where
  wgray : (k + 1)

def wctx (k w : Nat) : Ctx := Ctx.mealy "afifo_write" (WIn k w) (WOut k w) (WRegs k) ⟨.sync 0⟩ #[]

def wbody (i : WIn k w Sig) (r : WRegs k Sig) : M (wctx k w) (Step (WOut k w) (WRegs k)) := do
  let wbin ← ungrayB r.wgray
  let rbin ← ungrayB i.rsync
  let cap ← const (k + 1) (BitVec.ofNat (k + 1) (2 ^ k))
  let limit ← xor rbin cap
  let full ← eq wbin limit
  let ready ← not full
  let live ← not i.rst
  let offer ← and i.valid ready
  let push ← and offer live
  let one ← const (k + 1) 1
  let inc ← add wbin one
  let wbin' ← mux push inc wbin
  let wgray' ← grayB wbin'
  let waddr ← slice wbin 0 k
  pure { out := ⟨ready, r.wgray, push, waddr, i.data⟩, next := ⟨wgray'⟩ }

/-! ## The read domain -/

hdl_record RIn (k w : Nat) where
  rst : 1
  ready : 1
  wsync : (k + 1)
  rdata : w

hdl_record ROut (k w : Nat) where
  valid : 1
  data : w
  rgray : (k + 1)
  raddr : k

hdl_record RRegs (k : Nat) where
  rgray : (k + 1)
  raddr : k

def rctx (k w : Nat) : Ctx := Ctx.mealy "afifo_read" (RIn k w) (ROut k w) (RRegs k) ⟨.sync 0, .sync 0⟩ #[]

def rbody (i : RIn k w Sig) (r : RRegs k Sig) : M (rctx k w) (Step (ROut k w) (RRegs k)) := do
  let rbin ← ungrayB r.rgray
  let wbin ← ungrayB i.wsync
  let same ← eq rbin wbin
  let valid ← not same
  let live ← not i.rst
  let ask ← and i.ready valid
  let pop ← and ask live
  let one ← const (k + 1) 1
  let inc ← add rbin one
  let rbin' ← mux pop inc rbin
  let rgray' ← grayB rbin'
  let raddr' ← slice rbin' 0 k
  pure { out := ⟨valid, i.rdata, r.rgray, r.raddr⟩, next := ⟨rgray', raddr'⟩ }

/-! ## The multi-clock design -/

def wmodule (k w : Nat) : Module := (wctx k w).module (mealy (WIn k w) (WOut k w) (WRegs k) wbody)
def rmodule (k w : Nat) : Module := (rctx k w).module (mealy (RIn k w) (ROut k w) (RRegs k) rbody)

def design (k w : Nat) : MDesign where
  design := ⟨#[wmodule k w, rmodule k w]⟩
  tops := #[0, 1]
  crossings := #[⟨0, 1, 1⟩, ⟨1, 2, 0⟩]
  mems := #[⟨.ofString "ram", k, w, 0, 2, 3, 4, 1, 3⟩]

/-! ## The domains as functions of records -/

section Domains
variable {k w : Nat}

def wfull (i : WIn k w BitVec) (r : WRegs k BitVec) : BitVec 1 :=
  BitVec.ofBool (CmpOp.eq.eval (ungray r.wgray) (ungray i.rsync ^^^ BitVec.ofNat (k + 1) (2 ^ k)))
def wpush (i : WIn k w BitVec) (r : WRegs k BitVec) : BitVec 1 := (i.valid &&& ~~~(wfull i r)) &&& ~~~i.rst
def wout (i : WIn k w BitVec) (r : WRegs k BitVec) : WOut k w BitVec :=
  ⟨~~~(wfull i r), r.wgray, wpush i r, (ungray r.wgray).extractLsb' 0 k, i.data⟩
def wnext (i : WIn k w BitVec) (r : WRegs k BitVec) : WRegs k BitVec :=
  ⟨gray (if (wpush i r).getLsbD 0 then ungray r.wgray + 1 else ungray r.wgray)⟩

def rempty (i : RIn k w BitVec) (r : RRegs k BitVec) : BitVec 1 :=
  BitVec.ofBool (CmpOp.eq.eval (ungray r.rgray) (ungray i.wsync))
def rpop (i : RIn k w BitVec) (r : RRegs k BitVec) : BitVec 1 := (i.ready &&& ~~~(rempty i r)) &&& ~~~i.rst
def rptr (i : RIn k w BitVec) (r : RRegs k BitVec) : BitVec (k + 1) :=
  if (rpop i r).getLsbD 0 then ungray r.rgray + 1 else ungray r.rgray
def rout (i : RIn k w BitVec) (r : RRegs k BitVec) : ROut k w BitVec := ⟨~~~(rempty i r), i.rdata, r.rgray, r.raddr⟩
def rnext (i : RIn k w BitVec) (r : RRegs k BitVec) : RRegs k BitVec := ⟨gray (rptr i r), (rptr i r).extractLsb' 0 k⟩

end Domains

def wdecIn (k w : Nat) (e : Env) : WIn k w BitVec := Bundle.decode (WIn k w) (e.ins.getD · 0)
def wdecRegs (k : Nat) (e : Env) : WRegs k BitVec := Bundle.decode (WRegs k) (e.st.regs.getD · 0)
def rdecIn (k w : Nat) (e : Env) : RIn k w BitVec := Bundle.decode (RIn k w) (e.ins.getD · 0)
def rdecRegs (k : Nat) (e : Env) : RRegs k BitVec := Bundle.decode (RRegs k) (e.st.regs.getD · 0)

theorem wctx_ok (k w : Nat) (hk : 0 < k) (hw : 0 < w) : (wctx k w).ok = true := by
  simp [Ctx.ok, wctx, Ctx.mealy, Bundle.ports, Bundle.fields, Bundle.toVec, HVec.toList, Reset.fits, hk, hw, Nat.two_pow_pos]

theorem rctx_ok (k w : Nat) (hk : 0 < k) (hw : 0 < w) : (rctx k w).ok = true := by
  simp [Ctx.ok, rctx, Ctx.mealy, Bundle.ports, Bundle.fields, Bundle.toVec, HVec.toList, Reset.fits, hk, hw,
    Nat.two_pow_pos]

theorem wbody_ensures (k w : Nat) (hk : 0 < k) (s : Build.State (wctx k w)) (i : WIn k w Sig)
    (r : WRegs k Sig) (hi : BRefines s i (wdecIn k w)) (hr : BRefines s r (wdecRegs k)) (hc : BRegCells s r) :
    Ensures s (wbody i r) (fun st t =>
      BRefines t st.out (fun e => wout (wdecIn k w e) (wdecRegs k e)) ∧
      BRefines t st.next (fun e => wnext (wdecIn k w e) (wdecRegs k e)) ∧
      WritesOk t st.writes (wctx k w).mems ∧ RegCell t st.out.wgray 0) := by
  obtain ⟨hrst, hvalid, hdata, hrsync, -⟩ := hi
  obtain ⟨hg, -⟩ := hr
  obtain ⟨hcell, -⟩ := hc
  unfold wbody
  rtl_let wbin, hwbin ← ungrayB_ensures hg (by omega)
  rtl_let rbin, hrbin ← ungrayB_ensures hrsync (by omega)
  rtl_let cap, hcap ← const_ensures _ (k + 1) (BitVec.ofNat (k + 1) (2 ^ k)) (by omega)
  rtl_let limit, hlimit ← bin_ensures .xor hrbin hcap (by omega)
  rtl_let full, hfull ← cmp_ensures .eq hwbin hlimit
  rtl_let ready, hready ← not_ensures hfull (by decide)
  rtl_let live, hlive ← not_ensures hrst (by decide)
  rtl_let offer, hoffer ← bin_ensures .and hvalid hready (by decide)
  rtl_let push, hpush ← bin_ensures .and hoffer hlive (by decide)
  rtl_let one, hone ← const_ensures _ (k + 1) 1 (by omega)
  rtl_let inc, hinc ← bin_ensures .add hwbin hone (by omega)
  rtl_let wbin', hwbin' ← mux_ensures hpush hinc hwbin (by omega)
  rtl_let wgray', hwgray' ← grayB_ensures hwbin' (by omega)
  rtl_let waddr, hwaddr ← slice_ensures 0 k hwbin hk (by omega)
  exact ensures_pure _ _ ⟨⟨hready, hg, hpush, hwaddr, hdata, trivial⟩, ⟨hwgray', trivial⟩, WritesOk.nil, hcell⟩

theorem rbody_ensures (k w : Nat) (hk : 0 < k) (s : Build.State (rctx k w)) (i : RIn k w Sig)
    (r : RRegs k Sig) (hi : BRefines s i (rdecIn k w)) (hr : BRefines s r (rdecRegs k)) (hc : BRegCells s r) :
    Ensures s (rbody i r) (fun st t =>
      BRefines t st.out (fun e => rout (rdecIn k w e) (rdecRegs k e)) ∧
      BRefines t st.next (fun e => rnext (rdecIn k w e) (rdecRegs k e)) ∧
      WritesOk t st.writes (rctx k w).mems ∧ RegCell t st.out.rgray 0 ∧ RegCell t st.out.raddr 1) := by
  obtain ⟨hrst, hready, hwsync, hrdata, -⟩ := hi
  obtain ⟨hg, ha, -⟩ := hr
  obtain ⟨hcg, hca, -⟩ := hc
  unfold rbody
  rtl_let rbin, hrbin ← ungrayB_ensures hg (by omega)
  rtl_let wbin, hwbin ← ungrayB_ensures hwsync (by omega)
  rtl_let same, hsame ← cmp_ensures .eq hrbin hwbin
  rtl_let valid, hvalid ← not_ensures hsame (by decide)
  rtl_let live, hlive ← not_ensures hrst (by decide)
  rtl_let ask, hask ← bin_ensures .and hready hvalid (by decide)
  rtl_let pop, hpop ← bin_ensures .and hask hlive (by decide)
  rtl_let one, hone ← const_ensures _ (k + 1) 1 (by omega)
  rtl_let inc, hinc ← bin_ensures .add hrbin hone (by omega)
  rtl_let rbin', hrbin' ← mux_ensures hpop hinc hrbin (by omega)
  rtl_let rgray', hrgray' ← grayB_ensures hrbin' (by omega)
  rtl_let raddr', hraddr' ← slice_ensures 0 k hrbin' hk (by omega)
  exact ensures_pure _ _ ⟨⟨hvalid, hrdata, hg, ha, trivial⟩, ⟨hrgray', hraddr', trivial⟩, WritesOk.nil, hcg, hca⟩

/-! ## The built modules -/

abbrev wwire (sp : Step (WOut k w) (WRegs k)) : Wiring :=
  ⟨refs (Bundle.toVec sp.out), refs (Bundle.toVec sp.next), sp.writes⟩
abbrev rwire (sp : Step (ROut k w) (RRegs k)) : Wiring :=
  ⟨refs (Bundle.toVec sp.out), refs (Bundle.toVec sp.next), sp.writes⟩

theorem wbuilt (k w : Nat) (hk : 0 < k) (hw : 0 < w) :
    ∃ (t : Build.State (wctx k w)) (sp : Step (WOut k w) (WRegs k)),
      (design k w).design.modules[0]? = some (t.toModule (wwire sp)) ∧
      BRefines t sp.out (fun e => wout (wdecIn k w e) (wdecRegs k e)) ∧
      BRefines t sp.next (fun e => wnext (wdecIn k w e) (wdecRegs k e)) ∧
      WritesOk t sp.writes (wctx k w).mems ∧ RegCell t sp.out.wgray 0 := by
  obtain ⟨t, sp, hm, h⟩ := mealy_build_cells (wctx_ok k w hk hw) wbody _ _ _
    (fun s i r hi hr hc => wbody_ensures k w hk s i r hi hr hc)
  exact ⟨t, sp, congrArg some hm, h⟩

theorem rbuilt (k w : Nat) (hk : 0 < k) (hw : 0 < w) :
    ∃ (t : Build.State (rctx k w)) (sp : Step (ROut k w) (RRegs k)),
      (design k w).design.modules[1]? = some (t.toModule (rwire sp)) ∧
      BRefines t sp.out (fun e => rout (rdecIn k w e) (rdecRegs k e)) ∧
      BRefines t sp.next (fun e => rnext (rdecIn k w e) (rdecRegs k e)) ∧
      WritesOk t sp.writes (rctx k w).mems ∧ RegCell t sp.out.rgray 0 ∧ RegCell t sp.out.raddr 1 := by
  obtain ⟨t, sp, hm, h⟩ := mealy_build_cells (rctx_ok k w hk hw) rbody _ _ _
    (fun s i r hi hr hc => rbody_ensures k w hk s i r hi hr hc)
  exact ⟨t, sp, congrArg some hm, h⟩

theorem topModule_w (k w : Nat) : (design k w).topModule 0 = wmodule k w := rfl
theorem topModule_r (k w : Nat) : (design k w).topModule 1 = rmodule k w := rfl

/-- Crossing 0 is driven by the write pointer register. -/
theorem regOut_wgray (k w : Nat) (hk : 0 < k) (hw : 0 < w) : (design k w).regOut 0 1 = (0, k + 1) := by
  obtain ⟨t, sp, hm, -, -, -, hc⟩ := wbuilt k w hk hw
  have hmod : (design k w).topModule 0 = t.toModule (wwire sp) := by
    rw [topModule_w]; simpa [design] using hm
  apply MDesign.regOut_of (n := sp.out.wgray.ref)
  · rw [hmod]
    exact t.toModule_output _ 1 _ rfl (by simp [wctx, Ctx.mealy, Bundle.ports, Bundle.fields])
  · rw [hmod, State.toModule_cells]; exact hc

/-- Crossing 1 is driven by the read pointer register. -/
theorem regOut_rgray (k w : Nat) (hk : 0 < k) (hw : 0 < w) : (design k w).regOut 1 2 = (0, k + 1) := by
  obtain ⟨t, sp, hm, -, -, -, hc, -⟩ := rbuilt k w hk hw
  have hmod : (design k w).topModule 1 = t.toModule (rwire sp) := by
    rw [topModule_r]; simpa [design] using hm
  apply MDesign.regOut_of (n := sp.out.rgray.ref)
  · rw [hmod]
    exact t.toModule_output _ 2 _ rfl (by simp [rctx, Ctx.mealy, Bundle.ports, Bundle.fields])
  · rw [hmod, State.toModule_cells]; exact hc

/-- The memory is read at the read address register. -/
theorem regOut_raddr (k w : Nat) (hk : 0 < k) (hw : 0 < w) : (design k w).regOut 1 3 = (1, k) := by
  obtain ⟨t, sp, hm, -, -, -, -, hc⟩ := rbuilt k w hk hw
  have hmod : (design k w).topModule 1 = t.toModule (rwire sp) := by
    rw [topModule_r]; simpa [design] using hm
  apply MDesign.regOut_of (n := sp.out.raddr.ref)
  · rw [hmod]
    exact t.toModule_output _ 3 _ rfl (by simp [rctx, Ctx.mealy, Bundle.ports, Bundle.fields])
  · rw [hmod, State.toModule_cells]; exact hc

/-! ## Gray decoding -/

theorem ungray_fold_gray (g : BitVec n) (m : Nat) :
    gray ((List.range m).foldl (fun a j => a ^^^ (g >>> j)) 0) = g ^^^ (g >>> m) := by
  induction m with
  | zero => simp [gray]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    revert ih
    generalize (List.range m).foldl (fun a j => a ^^^ (g >>> j)) 0 = u
    intro ih
    simp only [gray, BitVec.ushiftRight_xor_distrib] at ih ⊢
    rw [← BitVec.shiftRight_add]
    calc u ^^^ g >>> m ^^^ (u >>> 1 ^^^ g >>> (m + 1))
        = (u ^^^ u >>> 1) ^^^ (g >>> m ^^^ g >>> (m + 1)) := by
          simp only [BitVec.xor_assoc]
          congr 1
          rw [← BitVec.xor_assoc, BitVec.xor_comm (g >>> m) (u >>> 1), BitVec.xor_assoc]
      _ = g ^^^ g >>> (m + 1) := by
          rw [ih, BitVec.xor_assoc, ← BitVec.xor_assoc (g >>> m), BitVec.xor_self, BitVec.zero_xor]

theorem gray_ungray (g : BitVec n) : gray (ungray g) = g := by
  rw [ungray, ungray_fold_gray]
  simp [BitVec.ushiftRight_eq_zero (Nat.le_refl n)]

@[simp] theorem gray_zero : gray (0#n) = 0#n := by simp [gray]

@[simp] theorem ungray_zero : ungray (0#n) = 0#n := by
  have := ungray_gray (0#n)
  rwa [gray_zero] at this

/-! ## What each domain sees -/

section Ports
variable {k w : Nat}

/-- The write pointer register, the read pointer register and the read address register. -/
def wg (S : MDesign.State) : BitVec (k + 1) := bv (k + 1) ((S.store 0).regs.getD 0 0)
def rg (S : MDesign.State) : BitVec (k + 1) := bv (k + 1) ((S.store 1).regs.getD 0 0)
def ra (S : MDesign.State) : BitVec k := bv k ((S.store 1).regs.getD 1 0)

/-- The two external inputs of the write domain and the one of the read domain. -/
def ExtIns (e : MDesign.Event) (a b c : Nat) : Prop := e.ins = #[#[a, b], #[c]]

theorem domainIns_w (S : MDesign.State) (e : MDesign.Event) {a b c : Nat} (he : ExtIns e a b c) :
    (design k w).domainIns S e 0 = #[(e.rstOf 0).toNat, a, b, S.second.getD 1 0] := by
  simp [MDesign.domainIns, MDesign.syncIns, MDesign.memIns, design, show e.ins = _ from he, List.zipIdx]

theorem domainIns_r (S : MDesign.State) (e : MDesign.Event) {a b c : Nat} (he : ExtIns e a b c) :
    (design k w).domainIns S e 1 = #[(e.rstOf 1).toNat, c, S.second.getD 0 0, (design k w).memRead S 0] := by
  simp [MDesign.domainIns, MDesign.syncIns, MDesign.memIns, design, show e.ins = _ from he, List.zipIdx]

/-- The memory word the read domain sees: the word at the read address register. -/
theorem memRead_eq (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) :
    (design k w).memRead S 0 = (S.mems.getD 0 #[]).getD (ra (k := k) S).toNat 0 := by
  have h := regOut_raddr k w hk hw
  show (S.mems.getD 0 #[]).getD (bv ((design k w).regOut 1 3).2
    ((S.store 1).regs.getD ((design k w).regOut 1 3).1 0)).toNat 0 = _
  rw [h]
  rfl

/-- The write domain's inputs, decoded. -/
def wIns (S : MDesign.State) (e : MDesign.Event) (a b : Nat) : WIn k w BitVec :=
  ⟨bv 1 (e.rstOf 0).toNat, bv 1 a, bv w b, bv (k + 1) (S.second.getD 1 0)⟩

/-- The read domain's inputs, decoded. -/
def rIns (S : MDesign.State) (e : MDesign.Event) (c : Nat) (m : Nat) : RIn k w BitVec :=
  ⟨bv 1 (e.rstOf 1).toNat, bv 1 c, bv (k + 1) (S.second.getD 0 0), bv w m⟩

theorem wsem (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (e : MDesign.Event) {a b c : Nat} (he : ExtIns e a b c) :
    bv (k + 1) (((design k w).semOf S e 0).2.regs.getD 0 0) =
      resetField (e.rstOf 0) (.sync 0) (wnext (wIns (k := k) (w := w) S e a b) ⟨wg S⟩).wgray ∧
    ((design k w).semOf S e 0).1 = #[(~~~(wfull (wIns (k := k) (w := w) S e a b) ⟨wg S⟩)).toNat, (wg (k := k) S).toNat,
      (wpush (wIns (k := k) (w := w) S e a b) ⟨wg S⟩).toNat, ((ungray (wg (k := k) S)).extractLsb' 0 k).toNat,
      (bv w b).toNat] := by
  obtain ⟨t, sp, hm, ho, hn, -⟩ := wbuilt k w hk hw
  have hins := domainIns_w (k := k) (w := w) S e he
  constructor
  · have := congrArg (fun r : WRegs k BitVec => r.wgray)
      (mealy_sem_regs hm hn (S.store 0) ((design k w).domainIns S e 0) (e.rstOf 0))
    simp only [Bundle.reset, Bundle.decode, Bundle.toVec, Bundle.ofVec, HVec.zipWith, Bundle.widths,
      Bundle.fields, List.map, HVec.decode, HVec.head] at this
    show bv (k + 1) (((design k w).design.sem 0 (S.store 0) ((design k w).domainIns S e 0) (e.rstOf 0)).2.regs.getD 0 0) = _
    rw [this, hins]
    rfl
  · show ((design k w).design.sem 0 (S.store 0) ((design k w).domainIns S e 0) (e.rstOf 0)).1 = _
    rw [mealy_sem_outputs hm ho, hins]
    rfl

theorem rsem (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (e : MDesign.Event) {a b c : Nat} (he : ExtIns e a b c) :
    Bundle.decode (RRegs k) ((((design k w).semOf S e 1).2.regs).getD · 0) =
      Bundle.reset (e.rstOf 1) ⟨.sync 0, .sync 0⟩
        (rnext (rIns (k := k) (w := w) S e c ((design k w).memRead S 0)) ⟨rg S, ra S⟩) ∧
    ((design k w).semOf S e 1).1 = #[(~~~(rempty (rIns (k := k) (w := w) S e c ((design k w).memRead S 0)) ⟨rg S, ra S⟩)).toNat,
      (bv w ((design k w).memRead S 0)).toNat, (rg (k := k) S).toNat, (ra (k := k) S).toNat] := by
  obtain ⟨t, sp, hm, ho, hn, -⟩ := rbuilt k w hk hw
  have hins := domainIns_r (k := k) (w := w) S e he
  constructor
  · show Bundle.decode (RRegs k) (((design k w).design.sem 1 (S.store 1) ((design k w).domainIns S e 1)
      (e.rstOf 1)).2.regs.getD · 0) = _
    rw [mealy_sem_regs hm hn, hins]
    rfl
  · show ((design k w).design.sem 1 (S.store 1) ((design k w).domainIns S e 1) (e.rstOf 1)).1 = _
    rw [mealy_sem_outputs hm ho, hins]
    rfl

end Ports

/-! ## The design is the dual-clock model -/

section Model
variable {k w : Nat}

/-- The multi-clock state as a model state: the shared memory, the two
pointers (decoded from Gray) and the two synchronizers. -/
def decode (S : MDesign.State) : AsyncFifo.State k w :=
  ⟨fun a => bv w ((S.mems.getD 0 #[]).getD a.toNat 0), ungray (wg (k := k) S), ungray (rg (k := k) S),
    ⟨bv (k + 1) (S.first.getD 0 0), bv (k + 1) (S.second.getD 0 0)⟩,
    ⟨bv (k + 1) (S.first.getD 1 0), bv (k + 1) (S.second.getD 1 0)⟩⟩

theorem extIns_event (i : Input k w) : ExtIns (event i) i.valid.toNat i.data.toNat i.ready.toNat := rfl
theorem extIns_idle : ExtIns idle 0 0 0 := rfl

theorem bv_bool (b : Bool) : (bv 1 b.toNat).getLsbD 0 = b := by cases b <;> rfl

theorem bv_toNat {n : Nat} (x : BitVec n) : bv n x.toNat = x := by simp [bv]

theorem wready_bit (S : MDesign.State) (e : MDesign.Event) (a b : Nat) :
    (~~~(wfull (wIns (k := k) (w := w) S e a b) ⟨wg S⟩)).getLsbD 0 = enqReady (decode (k := k) (w := w) S) := by
  simp [wfull, wIns, enqReady, decode, CmpOp.eval, bne]

theorem wpush_bit (S : MDesign.State) (i : Input k w) :
    (wpush (wIns (k := k) (w := w) S (event i) i.valid.toNat i.data.toNat) ⟨wg S⟩).getLsbD 0 =
      (i.valid && enqReady (decode (k := k) (w := w) S) && !i.writeReset) := by
  have h := wready_bit (k := k) (w := w) S (event i) i.valid.toNat i.data.toNat
  simp only [wpush, BitVec.getLsbD_and, BitVec.getLsbD_not] at h ⊢
  rw [h]
  simp only [wIns, MDesign.Event.rstOf, event]
  cases i.valid <;> cases i.writeReset <;> simp [bv]

theorem rvalid_bit (S : MDesign.State) (e : MDesign.Event) (c m : Nat) :
    (~~~(rempty (rIns (k := k) (w := w) S e c m) ⟨rg S, ra S⟩)).getLsbD 0 = deqValid (decode (k := k) (w := w) S) := by
  simp [rempty, rIns, deqValid, decode, CmpOp.eval, bne]

theorem rpop_bit (S : MDesign.State) (i : Input k w) (m : Nat) :
    (rpop (rIns (k := k) (w := w) S (event i) i.ready.toNat m) ⟨rg S, ra S⟩).getLsbD 0 =
      (i.ready && deqValid (decode (k := k) (w := w) S) && !i.readReset) := by
  have h := rvalid_bit (k := k) (w := w) S (event i) i.ready.toNat m
  simp only [rpop, BitVec.getLsbD_and, BitVec.getLsbD_not] at h ⊢
  rw [h]
  simp only [rIns, MDesign.Event.rstOf, event]
  cases i.ready <;> cases i.readReset <;> simp [bv]

theorem next_store (S : MDesign.State) (e : MDesign.Event) (d : Nat) (hd : d < 2) :
    ((design k w).next S e).store d = (design k w).nextStore S e d := by
  simp [MDesign.next, MDesign.State.store, design, hd]

theorem wg_next (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) :
    wg (k := k) ((design k w).next S (event i)) = gray (AsyncFifo.next (decode (k := k) (w := w) S) i).write := by
  unfold wg
  rw [next_store S _ 0 (by decide)]
  unfold MDesign.nextStore
  have hedge : (event i).edgeOf 0 = i.writeEdge := rfl
  have hrst : (event i).rstOf 0 = i.writeReset := rfl
  rw [hedge]
  cases he : i.writeEdge
  · simp only [Bool.false_eq_true, ite_false, AsyncFifo.next, AsyncFifo.push, he, Bool.false_and]
    exact (gray_ungray _).symm
  · simp only [ite_true]
    rw [(wsem hk hw S (event i) (extIns_event i)).1, hrst]
    cases hr : i.writeReset
    · simp only [resetField, Bool.false_eq_true, ite_false, wnext, wpush_bit, AsyncFifo.next, AsyncFifo.push, he, hr]
      simp [decode]
    · simp [resetField, AsyncFifo.next, he, hr, gray_zero, bv]

theorem rsem_fields (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (e : MDesign.Event) {a b c : Nat}
    (he : ExtIns e a b c) :
    bv (k + 1) ((((design k w).semOf S e 1).2.regs).getD 0 0) = resetField (e.rstOf 1) (.sync 0)
      (gray (rptr (rIns (k := k) (w := w) S e c ((design k w).memRead S 0)) ⟨rg S, ra S⟩)) ∧
    bv k ((((design k w).semOf S e 1).2.regs).getD 1 0) = resetField (e.rstOf 1) (.sync 0)
      ((rptr (rIns (k := k) (w := w) S e c ((design k w).memRead S 0)) ⟨rg S, ra S⟩).extractLsb' 0 k) := by
  have h := (rsem hk hw S e he).1
  have h1 := congrArg (fun r : RRegs k BitVec => r.rgray) h
  have h2 := congrArg (fun r : RRegs k BitVec => r.raddr) h
  simp only [Bundle.reset, Bundle.decode, Bundle.toVec, Bundle.ofVec, HVec.zipWith, Bundle.widths,
    Bundle.fields, List.map, HVec.decode, HVec.head, HVec.tail] at h1 h2
  exact ⟨h1, h2⟩

theorem rg_next (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) :
    rg (k := k) ((design k w).next S (event i)) = gray (AsyncFifo.next (decode (k := k) (w := w) S) i).read := by
  unfold rg
  rw [next_store S _ 1 (by decide)]
  unfold MDesign.nextStore
  have hedge : (event i).edgeOf 1 = i.readEdge := rfl
  have hrst : (event i).rstOf 1 = i.readReset := rfl
  rw [hedge]
  cases he : i.readEdge
  · simp only [Bool.false_eq_true, ite_false, AsyncFifo.next, AsyncFifo.pop, he, Bool.false_and]
    exact (gray_ungray _).symm
  · simp only [ite_true]
    rw [(rsem_fields hk hw S (event i) (extIns_event i)).1, hrst]
    cases hr : i.readReset
    · simp only [resetField, Bool.false_eq_true, ite_false, rptr, rpop_bit, AsyncFifo.next, AsyncFifo.pop, he, hr]
      simp [decode]
    · simp [resetField, AsyncFifo.next, he, hr, bv]

/-- The read address register holds the low bits of the read pointer. -/
def AddrOk (S : MDesign.State) : Prop := ra (k := k) S = (ungray (rg (k := k) S)).setWidth k

theorem extract_setWidth {n : Nat} (x : BitVec (n + 1)) : x.extractLsb' 0 n = x.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb', BitVec.toNat_setWidth]

/-- A read-domain edge establishes `AddrOk`; nothing else breaks it. -/
theorem addrOk_next (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w)
    (h : i.readEdge = true ∨ AddrOk (k := k) S) : AddrOk (k := k) ((design k w).next S (event i)) := by
  unfold AddrOk ra rg
  rw [next_store S _ 1 (by decide)]
  unfold MDesign.nextStore
  have hedge : (event i).edgeOf 1 = i.readEdge := rfl
  rw [hedge]
  cases he : i.readEdge
  · simp only [he, Bool.false_eq_true, false_or] at h
    simpa [AddrOk, ra, rg] using h
  · simp only [ite_true]
    obtain ⟨h1, h2⟩ := rsem_fields hk hw S (event i) (extIns_event i)
    rw [h1, h2]
    cases (event i).rstOf 1
    · simp only [resetField, Bool.false_eq_true, ite_false, ungray_gray, extract_setWidth]
    · simp [resetField, bv]

theorem bv_testBit (x : BitVec 1) : (x.toNat).testBit 0 = x.getLsbD 0 := rfl

theorem shapeMem_getD (aw : Nat) (old : Array Nat) (j : Nat) (hj : j < 2 ^ aw) :
    (MDesign.shapeMem aw old).getD j 0 = old.getD j 0 := by
  unfold MDesign.shapeMem
  split
  · rfl
  · simp [Array.getD_eq_getD_getElem?, hj]

theorem shapeMem_size (aw : Nat) (old : Array Nat) : (MDesign.shapeMem aw old).size = 2 ^ aw := by
  unfold MDesign.shapeMem
  split
  · assumption
  · simp

theorem mem_next (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) (a : BitVec k) :
    bv w ((((design k w).next S (event i)).mems.getD 0 #[]).getD a.toNat 0) =
      (AsyncFifo.next (decode (k := k) (w := w) S) i).memory a := by
  have hm : ((design k w).next S (event i)).mems.getD 0 #[] =
      (design k w).nextMem S (event i) 0 ⟨.ofString "ram", k, w, 0, 2, 3, 4, 1, 3⟩ := by
    simp [MDesign.next, design]
  rw [hm]
  unfold MDesign.nextMem
  have hedge : (event i).edgeOf 0 = i.writeEdge := rfl
  simp only [hedge]
  have hold := shapeMem_getD k (S.mems.getD 0 #[]) a.toNat a.isLt
  have hsz := shapeMem_size k (S.mems.getD 0 #[])
  have hdec : (decode (k := k) (w := w) S).memory a = bv w ((S.mems.getD 0 #[]).getD a.toNat 0) := rfl
  generalize S.mems.getD 0 #[] = raw at hold hsz hdec
  generalize MDesign.shapeMem k raw = old at hold hsz
  cases he : i.writeEdge
  · simp only [Bool.false_eq_true, ite_false, hold, AsyncFifo.next, AsyncFifo.push, he, Bool.false_and, hdec]
  · simp only [ite_true]
    have ho : (design k w).outputs S (event i) 0 = ((design k w).semOf S (event i) 0).1 := rfl
    rw [ho, (wsem hk hw S (event i) (extIns_event i)).2]
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, bv_testBit, wpush_bit]
    simp only [AsyncFifo.next, AsyncFifo.push, he, Bool.true_and]
    have hpush : (i.valid && enqReady (decode (k := k) (w := w) S) && !i.writeReset) =
        (!i.writeReset && i.valid && enqReady (decode (k := k) (w := w) S)) := by
      cases i.valid <;> cases i.writeReset <;> simp
    rw [hpush]
    cases hp : (!i.writeReset && i.valid && enqReady (decode (k := k) (w := w) S))
    · simp only [Bool.false_eq_true, ite_false, Bool.false_and]
      rw [← Array.getD_eq_getD_getElem?, hold, hdec]
    · simp only [ite_true, Bool.true_and]
      by_cases hx : ((ungray (wg (k := k) S)).extractLsb' 0 k).toNat = a.toNat
      · have hx' : a = (decode (k := k) (w := w) S).write.setWidth k := by
          apply BitVec.eq_of_toNat_eq; rw [← hx, extract_setWidth]; rfl
        rw [hx, Array.getElem?_setIfInBounds_self_of_lt (by rw [hsz]; exact a.isLt)]
        simp [hx', bv]
      · have hx' : ¬ (a = (decode (k := k) (w := w) S).write.setWidth k) := by
          intro h; apply hx; rw [h, extract_setWidth]; rfl
        rw [Array.getElem?_setIfInBounds_ne hx, ← Array.getD_eq_getD_getElem?, hold]
        simp [hx', hdec]

theorem seenWrite_next (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) :
    (⟨bv (k + 1) (((design k w).next S (event i)).first.getD 0 0),
      bv (k + 1) (((design k w).next S (event i)).second.getD 0 0)⟩ : Sync2 (BitVec (k + 1))) =
      (AsyncFifo.next (decode (k := k) (w := w) S) i).seenWrite := by
  have h1 : ((design k w).next S (event i)).first.getD 0 0 = (design k w).nextFirst S (event i) 0 ⟨0, 1, 1⟩ := by
    simp [MDesign.next, design]
  have h2 : ((design k w).next S (event i)).second.getD 0 0 = MDesign.nextSecond S (event i) 0 ⟨0, 1, 1⟩ := by
    simp [MDesign.next, design]
  have hwg := wg_next hk hw S i
  rw [wg, next_store S _ 0 (by decide)] at hwg
  rw [h1, h2]
  unfold MDesign.nextFirst MDesign.nextSecond MDesign.regValue
  rw [regOut_wgray k w hk hw]
  simp only [bv_toNat]
  rw [hwg]
  have hedge : (event i).edgeOf 1 = i.readEdge := rfl
  have hrst : (event i).rstOf 1 = i.readReset := rfl
  simp only [hedge, hrst]
  cases he : i.readEdge
  · simp [AsyncFifo.next, he, decode]
  · cases hr : i.readReset
    · simp only [ite_true, Bool.false_eq_true, ite_false, bv_toNat, AsyncFifo.next, he, hr]
      simp [decode, gray_ungray, event, wg, rg]
    · simp [AsyncFifo.next, he, hr, bv]

theorem seenRead_next (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) :
    (⟨bv (k + 1) (((design k w).next S (event i)).first.getD 1 0),
      bv (k + 1) (((design k w).next S (event i)).second.getD 1 0)⟩ : Sync2 (BitVec (k + 1))) =
      (AsyncFifo.next (decode (k := k) (w := w) S) i).seenRead := by
  have h1 : ((design k w).next S (event i)).first.getD 1 0 = (design k w).nextFirst S (event i) 1 ⟨1, 2, 0⟩ := by
    simp [MDesign.next, design]
  have h2 : ((design k w).next S (event i)).second.getD 1 0 = MDesign.nextSecond S (event i) 1 ⟨1, 2, 0⟩ := by
    simp [MDesign.next, design]
  have hrg := rg_next hk hw S i
  rw [rg, next_store S _ 1 (by decide)] at hrg
  rw [h1, h2]
  unfold MDesign.nextFirst MDesign.nextSecond MDesign.regValue
  rw [regOut_rgray k w hk hw]
  simp only [bv_toNat]
  rw [hrg]
  have hedge : (event i).edgeOf 0 = i.writeEdge := rfl
  have hrst : (event i).rstOf 0 = i.writeReset := rfl
  simp only [hedge, hrst]
  cases he : i.writeEdge
  · simp [AsyncFifo.next, he, decode]
  · cases hr : i.writeReset
    · simp only [ite_true, Bool.false_eq_true, ite_false, bv_toNat, AsyncFifo.next, he, hr]
      simp [decode, gray_ungray, event, wg, rg]
    · simp [AsyncFifo.next, he, hr, bv]

/-- One global step of the design is one step of the dual-clock model, from every state. -/
theorem decode_next (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) :
    decode (k := k) (w := w) ((design k w).next S (event i)) = AsyncFifo.next (decode (k := k) (w := w) S) i := by
  have hm : (AsyncFifo.next (decode (k := k) (w := w) S) i).memory =
      fun a => bv w ((((design k w).next S (event i)).mems.getD 0 #[]).getD a.toNat 0) :=
    funext fun a => (mem_next hk hw S i a).symm
  have hwr : (AsyncFifo.next (decode (k := k) (w := w) S) i).write = ungray (wg (k := k) ((design k w).next S (event i))) := by
    rw [wg_next hk hw, ungray_gray]
  have hrd : (AsyncFifo.next (decode (k := k) (w := w) S) i).read = ungray (rg (k := k) ((design k w).next S (event i))) := by
    rw [rg_next hk hw, ungray_gray]
  rw [show AsyncFifo.next (decode (k := k) (w := w) S) i = ⟨(AsyncFifo.next (decode (k := k) (w := w) S) i).memory,
    (AsyncFifo.next (decode (k := k) (w := w) S) i).write, (AsyncFifo.next (decode (k := k) (w := w) S) i).read,
    (AsyncFifo.next (decode (k := k) (w := w) S) i).seenWrite, (AsyncFifo.next (decode (k := k) (w := w) S) i).seenRead⟩
    from rfl, hm, hwr, hrd, ← seenWrite_next hk hw, ← seenRead_next hk hw]
  rfl

/-- The observed ports are the model's, once the read address agrees with the read pointer. -/
theorem observe_eq (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (ha : AddrOk (k := k) S) :
    observe w (design k w) S = AsyncFifo.observe (decode (k := k) (w := w) S) := by
  have h0 : (design k w).outputs S idle 0 = ((design k w).semOf S idle 0).1 := rfl
  have h1 : (design k w).outputs S idle 1 = ((design k w).semOf S idle 1).1 := rfl
  unfold observe AsyncFifo.observe
  rw [h0, h1, (wsem hk hw S idle extIns_idle).2, (rsem hk hw S idle extIns_idle).2]
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, bv_testBit, wready_bit, rvalid_bit, bv_toNat]
  congr 2
  rw [memRead_eq hk hw, ha]
  rfl

theorem decode_stateFrom (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w) (t : Nat) :
    decode (k := k) (w := w) (stateFrom (design k w) S xs t) = AsyncFifo.stateFrom (decode (k := k) (w := w) S) xs t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show decode ((design k w).next (stateFrom (design k w) S xs t) (event (xs t))) = _
    rw [decode_next hk hw, ih]
    rfl

theorem seenRead_edge (xs : Nat → Input k w) : ∀ n, seenRead xs n = true → ∃ u, u < n ∧ (xs u).readEdge = true
  | 0, h => by simp [seenRead] at h
  | n + 1, h => by
    simp only [seenRead, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨u, hu, he⟩ := seenRead_edge xs n h
      exact ⟨u, by omega, he⟩
    · exact ⟨n, by omega, h⟩

/-- After startup the read address always agrees with the read pointer. -/
theorem addrOk_after (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w) (release : Nat)
    (hstart : Startup xs release) (t : Nat) (ht : release ≤ t) :
    AddrOk (k := k) (stateFrom (design k w) S xs t) := by
  obtain ⟨u, hu, he⟩ := seenRead_edge xs release hstart.2.2
  have key : ∀ n, AddrOk (k := k) (stateFrom (design k w) S xs (u + 1 + n)) := by
    intro n
    induction n with
    | zero => exact addrOk_next hk hw _ (xs u) (.inl he)
    | succ n ih => exact addrOk_next hk hw _ (xs (u + 1 + n)) (.inr ih)
  have := key (t - (u + 1))
  rwa [show u + 1 + (t - (u + 1)) = t by omega] at this

theorem outputs_eq (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w) (release : Nat)
    (hstart : Startup xs release) :
    (fun t => observe w (design k w) (stateFrom (design k w) S xs (release + t))) =
      fun t => AsyncFifo.observe (AsyncFifo.stateFrom (decode (k := k) (w := w) S) xs (release + t)) := by
  funext t
  rw [observe_eq hk hw _ (addrOk_after hk hw S xs release hstart _ (by omega)), decode_stateFrom hk hw]

theorem push_eq (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) (ha : AddrOk (k := k) S) :
    push w (design k w) S i = AsyncFifo.push (decode (k := k) (w := w) S) i := by
  simp only [push, AsyncFifo.push, observe_eq hk hw S ha, AsyncFifo.observe]

theorem pop_eq (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (i : Input k w) (ha : AddrOk (k := k) S) :
    pop w (design k w) S i = AsyncFifo.pop (decode (k := k) (w := w) S) i := by
  simp only [pop, AsyncFifo.pop, observe_eq hk hw S ha, AsyncFifo.observe]

end Model

/-! ## The queue reference -/

theorem correct (k w : Nat) (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w) (release : Nat)
    (hstart : Startup xs release)
    (htraffic : ∀ t, release ≤ t → (xs t).writeReset = false ∧ (xs t).readReset = false) :
    let inputs := fun t => queueInput (xs (release + t))
    let outputs := fun t => observe w (design k w) (stateFrom (design k w) S xs (release + t))
    QueueSpec.Trace (2 ^ k) inputs outputs (QueueSpec.run inputs outputs) := by
  intro inputs outputs
  have h : outputs = _ := outputs_eq hk hw S xs release hstart
  rw [h]
  exact trace_refines_queue (decode S) xs release hstart htraffic

theorem enqueue_progress (k w : Nat) (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w)
    (release t gap : Nat) (hstart : Startup xs release)
    (htraffic : ∀ u, release ≤ u → (xs u).writeReset = false ∧ (xs u).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun u => (xs (release + t + u)).writeEdge))
    (hcredit : (QueueSpec.run (fun u => queueInput (xs (release + u)))
        (fun u => observe w (design k w) (stateFrom (design k w) S xs (release + u))) t).length < 2 ^ k)
    (hoffer : ∀ u, u < 3 * gap → (xs (release + t + u)).valid = true) :
    ∃ u, u < 3 * gap ∧
      push w (design k w) (stateFrom (design k w) S xs (release + t + u)) (xs (release + t + u)) = true := by
  rw [outputs_eq hk hw S xs release hstart] at hcredit
  obtain ⟨u, hu, hp⟩ := write_progress_after_startup (decode S) xs release t gap hstart htraffic hf hcredit hoffer
  refine ⟨u, hu, ?_⟩
  rw [push_eq hk hw _ _ (addrOk_after hk hw S xs release hstart _ (by omega)), decode_stateFrom hk hw]
  exact hp

theorem dequeue_progress (k w : Nat) (hk : 0 < k) (hw : 0 < w) (S : MDesign.State) (xs : Nat → Input k w)
    (release t gap : Nat) (hstart : Startup xs release)
    (htraffic : ∀ u, release ≤ u → (xs u).writeReset = false ∧ (xs u).readReset = false)
    (hf : QueueSpec.EdgeFair gap (fun u => (xs (release + t + u)).readEdge))
    (hdata : QueueSpec.run (fun u => queueInput (xs (release + u)))
        (fun u => observe w (design k w) (stateFrom (design k w) S xs (release + u))) t ≠ [])
    (hoffer : ∀ u, u < 3 * gap → (xs (release + t + u)).ready = true) :
    ∃ u, u < 3 * gap ∧
      pop w (design k w) (stateFrom (design k w) S xs (release + t + u)) (xs (release + t + u)) = true := by
  rw [outputs_eq hk hw S xs release hstart] at hdata
  obtain ⟨u, hu, hp⟩ := read_progress_after_startup (decode S) xs release t gap hstart htraffic hf hdata hoffer
  refine ⟨u, hu, ?_⟩
  rw [pop_eq hk hw _ _ (addrOk_after hk hw S xs release hstart _ (by omega)), decode_stateFrom hk hw]
  exact hp

end HDLean.AsyncFifo.Word
