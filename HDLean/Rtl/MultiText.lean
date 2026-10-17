import HDLean.Rtl.Multi
import HDLean.Rtl.RTLILProof

/-!
# Multi-clock SystemVerilog and RTLIL

A multi-clock design prints as its modules (exactly as a single-clock design
prints them) followed by a top module `hd_mtop`: per domain a clock and a reset
pin, its external inputs (`x_<d>_<k>`) and outputs (`y_<d>_<k>`), and one
instance of its top module; per crossing two flops clocked by the destination
(`s1_<c>`, `s2_<c>`, cleared by its reset); per shared memory an array written
on the writer's clock and read asynchronously at the reader's address register.

The modules are decoded statement by statement as before. The top module's
structure is decoded from its header comments (`hdlean multiclock`, `domain`,
`crossing`, `shared`), and the rest of it is accepted only if printing the
decoded design reproduces the file exactly.
-/
namespace HDLean.Rtl.MultiText
open Emit Lex Backend.Text

/-! ## Words -/

def appendWord (a b : Word) : Word :=
  ⟨a.text ++ b.text, by simpa using And.intro a.noSpace b.noSpace, by simpa using And.intro a.noNewline b.noNewline⟩

macro "w!" s:str : term => `((⟨$s, by decide, by decide⟩ : HDLean.Backend.Text.Word))

/-- A word the decoder never inspects. -/
def raw (w : Word) : TW := ⟨w, classify w.text, rfl⟩

def n1 (pre : Word) (a : Nat) : TW := raw (prefixed pre a)
def n2 (pre : Word) (a b : Nat) : TW := raw (prefixed (appendWord (prefixed pre a) (w! "_")) b)

/-- `"\\sm_<k>"`, a shared memory's `MEMID`. -/
def smId (k : Nat) : TW := raw (appendWord (prefixed (w! "\"\\\\sm_") k) (w! "\""))

end HDLean.Rtl.MultiText

namespace HDLean.Rtl.MDesign
open HDLean.Rtl.MultiText Emit Lex Backend.Text
variable (md : HDLean.Rtl.MDesign)

def nExt (d : Nat) : Nat := (md.topModule d).inputs.size - 1 - (md.extraWidths d).length

def inWidth (d k : Nat) : Nat := ((md.topModule d).inputs[k]?.map Port.width).getD 0
def outW (d k : Nat) : Nat := (md.outWidth d k).getD 0
def domains : List Nat := List.range md.tops.size

/-- What the top module connects to input `k` of domain `d`'s instance. -/
def inputSig (d k : Nat) (sv : Bool) : TW :=
  let p := fun (s : String) => if sv then s else "\\" ++ s
  if k = 0 then n1 (if sv then w! "rst_" else w! "\\rst_") d
  else if k ≤ md.nExt d then n2 (if sv then w! "x_" else w! "\\x_") d k
  else
    let j := k - 1 - md.nExt d
    let cs := (md.crossings.toList.zipIdx.filter fun p => p.1.dst = d).map (·.2)
    let ms := (md.mems.toList.zipIdx.filter fun p => p.1.rdom = d).map (·.2)
    if h : j < cs.length then n1 (if sv then w! "s2_" else w! "\\s2_") cs[j]
    else n1 (if sv then w! "md_" else w! "\\md_") (ms.getD (j - cs.length) 0)

/-! ## Header (decoded) -/

def domainLine (_ : Nat) (t : Nat) : TLine := ⟨lit! "//", [lit! "domain", .num t]⟩
def crossingLine (_ : Nat) (c : Crossing) : TLine := ⟨lit! "//", [lit! "crossing", .num c.src, .num c.out, .num c.dst]⟩
def sharedLine (i : Nat) (mm : SharedMem) : TLine :=
  ⟨lit! "//", [lit! "shared", .num mm.addrWidth, .num mm.width, .num mm.wdom, .num mm.wen, .num mm.waddr,
    .num mm.wdata, .num mm.rdom, .num mm.raddr, .mem i mm.name]⟩

def headerLines : List TLine :=
  ⟨lit! "//", [lit! "hdlean", lit! "multiclock", .num md.tops.size, .num md.crossings.size, .num md.mems.size]⟩ ::
  md.tops.toList.zipIdx.flatMap (fun p => [domainLine p.2 p.1]) ++
  md.crossings.toList.zipIdx.flatMap (fun p => [crossingLine p.2 p.1]) ++
  md.mems.toList.zipIdx.flatMap (fun p => [sharedLine p.2 p.1])

/-! ## SystemVerilog top module (checked by reprint) -/

def range (w : Nat) : List TW := [lit! "[", .num (w - 1), lit! ":", .num 0, lit! "]"]

def svPorts : List TLine :=
  (md.domains.flatMap fun d =>
    [⟨lit! ",", [lit! "input", lit! "wire", n1 (w! "clk_") d]⟩, ⟨lit! ",", [lit! "input", lit! "wire", n1 (w! "rst_") d]⟩] ++
    (List.range (md.nExt d)).map (fun k =>
      ⟨lit! ",", [lit! "input", lit! "wire"] ++ range (md.inWidth d (k + 1)) ++ [n2 (w! "x_") d (k + 1)]⟩) ++
    (List.range (md.topModule d).outputs.size).map (fun k =>
      ⟨lit! ",", [lit! "output", lit! "wire"] ++ range (md.outW d k) ++ [n2 (w! "y_") d k]⟩))

def svInstance (d : Nat) : List TLine :=
  let m := md.topModule d
  [⟨.module (md.topOf d) m.name, [.inst d, lit! "(", lit! ".clk", lit! "(", n1 (w! "clk_") d, lit! ")"]⟩] ++
  (List.range m.inputs.size).map (fun k =>
    ⟨lit! ",", [SV.dotTW 'i' (.inl rfl) k (SV.inName m k), lit! "(", md.inputSig d k true, lit! ")"]⟩) ++
  (List.range m.outputs.size).map (fun k =>
    ⟨lit! ",", [SV.dotTW 'o' (.inr rfl) k ((m.outputs[k]?.map OutPort.name).getD default), lit! "(",
      n2 (w! "y_") d k, lit! ")"]⟩) ++
  [⟨lit! ",", [lit! ".rst", lit! "(", n1 (w! "rst_") d, lit! ")", lit! ")", lit! ";"]⟩]

def svCrossing (k : Nat) (c : Crossing) : List TLine :=
  let w := (md.regOut c.src c.out).2
  [⟨lit! "reg", range w ++ [n1 (w! "s1_") k, lit! ";"]⟩, ⟨lit! "reg", range w ++ [n1 (w! "s2_") k, lit! ";"]⟩,
   ⟨lit! "always", [lit! "@", lit! "(", lit! "posedge", n1 (w! "clk_") c.dst, lit! ")", lit! "if", lit! "(",
     n1 (w! "rst_") c.dst, lit! ")", lit! "begin", n1 (w! "s1_") k, lit! "<=", .num 0, lit! ";", n1 (w! "s2_") k, lit! "<=",
     .num 0, lit! ";", lit! "end", lit! "else", lit! "begin", n1 (w! "s1_") k, lit! "<=", n2 (w! "y_") c.src c.out,
     lit! ";", n1 (w! "s2_") k, lit! "<=", n1 (w! "s1_") k, lit! ";", lit! "end"]⟩]

def svMemDecl (k : Nat) (mm : SharedMem) : List TLine :=
  [⟨lit! "reg", range mm.width ++ [n1 (w! "sm_") k, lit! "[", .num 0, lit! ":", .num (2 ^ mm.addrWidth - 1), lit! "]",
     lit! ";"]⟩,
   ⟨lit! "wire", range mm.width ++ [n1 (w! "md_") k, lit! ";"]⟩]

def svMemLogic (k : Nat) (mm : SharedMem) : List TLine :=
  [⟨lit! "always", [lit! "@", lit! "(", lit! "posedge", n1 (w! "clk_") mm.wdom, lit! ")", lit! "if", lit! "(",
     n2 (w! "y_") mm.wdom mm.wen, lit! ")", n1 (w! "sm_") k, lit! "[", n2 (w! "y_") mm.wdom mm.waddr, lit! "]", lit! "<=",
     n2 (w! "y_") mm.wdom mm.wdata, lit! ";"]⟩,
   ⟨lit! "assign", [n1 (w! "md_") k, lit! "=", n1 (w! "sm_") k, lit! "[", n2 (w! "y_") mm.rdom mm.raddr, lit! "]",
     lit! ";"]⟩]

def svTop : List TLine :=
  [⟨lit! "module", [lit! "hd_mtop", lit! "("]⟩, ⟨lit! "input", [lit! "wire", lit! "hd_unused"]⟩] ++ md.svPorts ++
  [⟨lit! ")", [lit! ";"]⟩] ++
  md.crossings.toList.zipIdx.flatMap (fun p => md.svCrossing p.2 p.1) ++
  md.mems.toList.zipIdx.flatMap (fun p => svMemDecl p.2 p.1) ++
  md.domains.flatMap md.svInstance ++
  md.mems.toList.zipIdx.flatMap (fun p => svMemLogic p.2 p.1) ++
  [⟨lit! "endmodule", []⟩]

def svLines : List TLine := SV.designLines md.design ++ md.headerLines ++ md.svTop

def systemVerilog : String := renderLines md.svLines

/-! ## RTLIL top module (checked by reprint) -/

def domainStmt (_ : Nat) (t : Nat) : IL.PStmt := .comment [lit! "domain", .num t]
def crossingStmt (_ : Nat) (c : Crossing) : IL.PStmt := .comment [lit! "crossing", .num c.src, .num c.out, .num c.dst]
def sharedStmt (i : Nat) (mm : SharedMem) : IL.PStmt :=
  .comment [lit! "shared", .num mm.addrWidth, .num mm.width, .num mm.wdom, .num mm.wen, .num mm.waddr,
    .num mm.wdata, .num mm.rdom, .num mm.raddr, IL.W.mem i mm.name]

def ilHeader : List IL.PStmt :=
  .comment [lit! "hdlean", lit! "multiclock", .num md.tops.size, .num md.crossings.size, .num md.mems.size] ::
  md.tops.toList.zipIdx.map (fun p => domainStmt p.2 p.1) ++
  md.crossings.toList.zipIdx.map (fun p => crossingStmt p.2 p.1) ++
  md.mems.toList.zipIdx.map (fun p => sharedStmt p.2 p.1)

/-- Port wires of the top module, numbered from 1. -/
def ilPortsOf (d : Nat) : List (Nat → IL.PStmt) :=
  [fun n => .wire 1 (.input n) (n1 (w! "\\clk_") d), fun n => .wire 1 (.input n) (n1 (w! "\\rst_") d)] ++
  (List.range (md.nExt d)).map (fun k n => .wire (md.inWidth d (k + 1)) (.input n) (n2 (w! "\\x_") d (k + 1))) ++
  (List.range (md.topModule d).outputs.size).map (fun k n => .wire (md.outW d k) (.output n) (n2 (w! "\\y_") d k))

def ilPorts : List IL.PStmt :=
  ((md.domains.flatMap md.ilPortsOf).zipIdx.map fun p => p.1 (p.2 + 1))

open IL in
def ilInstance (d : Nat) : IL.PStmt :=
  let m := md.topModule d
  .cell (IL.W.module (md.topOf d) m.name) (raw (prefixed (w! "\\u_") d)) []
    ([(lit! "\\clk", [n1 (w! "\\clk_") d]), (lit! "\\rst", [n1 (w! "\\rst_") d])] ++
     (List.range m.inputs.size).map (fun k => (IL.W.input k (SV.inName m k), [md.inputSig d k false])) ++
     (List.range m.outputs.size).map (fun k =>
       (IL.W.output k ((m.outputs[k]?.map OutPort.name).getD default), [n2 (w! "\\y_") d k])))

open IL in
def ilFlop (k : Nat) (stage : Nat) (w dst : Nat) (src : TW) : List IL.PStmt :=
  let q := n1 (if stage = 1 then w! "\\s1_" else w! "\\s2_") k
  let dIn := n1 (if stage = 1 then w! "\\d1_" else w! "\\d2_") k
  [.wire w .none dIn,
   .cell (lit! "$mux") (n1 (if stage = 1 then w! "\\m1_" else w! "\\m2_") k) [(lit! "\\WIDTH", .num w)]
    [(lit! "\\A", [src]), (lit! "\\B", constSig w 0), (lit! "\\S", [n1 (w! "\\rst_") dst]), (lit! "\\Y", [dIn])],
   .cell (lit! "$dff") (n1 (if stage = 1 then w! "\\f1_" else w! "\\f2_") k)
    [(lit! "\\CLK_POLARITY", .num 1), (lit! "\\WIDTH", .num w)]
    [(lit! "\\CLK", [n1 (w! "\\clk_") dst]), (lit! "\\D", [dIn]), (lit! "\\Q", [q])]]

open IL in
def ilCrossing (k : Nat) (c : Crossing) : List IL.PStmt :=
  let w := (md.regOut c.src c.out).2
  [.wire w .none (n1 (w! "\\s1_") k), .wire w .none (n1 (w! "\\s2_") k)] ++
  ilFlop k 1 w c.dst (n2 (w! "\\y_") c.src c.out) ++ ilFlop k 2 w c.dst (n1 (w! "\\s1_") k)

open IL in
def ilMem (k : Nat) (mm : SharedMem) : List IL.PStmt :=
  [.memory mm.width (2 ^ mm.addrWidth) (n1 (w! "\\sm_") k), .wire mm.width .none (n1 (w! "\\md_") k),
   .cell (lit! "$memwr") (n1 (w! "\\mw_") k)
    [(lit! "\\MEMID", smId k), (lit! "\\ABITS", .num mm.addrWidth), (lit! "\\WIDTH", .num mm.width),
     (lit! "\\CLK_ENABLE", .num 1), (lit! "\\CLK_POLARITY", .num 1), (lit! "\\PRIORITY", .num 0)]
    [(lit! "\\CLK", [n1 (w! "\\clk_") mm.wdom]),
     (lit! "\\EN", lit! "{" :: List.replicate mm.width (n2 (w! "\\y_") mm.wdom mm.wen) ++ [lit! "}"]),
     (lit! "\\ADDR", [n2 (w! "\\y_") mm.wdom mm.waddr]), (lit! "\\DATA", [n2 (w! "\\y_") mm.wdom mm.wdata])],
   .cell (lit! "$memrd") (n1 (w! "\\mr_") k)
    [(lit! "\\MEMID", smId k), (lit! "\\ABITS", .num mm.addrWidth), (lit! "\\WIDTH", .num mm.width),
     (lit! "\\CLK_ENABLE", .num 0), (lit! "\\CLK_POLARITY", .num 0), (lit! "\\TRANSPARENT", .num 0)]
    [(lit! "\\CLK", [lit! "1'0"]), (lit! "\\EN", [lit! "1'1"]), (lit! "\\ADDR", [n2 (w! "\\y_") mm.rdom mm.raddr]),
     (lit! "\\DATA", [n1 (w! "\\md_") k])]]

def ilTop : List IL.PStmt :=
  [.module (raw (w! "\\hd_mtop"))] ++ md.ilPorts ++
  md.crossings.toList.zipIdx.flatMap (fun p => md.ilCrossing p.2 p.1) ++
  md.mems.toList.zipIdx.flatMap (fun p => ilMem p.2 p.1) ++
  md.domains.map md.ilInstance ++ [.endm]

def ilStmts : List IL.PStmt := IL.designStmts md.design ++ md.ilHeader ++ md.ilTop

def rtlil : String := IL.render md.ilStmts

end HDLean.Rtl.MDesign

namespace HDLean.Rtl.MultiText
open Emit Lex Backend.Text

/-! ## Decoding -/

def decHeaderSV : Dec (Nat × Nat × Nat) := oneLine fun
  | [.lit "//", .lit "hdlean", .lit "multiclock", .num nd, .num nc, .num nm] => some (nd, nc, nm)
  | _ => none
def decDomainSV : Dec Nat := oneLine fun
  | [.lit "//", .lit "domain", .num t] => some t
  | _ => none
def decCrossingSV : Dec Crossing := oneLine fun
  | [.lit "//", .lit "crossing", .num s, .num o, .num d] => some ⟨s, o, d⟩
  | _ => none
def decSharedSV : Dec SharedMem := oneLine fun
  | [.lit "//", .lit "shared", .num aw, .num w, .num wd, .num we, .num wa, .num wdt, .num rd, .num ra,
      .named 'm' _ n] => some ⟨n, aw, w, wd, we, wa, wdt, rd, ra⟩
  | _ => none

def decMultiSV (ls : List (List Tok)) : Option MDesign := do
  let (d, ls) ← SV.decDesign ls
  let ((nd, nc, nm), ls) ← decHeaderSV ls
  let (tops, ls) ← decRepeat (fun _ => decDomainSV) nd 0 ls
  let (cs, ls) ← decRepeat (fun _ => decCrossingSV) nc 0 ls
  let (ms, _) ← decRepeat (fun _ => decSharedSV) nm 0 ls
  pure ⟨d, tops.toArray, cs.toArray, ms.toArray⟩

/-- The meaning of a multi-clock SystemVerilog file, accepted only if it is
exactly the printing of the design it decodes to. -/
def _root_.HDLean.Rtl.MDesign.parseSystemVerilog (text : String) : Option MDesign :=
  match decMultiSV (lex text) with
  | some md => if md.systemVerilog = text then some md else none
  | none => none

def headerOfIL : IL.Stmt → Option (Nat × Nat × Nat)
  | .comment [.lit "hdlean", .lit "multiclock", .num nd, .num nc, .num nm] => some (nd, nc, nm)
  | _ => none
def domainOfIL : IL.Stmt → Option Nat
  | .comment [.lit "domain", .num t] => some t
  | _ => none
def crossingOfIL : IL.Stmt → Option Crossing
  | .comment [.lit "crossing", .num s, .num o, .num d] => some ⟨s, o, d⟩
  | _ => none
def sharedOfIL : IL.Stmt → Option SharedMem
  | .comment [.lit "shared", .num aw, .num w, .num wd, .num we, .num wa, .num wdt, .num rd, .num ra,
      .named 'm' _ n] => some ⟨n, aw, w, wd, we, wa, wdt, rd, ra⟩
  | _ => none

def decMultiIL (ss : List IL.Stmt) : Option MDesign := do
  let (d, ss) ← IL.decDesign ss
  let ((nd, nc, nm), ss) ← IL.sOne headerOfIL ss
  let (tops, ss) ← IL.sRepeat (fun _ => IL.sOne domainOfIL) nd 0 ss
  let (cs, ss) ← IL.sRepeat (fun _ => IL.sOne crossingOfIL) nc 0 ss
  let (ms, _) ← IL.sRepeat (fun _ => IL.sOne sharedOfIL) nm 0 ss
  pure ⟨d, tops.toArray, cs.toArray, ms.toArray⟩

def _root_.HDLean.Rtl.MDesign.parseRTLIL (text : String) : Option MDesign :=
  match (IL.lexStmts text).bind decMultiIL with
  | some md => if md.rtlil = text then some md else none
  | none => none

/-! ## Round trip -/

theorem decMultiSV_ok (md : HDLean.Rtl.MDesign) (hd : md.design.positive = true) :
    decMultiSV ((md.svLines).map TLine.toks) = some md := by
  have h1 := fun tail => SV.lines_ok decDomainSV MDesign.domainLine id (fun _ => True)
    (fun _ _ _ _ => rfl) md.tops.toList (fun _ _ => trivial) tail
  have h2 := fun tail => SV.lines_ok decCrossingSV MDesign.crossingLine id (fun _ => True)
    (fun _ _ _ _ => rfl) md.crossings.toList (fun _ _ => trivial) tail
  have h3 := fun tail => SV.lines_ok decSharedSV MDesign.sharedLine id (fun _ => True)
    (fun _ _ _ _ => rfl) md.mems.toList (fun _ _ => trivial) tail
  simp only [List.map_id, Array.length_toList] at h1 h2 h3
  simp only [MDesign.svLines, MDesign.headerLines, List.map_append, List.map_cons, List.append_assoc,
    List.cons_append, decMultiSV]
  rw [SV.decDesign_ok_tail _ hd]
  simp only [Option.bind_eq_bind, Option.bind_some, decHeaderSV, oneLine, TLine.toks, TW.num, List.map_cons,
    List.map_nil, Option.map_some]
  rw [h1]; simp only [Option.bind_some]
  rw [h2]; simp only [Option.bind_some]
  rw [h3]; simp only [Option.bind_some, pure]

/-- Printing then parsing returns the multi-clock design. -/
theorem _root_.HDLean.Rtl.MDesign.parse_systemVerilog (md : HDLean.Rtl.MDesign) (hd : md.design.positive = true) :
    MDesign.parseSystemVerilog md.systemVerilog = some md := by
  unfold MDesign.parseSystemVerilog
  rw [show lex md.systemVerilog = (md.svLines).map TLine.toks from lex_render _, decMultiSV_ok md hd]
  simp

theorem _root_.HDLean.Rtl.MDesign.parseSystemVerilog_canonical (text : String) (md : HDLean.Rtl.MDesign)
    (h : MDesign.parseSystemVerilog text = some md) : md.systemVerilog = text := by
  unfold MDesign.parseSystemVerilog at h
  split at h
  · split at h
    · rename_i heq; cases h; exact heq
    · cases h
  · cases h

theorem decMultiIL_ok (md : HDLean.Rtl.MDesign) (hd : md.design.rtlilOk = true) :
    decMultiIL ((md.ilStmts).map IL.PStmt.erase) = some md := by
  have h1 := fun tail => IL.items_ok domainOfIL MDesign.domainStmt id (fun _ => True)
    (fun _ _ _ => rfl) md.tops.toList (fun _ _ => trivial) tail
  have h2 := fun tail => IL.items_ok crossingOfIL MDesign.crossingStmt id (fun _ => True)
    (fun _ _ _ => rfl) md.crossings.toList (fun _ _ => trivial) tail
  have h3 := fun tail => IL.items_ok sharedOfIL MDesign.sharedStmt id (fun _ => True)
    (fun _ _ _ => rfl) md.mems.toList (fun _ _ => trivial) tail
  simp only [List.map_id, Array.length_toList] at h1 h2 h3
  simp only [MDesign.ilStmts, MDesign.ilHeader, List.map_append, List.map_cons, List.append_assoc,
    List.cons_append, decMultiIL]
  rw [IL.decDesign_ok_tail _ hd]
  simp only [Option.bind_eq_bind, Option.bind_some, IL.sOne, headerOfIL, IL.PStmt.erase, IL.toks, TW.num,
    List.map_cons, List.map_nil, Option.map_some]
  rw [h1]; simp only [Option.bind_some]
  rw [h2]; simp only [Option.bind_some]
  rw [h3]; simp only [Option.bind_some, pure]

theorem _root_.HDLean.Rtl.MDesign.parse_rtlil (md : HDLean.Rtl.MDesign) (hd : md.design.rtlilOk = true) :
    MDesign.parseRTLIL md.rtlil = some md := by
  unfold MDesign.parseRTLIL
  rw [show IL.lexStmts md.rtlil = some ((md.ilStmts).map IL.PStmt.erase) from IL.lexStmts_render _,
    Option.bind_some, decMultiIL_ok md hd]
  simp

theorem _root_.HDLean.Rtl.MDesign.parseRTLIL_canonical (text : String) (md : HDLean.Rtl.MDesign)
    (h : MDesign.parseRTLIL text = some md) : md.rtlil = text := by
  unfold MDesign.parseRTLIL at h
  split at h
  · split at h
    · rename_i heq; cases h; exact heq
    · cases h
  · cases h

end HDLean.Rtl.MultiText
