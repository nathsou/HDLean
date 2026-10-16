import HDLean.Backend.AigerProved
import HDLean.Backend.TextGrammar

set_option backward.isDefEq.respectTransparency false
namespace HDLean.Backend.Proved
open Text Text.Grammar

private abbrev Block (α : Type) := Grammar Line (List String) α Line.tokens
private def ilInputsRow : Row Nat :=
  before [⟨"wire", by decide, by decide⟩, ⟨"width", by decide, by decide⟩] (after natural [⟨"input", by decide, by decide⟩, ⟨"2", by decide, by decide⟩, ⟨"\\ins", by decide, by decide⟩])
private def ilInputs : Block Nat := line ilInputsRow (by intro a; simp [ilInputsRow, before, after, pair, Grammar.map, fixed, natural])

private def ilOutputsRow : Row Nat :=
  before [⟨"wire", by decide, by decide⟩, ⟨"width", by decide, by decide⟩] (after natural [⟨"output", by decide, by decide⟩, ⟨"3", by decide, by decide⟩, ⟨"\\outs", by decide, by decide⟩])
private def ilOutputs : Block Nat := line ilOutputsRow (by intro a; simp [ilOutputsRow, before, after, pair, Grammar.map, fixed, natural])

private def ilRegsRow : Row Nat :=
  before [⟨"wire", by decide, by decide⟩, ⟨"width", by decide, by decide⟩] (after natural [⟨"\\state", by decide, by decide⟩])
private def ilRegs : Block Nat := line ilRegsRow (by intro a; simp [ilRegsRow, before, after, pair, Grammar.map, fixed, natural])

private def ilGatesRow : Row Nat :=
  before [⟨"wire", by decide, by decide⟩, ⟨"width", by decide, by decide⟩] (after natural [⟨"\\gates", by decide, by decide⟩])
private def ilGates : Block Nat := line ilGatesRow (by intro a; simp [ilGatesRow, before, after, pair, Grammar.map, fixed, natural])

private def ilStart (moduleName : Word) : Block Unit := fixed [
  ⟨[⟨"autoidx", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"module", by decide, by decide⟩, moduleName], by simp⟩,
  ⟨[⟨"wire", by decide, by decide⟩, ⟨"input", by decide, by decide⟩, ⟨"1", by decide, by decide⟩, ⟨"\\clk", by decide, by decide⟩], by simp⟩]

private def ilHeader : Block Header :=
  (pair ilInputs (pair ilOutputs (pair ilRegs ilGates))).map
    (fun p => ⟨p.1-1,p.2.2.1-1,p.2.1-1,p.2.2.2-1⟩)
    (fun h => (h.inputs+1,(h.outputs+1,(h.latches+1,h.gates+1))))
    (by intro h; cases h; simp)

private def ilConstants (h : Header) : Block Unit := fixed [
  ⟨[⟨"wire", by decide, by decide⟩, ⟨"width", by decide, by decide⟩, numeral ((2*(h.inputs+h.latches+h.gates)+2)), ⟨"\\n", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, ⟨"0", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"1'0", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, ⟨"1", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"1'1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\outs", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (h.outputs), ⟨"]", by decide, by decide⟩, ⟨"1'0", by decide, by decide⟩], by simp⟩]

private def ilInv (k : Nat) : Block Unit := fixed [
  ⟨[⟨"cell", by decide, by decide⟩, ⟨"$not", by decide, by decide⟩, (prefixed ⟨"\\inv_", by decide, by decide⟩ (k))], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\A_SIGNED", by decide, by decide⟩, ⟨"0", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\A_WIDTH", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\Y_WIDTH", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\A", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*k)), ⟨"]", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\Y", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*k+1)), ⟨"]", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"end", by decide, by decide⟩], by simp⟩]

private def ilInput (k : Nat) : Block Unit := fixed [
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*(k+1))), ⟨"]", by decide, by decide⟩, ⟨"\\ins", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩], by simp⟩]

private def ilState (i k : Nat) : Block Unit := fixed [
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*(i+k+1))), ⟨"]", by decide, by decide⟩, ⟨"\\state", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩], by simp⟩]

private def ilEnd  : Block Unit := fixed [
  ⟨[⟨"end", by decide, by decide⟩], by simp⟩]

private def ilOutputRow (k : Nat) : Row (Nat) :=
  before [⟨"connect", by decide, by decide⟩, ⟨"\\outs", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩])
private def ilOutput (k : Nat) : Block (Nat) := line (ilOutputRow k) (by intro a; simp [ilOutputRow, before, after, pair, Grammar.map, fixed, natural])

private def ilNextDataRow  : Row (Nat) :=
  before [⟨"connect", by decide, by decide⟩, ⟨"\\D", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩])
private def ilNextData  : Block (Nat) := line (ilNextDataRow ) (by intro a; simp [ilNextDataRow, before, after, pair, Grammar.map, fixed, natural])

private def ilGateABRow  : Row (Nat) :=
  before [⟨"connect", by decide, by decide⟩, ⟨"\\A", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩])
private def ilGateAB  : Block (Nat) := line (ilGateABRow ) (by intro a; simp [ilGateABRow, before, after, pair, Grammar.map, fixed, natural])

private def ilGateBRow  : Row (Nat) :=
  before [⟨"connect", by decide, by decide⟩, ⟨"\\B", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩])
private def ilGateB  : Block (Nat) := line (ilGateBRow ) (by intro a; simp [ilGateBRow, before, after, pair, Grammar.map, fixed, natural])

private def ilGateTargetRow (k : Nat) : Row (Nat) :=
  before [⟨"connect", by decide, by decide⟩, ⟨"\\n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩, ⟨"\\gates", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩])
private def ilGateTarget (k : Nat) : Block (Nat) := line (ilGateTargetRow k) (by intro a; simp [ilGateTargetRow, before, after, pair, Grammar.map, fixed, natural])

private def ilNextStart (k : Nat) : Block Unit := fixed [
  ⟨[⟨"cell", by decide, by decide⟩, ⟨"$dff", by decide, by decide⟩, (prefixed ⟨"\\reg_", by decide, by decide⟩ (k))], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\WIDTH", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\CLK_POLARITY", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\CLK", by decide, by decide⟩, ⟨"\\clk", by decide, by decide⟩], by simp⟩]

private def ilNextEnd (k : Nat) : Block Unit := fixed [
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\Q", by decide, by decide⟩, ⟨"\\state", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"end", by decide, by decide⟩], by simp⟩]

private def ilNext (k : Nat) : Block Nat :=
  ((pair (ilNextStart k) (pair ilNextData (ilNextEnd k))).map
    (fun p => p.2.1) (fun n => ((),(n,()))) (by intro n; rfl))

private def ilGateStart (k : Nat) : Block Unit := fixed [
  ⟨[⟨"cell", by decide, by decide⟩, ⟨"$and", by decide, by decide⟩, (prefixed ⟨"\\and_", by decide, by decide⟩ (k))], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\A_SIGNED", by decide, by decide⟩, ⟨"0", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\B_SIGNED", by decide, by decide⟩, ⟨"0", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\A_WIDTH", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\B_WIDTH", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"parameter", by decide, by decide⟩, ⟨"\\Y_WIDTH", by decide, by decide⟩, ⟨"1", by decide, by decide⟩], by simp⟩]

private def ilGateEnd (k : Nat) : Block Unit := fixed [
  ⟨[⟨"connect", by decide, by decide⟩, ⟨"\\Y", by decide, by decide⟩, ⟨"\\gates", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"end", by decide, by decide⟩], by simp⟩]

private def ilGate (k : Nat) : Block Gate :=
  (pair (ilGateStart k) (pair ilGateAB (pair ilGateB (pair (ilGateEnd k) (ilGateTarget k))))).map
    (fun p => ⟨p.2.2.2.2 / 2,p.2.1,p.2.2.1⟩)
    (fun g => ((),(g.a,(g.b,((),2*g.lhs))))) (by intro g; cases g; simp)

/-- Standard RTLIL cells, with explicit scalar widths and no initial state constraints. -/
def Aag.ilLinesNamed (moduleName : Word) (g : Aag) : List Line :=
  let h : Header := ⟨g.inputs,g.next.length,g.outputs.length,g.gates.length⟩
  (ilStart moduleName).encode () ++ ilHeader.encode h ++ (ilConstants h).encode () ++
  repeatEncode ilInput 0 (List.replicate g.inputs ()) ++
  repeatEncode (ilState g.inputs) 0 (List.replicate g.next.length ()) ++
  repeatEncode ilInv 1 (List.replicate (g.inputs+g.next.length+g.gates.length) ()) ++
  repeatEncode ilGate 0 g.gates ++ repeatEncode ilOutput 0 g.outputs ++
  repeatEncode ilNext 0 g.next ++ ilEnd.encode ()

private def topWord : Word := ⟨"\\hd_top",by decide,by decide⟩
private def numberedWord (id : Nat) : Word := prefixed ⟨"\\hd_m_",by decide,by decide⟩ id

def Aag.ilLines (g : Aag) : List Line := g.ilLinesNamed topWord

def Aag.rtlil (g : Aag) : String := Text.render g.ilLines

def Aag.rtlilNamed (id : Nat) (g : Aag) : String := Text.render (g.ilLinesNamed (numberedWord id))

private def readILTokens (moduleName : Word) (tokens : List (List String)) : Option (Aag × List (List String)) := do
  let (_,rest) ← (ilStart moduleName).decode tokens
  let (h,rest) ← ilHeader.decode rest
  let (_,rest) ← (ilConstants h).decode rest
  let (_,rest) ← repeatDecode ilInput h.inputs 0 rest
  let (_,rest) ← repeatDecode (ilState h.inputs) h.latches 0 rest
  let (_,rest) ← repeatDecode ilInv (h.inputs+h.latches+h.gates) 1 rest
  let (gs,rest) ← repeatDecode ilGate h.gates 0 rest
  let (os,rest) ← repeatDecode ilOutput h.outputs 0 rest
  let (ns,rest) ← repeatDecode ilNext h.latches 0 rest
  let (_,rest) ← ilEnd.decode rest
  return (⟨h.inputs,ns,os,gs⟩,rest)

private def parseILTokens (moduleName : Word) (tokens : List (List String)) : Option Aag := do
  let (g,rest) ← readILTokens moduleName tokens
  if rest.isEmpty then return g else none

def Aag.parseRTLIL (text : String) : Option Aag := parseILTokens topWord (Text.tokenize text)

def Aag.parseRTLILNamed (id : Nat) (text : String) : Option Aag :=
  parseILTokens (numberedWord id) (Text.tokenize text)

private theorem il_read_roundtrip (moduleName : Word) (g : Aag) (tail : List (List String)) :
    readILTokens moduleName ((g.ilLinesNamed moduleName).map Line.tokens ++ tail) = some (g,tail) := by
  simp only [Aag.ilLinesNamed, List.map_append, List.append_assoc, readILTokens, Grammar.roundtrip]
  dsimp only [Bind.bind, Option.bind]
  rw [Grammar.roundtrip]
  dsimp only [Bind.bind, Option.bind]
  rw [Grammar.roundtrip]
  dsimp only [Bind.bind, Option.bind]
  have hi := repeat_roundtrip ilInput (List.replicate g.inputs ()) 0
  have hr := repeat_roundtrip (ilState g.inputs) (List.replicate g.next.length ()) 0
  have hv := repeat_roundtrip ilInv (List.replicate (g.inputs+g.next.length+g.gates.length) ()) 1
  simp only [List.length_replicate] at hi hr hv
  rw [hi]
  dsimp only [Bind.bind, Option.bind]
  rw [hr]
  dsimp only [Bind.bind, Option.bind]
  rw [hv]
  dsimp only [Bind.bind, Option.bind]
  rw [repeat_roundtrip]
  dsimp only [Bind.bind, Option.bind]
  rw [repeat_roundtrip]
  dsimp only [Bind.bind, Option.bind]
  rw [repeat_roundtrip]
  dsimp only [Bind.bind, Option.bind]
  have he := ilEnd.roundtrip () tail
  rw [he]
  cases g
  rfl

private theorem il_roundtrip (moduleName : Word) (g : Aag) :
    parseILTokens moduleName (Text.tokenize (Text.render (g.ilLinesNamed moduleName))) = some g := by
  rw [Text.tokenize_render]
  unfold parseILTokens
  have h := il_read_roundtrip moduleName g []
  simp only [List.append_nil] at h
  rw [h]
  rfl

def Aag.rtlilModuleLines (id : Nat) (g : Aag) : List Line := g.ilLinesNamed (numberedWord id)
def Aag.readRTLILModule (id : Nat) : List (List String) → Option (Aag × List (List String)) :=
  readILTokens (numberedWord id)

theorem Aag.read_rtlilModule (id : Nat) (g : Aag) (tail : List (List String)) :
    Aag.readRTLILModule id ((g.rtlilModuleLines id).map Line.tokens ++ tail) = some (g,tail) :=
  il_read_roundtrip (numberedWord id) g tail

theorem Aag.parse_rtlil (g : Aag) : Aag.parseRTLIL g.rtlil = some g := il_roundtrip topWord g

theorem Aag.parse_rtlilNamed (id : Nat) (g : Aag) :
    Aag.parseRTLILNamed id (g.rtlilNamed id) = some g := il_roundtrip (numberedWord id) g

theorem rtlil_print_correct (g : Graph) (hn : g.next.size = g.latches) (inputs state : Array Bool) :
    (Aag.parseRTLIL (Aag.ofGraph g).rtlil).map
      (fun parsed => parsed.graph.eval inputs state) = some (g.eval inputs state) := by
  rw [Aag.parse_rtlil]
  exact congrArg some (Graph.eval_eq_of_logic_eq _ _ (Aag.ofGraph_logic g hn) inputs state)

end HDLean.Backend.Proved
