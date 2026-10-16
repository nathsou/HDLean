import HDLean.Backend.AigerProved
import HDLean.Backend.TextGrammar

set_option backward.isDefEq.respectTransparency false
namespace HDLean.Backend.Proved
open Text Text.Grammar

private abbrev Block (α : Type) := Grammar Line (List String) α Line.tokens
private def svPortsRow : Row (Nat × Nat) :=
  before [⟨"module", by decide, by decide⟩, ⟨"hd_top", by decide, by decide⟩, ⟨"(", by decide, by decide⟩, ⟨"input", by decide, by decide⟩, ⟨"wire", by decide, by decide⟩, ⟨"clk", by decide, by decide⟩, ⟨",", by decide, by decide⟩, ⟨"input", by decide, by decide⟩, ⟨"wire", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (pair (after natural [⟨":", by decide, by decide⟩, ⟨"0", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"ins", by decide, by decide⟩, ⟨",", by decide, by decide⟩, ⟨"output", by decide, by decide⟩, ⟨"wire", by decide, by decide⟩, ⟨"[", by decide, by decide⟩]) (before [] (after natural [⟨":", by decide, by decide⟩, ⟨"0", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"outs", by decide, by decide⟩, ⟨")", by decide, by decide⟩, ⟨";", by decide, by decide⟩])))

private def svPorts : Block (Nat × Nat) := line svPortsRow (by intro a; simp [svPortsRow, before, after, pair, Grammar.map, fixed, natural])

private def svRegsRow : Row (Nat) :=
  before [⟨"reg", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨":", by decide, by decide⟩, ⟨"0", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"state", by decide, by decide⟩, ⟨";", by decide, by decide⟩])

private def svRegs : Block (Nat) := line svRegsRow (by intro a; simp [svRegsRow, before, after, pair, Grammar.map, fixed, natural])

private def svGatesRow : Row (Nat) :=
  before [⟨"wire", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨":", by decide, by decide⟩, ⟨"0", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"gates", by decide, by decide⟩, ⟨";", by decide, by decide⟩])

private def svGates : Block (Nat) := line svGatesRow (by intro a; simp [svGatesRow, before, after, pair, Grammar.map, fixed, natural])

private def svInvRow (k : Nat) : Row (Unit) :=
  fixed [⟨"assign", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*k+1)), ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"~", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*k)), ⟨"]", by decide, by decide⟩, ⟨";", by decide, by decide⟩]

private def svInv (k : Nat) : Block (Unit) := line (svInvRow k) (by intro a; simp [svInvRow, fixed])

private def svInputRow (k : Nat) : Row (Unit) :=
  fixed [⟨"assign", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*(k+1))), ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"ins", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩, ⟨";", by decide, by decide⟩]

private def svInput (k : Nat) : Block (Unit) := line (svInputRow k) (by intro a; simp [svInputRow, fixed])

private def svStateRow (i k : Nat) : Row (Unit) :=
  fixed [⟨"assign", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*(i+k+1))), ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"state", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩, ⟨";", by decide, by decide⟩]

private def svState (i k : Nat) : Block (Unit) := line (svStateRow i k) (by intro a; simp [svStateRow, fixed])

private def svNextRow (k : Nat) : Row (Nat) :=
  before [⟨"always", by decide, by decide⟩, ⟨"@", by decide, by decide⟩, ⟨"(", by decide, by decide⟩, ⟨"posedge", by decide, by decide⟩, ⟨"clk", by decide, by decide⟩, ⟨")", by decide, by decide⟩, ⟨"state", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩, ⟨"<=", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩, ⟨";", by decide, by decide⟩])

private def svNext (k : Nat) : Block (Nat) := line (svNextRow k) (by intro a; simp [svNextRow, before, after, pair, Grammar.map, fixed, natural])

private def svOutputRow (k : Nat) : Row (Nat) :=
  before [⟨"assign", by decide, by decide⟩, ⟨"outs", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩, ⟨";", by decide, by decide⟩])

private def svOutput (k : Nat) : Block (Nat) := line (svOutputRow k) (by intro a; simp [svOutputRow, before, after, pair, Grammar.map, fixed, natural])

private def svGateRow (k : Nat) : Row (Nat × Nat) :=
  before [⟨"assign", by decide, by decide⟩, ⟨"gates", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (pair (after natural [⟨"]", by decide, by decide⟩, ⟨"&", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩]) (before [] (after natural [⟨"]", by decide, by decide⟩, ⟨";", by decide, by decide⟩])))
private def svGateTargetRow (k : Nat) : Row Nat :=
  before [⟨"assign", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩] (after natural [⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"gates", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (k), ⟨"]", by decide, by decide⟩, ⟨";", by decide, by decide⟩])
private def svGate (k : Nat) : Block Gate :=
  ((pair (line (svGateRow k) (by intro a; simp [svGateRow, before, after, pair, Grammar.map, fixed, natural]))
    (line (svGateTargetRow k) (by intro a; simp [svGateTargetRow, before, after, pair, Grammar.map, fixed, natural]))).map
    (fun p => ⟨p.2 / 2, p.1.1, p.1.2⟩) (fun g => ((g.a,g.b),2*g.lhs))
    (by intro g; cases g; simp))

private def svHeader : Block Header :=
  (pair svPorts (pair svRegs svGates)).map
    (fun p => ⟨p.1.1,p.2.1,p.1.2,p.2.2⟩)
    (fun h => ((h.inputs,h.outputs),(h.latches,h.gates))) (by intro h; cases h; rfl)

private def svConstants (h : Header) : Block Unit := fixed [
  ⟨[⟨"wire", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral ((2*(h.inputs+h.latches+h.gates)+1)), ⟨":", by decide, by decide⟩, ⟨"0", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨";", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"assign", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, ⟨"0", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"1'b0", by decide, by decide⟩, ⟨";", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"assign", by decide, by decide⟩, ⟨"n", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, ⟨"1", by decide, by decide⟩, ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"1'b1", by decide, by decide⟩, ⟨";", by decide, by decide⟩], by simp⟩,
  ⟨[⟨"assign", by decide, by decide⟩, ⟨"outs", by decide, by decide⟩, ⟨"[", by decide, by decide⟩, numeral (h.outputs), ⟨"]", by decide, by decide⟩, ⟨"=", by decide, by decide⟩, ⟨"1'b0", by decide, by decide⟩, ⟨";", by decide, by decide⟩], by simp⟩]

private def svEnd : Block Unit := fixed [⟨[⟨"endmodule", by decide, by decide⟩], by simp⟩]

/-- Scalar gate equations use one common literal bus; arbitrary state has no initializer. -/
def Aag.svLines (g : Aag) : List Line :=
  let h : Header := ⟨g.inputs,g.next.length,g.outputs.length,g.gates.length⟩
  svHeader.encode h ++ (svConstants h).encode () ++
  repeatEncode svInput 0 (List.replicate g.inputs ()) ++
  repeatEncode (svState g.inputs) 0 (List.replicate g.next.length ()) ++
  repeatEncode svInv 1 (List.replicate (g.inputs+g.next.length+g.gates.length) ()) ++
  repeatEncode svGate 0 g.gates ++ repeatEncode svOutput 0 g.outputs ++
  repeatEncode svNext 0 g.next ++ svEnd.encode ()

def Aag.systemVerilog (g : Aag) : String := Text.render g.svLines

private def parseSVTokens (tokens : List (List String)) : Option Aag := do
  let (h,rest) ← svHeader.decode tokens
  let (_,rest) ← (svConstants h).decode rest
  let (_,rest) ← repeatDecode svInput h.inputs 0 rest
  let (_,rest) ← repeatDecode (svState h.inputs) h.latches 0 rest
  let (_,rest) ← repeatDecode svInv (h.inputs+h.latches+h.gates) 1 rest
  let (gs,rest) ← repeatDecode svGate h.gates 0 rest
  let (os,rest) ← repeatDecode svOutput h.outputs 0 rest
  let (ns,rest) ← repeatDecode svNext h.latches 0 rest
  let (_,rest) ← svEnd.decode rest
  if rest.isEmpty then return ⟨h.inputs,ns,os,gs⟩ else none

def Aag.parseSystemVerilog (text : String) : Option Aag := parseSVTokens (Text.tokenize text)

theorem Aag.parse_systemVerilog (g : Aag) : Aag.parseSystemVerilog g.systemVerilog = some g := by
  unfold Aag.parseSystemVerilog Aag.systemVerilog
  rw [Text.tokenize_render]
  simp only [Aag.svLines, List.map_append, List.append_assoc, parseSVTokens,
    Grammar.roundtrip]
  dsimp only [Bind.bind, Option.bind]
  rw [Grammar.roundtrip]
  dsimp only [Bind.bind, Option.bind]
  have hi := repeat_roundtrip svInput (List.replicate g.inputs ()) 0
  have hr := repeat_roundtrip (svState g.inputs) (List.replicate g.next.length ()) 0
  have hv := repeat_roundtrip svInv (List.replicate (g.inputs+g.next.length+g.gates.length) ()) 1
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
  have he := svEnd.roundtrip () []
  simp only [List.append_nil] at he
  rw [he]
  cases g
  rfl

theorem systemVerilog_print_correct (g : Graph) (hn : g.next.size = g.latches) (inputs state : Array Bool) :
    (Aag.parseSystemVerilog (Aag.ofGraph g).systemVerilog).map
      (fun parsed => parsed.graph.eval inputs state) = some (g.eval inputs state) := by
  rw [Aag.parse_systemVerilog]
  exact congrArg some (Graph.eval_eq_of_logic_eq _ _ (Aag.ofGraph_logic g hn) inputs state)

end HDLean.Backend.Proved
