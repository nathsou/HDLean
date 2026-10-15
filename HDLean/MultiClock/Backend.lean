import HDLean.MultiClock.Core
import HDLean.Backend.Parse
namespace HDLean.MultiClock

private def svLit (l : Backend.Lit) : String :=
  if l == 0 then "1'b0" else if l == 1 then "1'b1"
  else (if l % 2 == 1 then "~" else "") ++ s!"n{l / 2}"

/-- Each latch has its own positive-edge block and physical clock port. -/
def systemVerilog (g : Graph) : String := Id.run do
  let a := g.logic
  let ports := (Array.range g.domainCount).map (fun d => s!"input wire clk_{d}") ++
    (Array.range a.inputs).map (fun k => s!"input wire in_{k}") ++
    (Array.range a.outputs.size).map (fun k => s!"output wire out_{k}")
  let mut lines := #[s!"module {Backend.identifier a.name}(\n  {String.intercalate ",\n  " ports.toList}\n);"]
  for k in [:a.inputs] do lines := lines.push s!"  wire n{k + 1} = in_{k};"
  for k in [:a.latches] do lines := lines.push s!"  logic n{a.inputs + k + 1};"
  for gate in a.gates do
    lines := lines.push s!"  wire n{gate.lhs} = {svLit gate.a} & {svLit gate.b};"
  for k in [:a.outputs.size] do lines := lines.push s!"  assign out_{k} = {svLit a.outputs[k]!};"
  for k in [:a.latches] do
    lines := lines ++ #[s!"  always_ff @(posedge clk_{g.clock[k]?.getD 0}) begin",
      s!"    n{a.inputs + k + 1} <= {svLit a.next[k]!};", "  end"]
  lines := lines.push "endmodule"
  return String.intercalate "\n" lines.toList ++ "\n"

private def rtlSig (l : Backend.Lit) : String :=
  if l == 0 then "1'0" else if l == 1 then "1'1"
  else if l % 2 == 1 then s!"\\not_{l / 2}" else s!"\\n{l / 2}"

/-- Native RTLIL uses each assigned domain directly at its $dff CLK port. -/
def rtlil (g : Graph) : String := Id.run do
  let a := g.logic
  let mut lines := #["autoidx 1", s!"module \\{Backend.identifier a.name}"]
  for d in [:g.domainCount] do lines := lines.push s!"  wire input {d+1} \\clk_{d}"
  for k in [:a.inputs] do lines := lines.push s!"  wire input {k+g.domainCount+1} \\in_{k}"
  for k in [:a.outputs.size] do lines := lines.push s!"  wire output {a.inputs+k+g.domainCount+1} \\out_{k}"
  for k in [:a.inputs+a.latches+a.gates.size] do
    let v := k+1
    lines := lines ++ #[s!"  wire \\n{v}", s!"  wire \\not_{v}", s!"  cell $not \\inv_{v}",
      "    parameter \\A_SIGNED 0", "    parameter \\A_WIDTH 1", "    parameter \\Y_WIDTH 1",
      s!"    connect \\A \\n{v}", s!"    connect \\Y \\not_{v}", "  end"]
  for k in [:a.inputs] do lines := lines.push s!"  connect \\n{k+1} \\in_{k}"
  for gate in a.gates do
    lines := lines ++ #[s!"  cell $and \\and_{gate.lhs}", "    parameter \\A_SIGNED 0", "    parameter \\B_SIGNED 0",
      "    parameter \\A_WIDTH 1", "    parameter \\B_WIDTH 1", "    parameter \\Y_WIDTH 1",
      s!"    connect \\A {rtlSig gate.a}", s!"    connect \\B {rtlSig gate.b}",
      s!"    connect \\Y \\n{gate.lhs}", "  end"]
  for k in [:a.latches] do
    lines := lines ++ #[s!"  cell $dff \\reg_{k}", "    parameter \\WIDTH 1", "    parameter \\CLK_POLARITY 1",
      s!"    connect \\CLK \\clk_{g.clock[k]?.getD 0}", s!"    connect \\D {rtlSig a.next[k]!}",
      s!"    connect \\Q \\n{a.inputs+k+1}", "  end"]
  for k in [:a.outputs.size] do lines := lines.push s!"  connect \\out_{k} {rtlSig a.outputs[k]!}"
  lines := lines.push "end"
  return String.intercalate "\n" lines.toList ++ "\n"

private abbrev Token := List Nat
private abbrev Parser := StateT (List Token) (Except String)
private def takeLine : Parser Token := do
  match ← get with
  | [] => throw "unexpected end of multi-clock module"
  | x::xs => set xs; return x
private def peekLine : Parser Token := do return (← get).headD []
private def expect (x : Token) : Parser Unit := do
  unless (← takeLine) == x do throw "unexpected multi-clock syntax"
private def decimal (x : Token) : Parser Nat := do
  if x.isEmpty then throw "empty decimal"
  if x.headD 0 == 48 && x != [48] then throw "noncanonical decimal"
  let mut n := 0
  for b in x do
    unless 48 ≤ b && b ≤ 57 do throw "invalid decimal"
    n := n * 10 + b - 48
  return n
private def indexed (x pre post : Token) : Parser Nat := do
  unless pre.isPrefixOf x && post.reverse.isPrefixOf x.reverse do throw "invalid clock syntax"
  decimal ((x.drop pre.length).take (x.length-pre.length-post.length))
private def words (s : Token) : List Token :=
  (s.splitOn 32).filter (· != [])
private def finish : Parser Unit := do
  unless (← get).isEmpty do throw "trailing multi-clock tokens"

private def parseSV : Parser Graph := do
  let header ← takeLine
  let mut count := 0
  for _ in (← get) do
    if (bytes% "input wire clk_").isPrefixOf (← peekLine) then
      expect t!"input wire clk_{count},"
      count := count + 1
    else break
  let mut normalized := [header, bytes% "input wire clk,"]
  let mut clocks := #[]
  let mut started := false
  for _ in (← get) do
    let line ← takeLine
    if line == (bytes% "endmodule") then
      if started then normalized := normalized ++ [bytes% "end"]
      normalized := normalized ++ [line]
      finish
      break
    else if (bytes% "always_ff").isPrefixOf line then
      let clock ← indexed line (bytes% "always_ff @(posedge clk_") (bytes% ") begin")
      unless clock < count do throw "undeclared clock domain"
      if !started then normalized := normalized ++ [bytes% "always_ff @(posedge clk) begin"]
      started := true
      normalized := normalized ++ [← takeLine]
      expect (bytes% "end")
      clocks := clocks.push clock
    else
      if started then throw "unexpected syntax after clocked state update"
      normalized := normalized ++ [line]
  let logic ← match Backend.Format.systemVerilog.parseTokens normalized with
    | .ok a => pure a
    | .error e => throw e
  let g : Graph := ⟨logic, count, clocks⟩
  unless g.wellFormed do throw "invalid multi-clock graph"
  return g

private def parseRTLIL : Parser Graph := do
  expect (bytes% "autoidx 1")
  let header ← takeLine
  let mut count := 0
  for _ in (← get) do
    let tokens := words (← peekLine)
    if (bytes% "\\clk_").isPrefixOf (tokens[3]?.getD []) then
      expect t!"wire input {count+1} \\clk_{count}"
      count := count+1
    else break
  let mut normalized := [bytes% "autoidx 1", header, bytes% "wire input 1 \\clk"]
  let mut clocks := #[]
  for _ in (← get) do
    let line ← takeLine
    let tokens := words line
    if (bytes% "connect \\CLK ").isPrefixOf line then
      let clock ← indexed line (bytes% "connect \\CLK \\clk_") []
      unless clock < count do throw "undeclared clock domain"
      clocks := clocks.push clock
      normalized := normalized ++ [bytes% "connect \\CLK \\clk"]
    else if tokens[0]?.getD [] == (bytes% "wire") &&
        (tokens[1]?.getD [] == (bytes% "input") || tokens[1]?.getD [] == (bytes% "output")) then
      let [wire, direction, port, name] := tokens | throw "invalid port declaration"
      let port ← decimal port
      unless count < port do throw "invalid port number"
      normalized := normalized ++ [wire ++ [32] ++ direction ++ [32] ++ t!"{port-count+1}" ++ [32] ++ name]
    else normalized := normalized ++ [line]
  let logic ← match Backend.Format.rtlil.parseTokens normalized with
    | .ok a => pure a
    | .error e => throw e
  let g : Graph := ⟨logic, count, clocks⟩
  unless g.wellFormed do throw "invalid multi-clock graph"
  return g

inductive Format where
  | systemVerilog | rtlil
  deriving Repr, DecidableEq

def Format.print (f : Format) (g : Graph) : String :=
  match f with | .systemVerilog => MultiClock.systemVerilog g | .rtlil => MultiClock.rtlil g

def Format.parse (f : Format) (text : String) : Except String Graph :=
  (match f with | .systemVerilog => parseSV | .rtlil => parseRTLIL).run' (Backend.Format.tokenize text)

def Format.validates (f : Format) (text : String) (g : Graph) : Bool :=
  match f.parse text with
  | .error _ => false
  | .ok parsed => parsed.logic.logic == g.logic.logic && parsed.clock == g.clock &&
      parsed.domainCount == g.domainCount

def Format.meaning (f : Format) (text : String) (edges : Nat → Bool) (inputs state : Array Bool) :
    Option (Array Bool × Array Bool) :=
  match f.parse text with
  | .error _ => none
  | .ok g => some (g.eval edges inputs state)

theorem Graph.eval_eq {a b : Graph} (hlogic : a.logic.logic = b.logic.logic)
    (hclock : a.clock = b.clock) (edges inputs state) :
    a.eval edges inputs state = b.eval edges inputs state := by
  have hlatches : a.logic.latches = b.logic.latches := congrArg Backend.Logic.latches hlogic
  unfold Graph.eval
  rw [Backend.Graph.eval_eq_of_logic_eq _ _ hlogic, hlatches, hclock]

/-- The strict grammar checks every physical clock and every ordinary logic driver. -/
theorem Format.validates_sound (f : Format) (text : String) (g : Graph)
    (h : f.validates text g = true) (edges inputs state) :
    f.meaning text edges inputs state = some (g.eval edges inputs state) := by
  unfold Format.validates at h
  unfold Format.meaning
  split at h
  · contradiction
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact congrArg some (Graph.eval_eq h.1.1 h.1.2 edges inputs state)

/-- A final text certificate covers arbitrary simultaneous domain edges. -/
theorem Format.correct_of_validated (f : Format) (text : String) (g : Graph)
    (c : Circuit nd i r o) (hg : g.Equivalent c) (ht : f.validates text g = true)
    (xs : Vector Bool i) (s : Vector Bool r) (rst : Bool) (edge : Nat → Bool) :
    f.meaning text edge (xs.toArray.push rst) s.toArray = some
      ((Vector.ofFn (c.next (fun k => s[k]) ((fun k => xs[k]), rst) (fun d => edge d.val))).toArray,
       (Vector.ofFn (c.output (fun k => s[k]) (fun k => xs[k]))).toArray) := by
  rw [f.validates_sound text g ht]
  exact congrArg some (Graph.eval_correct hg xs s rst edge)

def checkedCompile (c : Circuit nd i r o) : Except String {g : Graph // g.Equivalent c} := do
  let g ← Backend.checkedCompileLocal c.combinational
  return ⟨⟨g.val,nd,(Vector.ofFn fun k => (c.clock k).val).toArray⟩,g.property,rfl,rfl⟩

structure Emitted (format : Format) (c : Circuit nd i r o) where
  text : String
  correct : ∀ (xs : Vector Bool i) (s : Vector Bool r) (rst : Bool) (edge : Nat → Bool),
    format.meaning text edge (xs.toArray.push rst) s.toArray = some
      ((Vector.ofFn (c.next (fun k => s[k]) ((fun k => xs[k]),rst) (fun d => edge d.val))).toArray,
       (Vector.ofFn (c.output (fun k => s[k]) (fun k => xs[k]))).toArray)

def checkedPrint (format : Format) (c : Circuit nd i r o) : Except String (Emitted format c) := do
  let g ← checkedCompile c
  let text := format.print g.val
  if h : format.validates text g.val = true then
    return ⟨text,format.correct_of_validated text g.val c g.property h⟩
  else throw "multi-clock backend text validation failed"

end HDLean.MultiClock
