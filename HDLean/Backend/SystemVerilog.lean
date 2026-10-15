import HDLean.Backend.Graph
namespace HDLean.Backend

/-- External identifiers are normalized; user names survive as metadata only. -/
def identifier (s : String) : String :=
  "hd_" ++ String.ofList (s.toList.map fun c => if c.isAlphanum && c.toNat < 128 || c == '_' then c else '_')
private def svLit (l : Lit) : String :=
  if l == 0 then "1'b0" else if l == 1 then "1'b1"
  else (if l % 2 == 1 then "~" else "") ++ s!"n{l / 2}"

/-- A deliberately small two-state synthesizable SystemVerilog subset. -/
def systemVerilog (g : Graph) : String := Id.run do
  let ports := #["input wire clk"] ++
    (Array.range g.inputs).map (fun k => s!"input wire in_{k}") ++
    (Array.range g.outputs.size).map (fun k => s!"output wire out_{k}")
  let mut lines := #[s!"module {identifier g.name}(\n  {String.intercalate ",\n  " ports.toList}\n);"]
  for k in [:g.inputs] do lines := lines.push s!"  wire n{k + 1} = in_{k};"
  for k in [:g.latches] do lines := lines.push s!"  logic n{g.inputs + k + 1};"
  for gate in g.gates do
    lines := lines.push s!"  wire n{gate.lhs} = {svLit gate.a} & {svLit gate.b};"
  for k in [:g.outputs.size] do lines := lines.push s!"  assign out_{k} = {svLit g.outputs[k]!};"
  if g.latches > 0 then
    lines := lines.push "  always_ff @(posedge clk) begin"
    for k in [:g.latches] do
      lines := lines.push s!"    n{g.inputs + k + 1} <= {svLit g.next[k]!};"
    lines := lines.push "  end"
  lines := lines.push "endmodule"
  return String.intercalate "\n" lines.toList ++ "\n"
end HDLean.Backend
