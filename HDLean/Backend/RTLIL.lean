import HDLean.Backend.SystemVerilog
namespace HDLean.Backend

private def rtlSig (l : Lit) : String :=
  if l == 0 then "1'0" else if l == 1 then "1'1"
  else if l % 2 == 1 then s!"\\not_{l / 2}" else s!"\\n{l / 2}"

/-- Yosys RTLIL with explicit one-bit $and/$not/$dff cells. No init attributes are emitted. -/
def rtlil (g : Graph) : String := Id.run do
  let mut lines := #["autoidx 1", s!"module \\{identifier g.name}", "  wire input 1 \\clk"]
  for k in [:g.inputs] do
    lines := lines.push s!"  wire input {k + 2} \\in_{k}"
  for k in [:g.outputs.size] do
    lines := lines.push s!"  wire output {g.inputs + k + 2} \\out_{k}"
  let vars := g.inputs + g.latches + g.gates.size
  for k in [:vars] do
    let v := k + 1
    lines := lines.push s!"  wire \\n{v}"
    lines := lines.push s!"  wire \\not_{v}"
    lines := lines.push s!"  cell $not \\inv_{v}"
    lines := lines ++ #["    parameter \\A_SIGNED 0", "    parameter \\A_WIDTH 1", "    parameter \\Y_WIDTH 1",
      s!"    connect \\A \\n{v}", s!"    connect \\Y \\not_{v}", "  end"]
  for k in [:g.inputs] do lines := lines.push s!"  connect \\n{k + 1} \\in_{k}"
  for gate in g.gates do
    lines := lines ++ #[s!"  cell $and \\and_{gate.lhs}", "    parameter \\A_SIGNED 0", "    parameter \\B_SIGNED 0",
      "    parameter \\A_WIDTH 1", "    parameter \\B_WIDTH 1", "    parameter \\Y_WIDTH 1",
      s!"    connect \\A {rtlSig gate.a}", s!"    connect \\B {rtlSig gate.b}",
      s!"    connect \\Y \\n{gate.lhs}", "  end"]
  for k in [:g.latches] do
    lines := lines ++ #[s!"  cell $dff \\reg_{k}", "    parameter \\WIDTH 1", "    parameter \\CLK_POLARITY 1",
      "    connect \\CLK \\clk", s!"    connect \\D {rtlSig g.next[k]!}",
      s!"    connect \\Q \\n{g.inputs + k + 1}", "  end"]
  for k in [:g.outputs.size] do lines := lines.push s!"  connect \\out_{k} {rtlSig g.outputs[k]!}"
  lines := lines.push "end"
  return String.intercalate "\n" lines.toList ++ "\n"
end HDLean.Backend
