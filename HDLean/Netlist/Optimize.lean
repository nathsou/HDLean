import HDLean.Netlist.Lower
namespace HDLean.Netlist

/-- Local constant/negation rewrites are small enough to prove once in the kernel. -/
def invert (a : Node d i r) : Node d i r := match a with
  | .lit b => .lit (!b)
  | .inv b => b
  | _ => .inv a

theorem invert_correct (a : Node d i r) (xs s) : (invert a).eval xs s = !(a.eval xs s) := by
  cases a <;> simp [invert, Node.eval]

def conjunction (a b : Node d i r) : Node d i r :=
  match a, b with
  | .lit false, _ | _, .lit false => .lit false
  | .lit true, b => b
  | a, .lit true => a
  | a, b => .and a b

theorem conjunction_correct (a b : Node d i r) (xs s) :
    (conjunction a b).eval xs s = (a.eval xs s && b.eval xs s) := by
  cases a <;> cases b <;> simp [conjunction, Node.eval] <;>
    repeat' (split <;> simp_all [Node.eval])

/-- Technology-independent rewrites preserve exact combinational semantics. -/
def optimize : Node d i r → Node d i r
  | .inv a => invert (optimize a)
  | .and a b => conjunction (optimize a) (optimize b)
  | a => a

theorem optimize_correct (a : Node d i r) (xs s) : (optimize a).eval xs s = a.eval xs s := by
  induction a with
  | lit b => rfl
  | input k => rfl
  | reg k => rfl
  | inv a ih => simp [optimize, invert_correct, Node.eval, ih]
  | and a b ha hb => simp [optimize, conjunction_correct, Node.eval, ha, hb]
end HDLean.Netlist
