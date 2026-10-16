import HDLean.Backend.SystemVerilogProved
import HDLean.Backend.RTLILProved
import HDLean.Netlist.Optimize

namespace HDLean.Backend.Proved

/-- The same semantic graph feeds all three external grammars. -/
inductive Format where
  | systemVerilog | aiger | rtlil
  deriving Repr, DecidableEq

def Format.print (f : Format) (g : Aag) : String := match f with
  | .systemVerilog => g.systemVerilog
  | .aiger => g.print
  | .rtlil => g.rtlil

def Format.decode (f : Format) : String → Option Aag := match f with
  | .systemVerilog => Aag.parseSystemVerilog
  | .aiger => Aag.parse
  | .rtlil => Aag.parseRTLIL

theorem Format.decode_print (f : Format) (g : Aag) : f.decode (f.print g) = some g := by
  cases f
  · exact Aag.parse_systemVerilog g
  · exact Aag.parse_print g
  · exact Aag.parse_rtlil g

/-- Every emitted module is well formed, independently of the syntax decoder. -/
theorem canonical_wellFormed (g : Graph) (hg : g.wellFormed = true) :
    (Aag.ofGraph g).graph.wellFormed = true := by
  cases g with | mk name i r gates next outputs ins states outs sources =>
    simp only [Aag.ofGraph, Aag.graph, Array.length_toList, Array.toArray_toList]
    unfold Graph.wellFormed at hg ⊢
    dsimp only at hg ⊢
    split at hg
    · contradiction
    · rename_i hdim
      have hd : (i == 0 || next.size != r) = false := by
        cases he : (i == 0 || next.size != r) <;> simp_all
      have hi : (i == 0) = false := (Bool.or_eq_false_iff.mp hd).1
      have hn : next.size = r := by simpa using (Bool.or_eq_false_iff.mp hd).2
      simp only [hn, hi, Array.size_replicate, bne_self_eq_false, Bool.or_self,
        Bool.false_eq_true, ↓reduceIte]
      split at hg
      · contradiction
      · exact hg

/-- Reject malformed bounds as well as malformed text. -/
def Format.parse (f : Format) (text : String) : Option Aag := do
  let g ← f.decode text
  if g.graph.wellFormed then some g else none

def Format.meaning (f : Format) (text : String) (inputs state : Array Bool) :
    Option (Array Bool × Array Bool) :=
  (f.parse text).map (fun g => g.graph.eval inputs state)

/-- Pure emission through the gate-count-preserving lowering and the proved AIG
optimisation; all semantic work is supplied by framework theorems. -/
def Format.emit (f : Format) (c : Dag d i r o) : String :=
  f.print (Aag.ofGraph (Dag.lowerOpt c))

/-- Generic source-to-text correctness. Instantiation never validates a concrete circuit. -/
theorem emit_correct (f : Format) (c : Dag d i r o)
    (xs : Vector Bool i) (s : Vector Bool r) (rst : Bool) :
    f.meaning (f.emit c) (xs.toArray.push rst) s.toArray = some
      ((Vector.ofFn (c.nextState (fun k => s[k]) ((fun k => xs[k]),rst))).toArray,
       (Vector.ofFn (c.evalOutput (fun k => s[k]) (fun k => xs[k]))).toArray) := by
  unfold Format.meaning Format.parse Format.emit
  rw [Format.decode_print]
  dsimp only [Bind.bind, Option.bind]
  rw [canonical_wellFormed (Dag.lowerOpt c) (Dag.lowerOpt_wellFormed c)]
  simp only [↓reduceIte, Option.map_some]
  have hn : (Dag.lowerOpt c).next.size = (Dag.lowerOpt c).latches := Dag.lowerOpt_next_size c
  rw [Graph.eval_eq_of_logic_eq _ _ (Aag.ofGraph_logic (Dag.lowerOpt c) hn), Dag.lowerOpt_correct]

end HDLean.Backend.Proved
