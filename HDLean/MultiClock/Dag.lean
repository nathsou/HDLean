import HDLean.Netlist.DagLower
import HDLean.Semantics.Clock

namespace HDLean.MultiClock.Shared

/-- A crossing names registered source bits. Only this primitive can name another domain. -/
structure Crossing (nd : Nat) (regs : Fin nd → Nat) where
  source : Fin nd
  width : Nat
  bits : Vector (Fin (regs source)) width

/-- Local combinational logic sees external pins or the second flop of a declared crossing. -/
inductive Port (external syncCount : Nat) (width : Fin syncCount → Nat) where
  | input (index : Fin external)
  | synchronized (crossing : Fin syncCount) (bit : Fin (width crossing))

structure MultiDag (nd : Nat) where
  inputs : Fin nd → Nat
  regs : Fin nd → Nat
  outputs : Fin nd → Nat
  syncCount : Fin nd → Nat
  sync : (dest : Fin nd) → Fin (syncCount dest) → Crossing nd regs
  localInputs : Fin nd → Nat
  port : (d : Fin nd) → Fin (localInputs d) →
    Port (inputs d) (syncCount d) (fun k => (sync d k).width)
  logic : (d : Fin nd) → Dag d.val (localInputs d) (regs d) (outputs d)

namespace MultiDag
variable (c : MultiDag nd)

structure State where
  registers : (d : Fin nd) → Fin (c.regs d) → Bool
  first : (d : Fin nd) → (k : Fin (c.syncCount d)) → Fin (c.sync d k).width → Bool
  second : (d : Fin nd) → (k : Fin (c.syncCount d)) → Fin (c.sync d k).width → Bool

structure Event where
  input : (d : Fin nd) → Fin (c.inputs d) → Bool
  reset : Fin nd → Bool
  edge : Fin nd → Bool
  sampleNew : (d : Fin nd) → (k : Fin (c.syncCount d)) → Fin (c.sync d k).width → Bool

def localInput (s : c.State) (e : c.Event) (d : Fin nd) : Fin (c.localInputs d) → Bool := fun j =>
  match c.port d j with
  | .input k => e.input d k
  | .synchronized k bit => s.second d k bit

/-- Destination edges commit local logic; all local right-hand sides see pre-event state. -/
def nextLocal (s : c.State) (e : c.Event) (d : Fin nd) : Fin (c.regs d) → Bool :=
  fun k => if e.edge d then (c.logic d).nextState (s.registers d) (c.localInput s e d,e.reset d) k else s.registers d k

/-- Each physical first flop can independently sample either source endpoint.
The second flop always samples the OLD first flop, including coincident edges. -/
def next (s : c.State) (e : c.Event) : c.State where
  registers := c.nextLocal s e
  first d k bit :=
    if e.edge d then
      if e.reset d then false
      else
        let crossing := c.sync d k
        let src := crossing.bits[bit]
        if e.sampleNew d k bit then c.nextLocal s e crossing.source src else s.registers crossing.source src
    else s.first d k bit
  second d k bit := if e.edge d then if e.reset d then false else s.first d k bit else s.second d k bit

def output (s : c.State) (e : c.Event) (d : Fin nd) : Fin (c.outputs d) → Bool :=
  (c.logic d).evalOutput (s.registers d) (c.localInput s e d)

/-- The lowered physical representation retains explicit two-flop sampling primitives.
A sampling primitive is not replaced with deterministic combinational wiring. -/
structure Graph where
  modules : (d : Fin nd) → Backend.Graph
  source : (dest : Fin nd) → Fin (c.syncCount dest) → Fin nd
  bits : (dest : Fin nd) → (k : Fin (c.syncCount dest)) →
    Vector (Fin (c.regs (source dest k))) (c.sync dest k).width

def lower : c.Graph := ⟨fun d => (c.logic d).lower,fun d k => (c.sync d k).source,fun d k => (c.sync d k).bits⟩

namespace Graph
variable {c}

/-- Physical graph execution uses ordinary gates locally and oracle sampling at every crossing. -/
def eval (g : c.Graph) (s : c.State) (e : c.Event) : c.State × ((d : Fin nd) → Fin (c.outputs d) → Bool) :=
  let localResult := fun d => (g.modules d).eval
    ((Vector.ofFn (c.localInput s e d)).toArray.push (e.reset d)) (Vector.ofFn (s.registers d)).toArray
  let localNext := fun d k => if e.edge d then (localResult d).1[k.val]?.getD false else s.registers d k
  ({ registers := localNext
     first := fun d k bit =>
       if e.edge d then
         if e.reset d then false
         else
           let source := g.source d k
           let src := (g.bits d k)[bit]
           if e.sampleNew d k bit then localNext source src else s.registers source src
       else s.first d k bit
     second := fun d k bit => if e.edge d then if e.reset d then false else s.first d k bit else s.second d k bit },
   fun d k => (localResult d).2[k.val]?.getD false)

end Graph

/-- Every sampling oracle is preserved by lowering, for arbitrary power-up and edge sets. -/
theorem lower_correct (s : c.State) (e : c.Event) :
    c.lower.eval s e = (c.next s e,c.output s e) := by
  have hl (d : Fin nd) := Dag.lower_correct (c.logic d)
    (Vector.ofFn (c.localInput s e d)) (Vector.ofFn (s.registers d)) (e.reset d)
  have hfn (d : Fin nd) : (fun k => (Vector.ofFn (s.registers d))[k]) = s.registers d := by funext k; simp
  have hfi (d : Fin nd) : (fun k => (Vector.ofFn (c.localInput s e d))[k]) = c.localInput s e d := by funext k; simp
  simp only [hfn,hfi] at hl
  unfold lower Graph.eval
  simp only [hl, Vector.getElem?_toArray, Vector.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Option.getD_some]
  rfl

theorem second_samples_first (s : c.State) (e : c.Event) (d : Fin nd) (k : Fin (c.syncCount d))
    (he : e.edge d = true) (hr : e.reset d = false) :
    (c.next s e).second d k = s.first d k := by
  funext bit
  simp [next,he,hr]

/-- Temporal source obligation: only one source bit differs over a sampling interval. -/
def SourceSafe (trace : Nat → c.State) (edges : Nat → Fin nd → Bool) : Prop :=
  ∀ (d : Fin nd) (k : Fin (c.syncCount d)) (a b : Nat),
    a < b → edges a d = true → edges b d = true →
    (∀ t, a < t → t < b → edges t d = false) →
    let crossing := c.sync d k
    ∃ changed : Option (Fin crossing.width), ∀ bit : Fin crossing.width,
      some bit ≠ changed →
      (trace a).registers crossing.source crossing.bits[bit] =
        (trace b).registers crossing.source crossing.bits[bit]

/-- A one-bit crossing satisfies the temporal obligation for every source trace and edge schedule. -/
theorem sourceSafe_single_bit (hwidth : ∀ d k, (c.sync d k).width = 1)
    (trace : Nat → c.State) (edges : Nat → Fin nd → Bool) : c.SourceSafe trace edges := by
  intro d k a b hab hea heb hbetween
  refine ⟨some ⟨0,by rw [hwidth]; decide⟩,?_⟩
  intro bit hne
  have hb : bit.val = 0 := by have := bit.isLt; have := hwidth d k; omega
  exact False.elim (hne (congrArg some (Fin.ext hb)))

/-- The graph's first flop retains the full sampling choice, rather than fixing it to old. -/
theorem first_samples (s : c.State) (e : c.Event) (d : Fin nd) (k : Fin (c.syncCount d))
    (bit : Fin (c.sync d k).width) (he : e.edge d = true) (hr : e.reset d = false) :
    (c.lower.eval s e).1.first d k bit =
      if e.sampleNew d k bit then c.nextLocal s e (c.sync d k).source (c.sync d k).bits[bit]
      else s.registers (c.sync d k).source (c.sync d k).bits[bit] := by
  rw [lower_correct]
  simp [next,he,hr]

end MultiDag
end HDLean.MultiClock.Shared
