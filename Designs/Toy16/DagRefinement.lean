import Designs.Toy16.DagConstruction
import HDLean.Backend.DagEmit
import Lean
set_option maxHeartbeats 100000
namespace HDLean.Toy16.DagPhysical
open Dag.Build

set_option maxHeartbeats 100000 in
private theorem bank_resetKinds (words : Fin 268 → WordExpr 0 0 (268*16) 16)
    (outputs : Vector (Expr 0 0 (268*16)) 79) :
    resetKinds = (wordBank "toy16" Physical.resetKind words outputs).state.map (·.reset) := by
  apply Vector.ext
  intro k hk
  simp only [resetKinds,wordBank,Vector.getElem_map,Vector.getElem_flatten,Vector.getElem_ofFn,Physical.resetKind]

private theorem resetKinds_eq (imem : Addr → Word) :
    resetKinds = (Physical.hardware imem).state.map (·.reset) :=
  bank_resetKinds (Physical.nextWord imem) Physical.outputBits

private theorem hardware_name (imem : Addr → Word) : (Physical.hardware imem).name = "toy16" := rfl


theorem hardware?_implements (imem : Addr → Word) :
    ∃ dag, hardware? imem = some dag ∧
      (∀ s xs, dag.nextState s xs = (Physical.hardware imem).next s xs) ∧
      (∀ s xs, dag.evalOutput s xs = (Physical.hardware imem).evalOutput s xs) := by
  simpa only [hardware?,resetKinds_eq imem,hardware_name imem] using
    run_implements (Physical.hardware imem) (program imem) (program_ensures imem empty)

theorem hardware?_isSome (imem : Addr → Word) : (hardware? imem).isSome = true := by
  obtain ⟨dag,h,_⟩ := hardware?_implements imem
  exact Option.isSome_of_eq_some h

/-- Computable shared CPU, with total construction proved for every instruction ROM. -/
def hardware (imem : Addr → Word) : Dag 0 0 (268*16) 79 :=
  (hardware? imem).get (hardware?_isSome imem)


theorem hardware_semantics (imem : Addr → Word) :
    (∀ s xs, (hardware imem).nextState s xs = (Physical.hardware imem).next s xs) ∧
    (∀ s xs, (hardware imem).evalOutput s xs = (Physical.hardware imem).evalOutput s xs) := by
  obtain ⟨dag,h,hn,ho⟩ := hardware?_implements imem
  have heq : hardware imem = dag := Option.get_of_eq_some _ h
  simpa only [heq] using And.intro hn ho

theorem next_eq (imem : Addr → Word) (s xs) :
    (hardware imem).nextState s xs = (Physical.hardware imem).next s xs :=
  (hardware_semantics imem).1 s xs

theorem output_eq (imem : Addr → Word) (s xs) :
    (hardware imem).evalOutput s xs = (Physical.hardware imem).evalOutput s xs :=
  (hardware_semantics imem).2 s xs

attribute [local irreducible] hardware


theorem decode_next (imem : Addr → Word) (s rst) :
    Physical.decode ((hardware imem).nextState s (Fin.elim0,rst)) = (core imem).next (Physical.decode s) rst := by
  exact (congrArg Physical.decode (next_eq imem s (Fin.elim0,rst))).trans
    (Physical.decode_next imem s rst)


theorem decode_output (imem : Addr → Word) (s) :
    Physical.observe ((hardware imem).evalOutput s Fin.elim0) = (core imem).out (Physical.decode s) := by
  exact (congrArg Physical.observe (output_eq imem s Fin.elim0)).trans
    (Physical.decode_output imem s)

def machine (imem : Addr → Word) : PMachine (Fin (268*16) → Bool) Bool (Fin 79 → Bool) where
  out s := (hardware imem).evalOutput s Fin.elim0
  next s rst := (hardware imem).nextState s (Fin.elim0,rst)


theorem hardware_state (imem : Addr → Word) (s₀) (rst : Nat → Bool) (t : Nat) :
    Physical.decode ((machine imem).stateFrom s₀ rst t) = (core imem).stateFrom (Physical.decode s₀) rst t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [PMachine.stateFrom_succ]
    exact (decode_next imem ((machine imem).stateFrom s₀ rst t) (rst t)).trans
      (congrArg (fun q => (core imem).next q (rst t)) ih)


theorem hardware_trace (imem : Addr → Word) (s₀) (rst : Nat → Bool) (t : Nat) :
    Physical.observe ((machine imem).runFrom s₀ rst t) = (core imem).runFrom (Physical.decode s₀) rst t := by
  exact (decode_output imem ((machine imem).stateFrom s₀ rst t)).trans
    (congrArg (core imem).out (hardware_state imem s₀ rst t))


/-- Full-ISA retirement and bounded progress of the shared physical CPU. -/

theorem hardware_correct (imem : Addr → Word) (s₀) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem,
      let retire := fun t => Physical.observe ((machine imem).runFrom s₀ rst (t+1))
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt := by
  simpa only [hardware_trace] using core_correct imem (Physical.decode s₀) rst hr hd



theorem denote_stateFrom (imem : Addr → Word) (s₀) (rst : Nat → Bool) (t : Nat) :
    ((hardware imem).denote (Dag.isMoore_of_no_inputs _)).stateFrom s₀ (fun n => (Fin.elim0, rst n)) t =
      (machine imem).stateFrom s₀ rst t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [PMachine.stateFrom_succ, ih]
    rfl

theorem denote_runFrom (imem : Addr → Word) (s₀) (rst : Nat → Bool) (t : Nat) :
    ((hardware imem).denote (Dag.isMoore_of_no_inputs _)).runFrom s₀ (fun n => (Fin.elim0, rst n)) t =
      (machine imem).runFrom s₀ rst t := by
  simp only [PMachine.runFrom, denote_stateFrom]
  change (hardware imem).evalOutput _ (fun _ => false) = (hardware imem).evalOutput _ Fin.elim0
  congr 1
  funext k
  exact k.elim0

/-- The challenge statement, phrased with the framework's `Dag.denote`. -/
theorem hardware_correct_denote (imem : Addr → Word) (s₀) (rst : Nat → Bool)
    (hr : rst 0 = true) (hd : ∀ t, 0 < t → rst t = false) :
    ∃ regs mem,
      let retire := fun t => Physical.observe (((hardware imem).denote (Dag.isMoore_of_no_inputs _)).runFrom
        s₀ (fun n => (Fin.elim0, rst n)) (t+1))
      RetiresLike retire (isaRetire imem (ArchState.atReset regs mem)) ∧ Progress 2 retire Retire.halt := by
  simpa only [denote_runFrom] using hardware_correct imem s₀ rst hr hd

theorem emit_correct (f : Backend.Proved.Format) (imem : Addr → Word)
    (s : Vector Bool (268*16)) (rst : Bool) :
    f.meaning (f.emit (hardware imem)) #[rst] s.toArray = some
      ((Vector.ofFn ((Physical.hardware imem).next (fun k => s[k]) (Fin.elim0,rst))).toArray,
       (Vector.ofFn ((Physical.hardware imem).evalOutput (fun k => s[k]) Fin.elim0)).toArray) := by
  have h := Backend.Proved.emit_correct f (hardware imem) (#v[] : Vector Bool 0) s rst
  have he : (fun k : Fin 0 => (#v[] : Vector Bool 0)[k]) = Fin.elim0 := by funext k; nomatch k
  simpa only [next_eq,output_eq,he,Array.push_empty] using h

end HDLean.Toy16.DagPhysical
