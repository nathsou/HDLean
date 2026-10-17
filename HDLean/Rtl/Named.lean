import HDLean.Rtl.Record

/-!
# Composite records and named state

`hdl_record` declares a flat record of words. Larger state is composed from
records:

* `Both R S` holds an `R` and an `S` (fields of `R` first);
* `Lanes pre n T` holds `n` copies of the record `T`, named `pre0_f`, `pre1_f`, …
  (`Lanes.get`, `Lanes.ofFn`, `Lanes.mapM`).

Both are `Bundle`s, so `Ctx.mealy` and `mealy` take them like any record: a
program reads the whole state as handles (`R Sig`) and returns the next state,
usually as `{ r with field := … }` so that every register it does not mention
keeps its value. Widths are part of the record's type, so a register can only be
given a value of its own width.

Memories are found by name with `readMem` and `writePorts`; a missing or
mistyped memory is reported with its name.

`here%` is the source position where it is written (`file:line:column`), for
`scope here% do …`: a rejected cell then names the enclosing positions.
-/
namespace HDLean.Rtl

namespace HVec

def append : HVec F ws → HVec F vs → HVec F (ws ++ vs)
  | nil, ys => ys
  | cons x xs, ys => cons x (append xs ys)

def split : (ws : List Nat) → HVec F (ws ++ vs) → HVec F ws × HVec F vs
  | [], v => (nil, v)
  | _ :: ws, cons x xs => let p := split ws xs; (cons x p.1, p.2)

theorem split_append : ∀ {ws : List Nat} (a : HVec F ws) (b : HVec F vs), split ws (append a b) = (a, b)
  | [], nil, _ => rfl
  | _ :: _, cons x xs, b => by simp [append, split, split_append xs b]

theorem append_split : ∀ (ws : List Nat) (v : HVec F (ws ++ vs)), append (split ws v).1 (split ws v).2 = v
  | [], _ => rfl
  | _ :: ws, cons x xs => by simp [append, split, append_split ws xs]

def cast (h : ws = vs) (v : HVec F ws) : HVec F vs := h ▸ v

@[simp] theorem cast_cast (h : ws = vs) (h' : vs = ws) (v : HVec F ws) : cast h' (cast h v) = v := by
  subst h; rfl

def replicate (x : ∀ {w}, F w) : (ws : List Nat) → HVec F ws
  | [] => nil
  | _ :: ws => cons x (replicate x ws)

end HVec

namespace Bundle

/-- A record with nothing but placeholders, e.g. handles to cell 0. -/
def fill (R : (Nat → Type) → Type) [Bundle R] (x : ∀ {w}, F w) : R F := ofVec (HVec.replicate x _)

end Bundle

/-! ## Two records side by side -/

structure Both (R S : (Nat → Type) → Type) (F : Nat → Type) where
  fst : R F
  snd : S F

theorem map_snd_append (a b : List (String × Nat)) :
    (a ++ b).map Prod.snd = a.map Prod.snd ++ b.map Prod.snd := List.map_append

instance [Bundle R] [Bundle S] : Bundle (Both R S) where
  fields := Bundle.fields R ++ Bundle.fields S
  toVec r := HVec.cast (map_snd_append _ _).symm (HVec.append (Bundle.toVec r.fst) (Bundle.toVec r.snd))
  ofVec v :=
    let p := HVec.split (Bundle.widths R) (HVec.cast (map_snd_append _ _) v)
    ⟨Bundle.ofVec p.1, Bundle.ofVec p.2⟩
  ofVec_toVec r := by simp [HVec.split_append, Bundle.ofVec_toVec]
  toVec_ofVec v := by
    simp only [Bundle.toVec_ofVec, HVec.append_split]
    exact HVec.cast_cast _ _ v

/-! ## Lanes: `n` copies of a record -/

inductive LaneVec (T : (Nat → Type) → Type) (F : Nat → Type) : Nat → Type where
  | nil : LaneVec T F 0
  | cons {n : Nat} : T F → LaneVec T F n → LaneVec T F (n + 1)

/-- `n` copies of the record `T`; the fields of copy `i` are named `pre{i}_{field}`. -/
structure Lanes (pre : String) (n : Nat) (T : (Nat → Type) → Type) (F : Nat → Type) where
  vec : LaneVec T F n

namespace Lanes

variable {T : (Nat → Type) → Type} {F : Nat → Type}

def toList : LaneVec T F n → List (T F)
  | .nil => []
  | .cons x xs => x :: toList xs

def ofFnAux (f : Nat → T F) (k : Nat) : (n : Nat) → LaneVec T F n
  | 0 => .nil
  | n + 1 => .cons (f k) (ofFnAux f (k + 1) n)

/-- The lanes `f 0, …, f (n − 1)`. -/
def ofFn (f : Nat → T F) : Lanes pre n T F := ⟨ofFnAux f 0 n⟩

/-- Every lane, in order. -/
def lanes (v : Lanes pre n T F) : List (T F) := toList v.vec

/-- Lane `i` (the last lane beyond the end; `d` if there are none). -/
def getD (v : Lanes pre n T F) (i : Nat) (d : T F) : T F :=
  v.lanes[i]?.getD (v.lanes.getLastD d)

def mapMAux {m : Type → Type} [Monad m] (f : Nat → T F → m (T G)) (k : Nat) :
    LaneVec T F n → m (LaneVec T G n)
  | .nil => pure .nil
  | .cons x xs => do
    let y ← f k x
    let ys ← mapMAux f (k + 1) xs
    pure (.cons y ys)

/-- Apply `f i` to lane `i`, for every lane, in order. -/
def mapM {m : Type → Type} [Monad m] (f : Nat → T F → m (T G)) (v : Lanes pre n T F) : m (Lanes pre n T G) := do
  pure ⟨← mapMAux f 0 v.vec⟩

/-- The same record in every lane. -/
def replicate (x : T F) : Lanes pre n T F := ofFn fun _ => x

end Lanes

section LaneBundle
variable (T : (Nat → Type) → Type) [Bundle T]

def laneFields (pre : String) : Nat → Nat → List (String × Nat)
  | 0, _ => []
  | n + 1, k => (Bundle.fields T).map (fun p => (s!"{pre}{k}_{p.1}", p.2)) ++ laneFields pre n (k + 1)

def laneWidths : Nat → List Nat
  | 0 => []
  | n + 1 => Bundle.widths T ++ laneWidths n

theorem laneFields_widths (pre : String) : ∀ (n k : Nat), (laneFields T pre n k).map Prod.snd = laneWidths T n
  | 0, _ => rfl
  | n + 1, k => by
    simp only [laneFields, laneWidths, List.map_append, List.map_map, laneFields_widths pre n (k + 1)]
    rfl

variable {T}

def laneToVec : LaneVec T F n → HVec F (laneWidths T n)
  | .nil => .nil
  | .cons x xs => HVec.append (Bundle.toVec x) (laneToVec xs)

def laneOfVec : (n : Nat) → HVec F (laneWidths T n) → LaneVec T F n
  | 0, _ => .nil
  | n + 1, v =>
    let p := HVec.split (Bundle.widths T) v
    .cons (Bundle.ofVec p.1) (laneOfVec n p.2)

theorem laneOfVec_toVec : ∀ {n : Nat} (v : LaneVec T F n), laneOfVec n (laneToVec v) = v
  | 0, .nil => rfl
  | _ + 1, .cons x xs => by simp [laneToVec, laneOfVec, HVec.split_append, Bundle.ofVec_toVec, laneOfVec_toVec xs]

theorem laneToVec_ofVec : ∀ (n : Nat) (v : HVec F (laneWidths T n)), laneToVec (laneOfVec n v) = v
  | 0, .nil => rfl
  | n + 1, v => by
    simp only [laneOfVec, laneToVec, Bundle.toVec_ofVec, laneToVec_ofVec n]
    exact HVec.append_split _ v

instance : Bundle (Lanes pre n T) where
  fields := laneFields T pre n 0
  toVec r := HVec.cast (laneFields_widths T pre n 0).symm (laneToVec r.vec)
  ofVec v := ⟨laneOfVec n (HVec.cast (laneFields_widths T pre n 0) v)⟩
  ofVec_toVec r := by simp [laneOfVec_toVec]
  toVec_ofVec v := by
    simp only [laneToVec_ofVec]
    exact HVec.cast_cast _ _ v

end LaneBundle

namespace Build

open Lean Elab Term in
/-- The source position of this term, `file:line:column`, relative to the working directory. -/
elab "here%" : term => do
  let pos := (← getRef).getPos?.getD 0
  let p := (← getFileMap).toPosition pos
  let file ← getFileName
  let cwd ← IO.currentDir
  let rel := (file.dropPrefix? (cwd.toString ++ "/")).map (·.toString) |>.getD file
  return mkStrLit s!"{rel}:{p.line}:{p.column + 1}"

instance : Inhabited (Sig w) := ⟨⟨0⟩⟩

instance [Bundle R] : Inhabited (R Sig) := ⟨Bundle.fill R default⟩

/-- The index of the memory named `name`. -/
def Ctx.memIndex (c : Ctx) (name : String) : Option Nat :=
  c.mems.findIdx? (·.name == Ident.ofString name)

/-- Combinational read of the memory named `name` (a block-RAM read when the
result goes straight into a register). -/
def readMem (name : String) (w : Nat) (addr : Sig aw) : M c (Sig w) :=
  match c.memIndex name with
  | some k => scope s!"memory {name}" (memRead k w addr)
  | none => fail s!"no memory named {name}"

/-- The write ports of every memory, given by name; a memory that is not listed
gets none. -/
def writePorts (ports : List (String × Array WritePort)) : M c (Array (Array WritePort)) := do
  for (n, _) in ports do
    if (c.memIndex n).isNone then fail s!"write ports for {n}, which is not a declared memory"
  pure (c.mems.map fun m => ((ports.find? fun p => Ident.ofString p.1 == m.name).map Prod.snd).getD #[])

end Build

end HDLean.Rtl
