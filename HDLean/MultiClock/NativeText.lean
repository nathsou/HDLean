import HDLean.MultiClock.Native
import HDLean.Backend.TextGrammar

set_option backward.isDefEq.respectTransparency false

namespace HDLean.MultiClock.Shared
open Backend.Proved Backend.Text Backend.Text.Grammar

/-- Native clock ports and synchronizer flops; no synthesized sampling-oracle pin. -/
inductive NativeFormat where
  | systemVerilog | rtlil
  deriving DecidableEq, Repr

macro "hw!" s:str : term => `((⟨$s,by decide,by decide⟩ : HDLean.Backend.Text.Word))
private def row (first : Word) (rest : List Word := []) : Line := ⟨first::rest,by simp⟩
private def id (stem : Word) (d : Nat) : Word := prefixed stem d
private def appendWord (a b : Word) : Word :=
  ⟨a.text ++ b.text,by simpa using And.intro a.noSpace b.noSpace,
    by simpa using And.intro a.noNewline b.noNewline⟩
private def syncId (stem : Word) (d k : Nat) : Word :=
  prefixed (appendWord (id stem d) (hw!"_")) k
private def svRef (name : Word) (k : Nat) : List Word := [name,hw!"[",numeral k,hw!"]"]
private def ilRef (name : Word) (k : Nat) : List Word := [name,hw!"[",numeral k,hw!"]"]

namespace MultiDag
variable (c : MultiDag nd)

private def svPortNames (d : Fin nd) : List Word :=
  [id (hw!"clk_") d.val,id (hw!"reset_") d.val,id (hw!"in_") d.val,id (hw!"out_") d.val]

private def svDomain (d : Fin nd) : List Line :=
  let clk := id (hw!"clk_") d.val
  let reset := id (hw!"reset_") d.val
  let ins := id (hw!"in_") d.val
  let outs := id (hw!"out_") d.val
  let localIn := id (hw!"local_in_") d.val
  let localOut := id (hw!"local_out_") d.val
  [row (hw!"input") [hw!"wire",clk,hw!";"],row (hw!"input") [hw!"wire",reset,hw!";"],
   row (hw!"input") [hw!"wire",hw!"[",numeral (c.inputs d),hw!":",hw!"0",hw!"]",ins,hw!";"],
   row (hw!"output") [hw!"wire",hw!"[",numeral (c.outputs d),hw!":",hw!"0",hw!"]",outs,hw!";"],
   row (hw!"wire") [hw!"[",numeral (c.localInputs d+1),hw!":",hw!"0",hw!"]",localIn,hw!";"],
   row (hw!"wire") [hw!"[",numeral (c.outputs d+c.regs d),hw!":",hw!"0",hw!"]",localOut,hw!";"],
   row (id (hw!"hd_m_") d.val) [id (hw!"local_") d.val,hw!"(",hw!".clk",hw!"(",clk,hw!")",hw!",",hw!".ins",hw!"(",localIn,hw!")",hw!",",hw!".outs",hw!"(",localOut,hw!")",hw!")",hw!";"],
   row (hw!"assign") (svRef localIn (c.localInputs d) ++ [hw!"=",reset,hw!";"]),
   row (hw!"assign") (svRef localIn (c.localInputs d+1) ++ [hw!"=",hw!"1'b0",hw!";"]),
   row (hw!"assign") (svRef outs (c.outputs d) ++ [hw!"=",hw!"1'b0",hw!";"])] ++
  (List.finRange (c.localInputs d)).map (fun j =>
    row (hw!"assign") (svRef localIn j.val ++ [hw!"="] ++
      (match c.port d j with
      | .input k => svRef ins k.val
      | .synchronized k bit => svRef (syncId (hw!"second_") d.val k.val) bit.val) ++ [hw!";"])) ++
  (List.finRange (c.outputs d)).map (fun j =>
    row (hw!"assign") (svRef outs j.val ++ [hw!"="] ++ svRef localOut j.val ++ [hw!";"])) ++
  (List.finRange (c.syncCount d)).flatMap (fun k =>
    let first := syncId (hw!"first_") d.val k.val
    let second := syncId (hw!"second_") d.val k.val
    let crossing := c.sync d k
    [row (hw!"reg") [hw!"[",numeral (crossing.width-1),hw!":",hw!"0",hw!"]",first,hw!";"],
     row (hw!"reg") [hw!"[",numeral (crossing.width-1),hw!":",hw!"0",hw!"]",second,hw!";"]] ++
    (List.finRange crossing.width).flatMap (fun bit =>
      let clockPrefix := [hw!"@",hw!"(",hw!"posedge",clk,hw!")"]
      let source := id (hw!"local_out_") crossing.source.val
      [row (hw!"always") (clockPrefix ++ svRef first bit.val ++ [hw!"<=",reset,hw!"?",hw!"1'b0",hw!":"] ++
        svRef source (c.outputs crossing.source+crossing.bits[bit].val) ++ [hw!";"]),
       row (hw!"always") (clockPrefix ++ svRef second bit.val ++ [hw!"<=",reset,hw!"?",hw!"1'b0",hw!":"] ++
        svRef first bit.val ++ [hw!";"])]))

private def svTop : List Line :=
  [row (hw!"module") ([hw!"hd_top",hw!"("] ++ ((List.finRange nd).flatMap (svPortNames)).intersperse (hw!",") ++ [hw!")",hw!";"])] ++
  (List.finRange nd).flatMap c.svDomain ++ [row (hw!"endmodule")]

private def ilDomain (d : Fin nd) : List Line :=
  let clk := id (hw!"\\clk_") d.val
  let reset := id (hw!"\\reset_") d.val
  let ins := id (hw!"\\in_") d.val
  let outs := id (hw!"\\out_") d.val
  let localIn := id (hw!"\\local_in_") d.val
  let localOut := id (hw!"\\local_out_") d.val
  [row (hw!"wire") [hw!"input",numeral (4*d.val+1),clk],
   row (hw!"wire") [hw!"input",numeral (4*d.val+2),reset],
   row (hw!"wire") [hw!"width",numeral (c.inputs d+1),hw!"input",numeral (4*d.val+3),ins],
   row (hw!"wire") [hw!"width",numeral (c.outputs d+1),hw!"output",numeral (4*d.val+4),outs],
   row (hw!"wire") [hw!"width",numeral (c.localInputs d+2),localIn],
   row (hw!"wire") [hw!"width",numeral (c.outputs d+c.regs d+1),localOut],
   row (hw!"cell") [id (hw!"\\hd_m_") d.val,id (hw!"\\local_") d.val],
   row (hw!"connect") [hw!"\\clk",clk],row (hw!"connect") [hw!"\\ins",localIn],
   row (hw!"connect") [hw!"\\outs",localOut],row (hw!"end"),
   row (hw!"connect") (ilRef localIn (c.localInputs d) ++ [reset]),
   row (hw!"connect") (ilRef localIn (c.localInputs d+1) ++ [hw!"1'0"]),
   row (hw!"connect") (ilRef outs (c.outputs d) ++ [hw!"1'0"])] ++
  (List.finRange (c.localInputs d)).map (fun j => row (hw!"connect")
    (ilRef localIn j.val ++ match c.port d j with
      | .input k => ilRef ins k.val
      | .synchronized k bit => ilRef (syncId (hw!"\\second_") d.val k.val) bit.val)) ++
  (List.finRange (c.outputs d)).map (fun j => row (hw!"connect") (ilRef outs j.val ++ ilRef localOut j.val)) ++
  (List.finRange (c.syncCount d)).flatMap (fun k =>
    let first := syncId (hw!"\\first_") d.val k.val
    let second := syncId (hw!"\\second_") d.val k.val
    let crossing := c.sync d k
    [row (hw!"wire") [hw!"width",numeral (max 1 crossing.width),first],
     row (hw!"wire") [hw!"width",numeral (max 1 crossing.width),second]] ++
    (List.finRange crossing.width).flatMap (fun bit =>
      let source := id (hw!"\\local_out_") crossing.source.val
      let cellStem := syncId (hw!"\\sync_") d.val k.val
      let cell (secondStage : Bool) (q data : List Word) :=
        [row (hw!"cell") [hw!"$sdff",syncId (appendWord cellStem (hw!"_")) bit.val (if secondStage then 1 else 0)],
         row (hw!"parameter") [hw!"\\WIDTH",hw!"1"],row (hw!"parameter") [hw!"\\CLK_POLARITY",hw!"1"],
         row (hw!"parameter") [hw!"\\SRST_POLARITY",hw!"1"],row (hw!"parameter") [hw!"\\SRST_VALUE",hw!"1'0"],
         row (hw!"connect") [hw!"\\CLK",clk],row (hw!"connect") [hw!"\\SRST",reset],
         row (hw!"connect") ([hw!"\\D"] ++ data),row (hw!"connect") ([hw!"\\Q"] ++ q),row (hw!"end")]
      cell false (ilRef first bit.val) (ilRef source (c.outputs crossing.source+crossing.bits[bit].val)) ++
      cell true (ilRef second bit.val) (ilRef first bit.val)))

private def ilTop : List Line :=
  let lines := (List.finRange nd).flatMap c.ilDomain
  [row (hw!"module") [hw!"\\hd_top"]] ++
    lines.filter (fun line => line.tokens.head? == some "wire") ++
    lines.filter (fun line => line.tokens.head? != some "wire") ++ [row (hw!"end")]

def topLines (f : NativeFormat) : List Line := match f with
  | .systemVerilog => c.svTop
  | .rtlil => c.ilTop

end MultiDag
end HDLean.MultiClock.Shared

namespace HDLean.MultiClock.Shared
open Backend.Proved Backend.Text Backend.Text.Grammar

def NativeFormat.moduleLines (f : NativeFormat) (index : Nat) (g : Aag) : List Line := match f with
  | .systemVerilog => g.systemVerilogModuleLines index
  | .rtlil => g.rtlilModuleLines index

def NativeFormat.readModule (f : NativeFormat) (index : Nat) : List (List String) → Option (Aag × List (List String)) := match f with
  | .systemVerilog => Aag.readSystemVerilogModule index
  | .rtlil => Aag.readRTLILModule index

theorem NativeFormat.read_module (f : NativeFormat) (index : Nat) (g : Aag) (tail : List (List String)) :
    f.readModule index ((f.moduleLines index g).map Line.tokens ++ tail) = some (g,tail) := by
  cases f
  · exact Aag.read_systemVerilogModule index g tail
  · exact Aag.read_rtlilModule index g tail

def NativeFormat.libraryLines (f : NativeFormat) (modules : List (Nat × Aag)) : List Line :=
  modules.flatMap (fun (index,g) => f.moduleLines index g)

def NativeFormat.readLibrary (f : NativeFormat) : List Nat → List (List String) → Option (List Aag × List (List String))
  | [],tokens => some ([],tokens)
  | index::rest,tokens => do
    let (g,tokens) ← f.readModule index tokens
    let (gs,tokens) ← f.readLibrary rest tokens
    return (g::gs,tokens)

theorem NativeFormat.read_library (f : NativeFormat) (modules : List (Nat × Aag)) (tail : List (List String)) :
    f.readLibrary (modules.map Prod.fst) ((f.libraryLines modules).map Line.tokens ++ tail) =
      some (modules.map Prod.snd,tail) := by
  induction modules generalizing tail with
  | nil => rfl
  | cons module modules ih =>
    rcases module with ⟨index,g⟩
    simp only [libraryLines,List.flatMap_cons,List.map_append,List.append_assoc,List.map_cons,readLibrary]
    rw [f.read_module]
    dsimp only [Bind.bind,Option.bind]
    simp only [libraryLines] at ih
    rw [ih]
    rfl

namespace MultiDag
variable (c : MultiDag nd)

def nativeModules : List (Nat × Aag) :=
  (List.finRange nd).map (fun d => (d.val,Aag.ofGraph (c.nativeLower.modules d)))

def nativeLines (f : NativeFormat) : List Line :=
  f.libraryLines c.nativeModules ++ c.topLines f

def emitNative (f : NativeFormat) : String := Backend.Text.render (c.nativeLines f)

/-- Check port dimensions, literal state taps, and graph bounds. This is a
structural interface check; no Boolean equivalence or per-design proof search. -/
def nativeModuleShape (d : Fin nd) (g : Aag) : Bool :=
  g.graph.wellFormed && g.inputs == c.localInputs d+1 && g.next.length == c.regs d &&
    g.outputs.length == c.outputs d+c.regs d &&
    g.outputs.drop (c.outputs d) ==
      ((Array.range (c.regs d)).map (fun k => 2*(c.localInputs d+2+k))).toList

private theorem nativeModuleShape_lower (d : Fin nd) :
    c.nativeModuleShape d (Aag.ofGraph (c.nativeLower.modules d)) = true := by
  have hw := canonical_wellFormed _ (c.nativeLower_wellFormed d)
  simp only [nativeModuleShape,hw,Bool.true_and]
  simp [Aag.ofGraph,nativeLower,Backend.Graph.withStatePorts,Dag.lower,Array.toList_append,
    Array.toList_map,List.drop_append,Array.toList_range,Nat.add_assoc]

private def nativeModulesValid (modules : List Aag) : Bool :=
  modules.length == nd && ((List.finRange nd).zip modules).all (fun (d,g) => c.nativeModuleShape d g)

private theorem nativeModulesValid_lower : c.nativeModulesValid (c.nativeModules.map Prod.snd) = true := by
  simp only [nativeModulesValid,nativeModules,List.map_map,List.length_map,List.length_finRange,
    beq_self_eq_true,Bool.true_and]
  change ((List.finRange nd).zip ((List.finRange nd).map
    (fun d => Aag.ofGraph (c.nativeLower.modules d)))).all
    (fun (d,g) => c.nativeModuleShape d g) = true
  have h (ds : List (Fin nd)) :
      (ds.zip (ds.map (fun d => Aag.ofGraph (c.nativeLower.modules d)))).all
        (fun (d,g) => c.nativeModuleShape d g) = true := by
    induction ds with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.map_cons,List.zip_cons_cons,List.all_cons,nativeModuleShape_lower,
        Bool.true_and,ih]
  exact h _

/-- Decode every module body, then check the complete typed clock/crossing wiring.
This is syntax recognition; there is no source/target semantic comparison. -/
def decodeNative (f : NativeFormat) (text : String) : Option (List Aag) := do
  let (gs,tail) ← f.readLibrary (c.nativeModules.map Prod.fst) (Backend.Text.tokenize text)
  if !c.nativeModulesValid gs then none else do
   let (_,tail) ← (fixed (view := Line.tokens) (c.topLines f)).decode tail
   if tail.isEmpty then some gs else none

theorem decode_emitNative (f : NativeFormat) :
    c.decodeNative f (c.emitNative f) = some (c.nativeModules.map Prod.snd) := by
  unfold decodeNative emitNative nativeLines
  rw [Backend.Text.tokenize_render,List.map_append,NativeFormat.read_library]
  dsimp only [Bind.bind,Option.bind]
  rw [nativeModulesValid_lower]
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
  have h := (fixed (view := Line.tokens) (c.topLines f)).roundtrip () []
  simp only [List.append_nil] at h
  change (fixed (view := Line.tokens) (c.topLines f)).decode ((c.topLines f).map Line.tokens) = some ((),[]) at h
  rw [h]
  rfl

end MultiDag
end HDLean.MultiClock.Shared

namespace HDLean.MultiClock.Shared.MultiDag
open Backend.Proved
variable (c : MultiDag nd)

private def emptyModule : Aag := ⟨0,[],[],[]⟩

/-- The recovered module table plus the decoded clock/crossing topology. -/
def decodedGraph (modules : List Aag) : c.Graph :=
  { c.nativeLower with modules := fun d => ((modules[d.val]?).getD emptyModule).graph }

def nativeMeaning (f : NativeFormat) (text : String) (s : c.State) (e : c.Event) :=
  (c.decodeNative f text).map (fun modules => (c.decodedGraph modules).eval s e)

private theorem nativeModules_get (d : Fin nd) :
    ((c.nativeModules.map Prod.snd)[d.val]?).getD emptyModule = Aag.ofGraph (c.nativeLower.modules d) := by
  simp only [nativeModules,List.map_map]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_finRange]
  rfl

/-- Source-to-native-text correctness, including every physical sampling oracle. -/
theorem emitNative_correct (f : NativeFormat) (s : c.State) (e : c.Event) :
    c.nativeMeaning f (c.emitNative f) s e = some (c.next s e,c.output s e) := by
  unfold nativeMeaning
  rw [decode_emitNative]
  simp only [Option.map_some]
  have he (d : Fin nd) (xs state : Array Bool) :
      ((c.decodedGraph (c.nativeModules.map Prod.snd)).modules d).eval xs state =
        (c.nativeLower.modules d).eval xs state := by
    simp only [decodedGraph,nativeModules_get]
    exact Backend.Graph.eval_eq_of_logic_eq _ _
      (Aag.ofGraph_logic _ (by simp [nativeLower,Backend.Graph.withStatePorts,Dag.lower])) xs state
  have hg : (c.decodedGraph (c.nativeModules.map Prod.snd)).eval s e = c.nativeLower.eval s e := by
    simp only [Graph.eval,he]
    rfl
  rw [hg,nativeLower_correct]

end HDLean.MultiClock.Shared.MultiDag
