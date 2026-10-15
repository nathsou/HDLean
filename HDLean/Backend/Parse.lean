import Lean
import HDLean.Backend.LocalValidate
import HDLean.Backend.SystemVerilog
import HDLean.Backend.Aiger
import HDLean.Backend.RTLIL

namespace HDLean.Backend

private theorem encodeAscii (b : UInt8) (h : b.toNat < 128) :
    String.utf8EncodeChar (Char.ofNat b.toNat) = [b] := by
  have hc : b.toNat.isValidChar := by
    simp only [Nat.isValidChar]
    omega
  simp only [Char.ofNat, dite_eq_left hc, Char.ofNatAux,
    String.utf8EncodeChar]
  simp [show b.toNat ≤ 127 by omega]

theorem validAscii (bs : List UInt8) (h : bs.all (fun b => decide (b.toNat < 128)) = true) :
    bs.toByteArray.IsValidUTF8 := by
  refine .intro (bs.map (fun b => Char.ofNat b.toNat)) ?_
  unfold List.utf8Encode
  congr 1
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, List.flatMap_cons, encodeAscii b h.1, List.singleton_append]
    rw [← ih h.2]

def asciiText (bs : List UInt8) (h : bs.all (fun b => decide (b.toNat < 128)) = true) : String :=
  String.ofByteArray ⟨⟨bs⟩⟩ (by
    have he : bs.toByteArray = (⟨⟨bs⟩⟩ : ByteArray) := by
      apply ByteArray.ext
      exact List.data_toByteArray
    rw [← he]
    exact validAscii bs h)

/-- Parser tokens are raw UTF-8 bytes. Source text is decoded into bytes once;
no String/list/UTF-8 round trips are needed during kernel replay. -/
private abbrev Token := List Nat
private def Token.ofNat (n : Nat) : Token := digits (n+1) n []
where
  digits : Nat → Nat → Token → Token
    | 0, _, acc => acc
    | fuel+1, n, acc =>
      let acc := (n % 10 + 48) :: acc
      if n < 10 then acc else digits fuel (n / 10) acc

macro "bytes%" s:str : term => do
  let xs : Array Lean.Term := s.getString.toUTF8.data.map fun b => ⟨Lean.Syntax.mkNumLit (toString b.toNat)⟩
  `(([$xs,*] : List Nat))

syntax:max "t!" interpolatedStr(term) : term
macro_rules
  | `(t! $s) => do
    let out ← Lean.TSyntax.expandInterpolatedStrChunks s.raw.getArgs
      (fun a b => do
        let a : Lean.Term := ⟨a⟩
        let b : Lean.Term := ⟨b⟩
        `($a ++ $b))
      (fun a => do
        let a : Lean.Term := ⟨a⟩
        `(Token.ofNat $a))
      (fun s => `(bytes% $(Lean.Syntax.mkStrLit s)))
    pure out

private def token (s : String) : Token := s.toByteArray.data.toList.map UInt8.toNat
private instance : Coe String Token := ⟨token⟩
private instance : ToString Token := ⟨fun s => String.ofList (s.map Char.ofNat)⟩
private def Token.hdDrop (s : Token) (n : Nat) : Token := s.drop n
private def Token.hdDropEnd (s : Token) (n : Nat) : Token := s.take (s.length - n)
private def Token.hdStartsWith (s : Token) (pre : Token) : Bool := pre.isPrefixOf s
private def Token.hdEndsWith (s : Token) (suf : Token) : Bool := suf.reverse.isPrefixOf s.reverse
private def Token.hdStripSuffix (s : Token) (suf : Token) : Token :=
  if s.hdEndsWith suf then s.hdDropEnd suf.length else s
private def Token.hdTrim (s : Token) : Token :=
  let white := fun c => c == 32 || c == 9 || c == 13
  ((s.dropWhile white).reverse.dropWhile white).reverse
private def Token.hdSplit (s : Token) (delimiter : Nat) : List Token := go s []
where
  go : Token → Token → List Token
    | [], current => [current.reverse]
    | c :: rest, current =>
      if c == delimiter then current.reverse :: go rest []
      else go rest (c :: current)
private def Token.hdNat? (s : Token) : Option Nat := do
  if s.isEmpty then none
  else s.foldlM (fun n c =>
    if 48 ≤ c && c ≤ 57 then some (10 * n + c - 48) else none) 0
deriving instance ReflBEq, LawfulBEq for Gate

/-- The semantic part of a module; names and source annotations are metadata. -/
structure Logic where
  inputs : Nat
  latches : Nat
  gates : Array Gate
  next : Array Lit
  outputs : Array Lit
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def Graph.logic (g : Graph) : Logic := ⟨g.inputs, g.latches, g.gates, g.next, g.outputs⟩

theorem Graph.eval_eq_of_logic_eq (a b : Graph) (h : a.logic = b.logic) (inputs state) :
    a.eval inputs state = b.eval inputs state := by
  cases a
  cases b
  simp only [Graph.logic, Logic.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

private abbrev Parser := StateT (List Token) (Except String)

private def reject {α} (message : String) : Parser α := throw message

private def line : Parser Token := do
  match ← get with
  | [] => reject "unexpected end of module"
  | s :: rest => set rest; return s

private def expect (expected : Token) : Parser Unit := do
  let actual ← line
  unless actual == expected do reject s!"expected '{expected}', got '{actual}'"

private def peek : Parser Token := return (← get).headD []

private def natural (text : Token) : Parser Nat := do
  let some n := text.hdNat? | reject s!"invalid natural: {text}"
  return n

private def indexed (text : Token) (pre : Token) (suffix : Token := []) : Parser Nat := do
  unless text.hdStartsWith pre && text.hdEndsWith suffix do
    reject s!"expected {pre}<number>{suffix}, got {text}"
  let digits := (text.hdDrop pre.length).hdDropEnd suffix.length
  let n ← natural digits
  unless digits == [48] || digits.head? != some 48 do reject "noncanonical numeric identifier"
  return n

private def words (text : Token) : List Token := (text.hdSplit 32).filter (· != [])

private def lines (text : String) : List Token :=
  ((token text).hdSplit 10).map (·.hdTrim) |>.filter (· != [])

private def finish : Parser Unit := do
  unless (← get).isEmpty do reject "unexpected trailing module content"

private def makeGraph (name : String) (inputs latches : Nat) (gates : Array Gate)
    (next outputs : Array Lit) : Parser Graph := do
  let g : Graph := ⟨name, inputs, latches, gates, next, outputs,
    (Array.range inputs).map (fun k => s!"in_{k}"),
    (Array.range latches).map (fun k => s!"state_{k}"),
    (Array.range outputs.size).map (fun k => s!"out_{k}"), Array.replicate latches ""⟩
  unless g.wellFormed do reject "malformed, cyclic, or out-of-bounds module"
  return g

/-- ASCII AIGER subset: sequential canonical numbering, explicit arbitrary latch
initialization, and no constraints, fairness clauses or hidden initialization. -/
private def parseAigerBody : Parser Graph := do
  let [tag, m, i, l, o, a] := words (← line) | reject "expected an aag header"
  unless tag == (bytes% "aag") do reject "expected an aag header"
  let m ← natural m; let i ← natural i; let l ← natural l
  let o ← natural o; let a ← natural a
  unless m == i + l + a do reject "inconsistent AIGER maximum variable"
  for k in [:i] do
    let v ← natural (← line)
    unless v == 2 * (k + 1) do reject "noncanonical AIGER input"
  let mut ns := #[]
  for k in [:l] do
    let [q, d, init] := words (← line) | reject "latches require explicit arbitrary initialization"
    let q ← natural q; let d ← natural d; let init ← natural init
    unless q == 2 * (i + k + 1) && init == q do reject "initialized or noncanonical AIGER latch"
    ns := ns.push d
  let mut os := #[]
  for _ in [:o] do os := os.push (← natural (← line))
  let mut gs := #[]
  for k in [:a] do
    let [lhs, x, y] := words (← line) | reject "invalid AIGER AND"
    let lhs ← natural lhs; let x ← natural x; let y ← natural y
    unless lhs == 2 * (i + l + k + 1) do reject "noncanonical AIGER AND index"
    gs := gs.push ⟨lhs / 2, x, y⟩
  if (← peek) == (bytes% "c") then
    let _ ← line
    set ([] : List Token) -- AIGER comments have no semantics.
  finish
  makeGraph "aiger" i l gs ns os

private def svLiteral (text : Token) : Parser Lit := do
  if text == (bytes% "1'b0") then return 0
  if text == (bytes% "1'b1") then return 1
  let negative := text.hdStartsWith (bytes% "~")
  let k ← indexed (if negative then (text.hdDrop 1) else text) (bytes% "n")
  unless k > 0 do reject "constant variable n0 is undeclared"
  return 2 * k + if negative then 1 else 0

private def terminated (text : Token) : Parser Token := do
  unless text.hdEndsWith (bytes% ";") do reject "missing SV semicolon"
  return (text.hdDropEnd 1)

private def validName (name : Token) : Bool :=
  name.hdStartsWith (bytes% "hd_") && name.all (fun c =>
    (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || (48 ≤ c && c ≤ 57) || c == 95)

/-- Exact two-state SV grammar: one positive edge clock, combinational AND/inverter
assignments, one nonblocking update per register, no initial blocks or other events. -/
private def parseSVBody : Parser Graph := do
  let header ← line
  unless header.hdStartsWith (bytes% "module ") && header.hdEndsWith (bytes% "(") do reject "expected SV module header"
  let name := ((header.hdDrop 7).hdDropEnd 1)
  unless validName name do reject "invalid SV module identifier"
  let clock ← line
  unless clock == (bytes% "input wire clk,") do reject "expected unique implicit clock"
  let mut i := 0
  let mut o := 0
  for _ in (← (get : Parser (List Token))) do
    if (← peek) != (bytes% ");") then
      let raw ← line
      unless raw.hdEndsWith (bytes% ",") == ((← peek) != (bytes% ");")) do reject "invalid SV port separator"
      let port := (raw.hdStripSuffix (bytes% ","))
      let [direction, kind, p] := words port | reject "unsupported SV port"
      unless kind == (bytes% "wire") do reject "unsupported SV port type"
      if direction == (bytes% "input") then
        let k ← indexed p (bytes% "in_")
        unless k == i && o == 0 do reject "invalid or reordered SV input"
        i := i + 1
      else if direction == (bytes% "output") then
        let k ← indexed p (bytes% "out_")
        unless k == o do reject "invalid or reordered SV output"
        o := o + 1
      else reject "unsupported SV port"
    else break
  expect (bytes% ");")
  for k in [:i] do expect t!"wire n{k + 1} = in_{k};"
  let mut r := 0
  for _ in (← (get : Parser (List Token))) do
    if (← peek).hdStartsWith (bytes% "logic ") then
      expect t!"logic n{i + r + 1};"
      r := r + 1
    else break
  let mut gs := #[]
  for _ in (← (get : Parser (List Token))) do
    if (← peek).hdStartsWith (bytes% "wire ") then
      let [tag, lhs, assign, a, op, b] := words (← line) | reject "unsupported SV expression"
      unless tag == (bytes% "wire") && assign == (bytes% "=") && op == (bytes% "&") do reject "unsupported SV expression"
      let lhs ← indexed lhs (bytes% "n")
      let a ← svLiteral a; let b ← svLiteral (← terminated b)
      unless lhs == i + r + gs.size + 1 do reject "invalid SV gate order"
      gs := gs.push ⟨lhs, a, b⟩
    else break
  let mut os := #[]
  for k in [:o] do
    let [tag, p, op, value] := words (← line) | reject "missing SV output assignment"
    unless tag == (bytes% "assign") && op == (bytes% "=") do reject "missing SV output assignment"
    unless p == t!"out_{k}" do reject "duplicate or reordered SV output driver"
    os := os.push (← svLiteral (← terminated value))
  let mut ns := #[]
  if r > 0 then
    expect (bytes% "always_ff @(posedge clk) begin")
    for k in [:r] do
      let [q, op, d] := words (← line) | reject "expected nonblocking register update"
      unless op == (bytes% "<=") do reject "expected nonblocking register update"
      unless q == t!"n{i + k + 1}" do reject "duplicate or reordered SV state driver"
      ns := ns.push (← svLiteral (← terminated d))
    expect (bytes% "end")
  expect (bytes% "endmodule")
  finish
  makeGraph (toString name) i r gs ns os

private def rtlLiteral (text : Token) : Parser Lit := do
  if text == (bytes% "1'0") then return 0
  if text == (bytes% "1'1") then return 1
  let negative := text.hdStartsWith (bytes% "\\not_")
  let k ← indexed text (if negative then (bytes% "\\not_") else (bytes% "\\n"))
  unless k > 0 do reject "constant variable n0 is undeclared"
  return 2 * k + if negative then 1 else 0

/-- RTLIL grammar restricted to explicit one-bit $and/$not/$dff cells. Cell
parameters, clocks, edge polarity, all drivers, and inverted wires are checked. -/
private def parseRTLILBody : Parser Graph := do
  expect (bytes% "autoidx 1")
  let header ← line
  unless header.hdStartsWith (bytes% "module \\") do reject "expected RTLIL module"
  let name := (header.hdDrop 8)
  unless validName name do reject "invalid RTLIL module identifier"
  expect (bytes% "wire input 1 \\clk")
  let mut i := 0
  for _ in (← (get : Parser (List Token))) do
    if (← peek).hdStartsWith (bytes% "wire input ") then
      expect t!"wire input {i + 2} \\in_{i}"
      i := i + 1
    else break
  let mut o := 0
  for _ in (← (get : Parser (List Token))) do
    if (← peek).hdStartsWith (bytes% "wire output ") then
      expect t!"wire output {i + o + 2} \\out_{o}"
      o := o + 1
    else break
  let mut vars := 0
  for _ in (← (get : Parser (List Token))) do
    if (← peek).hdStartsWith (bytes% "wire \\n") then
      let k := vars + 1
      expect t!"wire \\n{k}"
      expect t!"wire \\not_{k}"
      expect t!"cell $not \\inv_{k}"
      expect (bytes% "parameter \\A_SIGNED 0")
      expect (bytes% "parameter \\A_WIDTH 1")
      expect (bytes% "parameter \\Y_WIDTH 1")
      expect t!"connect \\A \\n{k}"
      expect t!"connect \\Y \\not_{k}"
      expect (bytes% "end")
      vars := k
    else break
  for k in [:i] do expect t!"connect \\n{k + 1} \\in_{k}"
  let mut gs := #[]
  for _ in (← (get : Parser (List Token))) do
    if (← peek).hdStartsWith (bytes% "cell $and ") then
      let header ← line
      let lhs ← indexed header (bytes% "cell $and \\and_")
      expect (bytes% "parameter \\A_SIGNED 0"); expect (bytes% "parameter \\B_SIGNED 0")
      expect (bytes% "parameter \\A_WIDTH 1"); expect (bytes% "parameter \\B_WIDTH 1")
      expect (bytes% "parameter \\Y_WIDTH 1")
      let a ← indexedConnection (bytes% "A")
      let b ← indexedConnection (bytes% "B")
      expect t!"connect \\Y \\n{lhs}"
      expect (bytes% "end")
      gs := gs.push ⟨lhs, a, b⟩
    else break
  let mut ns := #[]
  for _ in (← (get : Parser (List Token))) do
    if (← peek).hdStartsWith (bytes% "cell $dff ") then
      let k := ns.size
      expect t!"cell $dff \\reg_{k}"
      expect (bytes% "parameter \\WIDTH 1")
      expect (bytes% "parameter \\CLK_POLARITY 1")
      expect (bytes% "connect \\CLK \\clk")
      let d ← indexedConnection (bytes% "D")
      expect t!"connect \\Q \\n{i + k + 1}"
      expect (bytes% "end")
      ns := ns.push d
    else break
  unless vars == i + ns.size + gs.size do reject "missing or extraneous RTLIL variable"
  let mut os := #[]
  for k in [:o] do os := os.push (← indexedConnection t!"out_{k}")
  expect (bytes% "end")
  finish
  makeGraph (toString name) i ns.size gs ns os
where
  indexedConnection (port : Token) : Parser Lit := do
    let [tag, p, value] := words (← line) | reject "expected RTLIL connection"
    unless tag == (bytes% "connect") do reject "expected RTLIL connection"
    unless p == (bytes% "\\") ++ port do reject s!"expected RTLIL port {port}"
    rtlLiteral value

inductive Format where
  | systemVerilog | aiger | rtlil
  deriving DecidableEq, Repr

/-- Tokenize the exact final bytes once. Exposed for compositional certificates. -/
def Format.tokenize (text : String) : List (List Nat) := lines text

private theorem Token.split_append_delimiter (a b current : Token) (delimiter : Nat)
    (h : ∀ c ∈ a, c ≠ delimiter) :
    Token.hdSplit.go delimiter (a ++ delimiter :: b) current =
      (current.reverse ++ a) :: Token.hdSplit.go delimiter b [] := by
  induction a generalizing current with
  | nil => simp [Token.hdSplit.go]
  | cons c cs ih =>
    have hc : c ≠ delimiter := h c (by simp)
    have hs : ∀ d ∈ cs, d ≠ delimiter := fun d hd => h d (by simp [hd])
    simp only [List.cons_append, Token.hdSplit.go, beq_iff_eq, hc, ↓reduceIte]
    rw [ih _ hs]
    simp [List.reverse_cons, List.append_assoc]

private theorem Token.split_lines (ls : List Token) (delimiter : Nat)
    (h : ∀ l ∈ ls, ∀ c ∈ l, c ≠ delimiter) :
    Token.hdSplit (ls.flatMap (fun l => l ++ [delimiter])) delimiter = ls ++ [[]] := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    unfold Token.hdSplit
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append]
    rw [Token.split_append_delimiter l _ [] delimiter (h l (by simp))]
    change l :: Token.hdSplit (ls.flatMap (fun l => l ++ [delimiter])) delimiter = _
    rw [ih (fun t ht => h t (by simp [ht]))]
    rfl

/-- Exact raw lines can be normalized separately in a compositional byte certificate. -/
def Format.normalizeByteLines (ls : List (List UInt8)) : List (List Nat) :=
  (ls.map (fun l => Token.hdTrim (l.map UInt8.toNat))).filter (· != [])

/-- Avoid quadratic kernel expansion of a long String while still proving the exact bytes.
Every input line is preserved, including its spaces; newlines are inserted explicitly. -/
theorem Format.tokenize_ascii_lines (ls : List (List UInt8))
    (ha : (ls.flatMap (fun l => l ++ [10])).all (fun b => decide (b.toNat < 128)) = true)
    (hn : ls.all (fun l => l.all (fun b => b.toNat != 10)) = true) :
    Format.tokenize (asciiText (ls.flatMap (fun l => l ++ [10])) ha) =
      Format.normalizeByteLines ls := by
  have hnl : ∀ l ∈ ls, ∀ b ∈ l, b.toNat ≠ 10 := by
    intro l hl b hb
    have h1 := List.all_eq_true.mp hn l hl
    have h2 := List.all_eq_true.mp h1 b hb
    simpa using h2
  have hmap : ∀ l ∈ ls.map (List.map UInt8.toNat), ∀ c ∈ l, c ≠ 10 := by
    intro l hl c hc
    obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact hnl raw hr b hb
  unfold Format.tokenize lines token asciiText
  simp only [List.map_flatMap, List.map_append, List.map_cons, List.map_nil, UInt8.toNat_ofNat]
  rw [show ls.flatMap (fun l => List.map UInt8.toNat l ++ [10]) =
    (ls.map (List.map UInt8.toNat)).flatMap (fun l => l ++ [10]) by rw [List.flatMap_map]]
  rw [Token.split_lines _ 10 hmap]
  simp [Format.normalizeByteLines, List.map_append, List.filter_append, Token.hdTrim, List.map_map, Function.comp_def]

/-- Run the formal grammar on an already tokenized byte stream. -/
def Format.parseTokens (format : Format) (tokens : List (List Nat)) : Except String Graph :=
  (match format with
    | .systemVerilog => parseSVBody
    | .aiger => parseAigerBody
    | .rtlil => parseRTLILBody).run' tokens

/-- Parse the formalized backend subsets. Everything outside the supported grammar fails. -/
def Format.parse (format : Format) (text : String) : Except String Graph :=
  format.parseTokens (Format.tokenize text)

def Format.print (format : Format) (g : Graph) : String :=
  match format with
  | .systemVerilog => HDLean.Backend.systemVerilog g
  | .aiger => HDLean.Backend.aiger g
  | .rtlil => HDLean.Backend.rtlil g

/-- The cycle semantics of the accepted textual subset; parse failures have no meaning. -/
def Format.meaning (format : Format) (text : String) (inputs state : Array Bool) :
    Option (Array Bool × Array Bool) :=
  match format.parse text with
  | .error _ => none
  | .ok g => some (g.eval inputs state)

def Format.validates (format : Format) (text : String) (g : Graph) : Bool :=
  match format.parse text with
  | .error _ => false
  | .ok parsed => parsed.logic == g.logic

/-- The parsed final bytes denote exactly the graph, for every input and power-up state. -/
theorem Format.validates_sound (format : Format) (text : String) (g : Graph)
    (h : format.validates text g = true) (inputs state) :
    format.meaning text inputs state = some (g.eval inputs state) := by
  unfold Format.validates at h
  unfold Format.meaning
  split at h <;> rename_i hp
  · contradiction
  · exact congrArg some (Graph.eval_eq_of_logic_eq _ _ (beq_iff_eq.mp h) inputs state)

/-- The final textual module implements the exact circuit, for every pre-edge state,
input and reset value; no fixed reset or initial value is assumed. -/
def Format.Correct (format : Format) (text : String) (c : Circuit d i r o) : Prop :=
  ∀ (xs : Vector Bool i) (state : Vector Bool r) (rst : Bool),
    format.meaning text (xs.toArray.push rst) state.toArray = some
      ((Vector.ofFn (c.next (fun k => state[k]) ((fun k => xs[k]), rst))).toArray,
       (Vector.ofFn (c.evalOutput (fun k => state[k]) (fun k => xs[k]))).toArray)

theorem Format.correct_of_validated (format : Format) (text : String)
    (g : Graph) (c : Circuit d i r o) (hg : g.Equivalent c)
    (ht : format.validates text g = true) : format.Correct text c := by
  intro xs state rst
  rw [format.validates_sound text g ht]
  exact congrArg some (hg.2.2.2.2 xs state rst)

structure Emitted (format : Format) (c : Circuit d i r o) where
  text : String
  correct : format.Correct text c

/-- Both untrusted construction stages are gated by proved validators. -/
def checkedPrint (format : Format) (c : Circuit d i r o) : Except String (Emitted format c) := do
  let g ← checkedCompileLocal c
  let text := format.print g.val
  if h : format.validates text g.val = true then
    return ⟨text, format.correct_of_validated text g.val c g.property h⟩
  else throw "backend text translation validation failed"

end HDLean.Backend
