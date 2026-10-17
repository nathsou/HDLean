import HDLean.Rtl.TextBase

/-!
# RTLIL statements

The word-level RTLIL printer first produces a list of RTLIL statements (wire
declarations, connections, cells with parameters and port connections,
memories, attributes, comments, module brackets), then prints them one or more
lines each. `decStmts_print` proves once that decoding the printed lines gives
back the statements, so design-level decoding works on statements, not lines.

Generated names are printed RTLIL-escaped (`\n_3`, `\i_0_en`, `\hd_1_alu`) and
classify like their unescaped SystemVerilog spelling.
-/
namespace HDLean.Rtl.IL
open Emit Lex Backend.Text

/-! ## Escaped words -/

private theorem named_list (pre : String) (k : Nat) (name : Ident) :
    (pre ++ Nat.repr k ++ "_" ++ name.text).toList = pre.toList ++ ((Nat.repr k).toList ++ '_' :: name.text.toList) := by
  simp [String.toList_append]

def escWireWord (k : Nat) : Word := prefixed ⟨"\\n_", by decide, by decide⟩ k
def escInstWord (k : Nat) : Word := prefixed ⟨"\\u_", by decide, by decide⟩ k

theorem classify_escWire (k : Nat) : classify (escWireWord k).text = .wire k := by
  simp [classify, escWireWord, prefixed, classifyList, symbolic, String.toList_append]

theorem classify_escInst (k : Nat) : classify (escInstWord k).text = .inst k := by
  simp [classify, escInstWord, prefixed, classifyList, symbolic, String.toList_append]

def escInput (k : Nat) (n : Ident) : Word := namedWord "\\i_" (by decide) (by decide) k n
def escOutput (k : Nat) (n : Ident) : Word := namedWord "\\o_" (by decide) (by decide) k n
def escReg (k : Nat) (n : Ident) : Word := namedWord "\\r_" (by decide) (by decide) k n
def escMem (k : Nat) (n : Ident) : Word := namedWord "\\m_" (by decide) (by decide) k n
def escTemp (k : Nat) (n : Ident) : Word := namedWord "\\t_" (by decide) (by decide) k n
def escModule (k : Nat) (n : Ident) : Word := namedWord "\\hd_" (by decide) (by decide) k n

theorem classify_escInput (k : Nat) (n : Ident) : classify (escInput k n).text = .named 'i' k n := by
  simp only [classify, escInput, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_escOutput (k : Nat) (n : Ident) : classify (escOutput k n).text = .named 'o' k n := by
  simp only [classify, escOutput, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_escReg (k : Nat) (n : Ident) : classify (escReg k n).text = .named 'r' k n := by
  simp only [classify, escReg, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_escMem (k : Nat) (n : Ident) : classify (escMem k n).text = .named 'm' k n := by
  simp only [classify, escMem, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_escTemp (k : Nat) (n : Ident) : classify (escTemp k n).text = .named 't' k n := by
  simp only [classify, escTemp, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_escModule (k : Nat) (n : Ident) : classify (escModule k n).text = .named 'h' k n := by
  simp only [classify, escModule, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

/-- `"\\m_<k>_<name>"`: a memory's name as a string parameter (`MEMID`). -/
def memIdWord (k : Nat) (n : Ident) : Word :=
  ⟨"\"\\" ++ (escMem k n).text ++ "\"", by simpa using (escMem k n).noSpace, by simpa using (escMem k n).noNewline⟩

theorem classify_memId (k : Nat) (n : Ident) : classify (memIdWord k n).text = .lit (memIdWord k n).text := by
  have h : (memIdWord k n).text.toList = '"' :: '\\' :: ('\\' :: ('m' :: '_' ::
      ((Nat.repr k).toList ++ '_' :: n.text.toList ++ ['"']))) := by
    simp [memIdWord, escMem, namedWord, String.toList_append]
  have key : ∀ L : List Char, classifyList ('"' :: '\\' :: '\\' :: 'm' :: '_' :: L) =
      .lit (String.ofList ('"' :: '\\' :: '\\' :: 'm' :: '_' :: L)) := fun L => rfl
  unfold classify
  rw [h, key, ← h, String.ofList_toList]

namespace W
def wire (k : Nat) : TW := ⟨escWireWord k, .wire k, classify_escWire k⟩
def inst (k : Nat) : TW := ⟨escInstWord k, .inst k, classify_escInst k⟩
def input (k : Nat) (n : Ident) : TW := ⟨escInput k n, .named 'i' k n, classify_escInput k n⟩
def output (k : Nat) (n : Ident) : TW := ⟨escOutput k n, .named 'o' k n, classify_escOutput k n⟩
def reg (k : Nat) (n : Ident) : TW := ⟨escReg k n, .named 'r' k n, classify_escReg k n⟩
def mem (k : Nat) (n : Ident) : TW := ⟨escMem k n, .named 'm' k n, classify_escMem k n⟩
def temp (k : Nat) (n : Ident) : TW := ⟨escTemp k n, .named 't' k n, classify_escTemp k n⟩
def module (k : Nat) (n : Ident) : TW := ⟨escModule k n, .named 'h' k n, classify_escModule k n⟩
def memId (k : Nat) (n : Ident) : TW := ⟨memIdWord k n, .lit (memIdWord k n).text, classify_memId k n⟩
end W

/-! ## Statements -/

inductive Dir where
  | none | input (n : Nat) | output (n : Nat)
  deriving DecidableEq, Repr

/-- A statement as printed: every word carries its classification. -/
inductive PStmt where
  | wire (w : Nat) (dir : Dir) (name : TW)
  | connect (lhs : TW) (rhs : List TW)
  | cell (ty name : TW) (params : List (TW × TW)) (conns : List (TW × List TW))
  | attr (name value : TW)
  | memory (w size : Nat) (name : TW)
  | comment (toks : List TW)
  | module (name : TW)
  | endm

/-- A statement as decoded. -/
inductive Stmt where
  | wire (w : Nat) (dir : Dir) (name : Tok)
  | connect (lhs : Tok) (rhs : List Tok)
  | cell (ty name : Tok) (params : List (Tok × Tok)) (conns : List (Tok × List Tok))
  | attr (name value : Tok)
  | memory (w size : Nat) (name : Tok)
  | comment (toks : List Tok)
  | module (name : Tok)
  | endm
  deriving DecidableEq

def toks (ws : List TW) : List Tok := ws.map TW.tok

def PStmt.erase : PStmt → Stmt
  | .wire w d n => .wire w d n.tok
  | .connect l r => .connect l.tok (toks r)
  | .cell t n ps cs => .cell t.tok n.tok (ps.map fun p => (p.1.tok, p.2.tok)) (cs.map fun c => (c.1.tok, toks c.2))
  | .attr n v => .attr n.tok v.tok
  | .memory w s n => .memory w s n.tok
  | .comment ts => .comment (toks ts)
  | .module n => .module n.tok
  | .endm => .endm

def dirTWs : Dir → List TW
  | .none => []
  | .input n => [lit! "input", .num n]
  | .output n => [lit! "output", .num n]

def PStmt.lines : PStmt → List TLine
  | .wire w d n => [⟨lit! "wire", [lit! "width", .num w] ++ dirTWs d ++ [n]⟩]
  | .connect l r => [⟨lit! "connect", l :: r⟩]
  | .cell t n ps cs =>
    ⟨lit! "cell", [t, n]⟩ :: ps.map (fun p => ⟨lit! "parameter", [p.1, p.2]⟩) ++
      cs.map (fun c => ⟨lit! "connect", c.1 :: c.2⟩) ++ [⟨lit! "end", []⟩]
  | .attr n v => [⟨lit! "attribute", [n, v]⟩]
  | .memory w s n => [⟨lit! "memory", [lit! "width", .num w, lit! "size", .num s, n]⟩]
  | .comment ts => [⟨lit! "#", ts⟩]
  | .module n => [⟨lit! "module", [n]⟩]
  | .endm => [⟨lit! "end", []⟩]

def render (ss : List PStmt) : String := renderLines (ss.flatMap PStmt.lines)

/-! ## Decoding statements -/

def decParams : List (List Tok) → List (Tok × Tok) × List (List Tok)
  | [.lit "parameter", p, v] :: rest => let r := decParams rest; ((p, v) :: r.1, r.2)
  | ls => ([], ls)

def decConns : List (List Tok) → List (Tok × List Tok) × List (List Tok)
  | (.lit "connect" :: p :: sig) :: rest => let r := decConns rest; ((p, sig) :: r.1, r.2)
  | ls => ([], ls)

def decStmt : List (List Tok) → Option (Stmt × List (List Tok))
  | [.lit "wire", .lit "width", .num w, n] :: rest => some (.wire w .none n, rest)
  | [.lit "wire", .lit "width", .num w, .lit "input", .num k, n] :: rest => some (.wire w (.input k) n, rest)
  | [.lit "wire", .lit "width", .num w, .lit "output", .num k, n] :: rest => some (.wire w (.output k) n, rest)
  | (.lit "connect" :: l :: r) :: rest => some (.connect l r, rest)
  | [.lit "cell", t, n] :: rest =>
    let p := decParams rest
    let c := decConns p.2
    match c.2 with
    | [.lit "end"] :: rest => some (.cell t n p.1 c.1, rest)
    | _ => none
  | [.lit "attribute", n, v] :: rest => some (.attr n v, rest)
  | [.lit "memory", .lit "width", .num w, .lit "size", .num s, n] :: rest => some (.memory w s n, rest)
  | (.lit "#" :: ts) :: rest => some (.comment ts, rest)
  | [.lit "module", n] :: rest => some (.module n, rest)
  | [.lit "end"] :: rest => some (.endm, rest)
  | _ => none

/-- All statements; `fuel` bounds their number. -/
def decStmts : Nat → List (List Tok) → Option (List Stmt)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, ls => do
    let (s, rest) ← decStmt ls
    let ss ← decStmts n rest
    pure (s :: ss)

def lexStmts (text : String) : Option (List Stmt) :=
  let ls := lex text
  decStmts ls.length ls

/-! ## Round trip of statements -/

theorem decParams_print (ps : List (TW × TW)) (rest : List (List Tok))
    (hr : ∀ l ∈ rest.head?, ∀ p v, l ≠ [.lit "parameter", p, v]) :
    decParams ((ps.map fun p => (⟨lit! "parameter", [p.1, p.2]⟩ : TLine)).map TLine.toks ++ rest) =
      (ps.map fun p => (p.1.tok, p.2.tok), rest) := by
  induction ps with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    unfold decParams
    split
    · rename_i p v rest'
      exact absurd rfl (hr _ (by simp) p v)
    · rfl
  | cons p ps ih =>
    have e : TLine.toks ⟨lit! "parameter", [p.1, p.2]⟩ = [.lit "parameter", p.1.tok, p.2.tok] := rfl
    simp only [List.map_cons, List.cons_append, e, decParams, ih]

theorem decConns_print (cs : List (TW × List TW)) (rest : List (List Tok))
    (hr : ∀ l ∈ rest.head?, ∀ p sig, l ≠ .lit "connect" :: p :: sig) :
    decConns ((cs.map fun c => (⟨lit! "connect", c.1 :: c.2⟩ : TLine)).map TLine.toks ++ rest) =
      (cs.map fun c => (c.1.tok, toks c.2), rest) := by
  induction cs with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    unfold decConns
    split
    · rename_i p sig rest'
      exact absurd rfl (hr _ (by simp) p sig)
    · rfl
  | cons c cs ih =>
    have e : TLine.toks ⟨lit! "connect", c.1 :: c.2⟩ = .lit "connect" :: c.1.tok :: toks c.2 := rfl
    simp only [List.map_cons, List.cons_append, e, decConns, ih]

theorem decStmt_print (s : PStmt) (rest : List (List Tok)) :
    decStmt ((s.lines.map TLine.toks) ++ rest) = some (s.erase, rest) := by
  cases s with
  | wire w d n => cases d <;> rfl
  | connect l r => rfl
  | cell t n ps cs =>
    simp only [PStmt.lines, List.map_cons, List.map_append, List.cons_append, List.append_assoc]
    have hp := decParams_print ps ((cs.map fun c => (⟨lit! "connect", c.1 :: c.2⟩ : TLine)).map TLine.toks ++
      ([TLine.toks ⟨lit! "end", []⟩] ++ rest)) (by
        intro l hl p v
        cases cs with
        | nil => simp [TLine.toks] at hl; subst hl; simp
        | cons c cs => simp [TLine.toks] at hl; subst hl; simp)
    have hc := decConns_print cs ([TLine.toks ⟨lit! "end", []⟩] ++ rest) (by
      intro l hl p sig; simp [TLine.toks] at hl; subst hl; simp)
    simp only [List.map_nil, List.singleton_append] at hp hc
    simp only [decStmt, TLine.toks, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hp hc ⊢
    rw [hp]
    simp only
    rw [hc]
    rfl
  | attr n v => rfl
  | memory w s n => rfl
  | comment ts => rfl
  | module n => rfl
  | endm => rfl

theorem PStmt.lines_ne (s : PStmt) : s.lines ≠ [] := by
  cases s <;> simp [PStmt.lines]

theorem decStmts_print : ∀ (ss : List PStmt) (n : Nat), ss.length ≤ n →
    decStmts n ((ss.flatMap PStmt.lines).map TLine.toks) = some (ss.map PStmt.erase)
  | [], n, _ => by cases n <;> rfl
  | s :: ss, n, hn => by
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    have hne := s.lines_ne
    obtain ⟨l, ls, hl⟩ : ∃ l ls, s.lines = l :: ls := by
      cases h : s.lines with
      | nil => exact absurd h hne
      | cons l ls => exact ⟨l, ls, rfl⟩
    simp only [List.flatMap_cons, List.map_append]
    rw [hl]
    simp only [List.map_cons, List.cons_append, decStmts]
    rw [← List.cons_append, ← List.map_cons, ← hl, decStmt_print]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [decStmts_print ss n (by simp at hn; omega)]
    rfl

theorem length_le_lines (ss : List PStmt) : ss.length ≤ (ss.flatMap PStmt.lines).length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have := s.lines_ne
    have : 0 < s.lines.length := List.length_pos_iff.mpr this
    simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega

/-- Lexing printed statements gives them back. -/
theorem lexStmts_render (ss : List PStmt) : lexStmts (render ss) = some (ss.map PStmt.erase) := by
  unfold lexStmts render
  rw [lex_render]
  exact decStmts_print ss _ (by simpa using length_le_lines ss)

end HDLean.Rtl.IL
