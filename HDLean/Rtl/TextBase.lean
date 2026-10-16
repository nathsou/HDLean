import HDLean.Rtl.Lex

/-!
# Lines of classified tokens

A printed token (`TW`) carries its classification. Printers produce lines of
`TW`; `render_lex` says that tokenizing and classifying the rendered text gives
back exactly the classified lines, so decoders and their round-trip proofs work
on token kinds only.
-/
namespace HDLean.Rtl.Emit
open Backend.Text Lex

structure TW where
  word : Word
  tok : Tok
  ok : classify word.text = tok

macro "lit!" s:str : term =>
  `((⟨⟨$s, by decide, by decide⟩, Tok.lit $s, by decide⟩ : HDLean.Rtl.Emit.TW))

namespace TW
def num (n : Nat) : TW := ⟨numWord n, .num n, classify_num n⟩
def const (w v : Nat) : TW := ⟨constWord w v, .const w v, classify_const w v⟩
def wire (k : Nat) : TW := ⟨wireWord k, .wire k, classify_wire k⟩
def inst (k : Nat) : TW := ⟨instWord k, .inst k, classify_inst k⟩
def input (k : Nat) (n : Ident) : TW := ⟨inputWord k n, .named 'i' k n, classify_input k n⟩
def output (k : Nat) (n : Ident) : TW := ⟨outputWord k n, .named 'o' k n, classify_output k n⟩
def reg (k : Nat) (n : Ident) : TW := ⟨regWord k n, .named 'r' k n, classify_reg k n⟩
def mem (k : Nat) (n : Ident) : TW := ⟨memWord k n, .named 'm' k n, classify_mem k n⟩
def module (k : Nat) (n : Ident) : TW := ⟨moduleWord k n, .named 'h' k n, classify_module k n⟩
end TW

/-- A nonempty line of classified tokens. -/
structure TLine where
  head : TW
  tail : List TW

def TLine.toks (l : TLine) : List Tok := l.head.tok :: l.tail.map TW.tok

def TLine.line (l : TLine) : Line := ⟨(l.head :: l.tail).map TW.word, by simp⟩

def TLine.of (ws : List TW) (default : TW := lit! ";") : TLine :=
  match ws with
  | [] => ⟨default, []⟩
  | w :: ws => ⟨w, ws⟩

@[simp] theorem TLine.toks_of (w : TW) (ws : List TW) (d : TW) :
    (TLine.of (w :: ws) d).toks = (w :: ws).map TW.tok := rfl

def renderLines (ls : List TLine) : String := Backend.Text.render (ls.map TLine.line)

def lex (text : String) : List (List Tok) := (Backend.Text.tokenize text).map (·.map classify)

theorem lex_render (ls : List TLine) : lex (renderLines ls) = ls.map TLine.toks := by
  simp only [lex, renderLines, Backend.Text.tokenize_render, List.map_map]
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, TLine.line, Line.tokens, List.map_map, TLine.toks, List.map_cons]
  congr 1
  · exact l.head.ok
  · apply List.map_congr_left; intro w _; exact w.ok

/-! ## Decoders over classified lines -/

abbrev Dec (α : Type) := List (List Tok) → Option (α × List (List Tok))

def oneLine (f : List Tok → Option α) : Dec α
  | l :: rest => (f l).map (·, rest)
  | [] => none

theorem oneLine_ok (f : List Tok → Option α) (l : List Tok) (a : α) (tail : List (List Tok))
    (h : f l = some a) : oneLine f (l :: tail) = some (a, tail) := by
  simp [oneLine, h]

def fixedLine (toks : List Tok) : Dec Unit := oneLine fun l => if l = toks then some () else none

theorem fixedLine_ok (toks : List Tok) (tail : List (List Tok)) :
    fixedLine toks (toks :: tail) = some ((), tail) := by
  simp [fixedLine, oneLine]

/-- `n` items, the `i`-th decoded by `d (base + i)`. -/
def decRepeat (d : Nat → Dec α) : Nat → Nat → Dec (List α)
  | 0, _, ls => some ([], ls)
  | n + 1, base, ls => do
    let (a, ls) ← d base ls
    let (as, ls) ← decRepeat d n (base + 1) ls
    pure (a :: as, ls)

/-- Round trip for repeated items: item `x` printed at index `i` decodes to `g x`. -/
theorem decRepeat_ok (d : Nat → Dec α) (enc : Nat → β → List (List Tok)) (g : β → α) (P : β → Prop)
    (h : ∀ i x tail, P x → d i (enc i x ++ tail) = some (g x, tail)) :
    ∀ (xs : List β) (base : Nat) (tail : List (List Tok)), (∀ x ∈ xs, P x) →
      decRepeat d xs.length base ((xs.zipIdx base).flatMap (fun p => enc p.2 p.1) ++ tail) = some (xs.map g, tail)
  | [], _, _, _ => rfl
  | x :: xs, base, tail, hp => by
    simp only [List.length_cons, decRepeat, List.zipIdx_cons, List.flatMap_cons, List.append_assoc]
    rw [h base x _ (hp x (by simp))]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [decRepeat_ok d enc g P h xs (base + 1) tail (fun y hy => hp y (by simp [hy]))]
    rfl

end HDLean.Rtl.Emit
