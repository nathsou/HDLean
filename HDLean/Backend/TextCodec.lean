import Std.Data.String.ToNat
import Init.Data.String.Lemmas.Pattern.Split.Char
import Init.Data.Char.Lemmas

set_option backward.isDefEq.respectTransparency false
namespace HDLean.Backend.Text

/-- Token boundaries are part of the grammar, including the final newline. -/
structure Word where
  text : String
  noSpace : ' ' ∉ text.toList
  noNewline : '\n' ∉ text.toList

private theorem repr_no_char (n : Nat) (c : Char) (h : c.isDigit = false) : c ∉ (Nat.repr n).toList := by
  intro hc
  have hd := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by decide) (by decide)
    (by simpa [Nat.toList_repr] using hc)
  simp [h] at hd

def numeral (n : Nat) : Word :=
  ⟨Nat.repr n, repr_no_char n ' ' (by decide), repr_no_char n '\n' (by decide)⟩

@[simp] theorem numeral_parse (n : Nat) : (numeral n).text.toNat? = some n := by
  exact Nat.toNat?_repr n

/-- Prefixes are fixed grammar words, for example an RTLIL escaped cell name. -/
def prefixed (pre : Word) (n : Nat) : Word :=
  ⟨pre.text ++ Nat.repr n, by simpa using And.intro pre.noSpace (repr_no_char n ' ' (by decide)),
    by simpa using And.intro pre.noNewline (repr_no_char n '\n' (by decide))⟩

def parsePrefixed (pre : String) (text : String) : Option Nat :=
  if pre.toList.isPrefixOf text.toList then
    (String.ofList (text.toList.drop pre.toList.length)).toNat?
  else none

@[simp] theorem prefixed_parse (pre : Word) (n : Nat) :
    parsePrefixed pre.text (prefixed pre n).text = some n := by
  simp only [parsePrefixed, prefixed, String.toList_append, List.isPrefixOf_iff_prefix, List.prefix_append,
    ite_true, List.drop_left, String.ofList_toList, Nat.toNat?_repr]

structure Line where
  words : List Word
  nonempty : words ≠ []

def Line.tokens (line : Line) : List String := line.words.map Word.text

def Line.render (line : Line) : String := String.intercalate " " line.tokens

def splitWords (text : String) : List String := (text.split ' ').toList.map (·.copy)

@[simp] theorem Line.split_render (line : Line) : splitWords line.render = line.tokens := by
  have h : ∀ s ∈ line.tokens, ' ' ∉ s.toList := by
    intro s hs
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hs
    exact w.noSpace
  have hn : line.tokens ≠ [] := by simpa [Line.tokens] using line.nonempty
  have hs : String.singleton ' ' = " " := by decide +kernel
  have ht := String.toList_split_intercalate h
  rw [hs] at ht
  simpa [splitWords, Line.render, hn] using ht

private theorem no_newline_join (words : List Word) :
    '\n' ∉ (String.intercalate " " (words.map Word.text)).toList := by
  induction words with
  | nil => simp
  | cons w words ih =>
    cases words with
    | nil => simpa using w.noNewline
    | cons x xs =>
      simpa [String.intercalate_cons_cons, String.toList_append, w.noNewline] using ih

@[simp] theorem Line.no_newline (line : Line) : '\n' ∉ line.render.toList :=
  no_newline_join line.words

/-- Right recursion copies each short fragment once in logical kernel reduction.
The standard library's accumulator implementation repeatedly copies the growing prefix. -/
def join (separator : String) : List String → String
  | [] => ""
  | [word] => word
  | word::next::rest => word ++ separator ++ join separator (next::rest)

theorem join_eq_intercalate (separator : String) (words : List String) :
    join separator words = String.intercalate separator words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    cases words with
    | nil => rfl
    | cons next rest =>
      simp only [join,String.intercalate_cons_cons] at *
      rw [ih]

/-- The compiled printer uses the standard library's buffer-oriented path. This
rewrite is proved; the logical definition remains suitable for pure kernel replay. -/
@[csimp] theorem join_eq_intercalate_fn : join = String.intercalate := by
  funext separator words
  exact join_eq_intercalate separator words

/-- A file always ends in a newline; empty files are represented by one newline. -/
def render (lines : List Line) : String :=
  join "\n" (lines.map Line.render ++ [""])

def splitLines (text : String) : List String :=
  ((text.split '\n').toList.map (·.copy)).dropLast

def tokenize (text : String) : List (List String) := (splitLines text).map splitWords

@[simp] theorem splitLines_render (lines : List Line) : splitLines (render lines) = lines.map Line.render := by
  have h : ∀ s ∈ lines.map Line.render ++ [""], '\n' ∉ s.toList := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨line, _, rfl⟩ := List.mem_map.mp hs
      exact line.no_newline
    · simp only [List.mem_singleton] at hs
      subst s
      simp
  have hn : lines.map Line.render ++ [""] ≠ [] := by simp
  have hs : String.singleton '\n' = "\n" := by decide +kernel
  have ht := congrArg List.dropLast (String.toList_split_intercalate h)
  rw [hs] at ht
  unfold render
  rw [join_eq_intercalate]
  simpa [splitLines, hn] using ht

@[simp] theorem tokenize_render (lines : List Line) :
    tokenize (render lines) = lines.map Line.tokens := by
  simp [tokenize, List.map_map, Function.comp_def]

end HDLean.Backend.Text
