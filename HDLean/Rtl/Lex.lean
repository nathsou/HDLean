import HDLean.Backend.TextCodec
import HDLean.Rtl.Syntax

/-!
# Tokens of emitted HDL text

Printers build every token from one of the constructors below, and decoders
first `classify` each token. Classification of a printed token is proved once
per token kind, so decoders pattern-match on token *kinds* and never compare
symbolic strings.

Kinds are told apart by their first characters: numerals and sized constants
start with a digit; generated names start with a letter followed by `_`
(`n_3`, `u_3`, `i_0_en`, `hd_1_alu`); everything else is a literal.
-/
namespace HDLean.Rtl.Lex
open Backend.Text

inductive Tok where
  | num (n : Nat)
  /-- `<w>'d<v>` -/
  | const (w v : Nat)
  /-- `n_<k>` -/
  | wire (k : Nat)
  /-- `u_<k>` -/
  | inst (k : Nat)
  /-- `<c>_<k>_<name>` for `c` in `i o r m`, and `hd_<k>_<name>` for `c = 'h'` -/
  | named (c : Char) (k : Nat) (name : Ident)
  | lit (s : String)
  deriving Repr, DecidableEq

/-- Split at the first occurrence of `c`. -/
def splitFirst (c : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | x :: xs => if x = c then some ([], xs) else (splitFirst c xs).map fun p => (x :: p.1, p.2)

theorem splitFirst_append (c : Char) (b : List Char) :
    ∀ (a : List Char), c ∉ a → splitFirst c (a ++ c :: b) = some (a, b)
  | [], _ => by simp [splitFirst]
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    have hxs : c ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitFirst, hx, splitFirst_append c b xs hxs]

theorem splitFirst_none (c : Char) : ∀ (a : List Char), c ∉ a → splitFirst c a = none
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    have hxs : c ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitFirst, hx, splitFirst_none c xs hxs]

def digits (l : List Char) : Option Nat := (String.ofList l).toNat?

@[simp] theorem digits_toDigits (n : Nat) : digits (Nat.toDigits 10 n) = some n := Nat.toNat?_repr n

theorem digits_repr (n : Nat) : digits (Nat.repr n).toList = some n := by simp

theorem repr_isDigit (n : Nat) : ∀ c ∈ (Nat.repr n).toList, c.isDigit = true := by
  intro c hc
  exact Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by decide) (by decide) (by simpa [Nat.toList_repr] using hc)

theorem repr_not_mem (n : Nat) (c : Char) (h : c.isDigit = false) : c ∉ (Nat.repr n).toList := by
  intro hc; have := repr_isDigit n c hc; simp [h] at this

@[simp] theorem toDigits_not_mem (n : Nat) (c : Char) (h : c.isDigit = false) : c ∉ Nat.toDigits 10 n := by
  simpa using repr_not_mem n c h

theorem repr_cons (n : Nat) : ∃ d ds, (Nat.repr n).toList = d :: ds ∧ d.isDigit = true := by
  cases h : (Nat.repr n).toList with
  | nil => simp [Nat.toList_repr, Nat.toDigits_ne_nil] at h
  | cons d ds => exact ⟨d, ds, rfl, repr_isDigit n d (by simp [h])⟩

def parseNamed (l : List Char) : Option (Nat × Ident) := do
  let (a, b) ← splitFirst '_' l
  let k ← digits a
  if h : b.all identChar = true then
    some (k, ⟨String.ofList b, by simpa using h⟩)
  else none

/-- Classify a token that starts with a digit. -/
def numeric (l : List Char) : Tok :=
  match splitFirst '\'' l with
  | some (a, 'd' :: b) => match digits a, digits b with
    | some w, some v => .const w v
    | _, _ => .lit (String.ofList l)
  | _ => match digits l with
    | some n => .num n
    | none => .lit (String.ofList l)

def symbolic (l : List Char) : Tok :=
  match l with
  | 'n' :: '_' :: rest => (digits rest).elim (.lit (String.ofList l)) .wire
  | 'u' :: '_' :: rest => (digits rest).elim (.lit (String.ofList l)) .inst
  | 'h' :: 'd' :: '_' :: rest => (parseNamed rest).elim (.lit (String.ofList l)) fun p => .named 'h' p.1 p.2
  | c :: '_' :: rest =>
    if c = 'i' ∨ c = 'o' ∨ c = 'r' ∨ c = 'm' then
      (parseNamed rest).elim (.lit (String.ofList l)) fun p => .named c p.1 p.2
    else .lit (String.ofList l)
  | _ => .lit (String.ofList l)

def classifyList : List Char → Tok
  | [] => .lit ""
  | c :: rest => if c.isDigit then numeric (c :: rest) else symbolic (c :: rest)

def classify (s : String) : Tok := classifyList s.toList

/-! ## Printed tokens -/

private theorem no_space_ident (name : Ident) : ' ' ∉ name.text.toList := by
  intro h
  have := List.all_eq_true.mp name.valid _ h
  simp [identChar] at this

private theorem no_newline_ident (name : Ident) : '\n' ∉ name.text.toList := by
  intro h
  have := List.all_eq_true.mp name.valid _ h
  simp [identChar] at this

def wireWord (k : Nat) : Word := prefixed ⟨"n_", by decide, by decide⟩ k
def instWord (k : Nat) : Word := prefixed ⟨"u_", by decide, by decide⟩ k
def numWord (n : Nat) : Word := numeral n

def constWord (w v : Nat) : Word :=
  ⟨Nat.repr w ++ "'d" ++ Nat.repr v,
    by simp [repr_not_mem w ' ' (by decide), repr_not_mem v ' ' (by decide)],
    by simp [repr_not_mem w '\n' (by decide), repr_not_mem v '\n' (by decide)]⟩

/-- `<pre><k>_<name>`; the prefix ends in `_`. -/
def namedWord (pre : String) (h1 : ' ' ∉ pre.toList) (h2 : '\n' ∉ pre.toList) (k : Nat) (name : Ident) : Word :=
  ⟨pre ++ Nat.repr k ++ "_" ++ name.text,
    by simp [h1, repr_not_mem k ' ' (by decide), no_space_ident],
    by simp [h2, repr_not_mem k '\n' (by decide), no_newline_ident]⟩

def inputWord (k : Nat) (n : Ident) : Word := namedWord "i_" (by decide) (by decide) k n
def outputWord (k : Nat) (n : Ident) : Word := namedWord "o_" (by decide) (by decide) k n
def regWord (k : Nat) (n : Ident) : Word := namedWord "r_" (by decide) (by decide) k n
def memWord (k : Nat) (n : Ident) : Word := namedWord "m_" (by decide) (by decide) k n
def moduleWord (k : Nat) (n : Ident) : Word := namedWord "hd_" (by decide) (by decide) k n

/-! ## Classification of printed tokens -/

theorem classify_num (n : Nat) : classify (numWord n).text = .num n := by
  obtain ⟨d, ds, h, hd⟩ := repr_cons n
  have hq : splitFirst '\'' (Nat.repr n).toList = none := splitFirst_none _ _ (repr_not_mem n _ (by decide))
  simp only [classify, numWord, numeral, h, classifyList, hd, ite_true, numeric]
  rw [← h, hq]
  try simp

theorem classify_const (w v : Nat) : classify (constWord w v).text = .const w v := by
  obtain ⟨d, ds, h, hd⟩ := repr_cons w
  have hs : splitFirst '\'' (Nat.repr w ++ "'d" ++ Nat.repr v).toList = some ((Nat.repr w).toList, 'd' :: (Nat.repr v).toList) := by
    simp only [String.toList_append]
    rw [show (Nat.repr w).toList ++ "'d".toList ++ (Nat.repr v).toList =
      (Nat.repr w).toList ++ '\'' :: ('d' :: (Nat.repr v).toList) by simp]
    exact splitFirst_append _ _ _ (repr_not_mem w _ (by decide))
  have hl : (Nat.repr w ++ "'d" ++ Nat.repr v).toList = d :: (ds ++ "'d".toList ++ (Nat.repr v).toList) := by
    simp [String.toList_append, h]
  simp only [classify, constWord, hl, classifyList, hd, ite_true, numeric]
  rw [← hl, hs]
  try simp

theorem classify_wire (k : Nat) : classify (wireWord k).text = .wire k := by
  simp [classify, wireWord, prefixed, classifyList, symbolic, String.toList_append]

theorem classify_inst (k : Nat) : classify (instWord k).text = .inst k := by
  simp [classify, instWord, prefixed, classifyList, symbolic, String.toList_append]

@[simp] theorem parseNamed_word (k : Nat) (name : Ident) :
    parseNamed (Nat.toDigits 10 k ++ '_' :: name.text.toList) = some (k, name) := by
  simp only [parseNamed, splitFirst_append _ _ _ (toDigits_not_mem k '_' (by decide))]
  have hv : name.text.toList.all identChar = true := name.valid
  simp only [Option.bind_eq_bind, Option.bind_some, digits_toDigits, String.ofList_toList, hv, dite_true]

private theorem named_list (pre : String) (k : Nat) (name : Ident) :
    (pre ++ Nat.repr k ++ "_" ++ name.text).toList = pre.toList ++ ((Nat.repr k).toList ++ '_' :: name.text.toList) := by
  simp [String.toList_append]

theorem classify_input (k : Nat) (n : Ident) : classify (inputWord k n).text = .named 'i' k n := by
  simp only [classify, inputWord, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_output (k : Nat) (n : Ident) : classify (outputWord k n).text = .named 'o' k n := by
  simp only [classify, outputWord, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_reg (k : Nat) (n : Ident) : classify (regWord k n).text = .named 'r' k n := by
  simp only [classify, regWord, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_mem (k : Nat) (n : Ident) : classify (memWord k n).text = .named 'm' k n := by
  simp only [classify, memWord, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

theorem classify_module (k : Nat) (n : Ident) : classify (moduleWord k n).text = .named 'h' k n := by
  simp only [classify, moduleWord, namedWord, named_list]
  simp [classifyList, symbolic, parseNamed_word]

end HDLean.Rtl.Lex
