import Lax391470Proofs.Encoding

/-!
Streams of tokens — self-delimiting numbers and raw bits — and their binary code.
-/

namespace Lax391470Proofs.TokModel

open Lax391470.BinaryEncoding Lax434930.PolynomialTime Lax391470Proofs.Encoding

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A token: a natural number, or one raw bit. -/
inductive Tok
  | num (v : ℕ)
  | bit (b : Bool)
  deriving DecidableEq

set_option genSizeOfSpec false in
/-- What a format expects next. -/
inductive Kind
  | num | bit | done

def Tok.kind : Tok → Kind
  | .num _ => .num
  | .bit _ => .bit

def Tok.code : Tok → Word
  | .num v => encodeNat v
  | .bit b => [b]

/-- The code of a stream of tokens. -/
def code (ts : List Tok) : Word := ts.flatMap Tok.code

lemma code_append (ts us : List Tok) : code (ts ++ us) = code ts ++ code us := by
  simp [code]

/-- A format: what comes after the tokens read so far. -/
abbrev Format := List Tok → Kind

/-- The stream follows the format, and the format is complete after it. -/
def Conforms (E : Format) (ts : List Tok) : Prop :=
  (∀ k < ts.length, (ts.getD k (.bit false)).kind = E (ts.take k)) ∧ E ts = .done

/-! ### Binary digits -/

lemma ofBits_append (ds : List Bool) (b : Bool) :
    ofBits (ds ++ [b]) = ofBits ds + if b then 2 ^ ds.length else 0 := by
  induction ds with
  | nil => cases b <;> simp [ofBits, Nat.bit]
  | cons a t ih =>
    simp only [ofBits, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih]
    cases a <;> cases b <;> simp [Nat.bit, pow_succ] <;> ring

/-- A digit string whose last digit is one is the digit string of its value. -/
lemma bits_ofBits (ds : List Bool) (h : ds = [] ∨ ds.getLast? = some true) :
    (ofBits ds).bits = ds := by
  induction ds with
  | nil => simp [ofBits]
  | cons a t ih =>
    have ht : t = [] ∨ t.getLast? = some true := by
      rcases t with _ | ⟨b, u⟩
      · exact Or.inl rfl
      · right
        rcases h with h | h
        · cases h
        · simpa [List.getLast?_cons_cons] using h
    have e : ofBits (a :: t) = Nat.bit a (ofBits t) := rfl
    rw [e, Nat.bits_append_bit _ _ ?_, ih ht]
    intro h0
    rcases t with _ | ⟨b, u⟩
    · rcases h with h | h
      · cases h
      · simpa using h
    · exfalso
      have hb := ih ht
      rw [h0] at hb
      simp at hb

lemma encodeNat_ofBits (ds : List Bool) (h : ds = [] ∨ ds.getLast? = some true) :
    encodeNat (ofBits ds) = List.replicate ds.length true ++ [false] ++ ds := by
  unfold encodeNat
  rw [bits_ofBits ds h]

end Lax391470Proofs.TokModel
