import Lax391470Proofs.AuxFormat
import Lax391470Proofs.V1Format

/-!
The format of an instance of the auxiliary problem followed by a schedule: after the
tokens of the instance, one start time for every job of the underlying instance.
-/

namespace Lax391470Proofs.V2Format

open Lax391470 Lax391470.BinaryEncoding Lax391470Proofs.TokModel Lax391470Proofs.TokScan
open Lax391470Proofs.AuxFormat Lax434930.PolynomialTime

/-- The kind of the token at position `j` after the two counts. -/
def kind2 (n N j : ℕ) : Kind :=
  if j < 3 * n + 4 * N then kindAt n N j
  else if j < 3 * n + 4 * N + (n + 2 * N) then .num
  else .done

/-- The format: an instance, then `n + 2N` start times. -/
def E2 : Format := fun ts =>
  match ts with
  | .num n :: .num N :: rest => kind2 n N rest.length
  | [] => .num
  | [_] => .num
  | _ => .done

lemma E2_cons (n N : ℕ) (rest : List Tok) :
    E2 (.num n :: .num N :: rest) = kind2 n N rest.length := rfl

lemma kind2_lt {n N j : ℕ} (h : j < 3 * n + 4 * N) : kind2 n N j = kindAt n N j := by
  unfold kind2; rw [if_pos h]

lemma E2_one (a : Tok) : E2 [a] = .num := by cases a <;> rfl
lemma EA_one (a : Tok) : EA [a] = .num := by cases a <;> rfl

/-- The tokens of `m` start times. -/
def schedToks (t : ℕ → ℕ) (m : ℕ) : List Tok := (List.range m).map fun j => .num (t j)

lemma schedToks_length (t : ℕ → ℕ) (m : ℕ) : (schedToks t m).length = m := by
  simp [schedToks]

lemma schedToks_get (t : ℕ → ℕ) (m j : ℕ) (hj : j < m) :
    (schedToks t m).getD j (.bit false) = .num (t j) := by
  unfold schedToks
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

/-- An instance followed by a schedule. -/
def toks2 (A : AuxiliaryProblem.Instance) (t : ℕ → ℕ) : List Tok :=
  toksOf A ++ schedToks t (A.ordinary + 2 * A.pairs)

lemma toks2_eq (A : AuxiliaryProblem.Instance) (t : ℕ → ℕ) :
    toks2 A t = .num A.ordinary :: .num A.pairs ::
      (body A ++ schedToks t (A.ordinary + 2 * A.pairs)) := by
  unfold toks2; rw [toksOf_eq]; rfl

lemma rest_kind (A : AuxiliaryProblem.Instance) (t : ℕ → ℕ) (k : ℕ)
    (hk : k < 3 * A.ordinary + 4 * A.pairs + (A.ordinary + 2 * A.pairs)) :
    ((body A ++ schedToks t (A.ordinary + 2 * A.pairs)).getD k (.bit false)).kind =
      kind2 A.ordinary A.pairs k := by
  by_cases h5 : k < 3 * A.ordinary + 4 * A.pairs
  · rw [List.getD_append _ _ _ _ (by rw [body_length]; exact h5), body_kind A k h5, kind2_lt h5]
  · rw [List.getD_append_right _ _ _ _ (by rw [body_length]; omega), body_length,
      schedToks_get _ _ _ (by omega)]
    unfold kind2
    rw [if_neg h5, if_pos hk]; rfl

/-- **An instance followed by a schedule conforms to the format.** -/
theorem conforms_toks2 (A : AuxiliaryProblem.Instance) (t : ℕ → ℕ) :
    Conforms E2 (toks2 A t) := by
  rw [toks2_eq]
  have hl : (body A ++ schedToks t (A.ordinary + 2 * A.pairs)).length =
      3 * A.ordinary + 4 * A.pairs + (A.ordinary + 2 * A.pairs) := by
    rw [List.length_append, body_length, schedToks_length]
  constructor
  · intro k hk
    simp only [List.length_cons] at hk
    rcases k with _ | _ | j
    · rfl
    · rfl
    · simp only [List.getD_cons_succ, List.take_succ_cons, E2_cons]
      rw [List.length_take, hl, Nat.min_eq_left (by omega)]
      exact rest_kind A t j (by omega)
  · rw [E2_cons, hl]; unfold kind2; rw [if_neg (by omega), if_neg (by omega)]

/-- The first two tokens of a stream that follows the format are numbers. -/
lemma two_nums {ts : List Tok} (hf : Follows E2 ts) (h2 : 2 ≤ ts.length) :
    ∃ n N rest, ts = .num n :: .num N :: rest := by
  rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at h2
  · simp at h2
  have ha : a.kind = .num := by simpa [E2] using hf 0 (by simp)
  have hb : b.kind = .num := by
    have := hf 1 (by simp)
    simpa [E2_one] using this
  exact ⟨_, _, rest, by rw [tok_of_num ha, tok_of_num hb]⟩

/-- **The boundary.** If the scan of a word stops between two tokens, having read exactly
the tokens of an instance, the word is the code of these tokens and they conform to the
format of instances. -/
theorem boundary {w : Word} (h0 : (run E2 init w).ph = 0) (hL : (run E2 init w).L = 0)
    (hT : (run E2 init w).toks.length =
      2 + 3 * ((run E2 init w).toks.map TokProg.Tok.val).getD 0 0 +
        4 * ((run E2 init w).toks.map TokProg.Tok.val).getD 1 0) :
    code (run E2 init w).toks = w ∧ Conforms EA (run E2 init w).toks := by
  obtain ⟨hg, hc⟩ := run_inv E2 w (by omega)
  have h1 : consumed (run E2 init w) = code (run E2 init w).toks := by simp [consumed, h0, hL]
  refine ⟨by rw [← h1, hc], ?_⟩
  have hf := hg.fol
  obtain ⟨n, N, rest, hts⟩ := two_nums hf (by omega)
  rw [hts] at hT hf ⊢
  have hlen : rest.length = 3 * n + 4 * N := by
    simp [TokProg.Tok.val] at hT; omega
  constructor
  · intro k hk
    rw [hf k hk]
    rcases k with _ | _ | j
    · rfl
    · rw [show (Tok.num n :: Tok.num N :: rest).take 1 = [Tok.num n] from rfl, E2_one, EA_one]
    · have e : (Tok.num n :: Tok.num N :: rest).take (j + 1 + 1) =
          .num n :: .num N :: rest.take j := rfl
      simp only [List.length_cons] at hk
      rw [e, E2_cons, EA_cons, kind2_lt (by rw [List.length_take]; omega)]
  · rw [EA_cons, hlen]; simp [kindAt]

/-- The length of a conforming stream. -/
lemma conf2_length {ts : List Tok} (hc : Conforms E2 ts) :
    ts.length = 2 + (3 * (ts.map TokProg.Tok.val).getD 0 0 +
      4 * (ts.map TokProg.Tok.val).getD 1 0 +
      ((ts.map TokProg.Tok.val).getD 0 0 + 2 * (ts.map TokProg.Tok.val).getD 1 0)) := by
  obtain ⟨hf, hd⟩ := hc
  have h2 : 2 ≤ ts.length := by
    rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [E2] at hd
    · rw [E2_one] at hd; cases hd
    · simp
  obtain ⟨n, N, rest, rfl⟩ := two_nums hf h2
  rw [E2_cons] at hd
  have h1 : ¬ rest.length < 3 * n + 4 * N + (n + 2 * N) := by
    intro hlt
    unfold kind2 kindAt at hd
    split_ifs at hd
  have h3 : rest.length = 3 * n + 4 * N + (n + 2 * N) := by
    by_contra hne
    have hk := hf (2 + (3 * n + 4 * N + (n + 2 * N))) (by simp; omega)
    have e : (Tok.num n :: Tok.num N :: rest).take (2 + (3 * n + 4 * N + (n + 2 * N))) =
        .num n :: .num N :: rest.take (3 * n + 4 * N + (n + 2 * N)) := by
      rw [show 2 + (3 * n + 4 * N + (n + 2 * N)) = (3 * n + 4 * N + (n + 2 * N)) + 1 + 1 by ring]
      rfl
    rw [e, E2_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
    have : kind2 n N (3 * n + 4 * N + (n + 2 * N)) = .done := by
      unfold kind2; rw [if_neg (by omega), if_neg (by omega)]
    rw [this] at hk
    exact kind_ne_done _ hk
  simp [TokProg.Tok.val, h3]; omega

end Lax391470Proofs.V2Format
