import Lax391470Proofs.TokProg

/-!
Everything the tokenizer holds is bounded in terms of the number of bits read.
-/

namespace Lax391470Proofs.TokBound

open Lax391470Proofs.TokModel Lax391470Proofs.TokScan Lax391470Proofs.TokProg
open Lax391470Proofs.Encoding Lax434930.PolynomialTime

lemma ofBits_lt (ds : List Bool) : ofBits ds < 2 ^ ds.length := by
  induction ds using List.reverseRecOn with
  | nil => simp [ofBits]
  | append_singleton ds b ih =>
    rw [ofBits_append, List.length_append, List.length_singleton, pow_succ]
    split <;> omega

variable (E : Format)

/-- The state after `k` bits. -/
structure Bd (s : St) (k : ℕ) : Prop where
  ph : s.ph ≤ 2
  val : s.val = ofBits s.dg
  pw : s.pw = 2 ^ s.dg.length
  dg : s.dg.length ≤ k
  L : s.L ≤ k
  T : s.toks.length ≤ k
  tok : ∀ t ∈ s.toks, Tok.val t < 2 ^ (k + 1)

lemma bd_init : Bd init 0 :=
  ⟨by simp [init], by simp [init, ofBits], by simp [init], by simp [init], by simp [init],
    by simp [init], by simp [init]⟩

lemma bd_step {s : St} {k : ℕ} (h : Bd s k) (b : Bool) : Bd (step E s b) (k + 1) := by
  obtain ⟨hph, hval, hpw, hdg, hL, hT, htok⟩ := h
  have hmono : ∀ t ∈ s.toks, Tok.val t < 2 ^ (k + 1 + 1) := fun t ht =>
    lt_of_lt_of_le (htok t ht) (Nat.pow_le_pow_right (by omega) (by omega))
  have h2 : (2 : ℕ) ≤ 2 ^ (k + 1 + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := rfl
      _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hvlt := ofBits_lt s.dg
  have hpk : 2 ^ s.dg.length ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hdg
  have hk2 : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by ring
  obtain ⟨ph, L, val, pw, dg, toks⟩ := s
  simp only at hph hval hpw hdg hL hT htok hmono hvlt hpk
  have hcases : ph = 0 ∨ ph = 1 ∨ ph = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · rcases hE : E toks with _ | _ | _
    · cases b
      · by_cases hL0 : L = 0
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0] <;> try omega
          all_goals first
            | exact hval
            | exact hpw
            | (intro t ht; rcases ht with ht | rfl
               · exact hmono t ht
               · simp [Tok.val])
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0, ofBits] <;> try omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE] <;> try omega
    · by_cases hL0 : L = 0
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0] <;> try omega
        all_goals first
          | exact hval
          | exact hpw
          | (intro t ht; rcases ht with ht | rfl
             · exact hmono t ht
             · cases b <;> simp [Tok.val])
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, hL0, dead] <;> try omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hE, dead] <;> try omega
  · by_cases hlast : dg.length + 1 = L
    · cases b
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hlast, dead] <;> try omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hlast, ofBits] <;> try omega
        intro t ht
        rcases ht with ht | rfl
        · exact hmono t ht
        · simp only [Tok.val]; omega
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, hlast] <;> try omega
      all_goals first
        | exact hmono
        | (rw [ofBits_append, hval, hpw])
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [step, dead] <;> try omega

end Lax391470Proofs.TokBound
