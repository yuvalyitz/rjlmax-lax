import Lax391470.BinaryEncoding

/-!
The binary encodings are injective: every code is self-delimiting.
-/

namespace Lax391470Proofs.Encoding

open Lax391470 Lax391470.BinaryEncoding Lax434930.PolynomialTime

/-- A code is *prefix-free*: a code word followed by anything determines both. -/
def PrefixFree {α : Type} (e : α → Word) : Prop :=
  ∀ a b x y, e a ++ x = e b ++ y → a = b ∧ x = y

def ofBits : List Bool → ℕ := List.foldr (fun b n => Nat.bit b n) 0

lemma ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ofBits]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [ofBits, List.foldr_cons] at ih ⊢
    rw [ih]

lemma bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← ofBits_bits a, ← ofBits_bits b, h]

lemma replicate_true_inj (a b : ℕ) (u v : Word)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using h
    | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ] at h
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih b h
      exact ⟨by omega, h2⟩

lemma encodeNat_prefixFree : PrefixFree encodeNat := by
  intro a b x y h
  simp only [encodeNat, List.append_assoc, List.singleton_append] at h
  obtain ⟨hl, hr⟩ := replicate_true_inj _ _ _ _ h
  obtain ⟨hb, hxy⟩ := List.append_inj hr hl
  exact ⟨bits_injective hb, hxy⟩

lemma encodeInt_prefixFree : PrefixFree encodeInt := by
  intro a b x y h
  simp only [encodeInt, List.cons_append, List.cons.injEq] at h
  obtain ⟨hs, ht⟩ := h
  obtain ⟨hn, hxy⟩ := encodeNat_prefixFree _ _ _ _ ht
  refine ⟨?_, hxy⟩
  have : (a < 0) ↔ (b < 0) := by simpa using hs
  omega

/-- Two prefix-free codes in sequence are prefix-free. -/
lemma PrefixFree.pair {α β : Type} {e : α → Word} {f : β → Word} (he : PrefixFree e)
    (hf : PrefixFree f) : PrefixFree fun ab : α × β => e ab.1 ++ f ab.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ x y h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h2⟩ := he _ _ _ _ h
  obtain ⟨h3, h4⟩ := hf _ _ _ _ h2
  exact ⟨by rw [h1, h3], h4⟩

lemma bool_prefixFree : PrefixFree fun b : Bool => [b] := by
  intro a b x y h
  simpa using h

/-- A sequence of `n` code words of a prefix-free code determines its entries. -/
lemma flatMap_inj {α : Type} {e : α → Word} (he : PrefixFree e) :
    ∀ (n : ℕ) (f g : Fin n → α) (x y : Word),
      (List.finRange n).flatMap (fun i => e (f i)) ++ x =
        (List.finRange n).flatMap (fun i => e (g i)) ++ y → f = g ∧ x = y := by
  intro n
  induction n with
  | zero => intro f g x y h; exact ⟨funext fun i => i.elim0, by simpa using h⟩
  | succ n ih =>
    intro f g x y h
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.append_assoc] at h
    obtain ⟨h0, hrest⟩ := he _ _ _ _ h
    obtain ⟨hfg, hxy⟩ := ih (fun i => f i.succ) (fun i => g i.succ) x y hrest
    refine ⟨funext fun i => ?_, hxy⟩
    refine Fin.cases h0 (fun j => ?_) i
    exact congrFun hfg j

theorem encodeInstance_injective : Function.Injective encodeInstance := by
  rintro ⟨n, r, d, p⟩ ⟨n', r', d', p'⟩ h
  simp only [encodeInstance] at h
  obtain ⟨hn, hrest⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hn
  have hc := (encodeInt_prefixFree.pair encodeInt_prefixFree).pair encodeNat_prefixFree
  obtain ⟨hf, -⟩ := flatMap_inj hc n (fun j => ((r j, d j), p j)) (fun j => ((r' j, d' j), p' j))
    [] [] (by simpa using hrest)
  have hr : r = r' := funext fun j => by have := congrFun hf j; simp_all
  have hd : d = d' := funext fun j => by have := congrFun hf j; simp_all
  have hp : p = p' := funext fun j => by have := congrFun hf j; simp_all
  rw [hr, hd, hp]

theorem encodeAux_injective : Function.Injective encodeAux := by
  rintro ⟨n, r, d, l, N, a, b, c, e⟩ ⟨n', r', d', l', N', a', b', c', e'⟩ h
  simp only [encodeAux, List.append_assoc] at h
  obtain ⟨hn, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨hN, h⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hn; subst hN
  have hc1 := (encodeNat_prefixFree.pair encodeNat_prefixFree).pair bool_prefixFree
  obtain ⟨hf, h⟩ := flatMap_inj hc1 n (fun o => ((r o, d o), l o))
    (fun o => ((r' o, d' o), l' o)) _ _ (by simpa using h)
  have hc2 := ((encodeNat_prefixFree.pair encodeNat_prefixFree).pair encodeNat_prefixFree).pair
    encodeNat_prefixFree
  obtain ⟨hg, -⟩ := flatMap_inj hc2 N (fun i => (((a i, b i), c i), e i))
    (fun i => (((a' i, b' i), c' i), e' i)) [] [] (by simpa using h)
  have hr : r = r' := funext fun j => by have := congrFun hf j; simp_all
  have hd : d = d' := funext fun j => by have := congrFun hf j; simp_all
  have hl : l = l' := funext fun j => by have := congrFun hf j; simp_all
  have ha : a = a' := funext fun j => by have := congrFun hg j; simp_all
  have hb : b = b' := funext fun j => by have := congrFun hg j; simp_all
  have hcc : c = c' := funext fun j => by have := congrFun hg j; simp_all
  have he : e = e' := funext fun j => by have := congrFun hg j; simp_all
  rw [hr, hd, hl, ha, hb, hcc, he]

end Lax391470Proofs.Encoding
