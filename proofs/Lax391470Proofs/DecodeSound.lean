import Lax429075.Encoding

/-!
The decoder of formulas of `lax-429075` inverts its encoder from the other side: a word
it decodes to `F` is the encoding of `F`. The source states the round trip
`decodeCNF (encodeCNF F) = some F` (`EncodingCorrect.roundtrip`); this is its converse,
proved by following the parser. The proof is adapted from `Lax429075Proofs.DecoderSoundness`
(Édouard Bonnet, `lax-429075`), where the converse is proved but not stated as a result.
-/

namespace Lax391470Proofs.DecodeSound

open Lax429075 Lax429075.CNF Lax429075.Encoding Lax434930.PolynomialTime

lemma parseNat_sound (w : Word) (n : ℕ) (tail : Word) (h : parseNat w = some (n, tail)) :
    w = encodeNat n ++ tail := by
  induction w generalizing n tail with
  | nil => simp [parseNat] at h
  | cons b w ih =>
    cases b with
    | false => cases h; rfl
    | true =>
      cases hp : parseNat w with
      | none => simp [parseNat, hp] at h
      | some p =>
        obtain ⟨j, rest⟩ := p
        simp only [parseNat, hp] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih j rest hp]
        simp [encodeNat, List.replicate_succ]

lemma parseLiteral_sound (w : Word) (l : Literal) (tail : Word)
    (h : parseLiteral w = some (l, tail)) : w = encodeLiteral l ++ tail := by
  cases hn : parseNat w with
  | none => simp [parseLiteral, hn] at h
  | some p =>
    obtain ⟨n, rest⟩ := p
    cases rest with
    | nil => simp [parseLiteral, hn] at h
    | cons b rest =>
      simp only [parseLiteral, hn] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [encodeLiteral, List.append_assoc] using parseNat_sound w n (b :: tail) hn

lemma parseList_sound {α : Type} (enc : α → Word) (dec : Word → Option (α × Word))
    (hdec : ∀ w a tail, dec w = some (a, tail) → w = enc a ++ tail)
    (fuel : ℕ) (w : Word) (as : List α) (tail : Word)
    (h : parseList dec fuel w = some (as, tail)) : w = encodeList enc as ++ tail := by
  induction fuel generalizing w as tail with
  | zero => simp [parseList] at h
  | succ fuel ih =>
    cases w with
    | nil => simp [parseList] at h
    | cons b w =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hd : dec w with
        | none => simp [parseList, hd] at h
        | some p =>
          obtain ⟨a, rest⟩ := p
          rw [parseList, hd] at h
          change (parseList dec fuel rest).bind (fun p => some (a :: p.1, p.2)) =
            some (as, tail) at h
          cases ht : parseList dec fuel rest with
          | none => simp [ht] at h
          | some p =>
            obtain ⟨bs, rest'⟩ := p
            simp only [ht, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [hdec w a rest hd, ih rest bs rest' ht]
            simp [encodeList, List.append_assoc]

/-- A word the decoder accepts is the encoding of the formula it returns. -/
theorem decodeCNF_sound (w : Word) (F : Formula) (h : decodeCNF w = some F) :
    encodeCNF F = w := by
  cases hp : parseList parseClause w.length w with
  | none => simp [decodeCNF, hp] at h
  | some p =>
    obtain ⟨G, rest⟩ := p
    unfold decodeCNF at h
    rw [hp] at h
    change (if rest = [] then some G else none) = some F at h
    by_cases hr : rest = []
    · subst rest
      simp only [↓reduceIte, Option.some.injEq] at h
      subst F
      have hC : ∀ v C tail, parseClause v = some (C, tail) → v = encodeClause C ++ tail :=
        fun v C tail hv => parseList_sound encodeLiteral parseLiteral parseLiteral_sound
          v.length v C tail hv
      simpa [encodeCNF] using (parseList_sound encodeClause parseClause hC w.length w G [] hp).symm
    · simp [hr] at h

end Lax391470Proofs.DecodeSound
