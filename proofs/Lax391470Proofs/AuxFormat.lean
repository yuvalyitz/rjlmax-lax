import Lax391470Proofs.TokScan
import Lax391470Proofs.RecList
import Lax391470Proofs.L2Model

/-!
The encoding of an instance of the auxiliary problem, as a stream of tokens.
-/

namespace Lax391470Proofs.AuxFormat

open Lax391470 Lax391470.BinaryEncoding Lax391470Proofs.TokModel

variable (A : AuxiliaryProblem.Instance)

/-- The three tokens of ordinary job `o`. -/
def ordRec (o : ℕ) : List Tok :=
  if h : o < A.ordinary then [.num (A.r ⟨o, h⟩), .num (A.d ⟨o, h⟩), .bit (A.long ⟨o, h⟩)]
  else [.num 0, .num 0, .bit false]

/-- The four tokens of pair `i`. -/
def pairRec (i : ℕ) : List Tok :=
  if h : i < A.pairs then
    [.num (A.longEarly ⟨i, h⟩), .num (A.longDue ⟨i, h⟩), .num (A.shortEarly ⟨i, h⟩),
      .num (A.shortDue ⟨i, h⟩)]
  else [.num 0, .num 0, .num 0, .num 0]

lemma ordRec_length (o : ℕ) : (ordRec A o).length = 3 := by unfold ordRec; split <;> rfl
lemma pairRec_length (i : ℕ) : (pairRec A i).length = 4 := by unfold pairRec; split <;> rfl

/-- The tokens of the encoding of `A`. -/
def toksOf : List Tok :=
  [.num A.ordinary, .num A.pairs] ++ (List.range A.ordinary).flatMap (ordRec A) ++
    (List.range A.pairs).flatMap (pairRec A)

lemma code_flatMap (l : List ℕ) (f : ℕ → List Tok) :
    code (l.flatMap f) = l.flatMap fun k => code (f k) := by
  simp [code, List.flatMap_assoc]

theorem encodeAux_eq : encodeAux A = code (toksOf A) := by
  unfold encodeAux toksOf
  rw [code_append, code_append, code_flatMap, code_flatMap, L2Model.flatMap_finRange,
    L2Model.flatMap_finRange]
  congr 1
  · congr 1
    · simp [code, Tok.code]
    · refine List.flatMap_congr fun o ho => ?_
      have h : o < A.ordinary := List.mem_range.mp ho
      simp [ordRec, h, code, Tok.code]
  · refine List.flatMap_congr fun i hi => ?_
    have h : i < A.pairs := List.mem_range.mp hi
    simp [pairRec, h, code, Tok.code]

lemma toksOf_length : (toksOf A).length = 2 + 3 * A.ordinary + 4 * A.pairs := by
  unfold toksOf
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [RecList.length_flatMap_const _ 3 (ordRec_length A), RecList.length_flatMap_const _ 4
    (pairRec_length A)]

/-- The format: two counts, then `n` records of two numbers and a bit, then `N` records of
four numbers. -/
def EA : Format := fun ts =>
  match ts with
  | .num n :: .num N :: rest =>
    if rest.length < 3 * n then (if rest.length % 3 = 2 then .bit else .num)
    else if rest.length < 3 * n + 4 * N then .num else .done
  | [] => .num
  | [_] => .num
  | _ => .done

/-- The kind of the token at position `j` after the two counts. -/
def kindAt (n N j : ℕ) : Kind :=
  if j < 3 * n then (if j % 3 = 2 then .bit else .num)
  else if j < 3 * n + 4 * N then .num else .done

lemma EA_cons (n N : ℕ) (rest : List Tok) :
    EA (.num n :: .num N :: rest) = kindAt n N rest.length := rfl

/-- The records after the two counts. -/
def body : List Tok :=
  (List.range A.ordinary).flatMap (ordRec A) ++ (List.range A.pairs).flatMap (pairRec A)

lemma toksOf_eq : toksOf A = .num A.ordinary :: .num A.pairs :: body A := by
  simp [toksOf, body]

lemma body_length : (body A).length = 3 * A.ordinary + 4 * A.pairs := by
  unfold body
  rw [List.length_append, RecList.length_flatMap_const _ 3 (ordRec_length A),
    RecList.length_flatMap_const _ 4 (pairRec_length A)]

lemma body_ord (o c : ℕ) (ho : o < A.ordinary) (hc : c < 3) (d : Tok) :
    (body A).getD (3 * o + c) d = (ordRec A o).getD c d := by
  unfold body
  rw [List.getD_append _ _ _ _ (by
    rw [RecList.length_flatMap_const _ 3 (ordRec_length A)]; omega)]
  exact RecList.getD_flatMap_const _ 3 (ordRec_length A) _ _ _ ho hc d

lemma body_pair (i c : ℕ) (hi : i < A.pairs) (hc : c < 4) (d : Tok) :
    (body A).getD (3 * A.ordinary + (4 * i + c)) d = (pairRec A i).getD c d := by
  unfold body
  rw [List.getD_append_right _ _ _ _ (by
    rw [RecList.length_flatMap_const _ 3 (ordRec_length A)]; omega),
    RecList.length_flatMap_const _ 3 (ordRec_length A), Nat.add_sub_cancel_left]
  exact RecList.getD_flatMap_const _ 4 (pairRec_length A) _ _ _ hi hc d

lemma body_kind (j : ℕ) (hj : j < 3 * A.ordinary + 4 * A.pairs) :
    ((body A).getD j (.bit false)).kind = kindAt A.ordinary A.pairs j := by
  unfold kindAt
  by_cases h : j < 3 * A.ordinary
  · rw [if_pos h]
    have e : j = 3 * (j / 3) + j % 3 := by omega
    have ho : j / 3 < A.ordinary := by omega
    rw [e, body_ord A _ _ ho (by omega), ← e]
    unfold ordRec; rw [dif_pos ho]
    have h3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3 <;> simp [h3, Tok.kind]
  · rw [if_neg h, if_pos hj]
    have e : j = 3 * A.ordinary + (4 * ((j - 3 * A.ordinary) / 4) + (j - 3 * A.ordinary) % 4) := by
      omega
    have hi : (j - 3 * A.ordinary) / 4 < A.pairs := by omega
    rw [e, body_pair A _ _ hi (by omega)]
    unfold pairRec; rw [dif_pos hi]
    have h4 : (j - 3 * A.ordinary) % 4 < 4 := by omega
    set c := (j - 3 * A.ordinary) % 4
    rcases c with _ | _ | _ | _ | c <;> simp [Tok.kind]; omega

/-- **The encoding conforms to the format.** -/
theorem conforms_toksOf : Conforms EA (toksOf A) := by
  rw [toksOf_eq]
  constructor
  · intro k hk
    simp only [List.length_cons, body_length] at hk
    rcases k with _ | _ | j
    · rfl
    · rfl
    · simp only [List.getD_cons_succ, List.take_succ_cons, EA_cons]
      rw [List.length_take, body_length, Nat.min_eq_left (by omega)]
      exact body_kind A j (by omega)
  · rw [EA_cons, body_length]; simp [kindAt]

/-! ### From a conforming stream back to an instance -/

/-- The number at position `k`, and `0` for a bit. -/
def numAt (ts : List Tok) (k : ℕ) : ℕ :=
  match ts.getD k (.bit false) with
  | .num v => v
  | .bit _ => 0

/-- The bit at position `k`, and `false` for a number. -/
def bitAt (ts : List Tok) (k : ℕ) : Bool :=
  match ts.getD k (.bit false) with
  | .num _ => false
  | .bit b => b

lemma tok_of_num {t : Tok} (h : t.kind = .num) : t = .num (match t with | .num v => v | .bit _ => 0) := by
  cases t with
  | num v => rfl
  | bit b => exact absurd h (fun h' => Kind.noConfusion h')

lemma tok_of_bit {t : Tok} (h : t.kind = .bit) :
    t = .bit (match t with | .num _ => false | .bit b => b) := by
  cases t with
  | num v => exact absurd h (fun h' => Kind.noConfusion h')
  | bit b => rfl

/-- The instance a stream of tokens describes. -/
def ofToks (ts : List Tok) : AuxiliaryProblem.Instance where
  ordinary := numAt ts 0
  r o := numAt ts (2 + (3 * o + 0))
  d o := numAt ts (2 + (3 * o + 1))
  long o := bitAt ts (2 + (3 * o + 2))
  pairs := numAt ts 1
  longEarly i := numAt ts (2 + (3 * numAt ts 0 + (4 * i + 0)))
  longDue i := numAt ts (2 + (3 * numAt ts 0 + (4 * i + 1)))
  shortEarly i := numAt ts (2 + (3 * numAt ts 0 + (4 * i + 2)))
  shortDue i := numAt ts (2 + (3 * numAt ts 0 + (4 * i + 3)))

lemma numAt_cons2 (a b : Tok) (rest : List Tok) (k : ℕ) :
    numAt (a :: b :: rest) (2 + k) = numAt rest k := by
  unfold numAt; rw [show 2 + k = k + 1 + 1 by ring]; rfl

lemma bitAt_cons2 (a b : Tok) (rest : List Tok) (k : ℕ) :
    bitAt (a :: b :: rest) (2 + k) = bitAt rest k := by
  unfold bitAt; rw [show 2 + k = k + 1 + 1 by ring]; rfl

lemma numAt_of {ts : List Tok} {k v : ℕ} (h : ts.getD k (.bit false) = .num v) :
    numAt ts k = v := by unfold numAt; rw [h]

lemma bitAt_of {ts : List Tok} {k : ℕ} {b : Bool} (h : ts.getD k (.bit false) = .bit b) :
    bitAt ts k = b := by unfold bitAt; rw [h]

lemma kind_ne_done (t : Tok) : t.kind ≠ .done := by cases t <;> simp [Tok.kind]

/-- **A conforming stream is the encoding of the instance it describes.** -/
theorem toksOf_ofToks {ts : List Tok} (hc : Conforms EA ts) : toksOf (ofToks ts) = ts := by
  obtain ⟨hf, hd⟩ := hc
  -- the two counts
  rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [EA] at hd
  · simp [EA] at hd
  have ha : a.kind = .num := by simpa [EA] using hf 0 (by simp)
  have hb : b.kind = .num := by
    have := hf 1 (by simp)
    simpa [EA] using this
  obtain ⟨n, rfl⟩ : ∃ n, a = .num n := ⟨_, tok_of_num ha⟩
  obtain ⟨N, rfl⟩ : ∃ N, b = .num N := ⟨_, tok_of_num hb⟩
  rw [EA_cons] at hd
  -- the length
  have hlen : rest.length = 3 * n + 4 * N := by
    have h1 : ¬ rest.length < 3 * n + 4 * N := by
      intro hlt
      unfold kindAt at hd
      split_ifs at hd
    by_contra hne
    have hk := hf (2 + (3 * n + 4 * N)) (by simp; omega)
    have e : (Tok.num n :: Tok.num N :: rest).take (2 + (3 * n + 4 * N)) =
        .num n :: .num N :: rest.take (3 * n + 4 * N) := by
      rw [show 2 + (3 * n + 4 * N) = (3 * n + 4 * N) + 1 + 1 by ring]; rfl
    rw [e, EA_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
    have : kindAt n N (3 * n + 4 * N) = .done := by simp [kindAt]
    rw [this] at hk
    exact kind_ne_done _ hk
  -- the kinds of the records
  have hkind : ∀ j < 3 * n + 4 * N, (rest.getD j (.bit false)).kind = kindAt n N j := by
    intro j hj
    have hk := hf (j + 2) (by simp; omega)
    have e : (Tok.num n :: Tok.num N :: rest).take (j + 2) = .num n :: .num N :: rest.take j := rfl
    rw [e, EA_cons, List.length_take, Nat.min_eq_left (by omega)] at hk
    simpa using hk
  set A := ofToks (Tok.num n :: Tok.num N :: rest) with hA
  have hAo : A.ordinary = n := rfl
  have hAp : A.pairs = N := rfl
  rw [toksOf_eq, hAo, hAp]
  congr 2
  refine List.ext_getElem (by rw [body_length, hlen, hAo, hAp]) fun j h1 h2 => ?_
  have hj : j < 3 * n + 4 * N := by rw [← hlen]; exact h2
  have hg : (body A).getD j (.bit false) = rest.getD j (.bit false) := by
    have hkj := hkind j hj
    unfold kindAt at hkj
    by_cases h3n : j < 3 * n
    · rw [if_pos h3n] at hkj
      have e : j = 3 * (j / 3) + j % 3 := by omega
      have ho : j / 3 < A.ordinary := by rw [hAo]; omega
      rw [e, body_ord A _ _ ho (by omega), ← e]
      unfold ordRec; rw [dif_pos ho]
      have h3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases h3 with h3 | h3 | h3
      · rw [h3, if_neg (by omega)] at hkj
        obtain ⟨v, hv⟩ : ∃ v, rest.getD j (.bit false) = .num v := ⟨_, tok_of_num hkj⟩
        have hidx : 3 * (j / 3) + 0 = j := by omega
        have : A.r ⟨j / 3, ho⟩ = v := by
          show numAt _ (2 + (3 * (j / 3) + 0)) = v
          rw [numAt_cons2, hidx]; exact numAt_of hv
        rw [hv, h3, this]; rfl
      · rw [h3, if_neg (by omega)] at hkj
        obtain ⟨v, hv⟩ : ∃ v, rest.getD j (.bit false) = .num v := ⟨_, tok_of_num hkj⟩
        have hidx : 3 * (j / 3) + 1 = j := by omega
        have : A.d ⟨j / 3, ho⟩ = v := by
          show numAt _ (2 + (3 * (j / 3) + 1)) = v
          rw [numAt_cons2, hidx]; exact numAt_of hv
        rw [hv, h3, this]; rfl
      · rw [h3, if_pos rfl] at hkj
        obtain ⟨v, hv⟩ : ∃ v, rest.getD j (.bit false) = .bit v := ⟨_, tok_of_bit hkj⟩
        have hidx : 3 * (j / 3) + 2 = j := by omega
        have : A.long ⟨j / 3, ho⟩ = v := by
          show bitAt _ (2 + (3 * (j / 3) + 2)) = v
          rw [bitAt_cons2, hidx]; exact bitAt_of hv
        rw [hv, h3, this]; rfl
    · rw [if_neg h3n, if_pos hj] at hkj
      have e : j = 3 * n + (4 * ((j - 3 * n) / 4) + (j - 3 * n) % 4) := by omega
      have hi : (j - 3 * n) / 4 < A.pairs := by rw [hAp]; omega
      have e' : j = 3 * A.ordinary + (4 * ((j - 3 * n) / 4) + (j - 3 * n) % 4) := by
        rw [hAo]; exact e
      rw [e', body_pair A _ _ hi (by omega), ← e']
      unfold pairRec; rw [dif_pos hi]
      obtain ⟨v, hv⟩ : ∃ v, rest.getD j (.bit false) = .num v := ⟨_, tok_of_num hkj⟩
      have hnum : ∀ c, (j - 3 * n) % 4 = c →
          numAt (Tok.num n :: Tok.num N :: rest) (2 + (3 * n + (4 * ((j - 3 * n) / 4) + c))) = v := by
        intro c hc
        rw [numAt_cons2, ← hc, ← e]; exact numAt_of hv
      have h4 : (j - 3 * n) % 4 = 0 ∨ (j - 3 * n) % 4 = 1 ∨ (j - 3 * n) % 4 = 2 ∨
          (j - 3 * n) % 4 = 3 := by omega
      rw [hv]
      rcases h4 with h4 | h4 | h4 | h4
      · have : A.longEarly ⟨(j - 3 * n) / 4, hi⟩ = v := hnum 0 h4
        rw [h4, this]; rfl
      · have : A.longDue ⟨(j - 3 * n) / 4, hi⟩ = v := hnum 1 h4
        rw [h4, this]; rfl
      · have : A.shortEarly ⟨(j - 3 * n) / 4, hi⟩ = v := hnum 2 h4
        rw [h4, this]; rfl
      · have : A.shortDue ⟨(j - 3 * n) / 4, hi⟩ = v := hnum 3 h4
        rw [h4, this]; rfl
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hg
  exact hg

open Lax391470Proofs.TokScan Lax434930.PolynomialTime in
/-- **The scan decodes instances of the auxiliary problem**: a word is an encoding exactly
when the scan accepts it, and then it encodes the instance read off the tokens. -/
theorem decode_iff (w : Word) :
    (Accepts EA (run EA init w) → encodeAux (ofToks (run EA init w).toks) = w) ∧
    (∀ A, encodeAux A = w → Accepts EA (run EA init w) ∧ A = ofToks (run EA init w).toks) := by
  constructor
  · intro h
    obtain ⟨hcode, hconf⟩ := accept_sound EA h
    rw [encodeAux_eq, toksOf_ofToks hconf, hcode]
  · intro A hA
    have hc := accept_complete EA (toksOf A) (conforms_toksOf A)
    rw [← encodeAux_eq, hA] at hc
    refine ⟨hc.1, Lax391470Proofs.Encoding.encodeAux_injective ?_⟩
    obtain ⟨hcode, hconf⟩ := accept_sound EA hc.1
    rw [hA, encodeAux_eq (ofToks _), toksOf_ofToks hconf, hcode]

end Lax391470Proofs.AuxFormat
