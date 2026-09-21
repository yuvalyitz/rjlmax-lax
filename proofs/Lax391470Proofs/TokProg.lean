import Lax391470Proofs.TokScan
import Lax391470Proofs.ReadAll

/-!
The tokenizer as an IMP+ loop. The format enters through one command, `nk`, which sets the
scalar `kind` to the code of what the format expects after the tokens read so far.
-/

namespace Lax391470Proofs.TokProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax391470Proofs.TokModel Lax391470Proofs.TokScan

abbrev V (s : String) : Expr := .var s
abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev bump (s : String) : Com := .assign s (add (V s) (.lit 1))
abbrev set (s : String) (n : ℕ) : Com := .assign s (.lit n)

/-- The number a token is stored as. -/
def Tok.val : Tok → ℕ
  | .num v => v
  | .bit b => if b then 1 else 0

/-- The code of a kind. -/
def kcode : Kind → ℕ
  | .num => 0
  | .bit => 1
  | .done => 2

/-- The token array reflects the tokens read. -/
def TokRefl (toks : List Tok) (σ : Env) : Prop :=
  σ.vars "T" = toks.length ∧ (σ.arrs "TK").take toks.length = toks.map Tok.val

/-- The scalars and arrays the scan owns; the format's command must leave them alone. -/
def scanVars : List String := ["ph", "L", "val", "pw", "i", "T", "p", "c", "Ln"]

/-- What is asked of the format's command. -/
def NkSpec (B Bt : ℕ) (E : Format) (cap : ℕ) (nk : Com) (Knk : ℕ) : Prop :=
  ∀ toks : List Tok, Follows E toks → toks.length ≤ cap →
    Spec B (fun σ => TokRefl toks σ ∧ ∀ t ∈ toks, Tok.val t < Bt) nk
      (fun σ σ' => σ'.vars "kind" = kcode (E toks) ∧
        (∀ y ∈ scanVars, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        σ'.inp = σ.inp) Knk

variable (nk : Com)

/-- Append the token whose value is in `tv`, and ask the format what comes next. -/
def put : Com := .seq (.store "TK" (V "T") (V "tv")) (.seq (bump "T") nk)

variable {B Bt : ℕ} {E : Format} {cap Knk : ℕ}

lemma take_set_succ (l : List ℕ) (k v : ℕ) (hk : k < l.length) :
    (l.set k v).take (k + 1) = l.take k ++ [v] := by
  rw [List.take_add_one, List.take_set_of_le (le_refl k)]
  simp [hk]

/-- **Appending a token.** -/
theorem put_spec (hnk : NkSpec B Bt E cap nk Knk) (toks : List Tok) (t : Tok)
    (hfol : Follows E (toks ++ [t])) (hcap : toks.length + 1 ≤ cap)
    (hvals : ∀ u ∈ toks ++ [t], Tok.val u < Bt) (hBt : Bt ≤ B) (hTB : toks.length + 1 < B) :
    Spec B (fun σ => TokRefl toks σ ∧ σ.vars "tv" = Tok.val t ∧
        toks.length < (σ.arrs "TK").length) (put nk)
      (fun σ σ' => TokRefl (toks ++ [t]) σ' ∧ σ'.vars "kind" = kcode (E (toks ++ [t])) ∧
        (∀ y ∈ scanVars, y ≠ "T" → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "TK" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
        (σ'.arrs "TK").length = (σ.arrs "TK").length)
      (20 + Knk) := by
  intro σ ⟨⟨hT, hTK⟩, htv, hlen⟩
  have hv : Tok.val t < B := lt_of_lt_of_le (hvals t (by simp)) hBt
  have r1 : Run B (.store "TK" (V "T") (V "tv")) σ (σ.setArr "TK" (σ.vars "T") (σ.vars "tv"))
      (1 + (V "T").size + (V "tv").size) :=
    Run.store (evalB_var (by rw [hT]; omega)) (evalB_var (by rw [htv]; exact hv))
      (by rw [hT]; exact hlen)
  set σ1 := σ.setArr "TK" (σ.vars "T") (σ.vars "tv") with h1
  have r2 : Run B (bump "T") σ1 (σ1.setVar "T" (σ1.vars "T" + 1)) (1 + (add (V "T") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by simp [h1, Env.setArr, hT]; omega))
      (evalB_lit (by omega)) (by simp [h1, Env.setArr, hT]; omega))
  set σ2 := σ1.setVar "T" (σ1.vars "T" + 1) with h2
  have hrefl2 : TokRefl (toks ++ [t]) σ2 := by
    refine ⟨by simp [h2, h1, Env.setVar, Env.setArr, hT], ?_⟩
    simp only [h2, h1, Env.setVar, Env.setArr, List.length_append, List.length_singleton,
      if_true, hT, htv]
    rw [take_set_succ _ _ _ hlen, hTK]; simp
  obtain ⟨σ3, r3, hk, hfv, hfa, hfo, hfi⟩ := hnk (toks ++ [t]) hfol (by simpa using hcap) σ2
    ⟨hrefl2, hvals⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]; omega), ?_, hk, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q1, q2⟩ := hrefl2
    exact ⟨by rw [hfv "T" (by simp [scanVars])]; exact q1, by rw [hfa]; exact q2⟩
  · intro y hy hne
    rw [hfv y hy]; simp [h2, h1, Env.setVar, Env.setArr, hne]
  · intro a ha
    rw [hfa]; simp [h2, h1, Env.setVar, Env.setArr, ha]
  · rw [hfo]; rfl
  · rw [hfi]; rfl
  · rw [hfa]; simp [h2, h1, Env.setVar, Env.setArr]

/-! ### The state of the scan, reflected -/

variable (E)

structure Refl (s : St) (σ : Env) : Prop where
  ph : σ.vars "ph" = s.ph
  L : σ.vars "L" = s.L
  val : σ.vars "val" = s.val
  pw : σ.vars "pw" = s.pw
  i : σ.vars "i" = s.dg.length
  tok : TokRefl s.toks σ
  kind : σ.vars "kind" = kcode (E s.toks)

/-- What a step leaves alone. -/
def Frame (σ σ' : Env) : Prop :=
  σ'.vars "p" = σ.vars "p" ∧ σ'.vars "Ln" = σ.vars "Ln" ∧ σ'.vars "c" = σ.vars "c" ∧
    (∀ b, b ≠ "TK" → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
    (σ'.arrs "TK").length = (σ.arrs "TK").length

variable {E}

lemma kcode_done {k : Kind} : kcode k = 2 ↔ k = .done := by cases k <;> simp [kcode]

/-- The values of the tokens of a state are small. -/
def Small (Bt : ℕ) (s : St) : Prop := ∀ t ∈ s.toks, Tok.val t < Bt

/-- **Appending a token, as a step of the scan**: if the model's step appends `t` and
changes nothing else, `tv := e; put` realises it. -/
theorem putStep_spec (hnk : NkSpec B Bt E cap nk Knk) (s s' : St) (t : Tok) (e : Expr)
    (hs' : s' = { s with toks := s.toks ++ [t] })
    (hfol : Follows E (s.toks ++ [t])) (hcap : s.toks.length + 1 ≤ cap)
    (hsmall : Small Bt s) (htB : Tok.val t < Bt) (hBt : Bt ≤ B) (hTB : s.toks.length + 1 < B) :
    Spec B (fun σ => Refl E s σ ∧ e.evalB B σ = some (Tok.val t) ∧
        s.toks.length < (σ.arrs "TK").length)
      (.seq (.assign "tv" e) (put nk))
      (fun σ σ' => Refl E s' σ' ∧ Frame σ σ') (1 + e.size + (20 + Knk)) := by
  intro σ ⟨hR, hev, hlen⟩
  have r1 : Run B (.assign "tv" e) σ (σ.setVar "tv" (Tok.val t)) (1 + e.size) := Run.assign hev
  obtain ⟨σ2, r2, hrefl, hk, hfv, hfa, hfo, hfi, hfl⟩ :=
    put_spec nk hnk s.toks t hfol hcap (by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hsmall u h
      · simp at h; rw [h]; exact htB) hBt hTB (σ.setVar "tv" (Tok.val t))
      ⟨⟨by simpa [Env.setVar] using hR.tok.1, by simpa [Env.setVar] using hR.tok.2⟩,
        by simp [Env.setVar], by simpa [Env.setVar] using hlen⟩
  have hv : ∀ y ∈ scanVars, y ≠ "T" → σ2.vars y = σ.vars y := fun y hy hne => by
    rw [hfv y hy hne]
    have : y ≠ "tv" := by
      intro h; rw [h] at hy; simp [scanVars] at hy
    simp [Env.setVar, this]
  refine ⟨σ2, r1.seq r2, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hv "ph" (by simp [scanVars]) (by decide), hR.ph, hs']
  · rw [hv "L" (by simp [scanVars]) (by decide), hR.L, hs']
  · rw [hv "val" (by simp [scanVars]) (by decide), hR.val, hs']
  · rw [hv "pw" (by simp [scanVars]) (by decide), hR.pw, hs']
  · rw [hv "i" (by simp [scanVars]) (by decide), hR.i, hs']
  · rw [hs']; exact hrefl
  · rw [hs']; exact hk
  · exact ⟨hv "p" (by simp [scanVars]) (by decide), hv "Ln" (by simp [scanVars]) (by decide),
      hv "c" (by simp [scanVars]) (by decide), fun b hb => by rw [hfa b hb]; rfl,
      by rw [hfo]; rfl, by rw [hfi]; rfl, by rw [hfl]; rfl⟩

/-- Back to a token boundary. -/
def reset : Com :=
  .seq (set "ph" 0) (.seq (set "L" 0) (.seq (set "val" 0) (.seq (set "pw" 1) (set "i" 0))))

theorem reset_spec (hB : 2 < B) :
    Spec B (fun _ => True) reset
      (fun σ σ' => σ'.vars "ph" = 0 ∧ σ'.vars "L" = 0 ∧ σ'.vars "val" = 0 ∧ σ'.vars "pw" = 1 ∧
        σ'.vars "i" = 0 ∧ (∀ y ∉ ["ph", "L", "val", "pw", "i"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 12 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2]

/-- **Completing a number.** -/
theorem putNum_spec (hnk : NkSpec B Bt E cap nk Knk) (s : St) (hB : 2 < B)
    (hfol : Follows E (s.toks ++ [.num (s.val + s.pw)])) (hcap : s.toks.length + 1 ≤ cap)
    (hsmall : Small Bt s) (hvB : s.val + s.pw < Bt) (hBt : Bt ≤ B) (hTB : s.toks.length + 1 < B) :
    Spec B (fun σ => Refl E s σ ∧ s.toks.length < (σ.arrs "TK").length)
      (.seq (.assign "tv" (add (V "val") (V "pw"))) (.seq reset (put nk)))
      (fun σ σ' => Refl E ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ σ' ∧ Frame σ σ')
      (4 + (12 + (20 + Knk))) := by
  intro σ ⟨hR, hlen⟩
  have r1 : Run B (.assign "tv" (add (V "val") (V "pw"))) σ (σ.setVar "tv" (s.val + s.pw))
      (1 + (add (V "val") (V "pw")).size) := by
    have := Run.assign (B := B) (σ := σ) (x := "tv") (e := add (V "val") (V "pw"))
      (v := s.val + s.pw) (by
        have h := evalB_bin (op := .add) (evalB_var (x := "val") (σ := σ) (B := B)
          (by rw [hR.val]; omega)) (evalB_var (x := "pw") (σ := σ) (B := B) (by rw [hR.pw]; omega))
          (by simp [hR.val, hR.pw]; omega)
        simpa [hR.val, hR.pw] using h)
    exact this
  set σ1 := σ.setVar "tv" (s.val + s.pw) with h1
  obtain ⟨σ2, r2, q1, q2, q3, q4, q5, qv, qa, qo, qi⟩ := reset_spec (B := B) hB σ1 trivial
  obtain ⟨σ3, r3, hrefl, hk, hfv, hfa, hfo, hfi, hfl⟩ :=
    put_spec nk hnk s.toks (.num (s.val + s.pw)) hfol hcap (by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hsmall u h
      · simp at h; rw [h]; exact hvB) hBt hTB σ2
      ⟨⟨by rw [qv "T" (by decide)]; simpa [h1, Env.setVar] using hR.tok.1,
        by rw [qa]; simpa [h1, Env.setVar] using hR.tok.2⟩,
        by rw [qv "tv" (by decide)]; simp [h1, Env.setVar, Tok.val],
        by rw [qa]; simpa [h1, Env.setVar] using hlen⟩
  have hv : ∀ y ∈ scanVars, y ≠ "T" → σ3.vars y = σ2.vars y := hfv
  have hv0 : ∀ y, y ∉ ["ph", "L", "val", "pw", "i"] → y ≠ "tv" → σ2.vars y = σ.vars y :=
    fun y h1' h2' => by rw [qv y h1']; simp [h1, Env.setVar, h2']
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]), ⟨?_, ?_, ?_, ?_, ?_, hrefl, hk⟩, ?_⟩
  · rw [hv "ph" (by simp [scanVars]) (by decide), q1]
  · rw [hv "L" (by simp [scanVars]) (by decide), q2]
  · rw [hv "val" (by simp [scanVars]) (by decide), q3]
  · rw [hv "pw" (by simp [scanVars]) (by decide), q4]
  · rw [hv "i" (by simp [scanVars]) (by decide), q5]; rfl
  · exact ⟨by rw [hv "p" (by simp [scanVars]) (by decide), hv0 "p" (by decide) (by decide)],
      by rw [hv "Ln" (by simp [scanVars]) (by decide), hv0 "Ln" (by decide) (by decide)],
      by rw [hv "c" (by simp [scanVars]) (by decide), hv0 "c" (by decide) (by decide)],
      fun b hb => by rw [hfa b hb, qa]; rfl, by rw [hfo, qo]; rfl, by rw [hfi, qi]; rfl,
      by rw [hfl, qa]; rfl⟩

/-! ### Conditionals whose outcome is known -/

theorem ite_true_spec {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some true) (h : Spec B P c Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) := by
  intro σ hσ
  obtain ⟨σ', r, q⟩ := h σ hσ
  exact ⟨σ', Run.ite_true (hb σ hσ) r, q⟩

theorem ite_false_spec {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some false) (h : Spec B P d Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) := by
  intro σ hσ
  obtain ⟨σ', r, q⟩ := h σ hσ
  exact ⟨σ', Run.ite_false (hb σ hσ) r, q⟩

lemma eval_eq_lit {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x < B) (hn : n < B) :
    (Cond.eq (V x) (.lit n)).evalB B σ = some (σ.vars x == n) :=
  evalB_condEq (evalB_var hx) (evalB_lit hn)

/-! ### The steps that only touch scalars -/

variable (E)

/-- What the scan knows at the start of a step on the bit `b`. -/
structure Pre (s : St) (b : Bool) (σ : Env) : Prop where
  refl : Refl E s σ
  cbit : σ.vars "c" = if b then 1 else 0
  room : s.toks.length < (σ.arrs "TK").length

variable {E}

theorem dead_spec (s : St) (b : Bool) (hB : 2 < B) :
    Spec B (Pre E s b) (set "ph" 2) (fun σ σ' => Refl E (dead s) σ' ∧ Frame σ σ') 2 := by
  run_vcg
  · obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
    obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar, dead]

theorem ones_spec (s : St) (b : Bool) (hLB : s.L + 1 < B) :
    Spec B (Pre E s b) (bump "L") (fun σ σ' => Refl E { s with L := s.L + 1 } σ' ∧ Frame σ σ')
      4 := by
  run_vcg
  all_goals obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar]
  all_goals first | omega

def startDigits : Com :=
  .seq (set "ph" 1) (.seq (set "val" 0) (.seq (set "pw" 1) (set "i" 0)))

theorem startDigits_spec (s : St) (b : Bool) (hB : 2 < B) :
    Spec B (Pre E s b) startDigits
      (fun σ σ' => Refl E { s with ph := 1, val := 0, pw := 1, dg := [] } σ' ∧ Frame σ σ') 8 := by
  run_vcg
  all_goals obtain ⟨hR, -, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all [Env.setVar]

/-- The model state after one more digit. -/
def digSt (s : St) (b : Bool) : St :=
  ⟨s.ph, s.L, s.val + (if b then s.pw else 0), 2 * s.pw, s.dg ++ [b], s.toks⟩

/-- One more digit, not the last. -/
def digit : Com :=
  .seq (.ite (.eq (V "c") (.lit 0)) .skip (.assign "val" (add (V "val") (V "pw"))))
    (.seq (.assign "pw" (.bin .mul (.lit 2) (V "pw"))) (bump "i"))

theorem digit_spec (s : St) (b : Bool) (hB : 2 < B) (hv : s.val + s.pw < B) (hp : 2 * s.pw < B)
    (hi : s.dg.length + 1 < B) :
    Spec B (Pre E s b) digit
      (fun σ σ' => Refl E (digSt s b) σ' ∧ Frame σ σ') 16 := by
  run_vcg
  all_goals obtain ⟨hR, hc, -⟩ := ‹Pre E s b σ›
  all_goals obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7⟩, h8⟩ := hR
  all_goals try simp only [Env.setVar] at *
  all_goals try (
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      cases b <;> simp_all [digSt])
  all_goals try simp
  all_goals (rw [h3, h4, h5] at *)
  all_goals first
    | omega
    | (cases b <;> simp_all <;> omega)

lemma cond_lit_true {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x = n) (hn : n < B) :
    (Cond.eq (V x) (.lit n)).evalB B σ = some true := by
  rw [eval_eq_lit (by rw [hx]; exact hn) hn, hx]; simp

lemma cond_lit_false {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x ≠ n) (hxB : σ.vars x < B)
    (hn : n < B) : (Cond.eq (V x) (.lit n)).evalB B σ = some false := by
  rw [eval_eq_lit hxB hn]; simp [hx]

/-! ### One step of the scan -/

def dispatch : Com :=
  .ite (.eq (V "ph") (.lit 0))
    (.ite (.eq (V "kind") (.lit 2)) (set "ph" 2)
      (.ite (.eq (V "kind") (.lit 1))
        (.ite (.eq (V "L") (.lit 0)) (.seq (.assign "tv" (V "c")) (put nk)) (set "ph" 2))
        (.ite (.eq (V "c") (.lit 0))
          (.ite (.eq (V "L") (.lit 0)) (.seq (.assign "tv" (.lit 0)) (put nk)) startDigits)
          (bump "L"))))
    (.ite (.eq (V "ph") (.lit 1))
      (.ite (.eq (add (V "i") (.lit 1)) (V "L"))
        (.ite (.eq (V "c") (.lit 0)) (set "ph" 2)
          (.seq (.assign "tv" (add (V "val") (V "pw"))) (.seq reset (put nk))))
        digit)
      (set "ph" 2))

/-- The numeric facts a step needs. -/
structure StepB (B Bt cap : ℕ) (s : St) : Prop where
  hB : 4 < B
  hBt : Bt ≤ B
  bt : 2 ≤ Bt
  vt : s.val + s.pw < Bt
  ph : s.ph < B
  L : s.L + 1 < B
  i : s.dg.length + 1 < B
  v : s.val + s.pw < B
  p : 2 * s.pw < B
  T : s.toks.length + 1 < B
  cap : s.toks.length + 1 ≤ cap
  small : Small Bt s

theorem dispatch_spec (hnk : NkSpec B Bt E cap nk Knk) (s : St) (b : Bool) (hb : StepB B Bt cap s)
    (hfol' : s.ph ≤ 1 → Follows E s.toks) (hnum : s.ph = 1 → E s.toks = .num) :
    Spec B (Pre E s b) (dispatch nk) (fun σ σ' => Refl E (step E s b) σ' ∧ Frame σ σ')
      (80 + Knk) := by
  have hB := hb.hB
  have kc : ∀ σ, Pre E s b σ → σ.vars "kind" = kcode (E s.toks) := fun σ h => h.refl.kind
  have kB : kcode (E s.toks) < B := by cases E s.toks <;> simp [kcode] <;> omega
  have cB : ∀ σ, Pre E s b σ → σ.vars "c" < B := fun σ h => by
    rw [h.cbit]; cases b <;> simp <;> omega
  by_cases h0 : s.ph = 0
  · have hfol := hfol' (by omega)
    rcases hE : E s.toks with _ | _ | _
    · -- a number is expected
      cases b
      · by_cases hL : s.L = 0
        · have hst : step E s false = { s with toks := s.toks ++ [.num 0] } := by
            simp [step, h0, hE, hL]
          refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                  (by rw [kc σ h]; exact kB) (by omega))
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  (ite_true_spec (fun σ h => cond_lit_true (h.refl.L.trans hL) (by omega))
                    ((putStep_spec nk hnk s (step E s false) (.num 0) (.lit 0) hst
                      (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small
                      (by have := hb.bt; simp [Tok.val]; omega) hb.hBt hb.T).pre
                      (fun σ h => ⟨h.refl, evalB_lit (by omega), h.room⟩)))))))
            (by simp [Cond.size, Expr.size]; omega)
        · have hst : step E s false = { s with ph := 1, val := 0, pw := 1, dg := [] } := by
            simp [step, h0, hE, hL]
          refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                  (by rw [kc σ h]; exact kB) (by omega))
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.L]; exact hL)
                      (by rw [h.refl.L]; have := hb.L; omega) (by omega))
                    ((startDigits_spec s false (by omega)).post
                      (fun σ σ' _ h => by rw [hst]; exact h)))))))
            (by simp [Cond.size, Expr.size]; omega)
      · have hst : step E s true = { s with L := s.L + 1 } := by simp [step, h0, hE]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
                (by rw [kc σ h]; exact kB) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [h.cbit]; decide)
                  (cB σ h) (by omega))
                ((ones_spec s true hb.L).post (fun σ σ' _ h => by rw [hst]; exact h))))))
          (by simp [Cond.size, Expr.size]; omega)
    · -- a raw bit is expected
      by_cases hL : s.L = 0
      · have hst : step E s b = { s with toks := s.toks ++ [.bit b] } := by
          simp [step, h0, hE, hL]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
              (ite_true_spec (fun σ h => cond_lit_true (h.refl.L.trans hL) (by omega))
                ((putStep_spec nk hnk s (step E s b) (.bit b) (V "c") hst
                  (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small
                  (by have := hb.bt; cases b <;> simp [Tok.val] <;> omega) hb.hBt hb.T).pre
                  (fun σ h => ⟨h.refl, by
                    have := evalB_var (B := B) (x := "c") (σ := σ) (cB σ h)
                    rw [this, h.cbit]; rfl, h.room⟩))))))
          (by simp [Cond.size, Expr.size]; omega)
      · have hst : step E s b = dead s := by simp [step, h0, hE, hL]
        refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
          (ite_false_spec (fun σ h => cond_lit_false (by rw [kc σ h, hE]; decide)
              (by rw [kc σ h]; exact kB) (by omega))
            (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
              (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.L]; exact hL)
                  (by rw [h.refl.L]; have := hb.L; omega) (by omega))
                ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))))
          (by simp [Cond.size, Expr.size]; omega)
    · -- nothing more is expected
      have hst : step E s b = dead s := by simp [step, h0, hE]
      refine Spec.mono (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h0) (by omega))
        (ite_true_spec (fun σ h => cond_lit_true (by rw [kc σ h, hE]; rfl) (by omega))
          ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))
        (by simp [Cond.size, Expr.size]; omega)
  · have hph0 : ∀ σ, Pre E s b σ → (Cond.eq (V "ph") (.lit 0)).evalB B σ = some false :=
      fun σ h => cond_lit_false (by rw [h.refl.ph]; exact h0) (by rw [h.refl.ph]; exact hb.ph)
        (by omega)
    by_cases h1 : s.ph = 1
    · have hfol := hfol' (by omega)
      have hE := hnum h1
      have hcond : ∀ σ, Pre E s b σ →
          (Cond.eq (add (V "i") (.lit 1)) (V "L")).evalB B σ =
            some (decide (s.dg.length + 1 = s.L)) := fun σ h => by
        have e1 := evalB_bin (op := .add) (evalB_var (x := "i") (σ := σ) (B := B)
          (by rw [h.refl.i]; have := hb.i; omega)) (evalB_lit (B := B) (σ := σ) (n := 1) (by omega))
          (by simp [h.refl.i]; exact hb.i)
        have e2 := evalB_var (B := B) (x := "L") (σ := σ) (by rw [h.refl.L]; have := hb.L; omega)
        rw [evalB_condEq e1 e2]
        simp only [Bop.apply_add, h.refl.i, h.refl.L]
        congr 1
      by_cases hlast : s.dg.length + 1 = s.L
      · cases b
        · have hst : step E s false = dead s := by simp [step, h1, hlast]
          refine Spec.mono (ite_false_spec hph0
            (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
              (ite_true_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
                (ite_true_spec (fun σ h => cond_lit_true (by rw [h.cbit]; rfl) (by omega))
                  ((dead_spec s false (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))))
            (by simp [Cond.size, Expr.size]; omega)
        · have hst : step E s true = ⟨0, 0, 0, 1, [], s.toks ++ [.num (s.val + s.pw)]⟩ := by
            simp [step, h1, hlast]
          refine Spec.mono (ite_false_spec hph0
            (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
              (ite_true_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
                (ite_false_spec (fun σ h => cond_lit_false (by rw [h.cbit]; decide) (cB σ h)
                    (by omega))
                  (((putNum_spec nk hnk s (by omega)
                    (follows_snoc E hfol (by simp [Tok.kind, hE])) hb.cap hb.small hb.vt hb.hBt hb.T).pre
                    (fun σ h => ⟨h.refl, h.room⟩)).post
                    (fun σ σ' _ h => by rw [hst]; exact h))))))
            (by simp [Cond.size, Expr.size]; omega)
      · have hst : step E s b = digSt s b := by simp [step, h1, hlast, digSt]
        refine Spec.mono (ite_false_spec hph0
          (ite_true_spec (fun σ h => cond_lit_true (h.refl.ph.trans h1) (by omega))
            (ite_false_spec (fun σ h => by rw [hcond σ h]; simp [hlast])
              ((digit_spec s b (by omega) hb.v hb.p hb.i).post
                (fun σ σ' _ h => by rw [hst]; exact h)))))
          (by simp [Cond.size, Expr.size]; omega)
    · have hst : step E s b = dead s := by
        obtain ⟨ph, L, val, pw, dg, toks⟩ := s
        simp only at h0 h1
        match ph, h0, h1 with
        | k + 2, _, _ => simp [step]
      refine Spec.mono (ite_false_spec hph0
        (ite_false_spec (fun σ h => cond_lit_false (by rw [h.refl.ph]; exact h1)
            (by rw [h.refl.ph]; exact hb.ph) (by omega))
          ((dead_spec s b (by omega)).post (fun σ σ' _ h => by rw [hst]; exact h))))
        (by simp [Cond.size, Expr.size]; omega)

end Lax391470Proofs.TokProg
