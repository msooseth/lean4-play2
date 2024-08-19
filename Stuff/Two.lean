import Mathlib

example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := by
  exact show p ∧ q from And.intro H_p H_q

example {p q : Prop} (H_p : p) (H_q : q) : (p ∧ q) := by
  constructor
  case left =>
    exact show p from H_p
  case right =>
    exact show q from H_q

example {p q : Prop} (H_pq : p ∧ q) : p := by
  exact show p from And.left H_pq

example {p q : Prop} (H_pq : p ∧ q) : p := by
  cases' H_pq with H_p H_q -- p, q
  exact show p from H_p

example {p q : Prop} (H_p : p) : (p ∨ q) := by
  exact show p ∨ q from Or.intro_left q H_p

example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := by
  exact show r from Or.elim H_pq H_pr H_qr

example {p q r : Prop} (H_pr : p → r) (H_qr : q → r) (H_pq : p ∨ q) : r := by
  cases' H_pq with H_p H_q
  case inl =>
    -- Assume p, apply modus ponens with H_pr
    exact show r from H_pr H_p
  case inr =>
    -- Assume q, apply modus ponens with H_qr
    exact show r from H_qr H_q

axiom LEM {p : Prop}: p ∨ ¬ p

example {p: Prop} (H_nnp : ¬¬p) : p := by
  have H_LEM : p ∨ ¬p := LEM

  -- Assuming ¬p derive p
  have H_np2p : ¬p → p := by
    intro (H_np : ¬p)
    -- ¬p and ¬¬p are a direct contradiction
    have H_false : False := H_nnp H_np
    -- Derive our goal from a falsity
    exact show p from False.elim H_false

  -- Assuming p derive p
  have H_p2p : p → p := by
    intro (H_p : p)
    exact show p from H_p

  -- By proof by cases, we derive p
  exact show p from Or.elim H_LEM H_p2p H_np2p

#check Classical.em

lemma negation_intro {p q : Prop} (H_pq : p → q) (H_pnq : p → ¬q) : ¬p := by
  have H_LEM : p ∨ ¬p := LEM

  -- Assuming ¬p derive ¬p
  have H_npp : ¬p → ¬p := by
    intro (H_np : ¬p)
    exact show ¬p from H_np

  -- Assuming p derive ¬p
  have H_pp : p → ¬p := by
    -- Use hypotheses to obtain q and ¬q
    intro (H_p : p)
    have H_q : q := H_pq H_p
    have H_nq : ¬q := H_pnq H_p

    -- We can derive falsity from a direct contradiction
    have H_false : False := H_nq H_q

    -- You can derive anything from false
    /- have H_UNUSED: p ∧ ¬p := False.elim H_false -/

    -- Including what we want, ¬p
    exact show ¬p from False.elim H_false

  -- By proof by cases, we derive ¬p
  exact show ¬p from Or.elim H_LEM H_pp H_npp

#print axioms negation_intro

example {p q : Prop} (H_pq : p → q) (H_pnq : p → ¬q) : ¬p := by
  have H_LEM : p ∨ ¬p := LEM
  cases' H_LEM with H_p H_np

  case inl =>
    have H_q : q := H_pq H_p
    have H_nq : ¬q := H_pnq H_p
    have H_false : False := H_nq H_q
    exact show ¬p from False.elim H_false

  case inr =>
    exact show ¬p from H_np

example {α : Type} {P : α → Prop} {y : α} (H : ∀ x : α,  P x) : P y := by
  exact show P y from H y

example {α : Type} {P Q R : α → Prop} (H_pq : ∀ x : α, P x → Q x) (H_qr : ∀ x : α, Q x → R x) : ∀ x : α, P x → R x := by
  intro (y: α)
  have H_pqx : P y → Q y := H_pq y
  have H_qrx : Q y → R y := H_qr y
  intro (H_py : P y)
  have H_qy : Q y := H_pqx H_py
  exact show R y from H_qrx H_qy

example {α : Type} {p : α → Prop} {b : Prop} (H_epx : ∃ x, p x) (H_pab : ∀ (a : α), p a → b) : b := by
  exact show b from Exists.elim H_epx H_pab

def a₁ : ℕ := 1
def a₂ : ℕ := 2
#check a₁
#eval a₁

inductive CustomList (T : Type) where
| cnil : CustomList T
| ccons (_ : T) (_ : CustomList T) : CustomList T -- parameters: hd, tl, return type: CustomList T

open CustomList

def clength {α : Type} : (CustomList α) → Nat
  | cnil => 0
  | (ccons _ as) => 1 + clength as

