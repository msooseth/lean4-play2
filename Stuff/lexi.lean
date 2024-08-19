import Mathlib

inductive Expr : Type where
| Val : Int -> Expr
| Add : Expr -> Expr -> Expr
deriving Repr, DecidableEq

open Expr

namespace denotational

@[simp]
def eval (e : Expr) : Int := match e with
| .Val a => a
| .Add a b => (eval a) + (eval b)

#eval eval (.Add (.Val 5) (.Val 3))

theorem eval_refl (a b x y: Expr) (ha : eval a = eval x) (hb : eval b = eval y) 
  : eval (Add a b) = eval (Add x y) := by 
    unfold eval
    rw [ha]
    rw [hb]
    
theorem eval_total : ∀ x : Expr, ∃ v : Int, eval x = v := by
  intro x
  induction x with
  | Val a => exact Exists.intro a (by unfold eval; rfl)
  | Add x y ihx ihy => match ihx with
    | ⟨vx, ihvx⟩ => match ihy with
      | ⟨vy, ihvy⟩ => 
        have h : eval (Add x y) = vx + vy := by 
          unfold eval
          rw [ihvx]
          rw [ihvy]
        exact Exists.intro (vx + vy) h

end denotational

namespace smallstep

-- apply a single step
def trans (e : Expr) : List Expr := match e with
| .Val _ => []
| .Add (Val a) (Val b) => [Val (a + b)]
| .Add a b => (trans a).map (λ a' => Add a' b) ++ (trans b).map (λ b' => Add a b')

inductive Tree where
| Node : Expr → List Tree → Tree

def nAdds : (e : Expr) → Nat 
| .Val _ => 0
| .Add a b => 1 + nAdds a + nAdds b

def exec (e : Expr) : Tree := match e with
| .Val a => .Node e []
| .Add l r => 
  have term (a : Expr) (b : Expr) : nAdds a < nAdds (Add a b) := by sorry 
  .Node e [exec l, exec r]
termination_by (nAdds e)
      

#eval trans (.Add (.Add (.Val 3) (.Val 2)) (.Add (.Val 4) (.Val 5)))

theorem confluent (e : Expr) (i j : Nat) (hi: i < (trans e).length) (hj : j < (trans e).length) : (trans e)[i] = (trans e)[j] := sorry

end smallstep
