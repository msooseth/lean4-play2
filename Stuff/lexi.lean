import Mathlib

inductive Expr : Type where
  | Val : Int -> Expr
  | Add : Expr -> Expr -> Expr

-- need: eval

/- def eval : Expr -> Int -/
/- | .Val a => sorry -/   
/- | _ => sorry -/
open Expr

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

