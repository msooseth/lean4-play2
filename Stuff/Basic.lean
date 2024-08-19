import Mathlib

-- Define namespace, which is natural numbers in this case
/- open Nat -/
def hello := "world"

namespace numerals

inductive nat : Type where 
  | zero : nat
  | succ : nat → nat

def add (a : nat) (b : nat) : nat := match b with
  | nat.succ x => nat.succ (add a x)
  | nat.zero => a

/- def pred (a : nat) : nat := match a with -/
/-     | nat.succ x => x -/
/-     | nat.zero => nat.zero -/

-- Let's prove a+0 = a (right identity)
theorem right_identity : ∀ x, add x nat.zero = x := by
  intro x
  unfold add
  rfl

theorem left_identity: ∀ x, add nat.zero x = x := by
  intro x
  induction x with
  | zero => unfold add; simp
  | succ z ih =>
    unfold add
    simp
    apply ih

/- constant and: Prop -> Prop -> Prop -/

/- theorem s_injectivity: ∀ x y, nat.succ x = nat.succ y → x = y := by -/
/-   intro x y h -/
/-   induction -/

-- Let's prove commutativity

end numerals

#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
/- #check Implies -- Prop → Prop → Prop -/

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
/- #check Implies (And p q) (And q p)  -- Prop -/

/- def double (x : Nat) : Nat := x + x -/
/- #check double 4 -/
/- #eval double 4 -/
#eval 4 + 4
def myadd := fun (x: Nat) => x + x
#eval myadd 4

def foo := let a := Nat; fun x : a => x + 2

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice
#check List.cons
def foo2 := List.cons 1 [2, 3, 4]
#print foo2

#check @List.cons

section
  universe u
  def Lst (α : Type u) : Type u := List α

  def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
  def Lst.nil {α : Type u} : Lst α := List.nil
  def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

  #check Lst.cons 0 Lst.nil

  def as : Lst Nat := Lst.nil
  def bs : Lst Nat := Lst.cons 5 Lst.nil
end

section
  universe u
  def ident {α : Type u} (x : α) := x

  #check ident         -- ?m → ?m
  #check ident 1       -- Nat
  #check ident "hello" -- String
  #check @ident        -- {α : Type u_1} → α → α
  #check @ident Nat 2
  #check @ident Int 2
end

#check List.nil
theorem t1 : p → (q → p) := 
  λ (hp : p) =>
  λ (hq : q) => hp
theorem t2 (hp : p) (hq : q) : p := hp

namespace hidden
  variable {p : Prop}
  variable {q : Prop}
  theorem t1 : p → q → p :=
    λ (hp : p) =>
    λ (_ : q) =>
    show p from hp
  #print t1
end hidden

def double := fun (n : Int) => n - 2*n
#check List.cons
#check @List.cons

#check @id Nat 5
#check id 5  -- This will check the type of `@id Nat 5`, which is `Nat``

#eval double 4
def half := fun (n:ℚ) => n / 2
#check @half
#eval half 3

def dommm : Int -> Int -> Int:= fun (_ b : Int) => b

#check dommm 4 6
#eval dommm 5 6

#check @Nat.add
#check Nat.add


variable (A B : Type)
def dom (f: A -> B) := A   
#check dom
#check @dom

def mine := fun (a : Nat) => a + 1
def mine' (n: Nat) := n+1

#check mine

inductive Mouse where
 | Normal : Mouse
 | Trackball : Mouse

#check Mouse
#check Mouse.Normal

inductive TreeM (α : Type) where
  | nil : TreeM α
  | node : α -> TreeM α -> TreeM α -> TreeM α

inductive Weekday where
  | Monday : Weekday
  | Tuesday : Weekday
  | Wednesday : Weekday
  | Thursday : Weekday
  | Friday : Weekday
  | Saturday : Weekday
  | Sunday : Weekday

def isLectureDay: Weekday → Bool
  | Weekday.Monday => true
  | Weekday.Tuesday => true
  | _ => false

  #check isLectureDay

  def switch: Bool -> Bool
    | true => false
    | false => true

/- #eval bab Nat Nat -/

#check And

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop


variable {p : Prop}
variable {q : Prop}

theorem t10 : (p → q → p : Prop) := fun (hp : p) => fun (_ : q) => hp
#check p->q->p

#check p → q → p ∧ q
/- #eval  (p->q->p ∧ q) -/
#check @true
#check true
#check ℕ
#check ℕ
