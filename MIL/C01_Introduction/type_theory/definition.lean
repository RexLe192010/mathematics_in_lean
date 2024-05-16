def f (x : Nat) := x + 3
#check f
#eval f 3 -- f(3)

def double (x : Nat) := 2 * x
#check double
#eval double 6

def greater (x y : Nat) :=
  if x > y then x -- indentation
  else y
#check greater
#eval greater (greater 3 4) 5 -- Embedded functions


def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3  -- 18
