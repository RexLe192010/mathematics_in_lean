section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

def g (x : Nat) := x + 6
def f (x : Nat) := x * x
#eval compose Nat Nat Nat g f 3
-- We can see that functions can still be called outside of section
-- but local variables cannot be called
