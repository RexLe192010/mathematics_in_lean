-- Namespaces can be nested
namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  #check a
  #check f
  #check fa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa

open Foo -- Open Foo such that local variables can be accessed

#check a
#check f
#check fa
#check Foo.fa
#eval Foo.fa -- 5 + 7 = 12

namespace Foo
-- Namespaces that have been closed can later be reopened,
-- even in another file
  def ffa : Nat := f (f a)
end Foo
