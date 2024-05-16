#eval 2 + 2
#check 2 + 2


#check 2 + 2 = 4
#check 2 + 2 > 5

#eval 2 + 2 = 4
#eval 2 + 2 > 50


def FermatLastTheorem :=
∀ x y z n : Nat, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n
#check FermatLastTheorem

theorem easy : 2 + 2 = 4 := rfl
#check easy

theorem hard : FermatLastTheorem := sorry
-- sorry is a placeholder when some theories cannot be proved
-- we just leave it as sorry
#check hard

def m := 2
#check m
#eval m

def b1 := true
#check b1
#eval b1

def b2 := false
#check b2
#eval b2

#check b1 && b2
#eval b1 && b2
#check b1 || b2

#check Nat → Nat
#check Nat × Nat -- Cartesian product
#check Prod Nat Nat -- Alternative notation

#check Nat × Nat → Nat
#check Nat → Nat → Nat

#check Nat.add 2 3
#eval Nat.add 2 300

#check (6, 7).2
#eval (6, 7).1

#check Prod


#check fun (x : Nat) =>  x + 6
#check λ (x : Nat) => x + 6 -- Equivalent expression
#check fun x => x + 6
#check λ x => x + 6
#eval (fun x => x + 10) 20 -- Evaluate the function with input 20


#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat
-- The three expressions above are the same


#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool
-- g(f(x)) compositions of functions
