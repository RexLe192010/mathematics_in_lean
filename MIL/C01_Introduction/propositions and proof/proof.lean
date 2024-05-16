variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
-- This is a tautology
-- This is a statement to the theorem, as well as a proof to the theorem

#print t1

-- p → q → p This is the type signature of the theorem t1.
-- It states that t1 is a proof of the implication p → q → p.
-- In words, this means "if p is true, then if q is true, then p is true again".
-- It's an example of a very simple tautology, demonstrating that if you start with p,
-- then no matter what else (q) is true, p is still true.

-- := This is an assignment operator.
-- It means that what follows is the definition of the theorem t1.

-- fun hp : p => This is a function that takes an argument hp,
-- which is a proof of p.
-- The fun keyword is used to define anonymous functions in Coq and similar languages,
-- and the => indicates the body of the function that follows.

-- fun hq : q => This is another function, nested within the first one,
-- that takes an argument hq, which is a proof of q.
-- This nested structure reflects the multiple implications in the
-- type signature p → q → p.

-- hp Finally, the body of the innermost function simply returns hp,
-- which is the proof of p we received as the argument of the outer function.
