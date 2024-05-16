def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop, meaning that (p and q) implies (q and p)
#eval And (3 + 3 = 6) (2 * 2 = 4)
#eval Or (3 + 3 = 6) (2 * 2 = 4)
#eval Not (3 + 3 = 8)
#eval (3 + 3 = 6) → (2 + 2 = 4) -- Implies
