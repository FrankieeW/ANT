import Mathlib

open Ideal Zsqrtd

abbrev R := Zsqrtd (-5)

#check (Algebra.norm ℤ (2 : R))
#check (Algebra.norm ℤ (1 + sqrtd : R))
#check (Algebra.norm ℤ (3 : R))
#check (Algebra.norm ℤ (1 - sqrtd : R))

-- Compute norms
#eval (Algebra.norm ℤ (2 : Zsqrtd (-5)))  -- Should be 4
#eval (Algebra.norm ℤ (1 + sqrtd : Zsqrtd (-5)))  -- Should be 6
#eval (Algebra.norm ℤ (3 : Zsqrtd (-5)))  -- Should be 9
#eval (Algebra.norm ℤ (1 - sqrtd : Zsqrtd (-5)))  -- Should be 6
