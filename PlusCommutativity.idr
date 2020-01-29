import Data.Vect

import AddArithmetic
import Equality

pc : (x, y: Nat) -> x + y = y + x
pc Z y     = x_eq_x_plus_zero y
pc (S k) y = 
  let rec = pc k y in -- k + y = y + k
  let rep = replace {P = \w => S(k + y) = S w} rec Refl in 
  let move = move_s_from_sum_xy_lemma y k in
    eq_transitive rep (eq_commute move)

--test
f: (n: Nat) -> (m: Nat) -> Vect (n + m) Nat -> Vect (m + n) Nat
f n m v = replace {P = \w => Vect w Nat} (pc n m) v
