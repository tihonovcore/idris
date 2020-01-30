import Equality
import PlusCommutativity
import AssociativityOfPlus

export
distr_lemma : (w, x, y, z: Nat) -> (w + x) + (y + z) = (w + y) + (x + z)
distr_lemma w x y z = 
  let acc1 = eq_commute (pa (w + x) y z) in 
  let acc2 = replace {P = \q => w + x + y + z = q + z} (pa w x y) Refl in
  let comm = replace {P = \q => w + (x + y) + z = w + q + z} (pc x y) Refl in
  let acc3 = replace {P = \q => w + (x + y) + z = q + z} (eq_commute (pa w y x)) comm in
  let acc4 = pa (w + y) x z in
    eq_transitive (eq_transitive acc1 acc2) (eq_transitive acc3 acc4)

export
distr : (x, y, z: Nat) -> x * (y + z) = x * y + x * z
distr Z     y z = Refl
distr (S k) y z = 
  let rec = distr k y z in
  let suc = cong {f = \w => (y + z) + w} rec in 
    eq_transitive suc (distr_lemma y z (k * y) (k * z))
