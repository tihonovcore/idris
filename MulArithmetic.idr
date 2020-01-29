import AddArithmetic
import PlusCommutativity
import AssociativityOfPlus
import Equality

z_eq_z_mul_x : (x: Nat) -> Z = Z * x
z_eq_z_mul_x x = Refl

z_eq_x_mul_z : (x: Nat) -> Z = x * Z
z_eq_x_mul_z Z     = Refl
z_eq_x_mul_z (S k) = z_eq_x_mul_z k

x_eq_one_mul_x : (x: Nat) -> x = (S Z) * x
x_eq_one_mul_x Z     = Refl
x_eq_one_mul_x (S k) = replace {P = \w => S k = S w} (x_eq_x_plus_zero k) Refl
  
x_eq_x_mul_one : (x: Nat) -> x = x * (S Z)
x_eq_x_mul_one Z     = Refl
x_eq_x_mul_one (S k) = cong {f = \w => S w} (x_eq_x_mul_one k)

mc_lemma_plus_perm : (p, k: Nat) -> (k + S Z) + (p * k + p) = (k + p * k) + (S Z + p)
mc_lemma_plus_perm p k = 
  let acc1 = eq_commute (pa (k + S Z) (p * k) p) in 
  let acc2 = replace {P = \w => k + (S Z) + p * k + p = w + p} (pa k (S Z) (p * k)) Refl in
  let comm = replace {P = \w => k + ((S Z) + p * k) + p = k + w + p} (pc (S Z) (p * k)) Refl in
  let acc3 = replace {P = \w => k + ((S Z) + p * k) + p = w + p} (eq_commute (pa k (p * k) (S Z))) comm in
  let acc4 = pa (k + p * k) (S Z) p in
    eq_transitive (eq_transitive acc1 acc2) (eq_transitive acc3 acc4)

mc_lemma: (x, k: Nat) -> x * (k + S Z) = x * k + x
mc_lemma Z     k = Refl
mc_lemma (S p) k = 
  let rec = mc_lemma p k in 
  let rep = replace {P = \w => (k + S Z) + p * (k + S Z) = (k + S Z) + w} rec Refl in 
    eq_transitive rep (mc_lemma_plus_perm p k)

mc : (x, y: Nat) -> x * y = y * x
mc x Z     = eq_commute (z_eq_x_mul_z x)
mc x (S k) = 
  let rec = cong {f = \w => x + w} (mc x k) in 
  let comm = eq_transitive (pc (x * k) x) rec in
  let lemm = eq_transitive (mc_lemma x k) comm in 
    replace {P = \w => x * w = x + k * x} (eq_commute (sx_eq_x_plus_one k)) lemm
  
