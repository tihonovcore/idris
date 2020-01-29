import Equality
import AddArithmetic

pa_lemma : (a: Nat) -> a + Z = a
pa_lemma Z = Refl
pa_lemma (S k) = let rec = pa_lemma k in _cong (\w => S w) rec

pa: (n, m, k: Nat) -> (n + m) + k = n + (m + k)
pa n m Z     =
  let lm = pa_lemma (n + m) in  --n + m + 0 = n + m
  let rep = replace {P = \w => n + m = n + w} (x_eq_x_plus_zero m) Refl in --n + m = n + (m + 0)
  eq_transitive lm rep
pa n m (S k) = 
  let rec = _cong (\w => S w) (pa n m k) in -- S(n + m + k) = S(n + (m + k))
  let move_left = eq_transitive (move_s_from_sum_xy_lemma (n + m) k) rec in -- n + m + Sk = S(n + (m + k))
  let move_right = eq_transitive move_left (eq_commute (move_s_from_sum_xy_lemma n (m + k))) in -- n + m + S k = n +S(m + k)
    replace {P = \w => n + m + S k = n + w} (eq_commute (move_s_from_sum_xy_lemma m k)) move_right -- n + m + S k = n + (m + S k) 
