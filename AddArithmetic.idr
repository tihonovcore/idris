export
x_eq_x_plus_zero : (x: Nat) -> x = x + Z
x_eq_x_plus_zero Z     = Refl
x_eq_x_plus_zero (S k) = replace {P = \w => S k = S w} (x_eq_x_plus_zero k) Refl

export
sx_eq_x_plus_one : (x: Nat) -> (S x) = x + 1
sx_eq_x_plus_one Z     = Refl
sx_eq_x_plus_one (S k) = replace {P = \w => S (S k) = S w} (sx_eq_x_plus_one k) Refl

export
sx_eq_one_plus_x : (x: Nat) -> (S x) = 1 + x
sx_eq_one_plus_x x = Refl

export
move_s_from_sum_xy_lemma : (x, y: Nat) -> x + (S y) = S(x + y)
move_s_from_sum_xy_lemma Z y     = Refl
move_s_from_sum_xy_lemma (S k) y = 
  replace 
    {P = \w => (S k) + (S y) = S w} 
    (move_s_from_sum_xy_lemma k y) 
    Refl

export
move_s_from_sum_xy : (x, y: Nat) -> (S x) + (S y) = S(S(x + y))
move_s_from_sum_xy x y = 
  replace 
    {P = \w => (S x) + (S y) = S w} 
    (move_s_from_sum_xy_lemma x y) 
    Refl

