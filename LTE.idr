import AddArithmetic 

pf : LTE 3 5
pf = LTESucc (LTESucc (LTESucc (LTEZero)))

export
rsucc : LTE x y -> LTE x (S y)
rsucc LTEZero     = LTEZero
rsucc (LTESucc x) = LTESucc (rsucc x)

export
lrsucc : LTE x y -> LTE (S x) (S y)
lrsucc LTEZero     = LTESucc LTEZero
lrsucc (LTESucc x) = LTESucc (LTESucc x)

plusn_lemma : LTE x (S (y + z)) -> LTE x (y + S z)
plusn_lemma lte {y} {z} = rewrite (move_s_from_sum_xy_lemma y z) in lte

export
plusn : LTE x y -> LTE (x + n) (y + n)
plusn LTEZero     {n = Z}     = LTEZero
plusn (LTESucc x) {n = Z}     = LTESucc (plusn x)
plusn LTEZero     {n = (S k)} = 
  let res = LTESucc (plusn LTEZero {n = k}) in 
  plusn_lemma res
plusn (LTESucc x) {n = (S k)} = LTESucc (plusn x)

export
lte_trans : LTE x y -> LTE y z -> LTE x z
lte_trans LTEZero _ = LTEZero
lte_trans (LTESucc y) (LTESucc x) = LTESucc (lte_trans y x)

export
lte_eq : LTE x y -> LTE y x -> x = y
lte_eq LTEZero     LTEZero = Refl
lte_eq (LTESucc x) (LTESucc y) = cong {f = \w => S w} (lte_eq x y)

export
lte_xx : (x: Nat) -> LTE x x
lte_xx Z     = LTEZero
lte_xx (S k) = LTESucc (lte_xx k)
