import AddArithmetic

total lemma : (x, y: Nat) -> (S x) = (S y) -> x = y
lemma y y Refl = Refl

total lemma' : (x: Nat) -> x * x = 0 -> x = 0
lemma' Z     prf = Refl
lemma' (S _) Refl impossible

total p3_lemma : (x : Nat) -> x + 1 = 1 -> x = 0
p3_lemma x prf = 
  let cm = plusCommutative x 1 in 
  let lm = sym (sx_eq_one_plus_x x) in
  let tr = trans cm lm in 
  let tr1 = trans (sym tr) prf in
    lemma x 0 tr1

total p3 : (x : Nat) -> x * x + 1 = 1 -> x = 0
p3 x prf = 
  let prev = p3_lemma (x * x) prf in 
    lemma' x prev

total p4 : (LT x 3) -> Either (x=Z) (Either (x=(S Z)) (x = (S (S Z))))
p4 (LTESucc LTEZero) = Left Refl
p4 (LTESucc (LTESucc LTEZero)) = Right (Left Refl)
p4 (LTESucc (LTESucc (LTESucc LTEZero))) = Right (Right Refl)

total p5 : (x: Nat) -> (LT x 3) -> (LT (x * x) 9)
p5 x y = 
  case p4 {x} y of
    Left  l => 
      let tmp = replace {P = \w => w * w = 0} (sym l) Refl in
        LTESucc (replace {P = \w => LTE w 8} (sym tmp) LTEZero)
    Right (Left  l) => 
      let tmp = replace {P = \w => w * w = 1} (sym l) Refl in
        LTESucc (replace {P = \w => LTE w 8} (sym tmp) (LTESucc LTEZero))
    Right (Right r) => 
      let tmp = replace {P = \w => w * w = 4} (sym r) Refl in --x*x=4
        LTESucc (replace {P = \w => LTE w 8} (sym tmp) (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))

total lm : GTE y x -> LTE y x -> y = x
lm LTEZero LTEZero = Refl
lm (LTESucc xy) (LTESucc yx) =
  let rec = lm xy yx in
  cong {f = \w => S w} rec

total p7 : (x: Nat) -> (GTE x (S Z)) -> (LT x (S (S Z))) -> x = (S Z)
p7 (S k) xy (LTESucc yx) = lm xy yx

total cm : x = y -> y = x
cm Refl = Refl

total p8_lemma : x = y -> LT x 3 -> LT y 3
p8_lemma eq px = replace {P = \w => LT w 3} eq px

total p8 : (x: Nat) -> Either (x = Z) (Either (x = (S Z)) (x = (S (S Z)))) -> LT x (S (S (S Z)))
p8 x (Left  l) = let less = LTESucc (LTEZero {right = 2}) in p8_lemma (cm l) less
p8 x (Right (Left  l)) = let less = LTESucc (LTESucc (LTEZero {right = 1})) in p8_lemma (cm l) less
p8 x (Right (Right r)) = let less = LTESucc (LTESucc (LTESucc (LTEZero {right = Z}))) in p8_lemma (cm r) less
