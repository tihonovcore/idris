import AddArithmetic
import LTE

v1 : GTE x y -> GTE y x -> x = y
v1 LTEZero LTEZero = Refl
v1 (LTESucc x) (LTESucc y) = cong {f = \w => S w} (v1 x y)

max : (x, y: Nat) ->  Nat
max Z y = y
max x Z = x
max (S x') (S y') = S (max x' y')

lm0 : {x, y: Nat} -> LTE x (max x y)
lm0 {x = Z} {y = y} = LTEZero
lm0 {x = (S k)} {y = Z} = lte_xx (S k)
lm0 {x = (S k)} {y = (S j)} = LTESucc $ lm0 {x = k} {y = j}

lm1 : (x, y: Nat) -> (LTE x (max x y)) -> (LTE (S x) (max (S x) y))
lm1 Z Z     z = lte_xx 1
lm1 Z (S k) z = LTESucc LTEZero -- 0=max(0, sk) -> 1<=max(1,sk) ~ 1<=S max(0, k) ~ 1<=Sk ~ LTESucc 0<=k
lm1 (S k) Z     z = lte_xx (S (S k))
lm1 (S k) (S j) z = let rec = lm1 k j lm0 in LTESucc rec

pf1 : (x, y: Nat) -> (LTE x (max x y), LTE y (max x y))
pf1 Z y = (LTEZero, lte_xx y)
pf1 (S k) Z = (LTESucc $ lte_xx k, LTEZero)
pf1 (S k) (S j) = case pf1 k j of
                    (l, r) => (LTESucc l, LTESucc r)

--                         wft? (Refl as arg is ok?)
v2 : LTE a b -> LTE a c -> (d = Main.max b c) -> (LTE b d, LTE c d)
v2 lte1 {b} lte2 {c} eq = rewrite eq in pf1 b c

data DIV : (a, b: Nat) -> Type where
  FromMul : (c: Nat) -> ((mult b c) = a) -> DIV a b

v3 : DIV a b -> DIV b c -> DIV a c
v3 (FromMul c1 prf1) (FromMul c2 prf2) = 
   let comp  = replace {P = \w => w * c1 = a} (sym prf2) prf1  in
   let assoc = multAssociative c c2 c1 in
     FromMul (mult c2 c1) (rewrite assoc in comp)


--Todododododood
data Parity : Nat -> Type where
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))

parity : (n:Nat) -> Parity n
parity Z     = Even {n=Z}
parity (S Z) = Odd {n=Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j)))     | Even = rewrite (sym (move_s_from_sum_xy j j)) in Even {n=S j}
  parity (S (S (S (j + j)))) | Odd  = rewrite (sym (move_s_from_sum_xy j j)) in Odd {n=S j}

--todo reverse(?)
toBin : Nat -> List Bool
toBin x = case parity x of 
            Even {n} => False :: if n == 0 then [] else toBin n
            Odd  {n} => True  :: if n == 0 then [] else toBin n

data Bin : List Bool -> Type where
  FNat : (a: Nat) -> Bin (toBin a)
