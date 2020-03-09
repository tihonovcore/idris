# idris proofs

[Equality](https://github.com/tihonovcore/idris/blob/master/Equality.idr)
* x = y -> y = x
* x = y -> y = z -> x = z
* (P: A -> B) -> x = y -> P x = P y

[AddArithmetic](https://github.com/tihonovcore/idris/blob/master/AddArithmetic.idr)
* x = x + 0
* S x = x + 1
* S x = 1 + x
* x + S y = S(x + y)
* S x + S y = S(S(x + y))

[PlusCommutativity](https://github.com/tihonovcore/idris/blob/master/PlusCommutativity.idr)
* x + y = y + x

[AssociativityOfPlus](https://github.com/tihonovcore/idris/blob/master/AssociativityOfPlus.idr)
* lemma: a + 0 = a
* (n + m) + k = n + (m + k)

[MulArithmetic](https://github.com/tihonovcore/idris/blob/master/MulArithmetic.idr)
* 0 = 0 * x
* 0 = x * 0
* x = 1 * x
* x = x * 1
* lemma: (k * p + 1) + (p * k + p) = (k + p * k) + (1 + p)
* lemma: x * (k + 1) = x * k + x
* x * y = y * x

[PlusMulArithmetic](https://github.com/tihonovcore/idris/blob/master/PlusMulArithmetic.idr)
* (w + x) + (y + z) = (w + y) + (x + z)
* x * (y + z) = x * y + x * z

[LTE](https://github.com/tihonovcore/idris/blob/master/LTE.idr)
* LTE 3 5
* LTE x y -> LTE x (S y)
* LTE x y -> LTE (S x) (S y)
* LTE x (S (y + z)) -> LTE x (y + S z)
* LTE x y -> LTE (x + n) (y + n)
* LTE x y -> LTE y z -> LTE x z
* LTE x y -> LTE y x -> x = y
* LTE x x

# Simple arithmetic proofs
* [(x + 2) ^ 2 = x ^ 2 + 4 \* x + 2](https://github.com/tihonovcore/idris/blob/master/v1v2v6.idr#L82)
* [(2 \* x + 1) ^ 2 = 4 \* x ^ 2 + 4 \* x + 1](https://github.com/tihonovcore/idris/blob/master/v1v2v6.idr#L87)
* [x ^ 2 + 1 = 1 -> x = 0](https://github.com/tihonovcore/idris/blob/master/v3v4v5v7v8.idr#L18)
* [x < 3 -> x = 0 or x = 1 or x = 2](https://github.com/tihonovcore/idris/blob/master/v3v4v5v7v8.idr#L23)
* [x < 3 -> x ^ 2 < 9](https://github.com/tihonovcore/idris/blob/master/v3v4v5v7v8.idr#L28)
* [x ^ 2 + x ^ 2 + x ^ 2 + x ^ 2 = 4 * x ^ 2](https://github.com/tihonovcore/idris/blob/master/v1v2v6.idr#L94)
* [x >= 1 -> x < 2 -> x = 1](https://github.com/tihonovcore/idris/blob/master/v3v4v5v7v8.idr#L42)
* [x = 0 or x = 1 or x = 2 -> x < 3](https://github.com/tihonovcore/idris/blob/master/v3v4v5v7v8.idr#L51)
