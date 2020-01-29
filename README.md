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
