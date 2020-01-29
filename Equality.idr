export
eq_commute: x = y -> y = x
eq_commute Refl = Refl

export
eq_transitive : x = y -> y = z -> x = z
eq_transitive Refl Refl = Refl

export
_cong : {A: Type} -> {B: Type} -> (P: A -> B) -> x = y -> (P x) = (P y)
_cong P Refl {x} = Refl {x = (P x)}

--test
_inc : Nat -> Nat
_inc k = S k
