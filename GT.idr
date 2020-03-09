import AddArithmetic

data GT_ : (n, m: Nat) -> Type where
  GTZero : GT_ (S k) Z
  GTSucc : GT_ n m -> GT_ (S n) (S m)
  
gt53 : GT_ 5 3
gt53 = GTSucc (GTSucc (GTSucc GTZero))

gt_trans : GT_ x y -> GT_ y z -> GT_ x z
gt_trans (GTSucc x) GTZero     = GTZero
gt_trans (GTSucc x) (GTSucc y) = GTSucc (gt_trans x y)

gt_Sx_x : (x: Nat) -> GT_ (x + 1) x
gt_Sx_x Z     = GTZero
gt_Sx_x (S k) = GTSucc (gt_Sx_x k)

gt_plusn_lemma_l : GT_ x (S (y + z)) -> GT_ x (y + S z)
gt_plusn_lemma_l gt {y} {z} = rewrite (move_s_from_sum_xy_lemma y z) in gt

gt_plusn_lemma_r : GT_ (S (x + y)) z -> GT_ (x + S y) z
gt_plusn_lemma_r gt {x} {y} = rewrite (move_s_from_sum_xy_lemma x y) in gt

gt_plusn : (n: Nat) -> GT_ x y -> GT_ (x + n) (y + n)
gt_plusn Z     GTZero = GTZero
gt_plusn Z     (GTSucc x) = GTSucc (gt_plusn 0 x)
gt_plusn (S k) GTZero = 
  let rec = gt_plusn k GTZero in
    GTSucc (gt_plusn_lemma_r rec)
gt_plusn (S k) (GTSucc x) =
  let rec = GTSucc (gt_plusn k x) in
    GTSucc (gt_plusn_lemma_l (gt_plusn_lemma_r rec))
 
 
 
