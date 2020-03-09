import Equality
import PlusMulArithmetic
import MulArithmetic
import AddArithmetic
import AssociativityOfPlus

%default total

distr' : (x, y, z: Nat) -> (x + y) * z = x * z + y * z
distr' x y z = 
  let lm1 = mc (x + y) z in 
  let lm2 = distr z x y in 
  let com1 = replace {P = \w => z * x + z * y = w + z * y} (mc z x) Refl in
  let com2 = replace {P = \w => x * z + z * y = x * z + w} (mc z y) Refl in
  eq_transitive (eq_transitive lm1 lm2) (eq_transitive com1 com2)

lemma_xx2 : (x: Nat) -> x + x = 2 * x
lemma_xx2 Z     = Refl
lemma_xx2 (S k) = rewrite eq_commute (x_eq_x_plus_zero k) in Refl
  
lemma : (x, y: Nat) -> y * x + x * y = 2 * x * y
lemma x y = 
  let com = replace {P = \w => y * x + x * y = w + x * y} (mc y x) Refl in
  let dis = eq_commute (distr x y y) in
  let eqq = replace {P = \w => x * (y + y) = x * w} (lemma_xx2 y) Refl in --x*(y+y)=x*(2*y)
  let acc = eq_transitive eqq (multAssociative x 2 y) in --x*(y+y)=(x*2)*y
  let res = replace {P = \w => x * (y + y) = w * y} (mc x 2) acc in
    eq_transitive com (eq_transitive dis res)

th : (a, b: Nat) -> (a + b) * (a + b) = a * a + 2 * a * b + b * b
th a b = 
  let dis1 = distr (a + b) a b in --(a+b)^2=(a+b)a + (a+b)b
  let dis2 = replace {P = \w => (a + b) * a + (a + b) * b = w + (a + b) * b} (distr' a b a) Refl in
  let dis3 = replace {P = \w => (a * a) + (b * a) + (a + b) * b = (a * a) + (b * a) + w} (distr' a b b) Refl in 
  let dist' = eq_transitive dis1 (eq_transitive dis2 dis3) in --(a+b)^2 = (aa+ba)+(ab+bb)
  let dist = eq_transitive dist' (eq_commute (pa (a*a + b*a) (a*b) (b*b))) in
  let acc = replace {P = \w => a*a + b*a + a*b + b*b = w + b*b} (pa (a*a) (b*a) (a*b)) Refl in 
  let moveTo2 = replace {P = \w => a*a + b*a + a*b + b*b = a*a + w + b*b} (lemma a b) acc in --aa+ba+ab+bb=aa+2ab+bb
    eq_transitive dist moveTo2

--variant 1 lemmas
t2f : (a: Nat) -> a + 2 * 2 = a + 4
t2f a = Refl

t2f_mul : (S (S Z)) * (S (S Z)) = (S (S (S (S Z))))
t2f_mul = Refl

txt2fx : (x: Nat) -> 2 * x * 2 = 4 * x
txt2fx x = 
  let assoc = eq_commute (multAssociative (S (S Z)) x (S (S Z))) in
  let commu = replace {P = \w => 2 * (x * 2) = 2 * w} (multCommutative x (S (S Z))) Refl in
  let assoc' = multAssociative 2 2 x in
  let t2f_mul' = replace {P = \w => 2 * 2 * x = w * x} t2f_mul Refl in 
    eq_transitive (eq_transitive assoc commu) (eq_transitive assoc' t2f_mul')
    
--variant 2 lemmas
lemma_one: (S Z) * (S Z) = (S Z)
lemma_one = Refl

tt2f: (S (S Z)) * (S (S Z)) = (S (S (S (S Z))))
tt2f = Refl

txtx2fxx : (x: Nat) -> 2 * x * (2 * x) = 4 * x * x
txtx2fxx x = 
  let assoc = multAssociative ((S (S Z)) * x) (S (S Z)) x in
  let assoc2 = eq_commute (multAssociative (S (S Z)) x (S (S Z))) in 
  let comm = multCommutative x (S (S Z)) in 
  let assocAndComm = replace {P = \w => 2 * x * 2 = 2 * w} comm assoc2 in 
  let assoc3 = multAssociative (S (S Z)) (S (S Z)) x in 
  let rep = replace {P = \w => 2 * (2 * x) = w * x} tt2f assoc3 in 
  let trans = eq_transitive assocAndComm rep in
  let trans2 = eq_transitive (multAssociative 2 x 2) trans in 
  let trans3 = eq_transitive assoc2 trans2 in 
    replace {P = \w => 2 * x * (2 * x) = w * x} trans3 assoc

t_tx_o2fx : (x: Nat) -> 2 * (2 * x) * 1 = 4 * x
t_tx_o2fx x = 
  let rm1 = eq_commute (x_eq_x_mul_one ((S (S Z)) * ((S (S Z)) * x))) in 
  let assoc = multAssociative (S (S Z)) (S (S Z)) x in 
  let lem_tt2f = replace {P = \w => 2 * 2 * x = w * x} tt2f Refl in 
    eq_transitive (eq_transitive rm1 assoc) lem_tt2f

--proofs
var1 : (x: Nat) -> (x + 2) * (x + 2) = x*x + 4*x + 4
var1 x = 
  let lm = th x (S (S Z)) in 
    replace {P = \w => (x+2)*(x+2) = x*x + w + 2*2} (txt2fx x) lm
    
var2 : (x: Nat) -> (2 * x + 1)*(2 * x + 1) = 4*x*x + 4*x + 1
var2 x = 
  let lm = th ((S (S Z)) * x) (S Z) in 
  let lm_C = replace {P = \w => (2*x+1)*(2*x+1)=2*x*(2*x)+2*(2*x)*1 + w} lemma_one lm in 
  let lm_B = replace {P = \w => (2*x+1)*(2*x+1)=2*x*(2*x)+ w + 1} (t_tx_o2fx x) lm_C in 
  let lm_A = replace {P = \w => (2*x+1)*(2*x+1)= w + 4*x + 1} (txtx2fxx x) lm_B in lm_A
 
var6 : (x: Nat) -> x*x + x*x + x*x + x*x = 4*x*x
var6 x = 
  let lem = lemma_xx2 (x*x) in 
  let comm = eq_commute (plusAssociative (x*x + x*x) (x*x) (x*x)) in
  let uselem1 = replace {P = \w => x*x + x*x + x*x + x*x = w + w} lem comm in 
  let lem2 = lemma_xx2 (2 * (x * x)) in 
  let trans = eq_transitive uselem1 lem2 in 
  let assoc = multAssociative 2 2 (x * x) in 
  let rep = replace {P = \w => 2 * 2 * (x * x) = w * (x * x)} tt2f Refl in 
  let trans2 = eq_transitive assoc (eq_transitive rep (multAssociative 4 x x)) in 
    eq_transitive trans trans2
 
