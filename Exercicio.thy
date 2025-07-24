(*
Author: Guilherme Borges Brandão <borgesbrandao13@gmail.com>
Author: Daniele Nantes Sobrinho <d.nantes-sobrinho@imperial.ac.uk> 
*)

theory Exercicio
  imports Main
  "First_Order_Terms.Unification"

begin


datatype \<F> = Unin string | AC | Hom

type_synonym \<V> = nat

type_synonym ach_term = "(\<F>, \<V>) term"

locale ACh_properties = 
  fixes Fun
    and AC
    and Hom
  assumes assoc: "Fun AC [(Fun AC [t1,t2]), t3] = Fun AC [t1 , Fun AC [t2,t3]]"
    and homomorphism: "Fun Hom [AC [t1,t2]] = Fun AC [Hom [t1], Hom [t2]]"

fun h_height:: "ach_term \<Rightarrow> nat" where (*Move*)
"h_height (Var x) = 0"|
"h_height (Fun (Unin f) []) = 0"|
"h_height (Fun (Unin f) (t#ts)) = max (h_height t) (h_height (Fun (Unin f) ts))"|
"h_height (Fun AC []) = 0"|
"h_height (Fun AC (t#ts)) = max (h_height t) (h_height (Fun AC ts))"






end
