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

(*
h_height(t) = 0, if t=x
              max{h_height(t1),...h_height(tn)}, if t=f(t1,...,tn)  here f is the AC symbol
              1 + h_height(t') if t = h(t')
*)
(*
map :: (a' \<Rightarrow> b') \<Rightarrow> [a'] \<Rightarrow> [b']
map f [] = []
map f (x # xs) = f(x) # (map f xs) 

s:: 'a \<Rightarrow> 'b           t:: 'a 
----------------------------------
          (s t) :: 'b

foldl:: ('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a 

foldl f e [] = e
foldl f e (t#ts) =  foldl f (f e t) ts  

*)

fun h_height:: "ach_term \<Rightarrow> nat" where (*Move*)
"h_height (Var x) = 0"|
"h_height (Fun (Unin f) []) = 0"|
"h_height (Fun (Unin f) (t#ts)) = max (h_height t) (h_height (Fun (Unin f) ts))"|
"h_height (Fun AC []) = 0"|
"h_height (Fun AC (t#ts)) = max (h_height t) (h_height (Fun AC ts))" |
"h_height (Fun h []) = 0" |
"h_height (Fun h (t # ts)) = 1 + (foldl max 0 (map h_height ts))"

(*
  height h(h(y)) = 1 + height(h(y)) = 1 + 1 + height(y)
  height h([t1,t2]) = 1 + max(height(t1),height(t2))
*)








end
