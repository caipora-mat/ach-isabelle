(*
Author: Guilherme Borges Brandão <borgesbrandao13@gmail.com>
Author: Daniele Nantes Sobrinho <d.nantes-sobrinho@imperial.ac.uk> 
*)

theory Exercicio
  imports Main
  "First_Order_Terms.Unification"

begin



datatype ach = Unin | AC | Hom

value "vars_term (Var x)"

definition vars_eq :: "('f, 'v) equation \<Rightarrow> 'v set" 
  where "vars_eq e \<equiv> let (s, t) = e in vars_term s \<union> vars_term t"

definition vars_eqs :: "('f, 'v) equations \<Rightarrow> 'v set"
  where "vars_eqs \<Gamma> \<equiv> \<Union> e \<in> \<Gamma>. vars_eq e"

definition is_flattened :: "('f, 'v) equation \<Rightarrow> bool" 
  where "is_flattened eq \<longleftrightarrow> (case eq of 
  (Var _, Var _) \<Rightarrow>  True | 
  (Var _ , Fun _ ts) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t) |
  (Fun _ ts, Var _) \<Rightarrow> True|
  _ \<Rightarrow> False)"

definition flattened_problem :: "('f, 'v) equations \<Rightarrow> bool" where
"flattened_problem \<Gamma> \<longleftrightarrow> (\<forall> eq \<in> \<Gamma>. is_flattened eq)"

fun fbs:: "('f, 'v) equations \<Rightarrow> ('f, 'v) equations" where
  "fbs {} = {}" |
  "fbs (insert (t1,t2) \<Gamma>) = 
  (if (\<not> is_Var t1)\<and>(\<not> is_Var t2) then 
    let V  = (fresh (vars_eqs \<Gamma>) V) in 
    {(V,t1),(V,t2)} \<union> (fbs \<Gamma>)
   else 
    insert (t1,t2) (fbs \<Gamma>))"


locale signature = 
  fixes arity :: "'f \<Rightarrow> nat"
    and label :: "'f \<Rightarrow> ach"
  assumes label_inj: "inj label"

begin

fun h_height:: "('f, 'v) term \<Rightarrow> nat" where (*Move*)
"h_height (Var x) = 0"|
"h_height (Fun f ts) = (if (label f = Hom) then
    (1 + foldl max 0 (map h_height ts))
    else foldl max 0 (map h_height ts))"




end







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

foldl f 0 [] = 0
foldl f 0 (t#ts) =  foldl f (f 0 t) ts  

*)

(* fun h_height:: "term \<Rightarrow> nat" where (*Move*)
"h_height (Var x) = 0"|
"h_height (Fun (Unin f) (ts)) = (foldl max 0 (map h_height ts))"|
"h_height (Fun AC (ts)) = (foldl max 0 (map h_height ts))" |
"h_height (Fun Hom (ts)) = 1 + (foldl max 0 (map h_height ts))"


  height h(h(y)) = 1 + height(h(y)) = 1 + 1 + height(y)
  height h([t1,t2]) = 1 + max(height(t1),height(t2))
*)


(*
type_synonym ('f, 'v) equation = "('f, 'v) term \<times> ('f, 'v) term"
*)



definition is_flattened :: "ach_equation \<Rightarrow> bool" where
"is_flattened eq \<longleftrightarrow> (case eq of 
(Var _, Var _) \<Rightarrow>  True | 
(Var _ , Fun _ ts) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t) |
_ \<Rightarrow> False)"

definition flattened_problem :: "ach_equations \<Rightarrow> bool" where
"flattened_problem \<Gamma> \<longleftrightarrow> (\<forall> eq \<in> \<Gamma>. is_flattened eq)"

(*
Flatten Both Sides
{t1=t2}\<union>\<Gamma> \<Rightarrow> {V=t1, V=t2}\<union> \<Gamma>, \<not> is_Var t1 \<and> \<not> is_Var t2
*)

fun fbs:: "ach_equations \<Rightarrow> ach_equations" where
  "fbs [] = []" |
  "fbs ((t1,t2) # \<Gamma>) = 
  (if (\<not> is_Var t1)\<and>(\<not> is_Var t2) then 
    let V = Var 100 in 
    [(V,t1),(V,t2)]@ (fbs \<Gamma>)
   else 
    (t1,t2)#(fbs \<Gamma>))"


(* 
   \<forall> (t1, t2) \<in> fbs (\<Gamma>) = (is_Var t1 \<or> is_Var t2)

 a = (s, t)

ListMem (t1, t2) (fbs ((s,t) # \<Gamma>)
Caso 1: (\<not> is_Var s) \<and> (\<not> is_Var t) \<Longrightarrow> (fbs ((s,t) # \<Gamma>) = [(V, s), (V, t)] @ (fbs \<Gamma>)

ListMem (t1, t2) ([(V, s), (V, t)] @ (fbs \<Gamma>)) 


Caso 2: (is_Var s) \<or> (is_Var t)
*)

lemma fbs_correctness: "(ListMem (t1, t2) (fbs(\<Gamma>))) \<Longrightarrow> (is_Var t1) \<or> (is_Var t2)"
  apply (induction \<Gamma>)
    apply (simp add: ListMem_iff)
  apply (simp add: ListMem_iff)
  by (smt (verit, ccfv_threshold) append.right_neutral append_Cons append_eq_append_conv2 fbs.elims
      list.distinct(1) list.inject prod.sel(1,2) same_append_eq set_ConsD term.disc(1))





  
  

(* (V, Fun f ts1) # ((V, Fun g ts2) # \<Gamma>) *)

(* 
(case eq of
  let V = Var 100 in
  (Fun f ts1, Fun g ts2) \<Rightarrow> \<Gamma>|
  _ \<Rightarrow> eq # \<Gamma>)"
 *)


end
