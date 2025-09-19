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
value "vars_term (Fun f [Var x, Var y])"


value "args (Fun f [Var x, Var y])"

type_synonym ('f, 'v) problem = "('f, 'v) equation list"

definition vars_eq :: "('f, 'v) equation \<Rightarrow> 'v set" 
  where "vars_eq e \<equiv> let (s, t) = e in vars_term s \<union> vars_term t"

definition vars_eqs :: "('f, 'v) problem \<Rightarrow> 'v set"
  where "vars_eqs \<Gamma> \<equiv> \<Union> e \<in> set \<Gamma>. vars_eq e"

definition new_var :: "('f, nat) problem \<Rightarrow> nat"
  where "new_var \<Gamma> \<equiv> Max (vars_eqs \<Gamma>) + 1"


definition is_flattened :: "('f, 'v) equation \<Rightarrow> bool" 
  where "is_flattened eq \<longleftrightarrow> (case eq of 
  (Var _, Var _) \<Rightarrow>  True | 
  (Var _ , Fun _ ts) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t) |
  (Fun _ ts, Var _) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t)|
  _ \<Rightarrow> False)"

(*
+[s1, ..., sn] tal que s1,..., sn nao tem ocorrencias de +
+[+[s1,s2], s3]] \<longrightarrow>+ +[s1, s2, s3] 

Pseudo-código: 

real_flat_aux :: term \<Rightarrow> term list \<Rightarrow> term list where
  real_flat_aux t acc = 
     (case t of 
      Var x \<Rightarrow> t # acc |
      Fun f (s#ts) \<Rightarrow> (case (label f) of 
       AC \<Rightarrow> (case s of 
            Var y = (s # acc)@(real_flat_aux ts) |
            Fun f' s' = (case (label f') of
                AC \<Rightarrow> (list.map real_flat_aux s') # acc
                _ \<Rightarrow> passa real_flat_aux pra dentro)
          )
       _ \<Rightarrow> (Fun f (list.map real_flat_aux ts)) # acc \<dots> (aplicar real_flat_aux no ts)
      )
    )


real_flat ::  term \<Rightarrow> term
 real_flat (Fun + ts) = 
    let tm_args = real_flat_aux ts [] in    (Caso +, analisar os outros casos)
      Fun + tm_args
 real_flat (Fun h ts) = ...

real_flat Fun + t1#ts \<Rightarrow> (if t1 = Fun + ts' then
   Fun + (ts' @ real_flat Fun + ts))

*)

definition flattened_problem :: "('f, 'v) equations \<Rightarrow> bool" where
"flattened_problem \<Gamma> \<longleftrightarrow> (\<forall> eq \<in> \<Gamma>. is_flattened eq)"

fun fbs:: "('f, nat) problem \<Rightarrow> ('f, nat) problem" where
  "fbs [] = []" |
  "fbs ((t1,t2) # \<Gamma>) = 
  (if (\<not> is_Var t1)\<and>(\<not> is_Var t2) then 
    let V = new_var ((t1,t2) # \<Gamma>)  in 
    [(Var V,t1),(Var V,t2)]@(fbs \<Gamma>)
   else 
    (t1,t2)#(fbs \<Gamma>))"


lemma fbs_correctness: "(ListMem (t1, t2) (fbs(\<Gamma>))) \<Longrightarrow> (is_Var t1) \<or> (is_Var t2)"
  sorry


locale signature = 
  fixes arity :: "'f \<Rightarrow> nat"
    and label :: "'f \<Rightarrow> ach"
  assumes label_inj: "inj label"

locale our_symbols = signature +
  fixes plus :: 'f (\<open>\<^bold>+\<close>)
    and h :: 'f
  assumes plus_ac: "label \<^bold>+ = AC"
    and h_hom : "label h = Hom"

begin

fun h_height:: "('f, 'v) term \<Rightarrow> nat" where (*Move*)
"h_height (Var x) = 0"|
"h_height (Fun f ts) = (if (label f = Hom) then
    (1 + foldl max 0 (map h_height ts))
    else foldl max 0 (map h_height ts))"

fun get_args_ac:: "('f, 'v) term \<Rightarrow> ('f, 'v) term list" where
  "get_args_ac t = (case t of 
                    Fun f ts \<Rightarrow> (case label f of
                                AC \<Rightarrow> args (Fun f ts)|
                                _ \<Rightarrow> [Fun f ts]
                                ) |
                    _ \<Rightarrow> [t]
                    )"

fun remove_ac_symbols :: "('f, 'v) term list \<Rightarrow> ('f, 'v) term list list" where
  "remove_ac_symbols [] = []" |
  "remove_ac_symbols (t # ts) = (case t of
                                Fun f ss' \<Rightarrow> (case label f of
                                              AC \<Rightarrow> (map get_args_ac ss') |
                                              _ \<Rightarrow> [Fun f ss'] # (remove_ac_symbols ts)) |
                                Var x \<Rightarrow> [Var x]#(remove_ac_symbols ts)
                                 )"
  

fun flatten_list :: "'a list list \<Rightarrow> 'a list" where (*Move*)
  "flatten_list [] = []" |
  "flatten_list (l # ls) = l @ (flatten_list ls)"

fun flat_args_ac :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list" where
  "flat_args_ac (Var x) = []" |
  "flat_args_ac (Fun f ts) = (case label f of
                              AC \<Rightarrow> flatten_list (remove_ac_symbols ts) | 
                              _ \<Rightarrow> ts)"

fun real_flat :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "real_flat (Var x) = Var x" | 
  "real_flat (Fun f ts) = Fun f (flat_args_ac (Fun f ts))"




(*fun real_flat_aux :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term list" where
  "real_flat_aux t acc = 
     (case t of 
      Var x \<Rightarrow> t # acc |
      Fun f s#ts \<Rightarrow> (case (label f) of
                       AC \<Rightarrow> (case s of 
                              Var y \<Rightarrow> (s # acc)@(map real_flat_aux ts) |
                              Fun f' s' = (case (label f') of
                                           AC \<Rightarrow> (map real_flat_aux s') # acc |
                                           _ \<Rightarrow> ((Fun f' real_flat_aux s')#acc)@(map real_flat_aux ts)
                                         )
                              )
                     )
      )"
*)



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
Flatten Both Sides
{t1=t2}\<union>\<Gamma> \<Rightarrow> {V=t1, V=t2}\<union> \<Gamma>, \<not> is_Var t1 \<and> \<not> is_Var t2
*)



(* 
   \<forall> (t1, t2) \<in> fbs (\<Gamma>) = (is_Var t1 \<or> is_Var t2)

 a = (s, t)

ListMem (t1, t2) (fbs ((s,t) # \<Gamma>)
Caso 1: (\<not> is_Var s) \<and> (\<not> is_Var t) \<Longrightarrow> (fbs ((s,t) # \<Gamma>) = [(V, s), (V, t)] @ (fbs \<Gamma>)

ListMem (t1, t2) ([(V, s), (V, t)] @ (fbs \<Gamma>)) 


Caso 2: (is_Var s) \<or> (is_Var t)
*)





  
  

(* (V, Fun f ts1) # ((V, Fun g ts2) # \<Gamma>) *)

(* 
(case eq of
  let V = Var 100 in
  (Fun f ts1, Fun g ts2) \<Rightarrow> \<Gamma>|
  _ \<Rightarrow> eq # \<Gamma>)"
 *)


end
