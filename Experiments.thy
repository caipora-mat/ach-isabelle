(*
Author: Guilherme Borges Brandão <borgesbrandao13@gmail.com>
Author: Daniele Nantes Sobrinho <d.nantes-sobrinho@imperial.ac.uk>
Author: Deivid Vale <email-here>
*)

theory Experiments
  imports Main
  "First_Order_Terms.Unifiers"

begin

definition is_variable_abstracted :: "('f, 'v) equation \<Rightarrow> bool" 
  where "is_variable_abstracted eq \<longleftrightarrow> (case eq of 
  (Var _, Var _) \<Rightarrow>  True | 
  (Var _ , Fun _ ts) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t) |
  (Fun _ ts, Var _) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t)|
  _ \<Rightarrow> False)"

type_synonym ('f, 'v) problem = "('f, 'v) equation list"

definition variable_abstracted_problem :: "('f, 'v) equations \<Rightarrow> bool" where
"variable_abstracted_problem \<Gamma> \<longleftrightarrow> (\<forall> eq \<in> \<Gamma>. is_variable_abstracted eq)"

definition vars_eq :: "('f, 'v) equation \<Rightarrow> 'v set" 
  where "vars_eq e \<equiv> let (s, t) = e in vars_term s \<union> vars_term t"

definition vars_eqs :: "('f, 'v) problem \<Rightarrow> 'v set"
  where "vars_eqs \<Gamma> \<equiv> \<Union> e \<in> set \<Gamma>. vars_eq e"



datatype ach = Unin | AC | Hom

locale signature = 
  fixes arity :: "'f \<Rightarrow> nat"
    and label :: "'f \<Rightarrow> ach"
  assumes label_inj: "inj label"


begin

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
                                              AC \<Rightarrow> (get_args_ac (Fun f ss'))#(remove_ac_symbols ts)|
                                              _ \<Rightarrow> [Fun f ss'] # (remove_ac_symbols ts)) |
                                Var x \<Rightarrow> [Var x]#(remove_ac_symbols ts)
                                 )"

fun concat :: "'a list list \<Rightarrow> 'a list" where 
  "concat [] = []" |
  "concat (l # ls) = l @ (concat ls)"



fun flat :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "flat (Var x) = Var x" |
  "flat (Fun f ts) = (case label f of
                          AC \<Rightarrow> Fun f (concat (remove_ac_symbols (map flat ts))) |
                          _ \<Rightarrow> Fun f (map flat ts)
                          )"

txt\<open>Some examples for the functions we defined above\<close>

lemma example_1:
  assumes "label f = AC"
  shows "get_args_ac (Fun f [Fun f [Var x, Var y], Var z]) = [Fun f [Var x, Var y], Var z]"
proof -
  have "get_args_ac (Fun f [Fun f [Var x, Var y], Var z]) = (case Fun f [Fun f [Var x, Var y], Var z] of
                                                            Fun f' ts' \<Rightarrow> (case label f' of  
                                                                          AC \<Rightarrow> args (Fun f' ts') |
                                                                          _ \<Rightarrow> [Fun f' ts']
                                                                          ) |
                                                             _ \<Rightarrow> [Fun f [Fun f [Var x, Var y], Var z]]
                                                            )"
    by simp
  also have "... = (case label f of
                    AC \<Rightarrow> args (Fun f [Fun f [Var x, Var y], Var z]) |
                    _ \<Rightarrow> [Fun f [Fun f [Var x, Var y], Var z]]
                    )"
    by simp
  also have "... = args (Fun f [Fun f [Var x, Var y], Var z])" by (simp add: assms)
  also have "... = [Fun f [Var x, Var y], Var z]" by simp
  finally show ?thesis by simp
qed


lemma example_2:
  assumes "label f = AC"
  shows "remove_ac_symbols [Fun f [Var x, Var y], Var z] = [[Var x, Var y], [Var z]]"
proof -
  have "remove_ac_symbols [Fun f [Var x, Var y], Var z] = (case Fun f [Var x, Var y] of 
                                                          Fun f' ss' \<Rightarrow> (case label f' of
                                                                        AC \<Rightarrow> (get_args_ac (Fun f' ss'))#(remove_ac_symbols [Var z]) |
                                                                        _ \<Rightarrow> [Fun f' ss']#(remove_ac_symbols [Var z])) |
                                                          Var v \<Rightarrow> [Var v]#(remove_ac_symbols [Var z])
                                                           )" by simp
  also have "... = (case label f of 
                   AC \<Rightarrow> (get_args_ac (Fun f [Var x, Var y])) # (remove_ac_symbols [Var z]) |
                   _ \<Rightarrow> [Fun f [Var x, Var y]] # (remove_ac_symbols [Var z])
                   )" by simp
  also have "... = (get_args_ac (Fun f [Var x, Var y])) # (remove_ac_symbols [Var z])" by (simp add: assms)
  also have "... = [[Var x, Var y], [Var z]]" by (simp add: assms)
  finally show ?thesis by simp
qed

lemma example_3: 
  assumes "label f = AC"
  shows "flat (Fun f [Fun f [Var x, Var y], Var z]) = Fun f [Var x, Var y, Var z]"
  apply (simp add: assms)
  done

lemma example_4:
  assumes "label f = AC"
  shows "flat (Fun f [Fun f [Var x, Var y], Fun f [Var z, Fun f [Var w, Var v]]]) = 
                      Fun f [Var x, Var y, Var z, Var w, Var v]"
  apply (simp add: assms)
  done

lemma example_5:
  assumes "label f = AC"
  and "label g = Unin"
  shows "flat (Fun f [Fun f [Var x, Var y], Fun g [Var z, Fun f [Var w, Var v]]]) = 
                      Fun f [Var x, Var y, Fun g [Var z, Fun f [Var w, Var v]]]"
  apply (simp add: assms)
  done




text \<open> we need:
lemma 1:  IsFlattened(flat t)
lemma 2: \<forall> t. t=_{AC} flat(t)\<close>


(*End of flat*)


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



end
