(*
Author: Guilherme Borges Brandão <borgesbrandao13@gmail.com>
Author: Daniele Nantes Sobrinho <d.nantes-sobrinho@imperial.ac.uk>
*)

theory Exercicio
  imports Main
  "First_Order_Terms.Unification"

begin

definition is_fake_flattened :: "('f, 'v) equation \<Rightarrow> bool" 
  where "is_fake_flattened eq \<longleftrightarrow> (case eq of 
  (Var _, Var _) \<Rightarrow>  True | 
  (Var _ , Fun _ ts) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t) |
  (Fun _ ts, Var _) \<Rightarrow> (\<forall> t \<in> set ts. is_Var t)|
  _ \<Rightarrow> False)"

type_synonym ('f, 'v) problem = "('f, 'v) equation list"

definition fake_flattened_problem :: "('f, 'v) equations \<Rightarrow> bool" where
"fake_flattened_problem \<Gamma> \<longleftrightarrow> (\<forall> eq \<in> \<Gamma>. is_fake_flattened eq)"

definition vars_eq :: "('f, 'v) equation \<Rightarrow> 'v set" 
  where "vars_eq e \<equiv> let (s, t) = e in vars_term s \<union> vars_term t"

definition vars_eqs :: "('f, 'v) problem \<Rightarrow> 'v set"
  where "vars_eqs \<Gamma> \<equiv> \<Union> e \<in> set \<Gamma>. vars_eq e"

definition new_var :: "('f, nat) problem \<Rightarrow> nat"
  where "new_var \<Gamma> \<equiv> Max (vars_eqs \<Gamma>) + 1"




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

fun flatten_list :: "'a list list \<Rightarrow> 'a list" where (*concat*)
  "flatten_list [] = []" |
  "flatten_list (l # ls) = l @ (flatten_list ls)"



fun real_flat :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "real_flat (Var x) = Var x" |
  "real_flat (Fun f ts) = (case label f of
                          AC \<Rightarrow> Fun f (flatten_list (remove_ac_symbols (map real_flat ts))) |
                          _ \<Rightarrow> Fun f (map real_flat ts)
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
  shows "real_flat (Fun f [Fun f [Var x, Var y], Var z]) = Fun f [Var x, Var y, Var z]"
  apply (simp add: assms)
  done

lemma example_4:
  assumes "label f = AC"
  shows "real_flat (Fun f [Fun f [Var x, Var y], Fun f [Var z, Fun f [Var w, Var v]]]) = 
                      Fun f [Var x, Var y, Var z, Var w, Var v]"
  apply (simp add: assms)
  done

lemma example_5:
  assumes "label f = AC"
  and "label g = Unin"
  shows "real_flat (Fun f [Fun f [Var x, Var y], Fun g [Var z, Fun f [Var w, Var v]]]) = 
                      Fun f [Var x, Var y, Fun g [Var z, Fun f [Var w, Var v]]]"
  apply (simp add: assms)
  done

fun h_height:: "('f, 'v) term \<Rightarrow> nat" where (*Move*)
"h_height (Var x) = 0"|
"h_height (Fun f ts) = (if (label f = Hom) then
    (1 + foldl max 0 (map h_height ts))
    else foldl max 0 (map h_height ts))"
  
  

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

(*fun real_flat_1 :: "('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "real_flat (Var x) = Var x" | 
  "real_flat (Fun f ts) = (case label f of 
                          AC \<Rightarrow> Fun f (flat_args_ac (Fun f (map real_flat ts))) |
                          _ \<Rightarrow> Fun f (map real_flat ts)
                          )" *)


end


(*Funçao Fresh:
fresh: 'v list \<Rightarrow> 'v


'v é um semigrupo (operaçao ++)

embedding: nat \<Rightarrow> 'v


fresh_pseudo: 'v list \<Rightarrow> 'v
1 - computar tamanho da lista |L| 
2 - escolha alguem em 'v, seja x
3 - Defina x_0 = x ++ embedding (|L| + 1)
4 - Se x_0 não pertence a L
     retorna x_0
    Caso contrário
     Defina x_1 = x ++ embedding (|L'| + 1)

Provar que para toda lista L, a imagem de fresh_pseudo L não pertence a L.
Criar um locale que assuma que exista embedding e que embedding é injetiva.
Definir a funçao fresh a partir de fresh_pseudo.

(* Note: I was trying to make this a single function, so it would become easier to use.
However, it seems Isabelle doesn't accept recursive let-in bindings.
Or I don't know the notation for it (in ML it is let rec, i tried let rec, let primerec, and so on)
TODO: certify that this is indeed the case.
fun fresh :: "'v list \<Rightarrow> 'v" where
"fresh l = (
  let rec f = \<lambda> l n .
  (
    let name_candidate = init \<star> (embedding n) in
    if name_candidate \<in> set l then
      f (removeAll name_candidate l) (Suc n)
    else
      name_candidate
  )
  in init)" *)

*)

locale name_freshness_defs =
  fixes embedding :: \<open>nat \<Rightarrow> 'v\<close>
    and init :: \<open>'v\<close>
    and concat :: \<open>'v \<Rightarrow> 'v \<Rightarrow> 'v\<close> (infixl \<open>\<star>\<close> 70)

begin
  fun fresh_aux :: \<open>'v list \<Rightarrow> nat \<Rightarrow> 'v\<close> where
  "fresh_aux l n = (
    let name = init \<star> (embedding n) in
    if name \<in> set l then
      fresh_aux (removeAll name l) (Suc n)
    else
      name
  )"

fun fresh :: \<open>'v list \<Rightarrow> 'v\<close> where
  "fresh l = fresh_aux l 0"

end

declare name_freshness_defs.fresh_aux.simps[code]
declare name_freshness_defs.fresh.simps[code]

locale name_freshness = name_freshness_defs +
  assumes embed_inj: "inj embedding"
  and op_semig : "(x \<star> y) \<star> z = x \<star> (y \<star> z)"

begin





lemma inc_test : "\<forall> l. fresh l \<notin> set [init]"
  sorry

lemma fresh_aux_sound : "\<forall> l n. fresh_aux l n \<notin> set l"
  sorry
(*
I commented this because it was producing an error.
proof(induct rule: fresh_aux.induct)

  case (1 l n)
  let ?name = "init \<star> embedding n"
  then show ?case sorry
*)
(*
lemma fresh_soulemma fresh_sound : "\<forall> l. fresh l \<notin> set l"
  using fresh_aux_sound by simp nd : "\<forall> l. fresh l \<notin> set l"
  using fresh_aux_sound by simp 
*)

end



(*
Try reading:
  https://isabelle.in.tum.de/website-Isabelle2025/dist/Isabelle2025/doc/codegen.pdf
on section 9.5, "Locales and Interpretation".
Code equations seems to be a form of a lemma, but i couldn't add them directly yet.
*)

global_interpretation nat_names : name_freshness "\<lambda> n . n" "0" "(+)"
  defines fresh_aux = name_freshness_defs.fresh_aux and fresh = name_freshness_defs.fresh
  by unfold_locales (auto)

value "nat_names.fresh [1,2]"

(*function fresh_aux :: "'v list \<Rightarrow> nat \<Rightarrow> 'v" where
  "fresh_aux L n  = (if x \<star> (embedding n) \<notin> set L 
                           then x \<star> (embedding n)
                           else fresh_aux L (Suc n)
                           )"
  apply (erule Product_Type.prod.exhaust)
  apply simp
  done

termination fresh_aux 
  apply (relation "measure (\<lambda>(L, n). length L - n - 1)")
   apply auto
  apply  ()
 *)


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
