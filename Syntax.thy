theory Syntax

imports Main "First_Order_Terms.Term"

begin

datatype ach = Unin | AC | Hom

locale signature =
  fixes arity :: "'f \<Rightarrow> nat"
    and label :: "'f \<Rightarrow> ach"
  assumes label_inj: "inj label"

begin

(* baby lemmas about labels *)
lemma non_ac : 
  assumes \<open>label f \<noteq> AC\<close>
  shows \<open>label f = Unin \<or> label f = Hom\<close>
using ach.exhaust assms by blast

section \<open>Flattened Terms\<close>

text \<open>blabla \<close>


inductive IsFlattened :: "('f, 'v) term \<Rightarrow> bool" where
  varIsFlattened:
    "IsFlattened (Var x)" |

  funIsFlattened:
    "\<lbrakk> label f \<noteq> AC;
       \<And>t. t \<in> set ts \<Longrightarrow> IsFlattened t \<rbrakk>
     \<Longrightarrow> IsFlattened (Fun f ts)" |

  acIsFlattened:
    "\<lbrakk> label f = AC;
       \<And>t. t \<in> set ts \<Longrightarrow> IsFlattened t;
       \<And>t g tss. t \<in> set ts \<Longrightarrow> t = Fun g tss \<Longrightarrow> g \<noteq> f \<rbrakk>
     \<Longrightarrow> IsFlattened (Fun f ts)"

(*

Is_Flattened t1 \<and> Is_Flattened t2 \<and> Is_Flattened t3 \<and> head(ti)\<noteq> f
------------------------------------------------------------------- f=AC
Is_flattened f[t1,t2,t3]
*)
lemma test1_IsFlattened:
  assumes "label f = Unin"
  shows "IsFlattened (Fun f [Var x, Fun f [Var y, Var x]])"
  by (metis ach.simps(2) assms empty_set funIsFlattened list.simps(15) set_ConsD singletonD
      varIsFlattened)


lemma test2_IsFlattened:
  assumes "label f = AC"
  shows "\<not> IsFlattened (Fun f [Var x, Fun f [Var y, Var x]])"
  using assms signature.IsFlattened.cases signature_axioms by force
 
 
(*
lemma test1_IsFlattened:
  assumes "label f = AC" and "label g = Hom"
  shows "\<not>(IsFlattened (Fun f [Var x, Fun g [Var y, Fun f [Var z, Fun f [Var z, Var x]]]]))"
  sorry 

  
lemma test2_IsFlattened:
  assumes "label f = AC" and "label g = Hom"
  shows "IsFlattened (Fun f [Var x, Fun g [Var y, Fun f [Var z, Fun f [Var z, Var x]]]])"
   sorry

*)
value  "set [Var x, Fun g [Fun f [Var y, Var x], Var x]]"

lemma example2:
  assumes "label f = AC" and "label g = Unin"
  shows "IsFlattened (Fun f [Var x, Fun g [Fun f [Var y, Var x], Var x]])"
  sorry

(* Now we define a function that decides the above predicate *)

fun is_headed_by_ac :: \<open>('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>is_headed_by_ac s =
    (case s of
      (Var _)   \<Rightarrow> False |
      (Fun g _) \<Rightarrow> (case label g of
        AC \<Rightarrow> True |
        _ \<Rightarrow> False)
  )\<close>


lemma test_is_headed_by_ac:
  assumes "label f = AC" and "label g = Unin"
  shows "is_headed_by_ac (Fun f [Var x, Fun g [Var y, Var z]])"
  using assms by simp

lemma test_is_not_headed_by_ac:
  assumes "label f = AC" and " label g = Hom"
  shows "\<not> is_headed_by_ac (Fun g [Var x, Fun f [Var y, Var z]])"
proof
  assume H: "is_headed_by_ac (Fun g [Var x, Fun f [Var y, Var z]])"
  from H have "(case label g of AC \<Rightarrow> True | _ \<Rightarrow> False)"
    by simp
  moreover from assms have "label g = Hom" 
    by simp
  ultimately show "False" by simp
qed


fun dec_IsFlattened :: \<open>('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_IsFlattened (Var _) = True\<close> |
  \<open>dec_IsFlattened (Fun f ts) =
    (case label f of
      AC \<Rightarrow> (
        let ac_arg = find is_headed_by_ac ts in
        (case ac_arg of
          None \<Rightarrow> True |
          Some _ \<Rightarrow> False)
      )|
      _  \<Rightarrow> foldl (\<and>) True (map dec_IsFlattened ts)
    )\<close>


lemma test_dec_IsFlattened:
  assumes "label f = AC"
  shows "\<not> dec_IsFlattened (Fun f [Var x, Fun f [Var y, Var z]])"
  using assms by simp

text \<open> The following should not be possible to prove. \<close>
lemma test1_dec_IsFlattened:
  assumes "label f = AC" and "label g = Hom"
  shows " dec_IsFlattened (Fun f [Var x, Fun g [Var y, Fun f [Var z, Fun f [Var z, Var x]]]])"
  apply (auto)
  apply (simp add: assms)
  done 

lemma dec_pred_flatten:
  assumes "IsFlattened s"
  shows " dec_IsFlattened s"
  apply (induction s)
   apply (simp)
  sorry

lemma dec_pred_is_flatten:
  "IsFlattened s \<longleftrightarrow> dec_IsFlattened s" (is "?L \<longleftrightarrow> ?R ")
  sorry

(*proof (cases s)
  case (Var x)
  then show ?thesis
    using Var varIsFlattened by fastforce
next
case (Fun f ts)
  then show ?thesis
  proof
    assume H: "IsFlattened (Fun f ts)"
    from H show ?thesis
      unfolding dec_IsFlattened_def
    proof (cases "label f = AC")
      case True
      (* AC case: use your acIsFlattened rule / elimination to match
         the condition that dec_IsFlattened checks for AC-symbols *)
      from H True show ?thesis
        by (auto elim: IsFlattened.cases)
    next
      case False
      (* non-AC case: use funIsFlattened + IH on all arguments *)
      from H False show ?thesis
        by (auto elim: IsFlattened.cases)
    qed
  next
    assume H: "dec_IsFlattened (Fun f ts)"
    show "IsFlattened (Fun f ts)"
      unfolding dec_IsFlattened_def
    proof (cases "label f = AC")
      case True
      (* AC case: build an IsFlattened proof using acIsFlattened *)
      from H True show ?thesis
        by (auto intro: IsFlattened.intros)
    next
      case False
      (* non-AC case: use funIsFlattened and IH on arguments *)
      from H False show ?thesis
        by (auto intro: IsFlattened.intros)
    qed
  qed
qed
*)
(*

This function is too complicated, the implementation above is simpler.
Leaving the old one here to compare. Deleate it on next commit.

fun dec_is_flatten_aux :: \<open>('f, 'v) term \<Rightarrow> bool \<Rightarrow> bool\<close> where
  (* \<open>dec_is_flatten_aux (Var _) True = False\<close>  | *)
  \<open>dec_is_flatten_aux (Var _) _ = True\<close>   |
  \<open>dec_is_flatten_aux (Fun f ts) False =
    (case (label f) of
      AC \<Rightarrow> foldl (\<and>) True (map (\<lambda> t. dec_is_flatten_aux t True) ts)|
      _ \<Rightarrow>  foldl (\<and>) True (map (\<lambda> t. dec_is_flatten_aux t False) ts)
    )\<close> |
  \<open>dec_is_flatten_aux (Fun f ts) True =
    (case (label f) of
      AC \<Rightarrow> False |
      _  \<Rightarrow> foldl (\<and>) True (map (\<lambda> t. dec_is_flatten_aux t False) ts)
    )\<close>

fun dec_is_flatten :: \<open>('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_is_flatten t = dec_is_flatten_aux t False\<close>


+ [s1 , ..., sm ]

  1. 


*)

text \<open>We define a function that flattens a term\<close>

fun pred_split_aux :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a list \<Rightarrow> 'a list * 'a list\<close> where
  \<open>pred_split_aux P xs (ys,ns)=
    (case xs of
      []      \<Rightarrow> (ys,ns) |
      x # xs' \<Rightarrow> (
        if P x then 
          pred_split_aux P xs' (x#ys, ns)
        else
          pred_split_aux P xs' (ys, x#ns)
      )
    )\<close>

fun pred_split :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list * 'a list\<close> where
  \<open>pred_split P xs = pred_split_aux P xs ([],[])\<close>

fun flatten :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term\<close> where
  \<open>flatten s = 
    (case s of
      Var _    \<Rightarrow> s |
      Fun f ss \<Rightarrow>
        (case label f of
          AC \<Rightarrow> (
            let args_split = pred_split is_headed_by_ac ss in
            let ac_args  = fst args_split in
            let nac_args = snd args_split in
            (case ac_args of
              []    \<Rightarrow> s |
              _ # _ \<Rightarrow> (
                let args_of_ac_args = concat (map args ac_args) in
                Fun f (args_of_ac_args @ nac_args)
              )
            )
        )|
          _  \<Rightarrow> Fun f (map flatten ss)
        )
    )\<close>

text \<open>O exemplo abaixo está com problema \<close>

lemma test1_Flatten:
  assumes "label f = AC" and "label g = Hom"
  shows " flatten (Fun f [Var x, Fun g [Var y, Fun f [Var z, Fun f [Var z, Var x]]]]) = Fun f [Var x, Fun g [Var y, Fun f [Var z, Var z, Var x]]] "
  apply (simp add: assms)
  sorry

lemma flatten_soundness: \<open>\<forall> t::('f, 'v) term. IsFlattened (flatten t)\<close>
  sorry

(* or *)

lemma flatten_soundness_dec: \<open>\<forall> t::('f, 'v) term. dec_IsFlattened t \<close>
  sorry


(* I think this function is correct in the sense of the lemmas above.
  However, i think it is still wrong: 
  notice that we only check for those arguments that are labelled with AC without ever
  discriminating them apart, and we put all together...
  this will cause flatten to change the semantics of the term whenever the
  input signature have more than one symbol labelled as AC.

  Mean Spirited Example:
  Let \<Sigma> be f : AC, and g : AC, (other symbols can be added...

  So flatten of s = f [t1 ; ..., g [s1,s2] , ...., g [s3, s4] , ... , tn) will compute as follows:

  ac_args = [ g[s1,s2] , g [s3, s4] ] (so we collected all AC arguments of s), 
  the non ac arguments are on the other list

  args_of_ac_args = [ [s1, s2] , [s3, s4] ] (collect all the arguments of the AC terms)

  then we flatten the list

  args_of_ac_args = [s1, s2, s3, s4 ]

  later we combine them back into the arguments of s

  flatten s = f [s1 , s2 , s3 , s4] @ [t1, ...., tn ]

  now see that g function symbol disappeared...

  BUT according to our relation IsFlattened flatten s is flat, which is actually correct

  but s above is not flat...

  if we consider a signature that has more than one ac symbol:
      s = f [t1 ; ..., g [s1,s2] , ...., g [s3, s4] , ... , tn)
      is flattened, (assuming f doesn't occur in the t_is for simplicity's sake)

      so IsFlattened MUST be defined with respect to the same function symbol
      not only the labels.

      This way, s is flattened because none of 
      its direct arguments are labelled AC AND are headed by f

      

Questions then:
  1. Can our ACh (or even the AC from maximal) algorithm deal with more than one AC symbol?
    - Intuitively, it can as long as we can dinamically change the label of a symbol.
    - But i am not sure if this was even considered by guilherme when defining the ACh unification.
    

Possible approaches:
  1. We restrict the whole formalization and terms to a single AC constructor.
    - Functions must change, but that's fine since we are earlier in the definitions.
    - The predicate IsFlattened and flatten function doesn't change

  2. We keep it general and allow for multiple AC symbols.
    - Then we need to change IsFlattened and flatten.
    - I don't think anything changes on the definition of equality since there we enforce
    that two functions headed by function symbol are equal only if their head symbols are equal.

I like 2 more, specially if the original paper only considered a single AC symbol... 
We can say we have a general ACh unification that is also formalized :)

I am taking this decision alone so discussions are needed.

*)

end
end