theory AC_equality

imports Main "First_Order_Terms.Term" "Syntax"

begin

context signature

begin

inductive eq_ac:: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> ("_ \<approx>\<^sub>A\<^sub>C  _" [80,80] 80) 
  where 
  ac_refl: \<open> \<lbrakk>is_flattened t\<rbrakk> \<Longrightarrow> t \<approx>\<^sub>A\<^sub>C t \<close> |
  
  nac_fun: \<open> \<lbrakk>
          is_flattened (Fun f ts);
          is_flattened (Fun f gs);
          label f \<noteq> AC ;
          length ts = length gs ;
          \<And>i. (i < length ts \<Longrightarrow> ts!i \<approx>\<^sub>A\<^sub>C gs!i)
          \<rbrakk> \<Longrightarrow>  (Fun f ts) \<approx>\<^sub>A\<^sub>C (Fun f gs)\<close> |

  ac_fun [simp]: \<open>\<lbrakk>
          is_flattened (Fun f ts);
          is_flattened (Fun f gs);
          label f = AC ;
          \<exists> i j. (i \<le> length ts \<and> j \<le> length gs \<and>
             (ts!i) \<approx>\<^sub>A\<^sub>C (gs!j) \<and>
             (Fun f (remove1 (ts!i) ts)) \<approx>\<^sub>A\<^sub>C (Fun f (remove1 (gs!j) gs))
          )
          \<rbrakk> \<Longrightarrow>  (Fun f ts) \<approx>\<^sub>A\<^sub>C (Fun f gs)\<close>

lemma test2 : 
  assumes "label f = AC"
  shows "Var x \<approx>\<^sub>A\<^sub>C Var x"
  apply (rule ac_refl) 
  apply (rule var_is_flattened)
  done

lemma test1 : 
  assumes "label g = Unin "
  shows "Fun g [Var x] \<approx>\<^sub>A\<^sub>C Fun g [Var x ]"
  apply (rule nac_fun)
      apply (rule fun_is_flattened)
       apply (simp add: assms)
      apply (auto)
    apply (rule fun_is_flattened)
     apply  (simp add: assms)
    apply (auto)
   apply (simp add:assms)
  apply (rule  ac_refl)
  apply (rule var_is_flattened)
  done

lemma test3 : 
  assumes "label f = AC "
  shows "flatten (Fun f [Var x, Fun f [Var z, Var y]]) \<approx>\<^sub>A\<^sub>C flatten (Fun f [Var x, Var y, Var z])"
  apply (simp add: assms)
  apply (rule ac_fun)
  apply (rule ac_is_flattened)
       apply (simp add: assms)
  subgoal 1
    apply (auto)
    done
  subgoal 2
    apply (auto)
    done 
    apply (rule ac_is_flattened)
      apply (simp add: assms)
  subgoal 1
    apply (auto)
    done
  subgoal 
    apply (auto)
    done
   apply (simp add: assms)
  apply (rule exI[where x = 0])
  apply (rule exI[where x = 0])
  apply (rule conjI)
   apply (simp)
  apply (rule conjI)
   apply (simp)
  apply (rule conjI)
   apply (simp)
   apply (rule ac_refl)
   apply (simp)
  apply (simp)
  apply (rule ac_fun)
  sorry


inductive_cases AC_equ_elims:
"t \<approx>\<^sub>A\<^sub>C t"
"(Fun f ts) \<approx>\<^sub>A\<^sub>C (Fun f gs)"

(*lemma test1x:
  assumes "label f = AC"
  and "x \<noteq> y"
shows "\<not>(eq_ac (Fun f [Var x]) (Fun f [Var y]))"
proof-
  have i: "[Var x] \<noteq> [Var y]"
    using assms by auto
  hence "Fun f [Var x] \<noteq> Fun f [Var y]"
    using ac_fun by simp
  then have "\<not>(\<exists> j. j \<le> length [Var y] \<and> eq_ac ([Var x] ! 0) ([Var y] ! j) \<and>
            eq_ac (Fun f (remove1 ([Var x] ! 0) [Var x])) (Fun f (remove1 ([Var y] ! j) [Var y])))"
    using eq_ac.cases length_0_conv neq_Nil_conv nth_Cons_0 remove1.simps(2)
        signature.AC_equ_elims(2) term.distinct(1) by (metis)
  with i assms show ?thesis using AC_equ_elims(2)[of f \<open>[Var x]\<close> \<open>[Var y]\<close>] by auto
qed*)

(*lemma test2x:
  assumes "label f = AC"
  shows "eq_ac (Fun f [Var x, Fun g []]) (Fun f [Fun g [], Var x])"
  apply (rule ac_fun)
    apply (simp add: assms, auto)
  sorry*)

(* 

  [x ; y ; z] = [y ; w ; x] \<Rightarrow> \<exists>j. x =AC rs!j, take j = 2 
                            \<Longrightarrow> x =AC x \<and> [y ; z] = [y ; w]
                            \<Longrightarrow> x =AC x \<and> y =AC y \<and> [z] = [w]
                            \<Longrightarrow> False

  E = { x + y = y + x ; (x + y) + z = x + (y + z) }

 \<approx>_E
   
  T(\<Sigma>,X) / \<approx>E (this is an initial algebra)

  if unif_ac(s,t) = \<sigma>, then s \<cdot> \<sigma> =AC t \<cdot> \<sigma> (syntactic soundness)
  
  s =AC t iff s \<approx>_AC t (algebraic soundness)

  can i conclude:
  
  unif_ac(s,t) = \<sigma> \<Longrightarrow> s \<sigma> \<approx>_AC t \<sigma>
*)


text \<open> Next, we have to prove that this inductive relation is indeed an equivalent relation. \<close>

(* comes directly from the refl axiom *)
lemma ac_eq_refl: \<open>t \<approx>\<^sub>A\<^sub>C t\<close>
  using ac_refl by blast
  

lemma ac_eq_sym: \<open>s \<approx>\<^sub>A\<^sub>C t \<Longrightarrow> t \<approx>\<^sub>A\<^sub>C s\<close>
proof (induction rule: eq_ac.induct)
  case (ac_refl t)
  then show ?case 
    using eq_ac.ac_refl by auto
next
  case (nac_fun f ts gs)
  then show ?case
    by (simp add: eq_ac.nac_fun)
next
  case (ac_fun f ts gs)
   have i:
   "\<exists> i j.  (i \<le> length gs \<and>
          j \<le> length ts) \<and> 
    (gs ! i \<approx>\<^sub>A\<^sub>C  ts ! j) \<and> (Fun f (remove1 (gs ! i) gs) \<approx>\<^sub>A\<^sub>C  Fun f (remove1 (ts ! j) ts))"
     using ac_fun.IH ac_fun.hyps by blast+
  then show ?case using eq_ac.ac_fun[OF ac_fun(1)] by auto
qed


lemma ac_eq_trans:  \<open>\<lbrakk>s \<approx>\<^sub>A\<^sub>C t ; t \<approx>\<^sub>A\<^sub>C u \<rbrakk> \<Longrightarrow>  s \<approx>\<^sub>A\<^sub>C u\<close>
  sorry


lemma ac_eq_subst: \<open> s \<approx>\<^sub>A\<^sub>C t \<Longrightarrow>  (s \<cdot> \<sigma>) \<approx>\<^sub>A\<^sub>C (t \<cdot> \<sigma>)\<close>
proof (induction s)
  case (Var x)
  then show ?case sorry
next
  case (Fun f ts)
  then show ?case sorry
qed
 

(* Question 1: is this really closure for \<Sigma>-operations when the arguments are lists?
  I'm thinking I have to say something like: \<forall> t \<in> set ts. ... 
  Question 2: perhaps we can put closure for \<Sigma>-operations and substitutions as axioms?
*)


lemma ac_eq_fun: 
  assumes \<open>s \<approx>\<^sub>A\<^sub>C t\<close>
  shows \<open>(Fun f [s]) \<approx>\<^sub>A\<^sub>C (Fun f [t])\<close>
proof(cases "label f = AC")
  case True
   have i: "length [s] = length [t]" by simp
   have "\<exists> i j.
       (i \<le>length [s] \<and> j \<le> length [t]) \<and> [s] ! i \<approx>\<^sub>A\<^sub>C  [t] ! j \<and> Fun f (remove1 ([s] ! i) [s]) \<approx>\<^sub>A\<^sub>C  Fun f (remove1 ([t] ! j) [t])"
    using assms ac_refl by force
   with i show ?thesis using ac_fun[OF True] by blast
next
  case False
    have i: "length [s] = length [t]" by simp
    have "\<And>i. i < length [s] \<Longrightarrow> [s]!i \<approx>\<^sub>A\<^sub>C [t]!i" 
      using assms ac_refl by simp
    with i show ?thesis using nac_fun[OF False i] by simp
qed


(*If t = f (t1,...,tn) and  t1 \<approx>AC t1' 

then f(t1,...,tn)\<approx>AC f(t1',...,tn')
*)

section \<open>Decidability of AC equality \<close>

text \<open>The purpose of this function is to then algorithimically decide the relation above.

We implement the deduction rules above as follows by destruction on their structure:
1. Two Vars are equal if they underlying names are equal.
  - It is sound because we can never show x = y with x \<noteq> y using reflexivity.
2. Compare whenever we have a variable and a function, those are all false.

3. We compare when the two terms are of the shape: (Fun f ts) (Fun g gs)

  

\<close>


function dec_ac :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_ac (Var x) (Var y) = (x = y)\<close> |
  \<open>dec_ac (Var _) (Fun _ _) = False\<close> |
  \<open>dec_ac (Fun _ _) (Var _) = False\<close> |
  \<open>dec_ac (Fun f ts) (Fun g gs) = (
    if (f = g) \<and> (length ts = length gs) then
      (if length ts = 0 then
        True
      else
        (case label f of
          AC \<Rightarrow> (
            let t0 = hd ts in
            let eq_exists = find (\<lambda> sj. dec_ac t0 sj) gs  in
            (case eq_exists of
              None \<Rightarrow> False |
              Some sj \<Rightarrow> dec_ac (Fun f (remove1 t0 ts)) (Fun f (remove1 sj gs)))
          )|
          _ \<Rightarrow> foldl (\<and>) True (map (\<lambda> (x,y). dec_ac x y) (zip ts gs))
        )
      )
    else
      False
  )\<close>
  by pat_completeness auto

(*
value "dec_ac (Var 0) (Fun f [Var 0])" (* I don't know why this doesn't compute since this case doesnt'depend on how label is defined... *)
*)

(* Every term is AC equivalent to its flattened version. *)
lemma flatten_ac_eq: \<open>(flatten t) \<approx>\<^sub>A\<^sub>C t\<close>
proof(induct t)
  case (Var x)
  then show ?case
    using ac_refl by auto
next
  case (Fun f ts)
  then show ?case 
  proof(cases "label f = AC")
    case True
    then show ?thesis sorry
  next
    case False
    have lengths: "length (map flatten ts) = length ts"
      by simp
    have i: "flatten (Fun f ts) = Fun f (map flatten ts)"
      using flatten.simps False non_ac by force
    from Fun nac_fun[OF False lengths] 
    have "Fun f (map flatten ts) \<approx>\<^sub>A\<^sub>C Fun f ts"
      using nth_mem by fastforce
    with i show ?thesis by auto
  qed
qed



end


end