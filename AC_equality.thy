theory AC_equality

imports Main "First_Order_Terms.Term" "Syntax"

begin

context signature

begin

inductive eq_acw :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> ("_ \<approx>\<^sub>A\<^sub>C\<^sub>w  _" [80,80] 80) 
  where 
  ac_refl: \<open>\<lbrakk>is_flattened t\<rbrakk> \<Longrightarrow> t \<approx>\<^sub>A\<^sub>C\<^sub>w t\<close> |

  nac_fun: \<open>\<lbrakk>
          is_flattened (Fun f ss);
          is_flattened (Fun f ts);
          label f \<noteq> AC ;
          length ss = length ts;
          \<And>i. (i < length ss \<Longrightarrow> ss!i \<approx>\<^sub>A\<^sub>C\<^sub>w ts!i)
          \<rbrakk> \<Longrightarrow>  (Fun f ss) \<approx>\<^sub>A\<^sub>C\<^sub>w (Fun f ts)\<close> |

  ac_fun : \<open>\<lbrakk>
          is_flattened (Fun f ss);
          is_flattened (Fun f ts);
          label f = AC ;
          \<exists> i j. (
            i \<le> length ss \<and>
            j \<le> length ts \<and>
            (ss!i) \<approx>\<^sub>A\<^sub>C\<^sub>w (ts!j) \<and>
            (Fun f (remove1 (ss!i) ss)) \<approx>\<^sub>A\<^sub>C\<^sub>w (Fun f (remove1 (ts!j) ts))
          )
          \<rbrakk> \<Longrightarrow> (Fun f ss) \<approx>\<^sub>A\<^sub>C\<^sub>w (Fun f gs)\<close>

definition eq_ac :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> ("_ \<approx>\<^sub>A\<^sub>C  _" [80,80] 80)
  where "eq_ac t1 t2 \<equiv> (flatten t1) \<approx>\<^sub>A\<^sub>C\<^sub>w (flatten t2)"

inductive_cases AC_equ_elims:
"t \<approx>\<^sub>A\<^sub>C\<^sub>w t"
"(Fun f ts) \<approx>\<^sub>A\<^sub>C\<^sub>w (Fun f gs)"

text \<open> Next, we have to prove that this inductive relation is indeed an equivalent relation. \<close>

lemma ac_eq_refl:
  assumes \<open>is_flattened t\<close>
  shows \<open>t \<approx>\<^sub>A\<^sub>C\<^sub>w t\<close>
  using assms ac_refl by auto

lemma ac_eq_sym: \<open>s \<approx>\<^sub>A\<^sub>C\<^sub>w t \<Longrightarrow> t \<approx>\<^sub>A\<^sub>C\<^sub>w s\<close>
proof (induction rule: eq_acw.induct)
  case (ac_refl t)
  then show ?case 
    using eq_acw.ac_refl by auto
next
  case (nac_fun f ts gs)
  then show ?case
    by (simp add: eq_acw.nac_fun)
next
  case (ac_fun f ts gs)
   have i:
   "\<exists> i j.  (i \<le> length gs \<and>
          j \<le> length ts) \<and> 
    (gs ! i \<approx>\<^sub>A\<^sub>C  ts ! j) \<and> (Fun f (remove1 (gs ! i) gs) \<approx>\<^sub>A\<^sub>C  Fun f (remove1 (ts ! j) ts))"
     using ac_fun.IH ac_fun.hyps by blast+
  then show ?case using eq_acw.ac_fun[OF ac_fun(1)] by auto
qed

lemma ac_eq_trans:  \<open>\<lbrakk>s \<approx>\<^sub>A\<^sub>C\<^sub>w t ; t \<approx>\<^sub>A\<^sub>C\<^sub>w u \<rbrakk> \<Longrightarrow>  s \<approx>\<^sub>A\<^sub>C\<^sub>w u\<close>
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

fun dec_acw_cases :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_acw_cases s t = (
    case (s,t) of
      (Var x, Var y) \<Rightarrow> (x = y) |
      (Var _, Fun _ _) \<Rightarrow> False |
      (Fun _ _, Var _) \<Rightarrow> False |
      (Fun t ts, Fun g gs) \<Rightarrow> False
  )\<close>

fun dec_acw :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_acw s t = (
    if (dec_is_flattened s & dec_is_flattened t) then
      dec_acw_cases s t
    else
      False
  )\<close>

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

(* Every term is AC equivalent to its flattened version. *)
lemma flatten_ac_eq: \<open>(flatten t) \<approx>\<^sub>A\<^sub>C t\<close>
proof(induct t)
  case (Var x)
  then show ?case
    apply (simp)
    by (metis eq_ac_def flatten_soundness signature.ac_eq_refl)
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

text \<open> Some sanity tests for eq_acw. \<close>

lemma test2 :
  assumes "label f = AC"
  shows "Var x \<approx>\<^sub>A\<^sub>C\<^sub>w Var x"
  apply (rule ac_refl) 
  apply (rule var_is_flattened)
  done

lemma test1 : 
  assumes "label g = Unin "
  shows "Fun g [Var x] \<approx>\<^sub>A\<^sub>C\<^sub>w Fun g [Var x ]"
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
  shows "flatten (Fun f [Var x, Fun f [Var z, Var y]]) \<approx>\<^sub>A\<^sub>C\<^sub>w flatten (Fun f [Var x, Var y, Var z])"
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
end
end