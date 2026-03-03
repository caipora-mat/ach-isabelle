theory AC_equality

imports Main "First_Order_Terms.Term" "Syntax"

begin

context signature

begin

inductive eq_acw :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> ("_ \<approx>\<^sub>A\<^sub>C\<^sub>w  _" [80,80] 80) where 
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
            i < length ss \<and>
            j < length ts \<and>
            (ss!i) \<approx>\<^sub>A\<^sub>C\<^sub>w (ts!j) \<and>
            (Fun f (remove1 (ss!i) ss)) \<approx>\<^sub>A\<^sub>C\<^sub>w (Fun f (remove1 (ts!j) ts))
          )
          \<rbrakk> \<Longrightarrow> (Fun f ss) \<approx>\<^sub>A\<^sub>C\<^sub>w (Fun f ts)\<close>

definition eq_ac :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> ("_ \<approx>\<^sub>A\<^sub>C  _" [80,80] 80)
  where "eq_ac t1 t2 \<equiv> (flatten t1) \<approx>\<^sub>A\<^sub>C\<^sub>w (flatten t2)"

inductive_cases AC_eqw_elims:
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
next case (nac_fun f ts gs)
  then show ?case
    by (simp add: eq_acw.nac_fun)
next
  case (ac_fun f ts gs)
   have i:
   "\<exists> i j. (
    i < length gs \<and> 
    j < length ts) \<and> 
    (gs ! i \<approx>\<^sub>A\<^sub>C\<^sub>w  ts ! j) \<and> 
    (Fun f (remove1 (gs ! i) gs) \<approx>\<^sub>A\<^sub>C\<^sub>w Fun f (remove1 (ts ! j) ts)
   )"
     using ac_fun.IH ac_fun.hyps by blast+
  then show ?case using eq_acw.ac_fun[OF ac_fun(1)] by sorry
qed

lemma ac_eq_trans: \<open>\<lbrakk>s \<approx>\<^sub>A\<^sub>C\<^sub>w t ; t \<approx>\<^sub>A\<^sub>C\<^sub>w u \<rbrakk> \<Longrightarrow>  s \<approx>\<^sub>A\<^sub>C\<^sub>w u\<close>
  sorry


lemma ac_eq_subst: \<open> s \<approx>\<^sub>A\<^sub>C\<^sub>w t \<Longrightarrow>  (s \<cdot> \<sigma>) \<approx>\<^sub>A\<^sub>C\<^sub>w (t \<cdot> \<sigma>)\<close>
proof (induction s)
  case (Var x)
  then show ?case sorry
next
  case (Fun f ts)
  then show ?case sorry
qed

lemma ac_eq_fun: 
  assumes \<open>s \<approx>\<^sub>A\<^sub>C t\<close>
  shows \<open>(Fun f [s]) \<approx>\<^sub>A\<^sub>C (Fun f [t])\<close>
proof(cases "label f = AC")
  case True
   have i: "length [s] = length [t]" by simp
   have "\<exists> i j.
       (i \<le>length [s] \<and> j \<le> length [t]) \<and> [s] ! i \<approx>\<^sub>A\<^sub>C  [t] ! j \<and> Fun f (remove1 ([s] ! i) [s]) \<approx>\<^sub>A\<^sub>C  Fun f (remove1 ([t] ! j) [t])"
    using assms ac_refl by force
   with i show ?thesis using ac_fun[OF True] by sorry
next
  case False
    have i: "length [s] = length [t]" by simp
    have "\<And>i. i < length [s] \<Longrightarrow> [s]!i \<approx>\<^sub>A\<^sub>C [t]!i" 
      using assms ac_refl by simp
    with i show ?thesis using nac_fun[OF False i] by sorry
  qed

section \<open>Decidability of AC equality \<close>

text \<open>The functions below will be moved to another file, with proper generalizations.\<close>
fun fmap :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option\<close> (infixl \<open><$>\<close> 70) where
  \<open>fmap f None = None\<close> |
  \<open>fmap f (Some x) = Some (f x)\<close>

fun pure :: \<open>'a \<Rightarrow> 'a option\<close> where
  \<open>pure x = Some x\<close>

fun app :: \<open>('a \<Rightarrow> 'b) option \<Rightarrow> 'a option \<Rightarrow> 'b option\<close> where
  \<open>app None _ = None\<close> |
  \<open>app (Some f) x = fmap f x\<close>

text \<open>dec_find_inces P xs ys is Some (x,y) if there exists x \<in> set xs and y \<in> set ys such that P x y.
It is None otherwise.
\<close>
fun dec_find_witness :: \<open>('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) option\<close> where
  \<open>dec_find_witness P xs ys = (
    case xs of
      [] \<Rightarrow> None |
      x#xs \<Rightarrow> (
        case (find (P x) ys) of
        None \<Rightarrow> dec_find_witness P xs ys |
        Some y \<Rightarrow> Some (x,y)
      )
)\<close>

lemma dec_find_witness_exist:
  assumes \<open>dec_find_witness P xs ys = Some (x,y)\<close>
  shows \<open>\<exists> i j.(i < length xs \<and> j < length ys \<and> xs!i = x \<and> ys!j = y \<and> P (xs!i) (ys!j))\<close>
  sorry

function dec_acw :: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_acw s t = (
    if (dec_is_flattened s & dec_is_flattened t) then
      (case (s,t) of
        (Var x, Var y)   \<Rightarrow> (x = y) |
        (Var _, Fun _ _) \<Rightarrow> False   |
        (Fun _ _, Var _) \<Rightarrow> False   |
        (Fun f ss, Fun g ts) \<Rightarrow> (
          if f = g then
            case label f of
              AC \<Rightarrow> (
                let witness = dec_find_witness dec_acw ss ts in
                case witness of
                  None \<Rightarrow> False |
                  Some (s,t) \<Rightarrow> dec_acw (Fun f (remove1 s ss)) (Fun g (remove1 t ts))
              )|
                _ \<Rightarrow> foldl (\<and>) True (map (\<lambda> (x,y). dec_acw x y) (zip ss ts))
          else
            False
        )
      )
    else
      False
  )\<close>
  by pat_completeness auto


(* Every term is AC equivalent to its flattened version. *)
lemma flatten_ac_eq: \<open>(flatten t) \<approx>\<^sub>A\<^sub>C t\<close>
  sorry
(*
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
    then show ?thesis
      apply (simp)
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
qed *)

(*
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
*)
end
end