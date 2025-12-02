theory AC_equality

imports Main "First_Order_Terms.Term" "Syntax"

begin

(*

Inductive definition of the relation =AC.

                      \<forall>i. t_i  =AC s_i   label f \<noteq> AC
      --------------------------------------------------------
                   f(t1,...tn) =AC f(s1, ..., sn)

      \<exists> j. t1 =AC s_j    f(t_2, ..., tn) =AC f(s1, ..., s_{j-1},s_{j+1} ..., s_n)
      -----------------------------------------------------------------------------------------
                  f(t1,...tn) =AC f(s1, ..., sn)



espirito de porco?

1. x + y = x + y + y


*)

(* 
  1. define proj em lista
  


*)

inductive eq_ac:: \<open>('v, 'f) term \<Rightarrow> ('v, 'f) term \<Rightarrow> bool\<close> where
  ac_refl: \<open>eq_ac t t\<close> |
  
  nac_fun: \<open> \<lbrakk>
          label f \<noteq> AC ;
          length ts > 0 ;
          length ts = length gs ;
          i < length ts \<Longrightarrow> ts!i = gs!i
          \<rbrakk> \<Longrightarrow> eq_ac (Fun f ts) (Fun f gs)\<close> |

  ac_fun: \<open>\<lbrakk>
          label f = AC ;
          length ts > 0 ;
          length ts = length gs ;
          \<exists> j. (
            ts!1 = gs!j \<and>
            eq_ac (Fun f (remove1 (ts!1) ts)) (Fun f (remove1 (ts!i) ts))
          )
          \<rbrakk> \<Longrightarrow> eq_ac (Fun f ts) (Fun f gs)\<close>

text \<open> Next, we have to prove that this inductive relation is indeed an equivalent relation. \<close>

(* comes directly from the refl axiom *)
lemma ac_eq_refl: \<open>eq_ac t t\<close>
  sorry

lemma ac_eq_sym: \<open>eq_ac s t \<Longrightarrow> eq_ac t s\<close>
  sorry

lemma ac_eq_trans: \<open>eq_ac s t \<and> eq_ac t u \<Longrightarrow> eq_ac s u\<close>
  sorry


lemma ac_eq_subst: \<open>eq_ac s t \<Longrightarrow> eq_ac (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)\<close>
  sorry

(* Question 1: is this really closure for \<Sigma>-operations when the arguments are lists?
  I'm thinking I have to say something like: \<forall> t \<in> set ts. ... 
  Question 2: perhaps we can put closure for \<Sigma>-operations and substitutions as axioms?
*)
lemma ac_eq_fun: \<open>eq_ac s t \<Longrightarrow> eq_ac (Fun f [s]) (Fun f [t])\<close>
  sorry