theory AC_equality

imports Main "First_Order_Terms.Term" "Syntax"

begin

context signature

begin

inductive eq_ac:: \<open>('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool\<close> where
  ac_refl: \<open>eq_ac t t\<close> |
  
  nac_fun: \<open> \<lbrakk>
          label f \<noteq> AC ;
          length ts = length gs ;
          \<And>i. (i < length ts \<Longrightarrow> eq_ac (ts!i) (gs!i))
          \<rbrakk> \<Longrightarrow> eq_ac (Fun f ts) (Fun f gs)\<close> |

  ac_fun: \<open>\<lbrakk>
          label f = AC ;
          length ts = length gs ;
          \<exists> j. ( j \<le> length ts \<and>
            eq_ac (ts!0) (gs!j) \<and>
            eq_ac (Fun f (remove1 (ts!0) ts)) (Fun f (remove1 (gs!j) gs))
          )
          \<rbrakk> \<Longrightarrow> eq_ac (Fun f ts) (Fun f gs)\<close>

lemma test1x:
  assumes "label f = AC"
  and "x \<noteq> y"
  shows "\<not>(eq_ac (Fun f [Var x]) (Fun f [Var y]))"
proof
  assume "eq_ac (Fun f [Var x]) (Fun f [Var y])"
  have "[Var x] \<noteq> [Var y]"
    using assms by simp
  hence "Fun f [Var x] \<noteq> Fun f [Var y]"
    using ac_fun by simp
  then have "\<not>(\<exists> j. j \<le> length [Var y] \<and> eq_ac ([Var x] ! 0) ([Var y] ! j) \<and>
            eq_ac (Fun f (remove1 ([Var x] ! 0) [Var x])) (Fun f (remove1 ([Var y] ! j) [Var y])))"
  proof(cases "j=0")
    case True
    then have "\<not>(eq_ac ([Var x] ! 0) ([Var y] ! 0))"
      using assms by simp
  next
    case False
    then show ?thesis sorry
  qed
    
  then show "False" using ac_fun assms by auto
    
  


lemma test2x:
  assumes "label f = AC"
  shows "eq_ac (Fun f [Var x, Fun g []]) (Fun f [Fun g [], Var x])"
  apply (rule ac_fun)
    apply (simp add: assms, auto)
  sorry

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
lemma ac_eq_refl: \<open>eq_ac t t\<close>
  using ac_refl by blast
  

lemma ac_eq_sym: \<open>eq_ac s t \<Longrightarrow> eq_ac t s\<close>
proof (induction rule: eq_ac.induct)
  case (ac_refl t)
  then show ?case 
    using ac_eq_refl by blast
next
  case (nac_fun f ts gs i)
  then show ?case 
    using eq_ac.nac_fun
    by metis
next
  case (ac_fun f ts gs)
  then show ?case sorry
qed



lemma ac_eq_trans: \<open>eq_ac s t \<and> eq_ac t u \<Longrightarrow> eq_ac s u\<close>
  sorry


lemma ac_eq_subst: \<open>eq_ac s t \<Longrightarrow> eq_ac (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)\<close>
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
lemma ac_eq_fun: \<open>eq_ac s t \<Longrightarrow> eq_ac (Fun f [s]) (Fun f [t])\<close>
  sorry

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

value "dec_ac (Var 0) (Fun f [Var 0])" (* I don't know why this doesn't compute since this case doesnt'depend on how label is defined... *)

(* Every term is AC equivalent to its flattened version. *)
lemma flatten_ac_eq: \<open>\<forall> t::('f, 'v) term. eq_ac (flatten t) t\<close>
  sorry

end
end