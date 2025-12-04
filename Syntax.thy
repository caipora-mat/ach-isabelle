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
lemma non_ac : \<open>label f \<noteq> AC \<Longrightarrow> label f = Unin \<or> label f = Hom\<close>
  using ach.exhaust by blast

section \<open>Flattened Terms\<close>

text \<open>\<close>

inductive IsFlattened :: \<open>('f, 'v) term \<Rightarrow> bool\<close> where
  (* Every variable term is flattened *)
  varIsFlattened: \<open>IsFlattened (Var x)\<close> |

  (* If s :: ('v, 'f) term is a non-AC application term, i.e., s is written as f(s1, ..., sn)
  then s is flattened if all of its arguments are.*)
  funIsFlattened:
  \<open>\<lbrakk>label f \<noteq> AC ; t \<in> set ts \<Longrightarrow> IsFlattened t\<rbrakk> \<Longrightarrow> IsFlattened (Fun f ts)\<close> |

  (* An application term (Fun f ts), headed by an AC symbol, is flattened whenever:
    for all t \<in> ts, and function symbol g occurring in t, g is not an AC symbol.*)
  acIsFlattened:
  \<open>\<lbrakk>label f = AC; t \<in> set ts;  t = Fun g tss; label g \<noteq> AC \<rbrakk>
      \<Longrightarrow> IsFlattened (Fun f ts)\<close>

value  "set [Var x, Fun g [Fun f [Var y, Var x], Var x]]"

lemma example2:
  assumes "label f = AC" and "label g = Unin"
  shows "IsFlattened (Fun f [Var x, Fun g [Fun f [Var y, Var x], Var x]])"
  apply (rule acIsFlattened)
   apply (simp add: assms(1))
    apply (simp)
    apply (auto)
   apply (simp add: assms(2))
  done

(* Now we define a function that decides the above predicate *)

fun dec_IsFlattened :: \<open>('f, 'v) term \<Rightarrow> bool\<close> where
  \<open>dec_IsFlattened (Var _) = True\<close> |
  \<open>dec_IsFlattened (Fun f ts) =
    (case label f of
      AC \<Rightarrow> (
        let is_headed_by_ac =
          \<lambda> s. (case s of
                  (Var _)   \<Rightarrow> False |
                  (Fun g _) \<Rightarrow> (case label g of AC \<Rightarrow> True | _ \<Rightarrow> False)
        ) in
        let ac_arg = find is_headed_by_ac ts in
        (case ac_arg of
          None \<Rightarrow> True |
          Some _ \<Rightarrow> False)
      )|
      _  \<Rightarrow> foldl (\<and>) True (map dec_IsFlattened ts)
    )\<close>

lemma dec_pred_is_flatten: \<open>\<forall>s. IsFlattened s \<longleftrightarrow> dec_IsFlattened s\<close>
  sorry

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

*)

text \<open>We define a function that flattens a term\<close>

end
end