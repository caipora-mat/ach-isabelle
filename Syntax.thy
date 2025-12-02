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


(* Collets all function symbols occuring in a term. *)
fun get_all_symbols :: "('f, 'v) term \<Rightarrow> 'f list" where
  \<open>get_all_symbols s = 
    (case s of
      Var _ \<Rightarrow> [] |
      Fun f ss \<Rightarrow> f # (concat (map get_all_symbols ss))
    )\<close>

(* Collects all AC symbols occurring in a term function. *)
fun get_all_ACs :: "('f, 'v) term \<Rightarrow> 'f list" where
  \<open>get_all_ACs (Var x) = []\<close> |
  \<open>get_all_ACs (Fun f ss) =
    (case (label f) of
      AC \<Rightarrow> f # (concat (map get_all_ACs ss)) |
      _  \<Rightarrow> concat (map get_all_ACs ss)
    )\<close>


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
  \<open>\<lbrakk>label f = AC; t \<in> set ts; g \<in> set (get_all_symbols t) \<and> g \<notin> set (get_all_ACs t)\<rbrakk>
      \<Longrightarrow> IsFlattened (Fun f ts)\<close>

text \<open> I think the definition of acIsFlattened is too strong, for example 
+(x, g(+(y,z),x) is flattened and it seems that the function does not agree with it.\<close>

lemma example2:
  assumes "label f = AC" and "label g = Unin"
  shows "IsFlattened (Fun f [Var x, Fun g [Fun f [Var y, Var x], Var x]])"
  apply (rule acIsFlattened)
    apply (simp add: assms(1))
  sorry

(* Now we define a function that decides the above predicate *)

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

lemma dec_pred_is_flatten: \<open>IsFlattened t \<longleftrightarrow> dec_is_flatten t\<close>
  sorry

(* TODO: prove this is sound and connect it with the predicate. *)

end


end