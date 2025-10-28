theory Freshness

imports Main

begin

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
  and init_not_null : "\<forall> x. init \<star> x \<noteq> init"

begin

  (*lemma inc_test : "\<forall> l. fresh l \<notin> set [init]"
    sorry*)

find_theorems abs
thm "finite_set"



  lemma fresh_aux_sound : "fresh_aux l n \<notin> set l"
    proof(cases "init \<star> embedding n \<in> set l")
      case True
      then show ?thesis
        sorry
    next
      case False
      then show ?thesis 
        using fresh_aux.simps by simp
    qed
    


  lemma fresh_sound : "\<forall> l. fresh l \<notin> set l"
    using fresh_aux_sound by simp


end

global_interpretation nat_names : name_freshness "\<lambda> n . n" "2" "(*)"
  by unfold_locales (auto)

value "nat_names.fresh [0,1,2]"

value "name_freshness_defs.fresh (\<lambda> n. n) 0 (+) [0, 1, 2]" (* Aha! Now it computes! *)

end