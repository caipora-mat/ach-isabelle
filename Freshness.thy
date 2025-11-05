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
  (* and init_not_null : "\<forall> x. (init \<noteq> x \<longrightarrow> init \<star> x \<noteq> init)" *)
  and is_cancelative : \<open>x \<star> y = x \<star> z \<longrightarrow> y = z\<close>

begin

lemma init_embed_inj : \<open>\<forall> n. inj (\<lambda> n. init \<star> (embedding n))\<close>
  using is_cancelative embed_inj inj_def
  by meson


lemma fresh_aux_subset:
  "set (removeAll (init \<star> embedding n) l) \<subseteq> set l"
  by (induction l) auto


lemma fresh_exist : \<open>\<exists> m. fresh_aux l n = init \<star> (embedding m)\<close>
  proof (induction "length l" arbitrary: n l rule: less_induct)
    case less
    then show ?case
    proof (cases "init \<star> embedding n \<in> set l")
      case False
      then show ?thesis using fresh_aux.simps by (smt (verit))
    next
      case True
      let ?a = "init \<star> embedding n"
      let ?l' = "removeAll ?a l"
      have "length ?l' < length l"
        using True by (simp add: length_removeAll_less)
      then obtain k where "fresh_aux ?l' (Suc n) = init \<star> embedding k"
        using less by blast
      hence "fresh_aux l n = init \<star> embedding k"
      using fresh_aux.simps True by simp
    thus ?thesis by blast
    qed
  qed

lemma fresh_aux_index_ge:
  "fresh_aux l n = init \<star> embedding k \<Longrightarrow> k \<ge> n"
proof (induction "length l" arbitrary: n l k rule: less_induct)
  case less
  then show ?case
  proof (cases "init \<star> embedding n \<in> set l")
    case False
    then have "fresh_aux l n = init \<star> embedding n" by simp
    then show ?thesis using \<open>fresh_aux l n = init \<star> embedding k\<close> less.prems init_embed_inj inj_def order_refl 
      by metis
  next
    case True
    let ?a = "init \<star> embedding n"
    let ?l' = "removeAll ?a l"
    have "length ?l' < length l" using True by (simp add: length_removeAll_less)
    have step_eq: "fresh_aux l n = fresh_aux ?l' (Suc n)"
      using fresh_aux.simps True by (smt (verit))
    from \<open>fresh_aux l n = init \<star> embedding k\<close> and step_eq
    have "fresh_aux ?l' (Suc n) = init \<star> embedding k" by simp
   hence "k \<ge> Suc n"
     using less \<open>length ?l' < length l\<close> by blast
    thus ?thesis by simp
  qed
qed


lemma fresh_aux_sound_aux: 
  assumes i: "x \<notin> set (removeAll a l)"
  and ii: "x \<noteq> a"
  and iii: "a \<in> set l"
shows "x \<notin> set l"
  using assms set_removeAll by auto


lemma fresh_aux_sound : "fresh_aux l n \<notin> set l"
proof (induction "length l" arbitrary: n l rule: less_induct)
  case less
  then show ?case
  proof(cases "init \<star> embedding n \<in> set l")
    case False
    then show ?thesis using fresh_aux.simps by simp
  next
  let ?l' = "removeAll (init \<star> embedding n) l"
  case True
  let ?a = "init \<star> embedding n"
     have len_l': "length ?l' < length l" 
       using True
       by (simp add: length_removeAll_less)
     have IH: "fresh_aux ?l' (Suc n) \<notin> set ?l'"
       using less[OF len_l'] by simp
     have eq: "fresh_aux l n = fresh_aux ?l' (Suc n)"
       using fresh_aux.simps True by (smt (verit))
     moreover have "fresh_aux ?l' (Suc n) \<noteq> ?a"
       proof
         assume eq: "fresh_aux ?l' (Suc n) = ?a"
         then obtain m where m_def: "fresh_aux ?l' (Suc n) = init \<star> embedding m"
           using fresh_exist by blast
         hence "m \<ge> Suc n"
           using \<open>fresh_aux ?l' (Suc n) = init \<star> embedding m\<close> fresh_aux_index_ge by blast
         moreover have "m \<noteq> n" using \<open>m \<ge> Suc n\<close> by simp
          ultimately have "init \<star> embedding m \<noteq> init \<star> embedding n"
            using init_embed_inj inj_def by metis
         with m_def eq show False by simp
       qed
    ultimately show ?thesis
      using IH True fresh_aux_sound_aux[of "fresh_aux ?l' (Suc n)" "init \<star> embedding n" l]
      by simp
  qed
qed
 


lemma fresh_sound : "\<forall> l. fresh l \<notin> set l"
  using fresh_aux_sound by simp


end

global_interpretation nat_names : name_freshness "\<lambda> n . n" "0" "(+)"
  by unfold_locales auto

value "nat_names.fresh [0,1]"

value "name_freshness_defs.fresh (\<lambda> n. n) 0 (+) [0, 1, 2]" (* Aha! Now it computes! *)

end