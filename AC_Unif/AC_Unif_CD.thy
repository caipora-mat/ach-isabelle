(*
Author: Guilherme Borges Brandão
*)

theory AC_Unif_CD
  imports AC_Unif_Termination "../Dioph/Dioph_CD_Termination"
begin

section \<open>AC-unification with the Contejean--Devie solver\<close>

text \<open>
  The algorithm of \<open>AC_Unif_Algorithm\<close>, with the Diophantine equation of each AC step solved by
  the Contejean--Devie algorithm (\<open>cd_solve_total\<close>, \<^file>\<open>../Dioph/Dioph_CD.thy\<close>), which
  computes exactly the minimal solutions and always terminates
  (\<^file>\<open>../Dioph/Dioph_CD_Termination.thy\<close>). It replaces the bounded enumeration of
  solutions used in the PVS formalization.
\<close>

locale ac_unif_cd =
  fixes ac :: "'f \<Rightarrow> bool"

sublocale ac_unif_cd \<subseteq> cd: ac_unif ac "\<lambda>n A. Some (cd_solve_total n A)"
  by (rule dioph_cdt.dioph_solver_axioms[folded ac_unif_def])

context ac_unif_cd
begin

text \<open>The solver never gives up.\<close>

lemma cd_total: "(\<lambda>n A. Some (cd_solve_total n A)) n A \<noteq> None"
  by simp

text \<open>The algorithm terminates on every input (\<open>AC_Unif_Termination\<close>), and is sound and complete.\<close>

theorem acunif_cd_terminates: "cd.acunif_dom ([(s, t)], Var, cd.nv0 s t)"
  by (rule cd.ac_unifiers_dom)

theorem ac_unifiers_cd_sound:
  assumes "\<theta> \<in> set (cd.ac_unifiers s t)"
  shows "s \<cdot> \<theta> \<approx> t \<cdot> \<theta>"
  by (rule cd.ac_unifiers_sound[OF assms])

theorem ac_unifiers_cd_complete:
  fixes \<delta> :: "('f, nat) subst"
  assumes "s \<cdot> \<delta> \<approx> t \<cdot> \<delta>"
  shows "\<exists>\<theta>\<in>set (cd.ac_unifiers s t). \<exists>\<rho>. \<forall>x\<in>vars_term s \<union> vars_term t. \<delta> x \<approx> \<theta> x \<cdot> \<rho>"
  by (rule cd.ac_unifiers_complete[OF _ assms]) simp

end

end
