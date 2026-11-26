section \<open>Solvers for homogeneous linear Diophantine systems\<close>

theory Dioph_Solver
  imports Main
begin

text \<open>
  Elementary AC-unification reduces to finding a generating set of the non-negative integer
  solutions of a homogeneous linear system \<open>A y = 0\<close> (Section 3 of Boudet and Contejean). The
  solver is a parameter: a function that, for \<open>n\<close> unknowns and the rows \<open>A\<close> of the system,
  either returns a finite list of solutions that generates all solutions as linear combinations
  with natural coefficients, or gives up (\<open>None\<close>). Minimality of the generators is not
  required.
\<close>

definition dot :: "int list \<Rightarrow> nat list \<Rightarrow> int" where
  "dot r y = sum_list (map2 (\<lambda>a b. a * int b) r y)"

definition is_sol :: "nat \<Rightarrow> int list list \<Rightarrow> nat list \<Rightarrow> bool" where
  "is_sol n A y \<longleftrightarrow> length y = n \<and> (\<forall>r \<in> set A. dot r y = 0)"

text \<open>Component \<open>j\<close> of the linear combination \<open>\<Sum>\<^sub>i k\<^sub>i b\<^sub>i\<close> of the vectors \<open>B\<close> with coefficients \<open>ks\<close>.\<close>

definition lc :: "nat list \<Rightarrow> nat list list \<Rightarrow> nat \<Rightarrow> nat" where
  "lc ks B j = sum_list (map2 (\<lambda>k b. k * b ! j) ks B)"

text \<open>The \<open>j\<close>-th unit vector of length \<open>n\<close>.\<close>

definition unitv :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "unitv n j = map (\<lambda>i. if i = j then 1 else 0) [0..<n]"

lemma length_unitv [simp]: "length (unitv n j) = n"
  by (simp add: unitv_def)

lemma unitv_nth: "i < n \<Longrightarrow> unitv n j ! i = (if i = j then 1 else 0)"
  by (simp add: unitv_def)

lemma lc_conv: "length ks = length B \<Longrightarrow> lc ks B j = (\<Sum>i<length B. ks ! i * B ! i ! j)"
  by (simp add: lc_def sum_list_sum_nth atLeast0LessThan)

lemma lc_zero: "lc (replicate (length B) 0) B j = 0"
  by (simp add: lc_conv)

lemma lc_append:
  "length ks = length B \<Longrightarrow> length ks' = length B' \<Longrightarrow>
    lc (ks @ ks') (B @ B') j = lc ks B j + lc ks' B' j"
  by (simp add: lc_def)

lemma lc_update:
  assumes "length ks = length B" "i < length B"
  shows "lc (ks[i := ks ! i + 1]) B j = lc ks B j + B ! i ! j"
proof -
  have "(\<Sum>l<length B. ks[i := ks ! i + 1] ! l * B ! l ! j) =
      (\<Sum>l<length B. ks ! l * B ! l ! j + (if l = i then B ! l ! j else 0))"
    using assms by (intro sum.cong) (auto simp: nth_list_update)
  also have "\<dots> = lc ks B j + B ! i ! j"
    using assms by (simp add: sum.distrib lc_conv)
  finally show ?thesis using assms by (simp add: lc_conv)
qed

lemma lc_map_cong:
  assumes "length ks = length B" "\<And>b. b \<in> set B \<Longrightarrow> f b ! j = g b ! j'"
  shows "lc ks (map f B) j = lc ks (map g B) j'"
  using assms by (simp add: lc_conv)

lemma dot_conv: "length y = n \<Longrightarrow> dot r y = (\<Sum>j<min (length r) n. r ! j * int (y ! j))"
  by (simp add: dot_def sum_list_sum_nth atLeast0LessThan)

text \<open>Row \<open>r\<close> is linear: applied to \<open>\<Sum>\<^sub>i k\<^sub>i b\<^sub>i\<close> it gives \<open>\<Sum>\<^sub>i k\<^sub>i (r \<cdot> b\<^sub>i)\<close>.\<close>

lemma dot_lc:
  assumes "length ks = length B" "\<forall>b \<in> set B. length b = n"
  shows "dot r (map (lc ks B) [0..<n]) = (\<Sum>i<length B. int (ks ! i) * dot r (B ! i))"
proof -
  have "dot r (map (lc ks B) [0..<n]) =
      (\<Sum>j<min (length r) n. \<Sum>i<length B. r ! j * int (ks ! i * B ! i ! j))"
    using assms(1) by (simp add: dot_conv lc_conv sum_distrib_left)
  also have "\<dots> = (\<Sum>i<length B. \<Sum>j<min (length r) n. int (ks ! i) * (r ! j * int (B ! i ! j)))"
    by (subst sum.swap) (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>i<length B. int (ks ! i) * dot r (B ! i))"
    using assms(2) by (simp add: dot_conv sum_distrib_left)
  finally show ?thesis .
qed

locale dioph_solver =
  fixes dsolve :: "nat \<Rightarrow> int list list \<Rightarrow> nat list list option"
  assumes dsolve_sol: "dsolve n A = Some B \<Longrightarrow> b \<in> set B \<Longrightarrow> is_sol n A b"
    and dsolve_gen: "dsolve n A = Some B \<Longrightarrow> is_sol n A y \<Longrightarrow>
      \<exists>ks. length ks = length B \<and> (\<forall>j < n. y ! j = lc ks B j)"

text \<open>The solver that always gives up.\<close>

interpretation dioph_none: dioph_solver "\<lambda>n A. None"
  by unfold_locales simp_all

end
