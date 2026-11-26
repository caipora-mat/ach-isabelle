section \<open>A solver by bounded enumeration, as in the PVS formalization\<close>

theory Dioph_Stickel
  imports Dioph_AFP
begin

text \<open>
  The certified AC-unification algorithm in PVS (Ayala-Rincón, Fernández, Silva and
  Nantes-Sobrinho) does not compute a basis of the solutions of \<open>a \<bullet> x = b \<bullet> y\<close>, but a spanning
  set: all nonzero solutions whose entries are below Stickel's bound
  \<open>max m n * max\<^sub>i\<^sub>,\<^sub>j lcm a\<^sub>i b\<^sub>j\<close>. The bound is correct because it dominates Huet's bounds on minimal
  solutions (AFP lemma \<open>max_coeff_bound'\<close>).
\<close>

text \<open>Largest element of a list, \<open>0\<close> for the empty list.\<close>

definition maxl :: "nat list \<Rightarrow> nat" where
  "maxl xs = foldr max xs 0"

lemma le_maxl: "x \<in> set xs \<Longrightarrow> x \<le> maxl xs"
  by (induction xs) (auto simp: maxl_def)

text \<open>Stickel's bound (PVS \<open>calculateUpperBound\<close>).\<close>

definition upper_bound :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
  "upper_bound a b = max (length a) (length b) * maxl [lcm x y. x \<leftarrow> a, y \<leftarrow> b]"

text \<open>All vectors of length \<open>k\<close> with entries at most \<open>B\<close>.\<close>

fun vecs :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
  "vecs B 0 = [[]]"
| "vecs B (Suc k) = [i # v. i \<leftarrow> [0..<Suc B], v \<leftarrow> vecs B k]"

lemma set_vecs: "set (vecs B k) = {v. length v = k \<and> (\<forall>x \<in> set v. x \<le> B)}"
proof (induction k)
  case (Suc k)
  show ?case
  proof (intro set_eqI iffI)
    fix v
    assume "v \<in> {v. length v = Suc k \<and> (\<forall>x \<in> set v. x \<le> B)}"
    then obtain i w where v: "v = i # w" "i \<le> B" "w \<in> set (vecs B k)"
      using Suc by (cases v) auto
    then show "v \<in> set (vecs B (Suc k))"
      by (auto simp: image_iff intro!: bexI[of _ i])
  qed (use Suc in auto)
qed auto

text \<open>All nonzero solutions within the bound (PVS \<open>dioSolver\<close>).\<close>

definition dio_solver :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat list) list" where
  "dio_solver a b = (let B = upper_bound a b in
     [(x, y). x \<leftarrow> vecs B (length a), y \<leftarrow> vecs B (length b), nonzero x \<and> a \<bullet> x = b \<bullet> y])"

lemma set_dio_solver:
  "set (dio_solver a b) = {(x, y). length x = length a \<and> length y = length b \<and>
     (\<forall>e \<in> set x. e \<le> upper_bound a b) \<and> (\<forall>e \<in> set y. e \<le> upper_bound a b) \<and>
     nonzero x \<and> a \<bullet> x = b \<bullet> y}"
  by (auto simp: dio_solver_def set_vecs Let_def)

text \<open>Huet's bounds \<open>Max b\<close> and \<open>Max a\<close> are below Stickel's bound.\<close>

lemma Max_le_upper_bound:
  assumes "hlde a b" "a \<noteq> []" "b \<noteq> []"
  shows "Max (set b) \<le> upper_bound a b" "Max (set a) \<le> upper_bound a b"
proof -
  have pos: "0 < x" if "x \<in> set a \<union> set b" for x
    using that hlde.no0[OF assms(1)] by (auto intro: gr0I)
  let ?L = "[lcm x y. x \<leftarrow> a, y \<leftarrow> b]"
  have "1 \<le> max (length a) (length b)" using assms(2) by (cases a) auto
  then have L: "maxl ?L \<le> upper_bound a b"
    unfolding upper_bound_def by (metis mult_le_mono1 mult_1)
  obtain x0 where x0: "x0 \<in> set a" using assms(2) by (cases a) auto
  obtain y0 where y0: "y0 \<in> set b" using assms(3) by (cases b) auto
  have "y \<le> upper_bound a b" if "y \<in> set b" for y
  proof -
    have "y \<le> lcm x0 y" using pos x0 that by (intro dvd_imp_le) (auto simp: lcm_pos_nat)
    also have "\<dots> \<le> maxl ?L" using x0 that by (intro le_maxl) auto
    finally show ?thesis using L by simp
  qed
  then show "Max (set b) \<le> upper_bound a b" using assms(3) by simp
  have "x \<le> upper_bound a b" if "x \<in> set a" for x
  proof -
    have "x \<le> lcm x y0" using pos y0 that by (intro dvd_imp_le) (auto simp: lcm_pos_nat)
    also have "\<dots> \<le> maxl ?L" using y0 that by (intro le_maxl) auto
    finally show ?thesis using L by simp
  qed
  then show "Max (set a) \<le> upper_bound a b" using assms(2) by simp
qed

text \<open>Every minimal solution lies within Stickel's bound.\<close>

lemma (in hlde) Minimal_Solutions_bounded:
  assumes "(x, y) \<in> Minimal_Solutions"
  shows "\<forall>e \<in> set x. e \<le> upper_bound a b" "\<forall>e \<in> set y. e \<le> upper_bound a b"
proof -
  have sol: "length x = m" "length y = n" "a \<bullet> x = b \<bullet> y" "nonzero x"
    using assms by (auto simp: Minimal_Solutions_def in_Solutions_iff)
  obtain i where i: "i < m" "x ! i \<noteq> 0"
    using sol(1,4) by (auto simp: nonzero_iff in_set_conv_nth)
  have "0 < a ! i" by (metis gr0I nth_mem no0(1) i(1))
  then have pos: "0 < a \<bullet> x" using i sol(1) by (intro dotprod_gt0) auto
  have ne: "a \<noteq> []" "b \<noteq> []"
  proof -
    show "a \<noteq> []" using sol(1,4) by (auto simp: nonzero_iff)
    show "b \<noteq> []"
    proof
      assume "b = []"
      then have "b \<bullet> y = 0" using sol(2) by simp
      then show False using pos sol(3) by linarith
    qed
  qed
  note H = Max_le_upper_bound[OF hlde_axioms ne] max_coeff_bound'[OF assms]
  show "\<forall>e \<in> set x. e \<le> upper_bound a b" "\<forall>e \<in> set y. e \<le> upper_bound a b"
    using H sol(1,2) by (auto simp: in_set_conv_nth) (metis le_trans)+
qed

interpretation stickel: eq_solver dio_solver
proof
  fix a b
  assume "hlde a b"
  then interpret hlde a b .
  show "set (dio_solver a b) \<subseteq> hlde_ops.Solutions a b"
    by (auto simp: set_dio_solver in_Solutions_iff)
  show "hlde_ops.Minimal_Solutions a b \<subseteq> set (dio_solver a b)"
    using Minimal_Solutions_bounded
    by (auto simp: set_dio_solver Minimal_Solutions_def in_Solutions_iff)
qed

text \<open>Systems by successive elimination, with the bounded-enumeration solver for each row.\<close>

interpretation dioph_stickel: dioph_solver "\<lambda>n A. Some (stickel.dsys n A)"
  by unfold_locales (auto dest: stickel.dsys_sol stickel.dsys_gen)

end
