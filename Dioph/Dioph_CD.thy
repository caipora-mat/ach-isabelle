section \<open>Minimal solutions of homogeneous linear Diophantine systems (Contejean and Devie)\<close>

theory Dioph_CD
  imports Dioph_Solver Diophantine_Eqns_Lin_Hom.List_Vector
begin

text \<open>
  The algorithm of Section 5 of Boudet, Contejean and Devie (LICS 1990), generalizing
  Fortenbacher's algorithm from one equation to a system \<open>A x = 0\<close>. Vectors and the pointwise
  order \<open>\<le>\<^sub>v\<close> are those of the AFP entry \<^emph>\<open>Homogeneous Linear Diophantine Equations\<close>.
  Breadth-first search from the unit vectors: a node \<open>v\<close> with \<open>A v \<noteq> 0\<close> may be incremented at
  \<open>j\<close> only if \<open>A v \<cdot> A e\<^sub>j < 0\<close> (condition \<open>(C\<^sub>p)\<close>); nodes above a solution already found are
  dropped. The solver is \<open>cd_solve_total\<close>. Correctness (Propositions 1 and 2) is proved here
  for the fuel-bounded run \<open>cd_solve\<close>; termination (Proposition 3), and hence correctness of
  \<open>cd_solve_total\<close>, is in \<^file>\<open>Dioph_CD_Termination.thy\<close>.
\<close>

subsection \<open>Images and inner products\<close>

text \<open>The image \<open>A v\<close>: each row of \<open>A\<close> dotted with \<open>v\<close>.\<close>

definition img :: "int list list \<Rightarrow> nat list \<Rightarrow> int list" where
  "img A v = map (\<lambda>r. dot r v) A"

text \<open>Integer inner product \<open>\<Sum> u\<^sub>i w\<^sub>i\<close>.\<close>

definition ip :: "int list \<Rightarrow> int list \<Rightarrow> int" where
  "ip u w = sum_list (map2 (*) u w)"

lemma ip_img: "ip (img A u) (img A v) = sum_list (map (\<lambda>r. dot r u * dot r v) A)"
  by (induction A) (simp_all add: ip_def img_def)

lemma sum_list_map_sum:
  "sum_list (map (\<lambda>r. \<Sum>i\<in>I. g i r) xs) = (\<Sum>i\<in>I. sum_list (map (g i) xs))"
  by (induction xs) (simp_all add: sum.distrib)

lemma sum_list_map_neg: "sum_list (map (\<lambda>x. - f x) xs) = - sum_list (map f xs)"
  for f :: "'a \<Rightarrow> int"
  by (induction xs) simp_all

lemma sum_list_squares_pos:
  "\<exists>r \<in> set A. f r \<noteq> 0 \<Longrightarrow> 0 < sum_list (map (\<lambda>r. f r * f r) A)"
  for f :: "'a \<Rightarrow> int"
proof (induction A)
  case (Cons a A)
  have ge: "0 \<le> sum_list (map (\<lambda>r. f r * f r) A)"
    by (induction A) simp_all
  show ?case
  proof (cases "f a = 0")
    case True then show ?thesis using Cons by simp
  next
    case False then show ?thesis
      by (simp, intro add_pos_nonneg[OF _ ge]) (auto simp: zero_less_mult_iff linorder_neq_iff)
  qed
qed simp

text \<open>Rows are linear on differences.\<close>

lemma dot_vdiff:
  assumes "m \<le>\<^sub>v x"
  shows "dot r (x -\<^sub>v m) = dot r x - dot r m"
proof -
  have l: "length m = length x" "length (x -\<^sub>v m) = length x"
    using assms by (auto simp: less_eq_def vdiff_def)
  have "dot r (x -\<^sub>v m) =
      (\<Sum>j<min (length r) (length x). r ! j * int (x ! j) - r ! j * int (m ! j))"
    unfolding dot_conv[OF refl] l(2)
  proof (intro sum.cong refl)
    fix j assume "j \<in> {..<min (length r) (length x)}"
    then have "j < length x" by simp
    then show "r ! j * int ((x -\<^sub>v m) ! j) = r ! j * int (x ! j) - r ! j * int (m ! j)"
      using assms l by (simp add: vdiff_def less_eq_def algebra_simps)
  qed
  also have "\<dots> = dot r x - dot r m"
    using l by (simp add: dot_conv[OF refl] sum_subtractf)
  finally show ?thesis .
qed

text \<open>A vector is the combination of the unit vectors with its components.\<close>

lemma dot_units:
  assumes "length w = q"
  shows "dot r w = (\<Sum>i<q. int (w ! i) * dot r (unitv q i))"
proof -
  let ?B = "map (unitv q) [0..<q]"
  have lc: "lc w ?B j = w ! j" if "j < q" for j
  proof -
    have "lc w ?B j = (\<Sum>i<q. w ! i * ?B ! i ! j)"
      using assms by (simp add: lc_conv)
    also have "\<dots> = (\<Sum>i<q. if i = j then w ! i else 0)"
      using that by (intro sum.cong) (auto simp: unitv_nth)
    finally show ?thesis using that by simp
  qed
  have eq: "map (lc w ?B) [0..<q] = w"
    using assms by (intro nth_equalityI) (simp_all add: lc)
  have "dot r w = (\<Sum>i<length ?B. int (w ! i) * dot r (?B ! i))"
    using dot_lc[of w ?B q r] assms by (simp add: eq)
  also have "\<dots> = (\<Sum>i<q. int (w ! i) * dot r (unitv q i))"
    by (intro sum.cong) auto
  finally show ?thesis .
qed

text \<open>
  Key lemma (proof of Proposition 1): if \<open>m \<le>\<^sub>v x\<close>, \<open>A x = 0\<close> and \<open>A m \<noteq> 0\<close>, then some
  \<open>j\<close> with \<open>m\<^sub>j < x\<^sub>j\<close> satisfies \<open>(C\<^sub>p)\<close>, since \<open>A m \<cdot> A (x - m) = - \<parallel>A m\<parallel>\<^sup>2 < 0\<close>.
\<close>

lemma cd_direction:
  assumes le: "m \<le>\<^sub>v x" and lx: "length x = q"
    and sx: "\<forall>r \<in> set A. dot r x = 0" and nm: "\<exists>r \<in> set A. dot r m \<noteq> 0"
  shows "\<exists>j < q. m ! j < x ! j \<and> ip (img A m) (img A (unitv q j)) < 0"
proof (rule ccontr)
  assume na: "\<not> ?thesis"
  let ?w = "x -\<^sub>v m"
  have lw: "length ?w = q" using lx by (simp add: vdiff_def)
  have wj: "?w ! j = x ! j - m ! j" if "j < q" for j
    using that lx by (simp add: vdiff_def)
  have "0 \<le> (\<Sum>j<q. int (?w ! j) * ip (img A m) (img A (unitv q j)))"
  proof (rule sum_nonneg)
    fix j assume "j \<in> {..<q}"
    then show "0 \<le> int (?w ! j) * ip (img A m) (img A (unitv q j))"
      using na wj[of j] by (cases "m ! j < x ! j") auto
  qed
  also have "\<dots> = sum_list (map (\<lambda>r. \<Sum>j<q. int (?w ! j) * (dot r m * dot r (unitv q j))) A)"
    by (simp add: sum_list_map_sum sum_list_const_mult ip_img)
  also have "\<dots> = sum_list (map (\<lambda>r. dot r m * dot r ?w) A)"
    by (simp add: dot_units[OF lw] sum_distrib_left mult.left_commute)
  also have "\<dots> = sum_list (map (\<lambda>r. - (dot r m * dot r m)) A)"
    using sx by (intro arg_cong[where f = sum_list] map_cong) (simp_all add: dot_vdiff[OF le])
  also have "\<dots> < 0"
    using sum_list_squares_pos[OF nm] by (simp add: sum_list_map_neg)
  finally show False by simp
qed

subsection \<open>The algorithm\<close>

text \<open>Increment component \<open>j\<close> of \<open>v\<close>.\<close>

definition bump :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "bump v j = v[j := Suc (v ! j)]"

text \<open>\<open>v\<close> lies pointwise above an element of \<open>M\<close>.\<close>

definition dominated :: "nat list list \<Rightarrow> nat list \<Rightarrow> bool" where
  "dominated M v \<longleftrightarrow> (\<exists>m \<in> set M. list_all2 (\<le>) m v)"

lemma dominated_iff: "dominated M v \<longleftrightarrow> (\<exists>m \<in> set M. m \<le>\<^sub>v v)"
  by (simp add: dominated_def less_eq_def list_all2_conv_all_nth)

text \<open>Successors of \<open>v\<close> allowed by \<open>(C\<^sub>p)\<close>: bump \<open>j\<close> only if \<open>A v \<cdot> A e\<^sub>j < 0\<close>.\<close>

definition succs :: "nat \<Rightarrow> int list list \<Rightarrow> nat list \<Rightarrow> nat list list" where
  "succs q A v = map (bump v) (filter (\<lambda>j. ip (img A v) (img A (unitv q j)) < 0) [0..<q])"

text \<open>One level, solutions \<open>M\<close>, frontier \<open>P\<close>: drop dominated nodes, collect solutions, expand the others.\<close>

definition cd_step :: "nat \<Rightarrow> int list list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow>
    nat list list \<times> nat list list" where
  "cd_step q A M P = (let P' = filter (\<lambda>v. \<not> dominated M v) P in
     (M @ filter (is_sol q A) P', remdups (concat (map (succs q A) (filter (\<lambda>v. \<not> is_sol q A v) P')))))"

text \<open>Iterate \<open>cd_step\<close> on the pair (solutions, frontier) until the frontier is empty.\<close>

partial_function (tailrec) cd_run ::
    "nat \<Rightarrow> int list list \<Rightarrow> nat list list \<times> nat list list \<Rightarrow> nat list list" where
  "cd_run q A s = (if snd s = [] then fst s else cd_run q A (cd_step q A (fst s) (snd s)))"

declare cd_run.simps [code]

text \<open>Minimal solutions of \<open>A x = 0\<close> (\<open>q\<close> unknowns, one row of \<open>A\<close> per equation), searching from the unit vectors.\<close>

definition cd_solve_total :: "nat \<Rightarrow> int list list \<Rightarrow> nat list list" where
  "cd_solve_total q A = cd_run q A ([], map (unitv q) [0..<q])"

lemma length_bump [simp]: "length (bump v j) = length v"
  by (simp add: bump_def)

lemma sum_list_bump: "j < length v \<Longrightarrow> sum_list (bump v j) = Suc (sum_list v)"
  unfolding bump_def
  by (induction v arbitrary: j) (auto split: nat.split)

lemma bump_le: "v \<le>\<^sub>v x \<Longrightarrow> j < length x \<Longrightarrow> v ! j < x ! j \<Longrightarrow> bump v j \<le>\<^sub>v x"
  by (simp add: bump_def)

lemma sum_list_unitv: "j < q \<Longrightarrow> sum_list (unitv q j) = 1"
proof -
  assume j: "j < q"
  have "sum_list (unitv q j) = (\<Sum>i<q. unitv q j ! i)"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>i<q. if i = j then 1 else 0)"
    by (intro sum.cong) (auto simp: unitv_nth)
  finally show ?thesis using j by simp
qed

subsection \<open>Fuel-bounded runs\<close>

text \<open>Iterate \<open>cd_step\<close> until the frontier is empty (\<open>Some M\<close>) or the fuel \<open>f\<close> runs out (\<open>None\<close>);
  used only in proofs.\<close>

fun cd_loop :: "nat \<Rightarrow> int list list \<Rightarrow> nat \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow>
    nat list list option" where
  "cd_loop q A f M [] = Some M"
| "cd_loop q A 0 M (v # P) = None"
| "cd_loop q A (Suc f) M (v # P) = (case cd_step q A M (v # P) of (M', P') \<Rightarrow> cd_loop q A f M' P')"

text \<open>\<open>cd_solve_total\<close> with at most \<open>f\<close> levels.\<close>

definition cd_solve :: "nat \<Rightarrow> nat \<Rightarrow> int list list \<Rightarrow> nat list list option" where
  "cd_solve f q A = cd_loop q A f [] (map (unitv q) [0..<q])"

text \<open>A successful bounded run computes the same result as \<open>cd_run\<close>.\<close>

lemma cd_loop_run: "cd_loop q A f M P = Some R \<Longrightarrow> cd_run q A (M, P) = R"
proof (induction f arbitrary: M P)
  case 0
  then show ?case by (cases P) (simp_all add: cd_run.simps)
next
  case (Suc f)
  show ?case
  proof (cases P)
    case Nil
    then show ?thesis using Suc.prems by (subst cd_run.simps) simp
  next
    case (Cons v P0)
    obtain M' P' where st: "cd_step q A M P = (M', P')" by fastforce
    have "cd_loop q A f M' P' = Some R" using Suc.prems Cons st by simp
    then have "cd_run q A (M', P') = R" by (rule Suc.IH)
    then show ?thesis using Cons st by (subst cd_run.simps) simp
  qed
qed

subsection \<open>Correctness\<close>

locale hlds =
  fixes q :: nat and A :: "int list list"
begin

definition Solutions :: "nat list set" where
  "Solutions = {y. is_sol q A y}"

definition Minimal_Solutions :: "nat list set" where
  "Minimal_Solutions = {x \<in> Solutions. nonzero x \<and> \<not> (\<exists>y \<in> Solutions. nonzero y \<and> y <\<^sub>v x)}"

lemma in_Solutions_iff: "y \<in> Solutions \<longleftrightarrow> length y = q \<and> (\<forall>r \<in> set A. dot r y = 0)"
  by (simp add: Solutions_def is_sol_def)

lemma Minimal_SolutionsD:
  assumes "x \<in> Minimal_Solutions"
  shows "x \<in> Solutions" "nonzero x" "length x = q"
    "y \<in> Solutions \<Longrightarrow> nonzero y \<Longrightarrow> y \<le>\<^sub>v x \<Longrightarrow> y = x"
  using assms by (auto simp: Minimal_Solutions_def in_Solutions_iff order_vec.le_less)

lemma nonzero_sum: "nonzero v \<longleftrightarrow> 0 < sum_list v" for v :: "nat list"
proof
  assume "nonzero v"
  then obtain x where "x \<in> set v" "x \<noteq> 0" by (auto simp: nonzero_iff)
  then show "0 < sum_list v" using member_le_sum_list[of x v] by simp
next
  assume s: "0 < sum_list v"
  show "nonzero v"
  proof (rule ccontr)
    assume "\<not> nonzero v"
    then have "v = zeroes (length v)" by (simp add: not_nonzero_iff)
    then have "sum_list v = 0" by (metis sum_list_replicate mult_0_right)
    then show False using s by (metis less_irrefl)
  qed
qed

lemma le_sum_eq: "v \<le>\<^sub>v x \<Longrightarrow> sum_list x \<le> sum_list v \<Longrightarrow> v = x"
proof (rule ccontr)
  assume "v \<le>\<^sub>v x" "sum_list x \<le> sum_list v" "v \<noteq> x"
  then have "v <\<^sub>v x" by (simp add: order_vec.le_neq_trans)
  then show False using less_vec_sum_list_less \<open>sum_list x \<le> sum_list v\<close> by (metis not_le)
qed

lemma sol_vdiff:
  assumes "x \<in> Solutions" "m \<in> Solutions" "m \<le>\<^sub>v x"
  shows "x -\<^sub>v m \<in> Solutions"
  using assms by (simp add: in_Solutions_iff dot_vdiff, simp add: vdiff_def)

text \<open>Every nonzero solution lies above a minimal one.\<close>

lemma minimal_below:
  assumes "y \<in> Solutions" "nonzero y"
  shows "\<exists>m \<in> Minimal_Solutions. m \<le>\<^sub>v y"
  using assms
proof (induction "sum_list y" arbitrary: y rule: less_induct)
  case less
  show ?case
  proof (cases "y \<in> Minimal_Solutions")
    case True then show ?thesis by blast
  next
    case False
    then obtain z where z: "z \<in> Solutions" "nonzero z" "z <\<^sub>v y"
      using less.prems by (auto simp: Minimal_Solutions_def)
    then obtain m where "m \<in> Minimal_Solutions" "m \<le>\<^sub>v z"
      using less.hyps[OF less_vec_sum_list_less[OF z(3)]] by blast
    then show ?thesis
      using z(3) by (meson order_vec.less_imp_le order_vec.order_trans)
  qed
qed

text \<open>Any list containing the minimal solutions generates all solutions.\<close>

lemma Solutions_gen_by:
  assumes "y \<in> Solutions" "Minimal_Solutions \<subseteq> set S"
  shows "\<exists>ks. length ks = length S \<and> (\<forall>j < q. y ! j = lc ks S j)"
  using assms
proof (induction "sum_list y" arbitrary: y rule: less_induct)
  case less
  have ly: "length y = q" using less.prems(1) by (simp add: in_Solutions_iff)
  show ?case
  proof (cases "nonzero y")
    case False
    then have "y ! j = lc (replicate (length S) 0) S j" if "j < q" for j
      using that ly lc_zero[of S j] by (auto simp: nonzero_iff)
    then show ?thesis by (intro exI[of _ "replicate (length S) 0"]) simp
  next
    case True
    then obtain m where m: "m \<in> Minimal_Solutions" "m \<le>\<^sub>v y"
      using less.prems(1) minimal_below by blast
    note md = Minimal_SolutionsD[OF m(1)]
    have sol: "y -\<^sub>v m \<in> Solutions"
      using sol_vdiff[OF less.prems(1) md(1) m(2)] .
    have "sum_list (y -\<^sub>v m) < sum_list y"
      using m(2) md(2) le_sum_list_mono[OF m(2)] by (simp add: nonzero_sum)
    from less.hyps[OF this sol less.prems(2)] obtain ks
      where ks: "length ks = length S" "\<forall>j < q. (y -\<^sub>v m) ! j = lc ks S j" by blast
    from m(1) less.prems(2) obtain i where i: "i < length S" "S ! i = m"
      by (metis in_set_conv_nth subsetD)
    show ?thesis
    proof (intro exI conjI allI impI)
      show "length (ks[i := ks ! i + 1]) = length S" using ks by simp
    next
      fix j assume j: "j < q"
      have "y ! j = (y -\<^sub>v m) ! j + m ! j"
        using j ly m(2) by (auto simp: vdiff_def less_eq_def)
      also have "\<dots> = lc (ks[i := ks ! i + 1]) S j"
        using lc_update[of ks S i j] ks i j by simp
      finally show "y ! j = lc (ks[i := ks ! i + 1]) S j" .
    qed
  qed
qed

text \<open>
  Invariant at level \<open>n\<close>: the frontier \<open>P\<close> holds vectors of size \<open>n\<close>, \<open>M\<close> holds exactly the
  minimal solutions of size \<open>< n\<close>, and every larger minimal solution lies above a frontier node.
\<close>

definition cd_inv :: "nat \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> bool" where
  "cd_inv n M P \<longleftrightarrow> 0 < n
    \<and> (\<forall>v \<in> set P. length v = q \<and> sum_list v = n)
    \<and> set M \<subseteq> Minimal_Solutions \<and> (\<forall>m \<in> set M. sum_list m < n)
    \<and> (\<forall>x \<in> Minimal_Solutions. sum_list x < n \<longrightarrow> x \<in> set M)
    \<and> (\<forall>x \<in> Minimal_Solutions. n \<le> sum_list x \<longrightarrow> (\<exists>v \<in> set P. v \<le>\<^sub>v x))"

lemma cd_inv_init: "cd_inv 1 [] (map (unitv q) [0..<q])"
  unfolding cd_inv_def
proof (intro conjI ballI impI)
  fix x assume x: "x \<in> Minimal_Solutions" "1 \<le> sum_list x"
  note xd = Minimal_SolutionsD[OF x(1)]
  obtain j where j: "j < q" "x ! j \<noteq> 0"
    using xd(2,3) by (auto simp: nonzero_iff in_set_conv_nth)
  have "unitv q j \<le>\<^sub>v x"
    using j xd(3) by (auto simp: less_eq_def unitv_nth)
  then show "\<exists>v \<in> set (map (unitv q) [0..<q]). v \<le>\<^sub>v x"
    using j by force
next
  fix x assume x: "x \<in> Minimal_Solutions" "sum_list x < 1"
  have "0 < sum_list x" using Minimal_SolutionsD(2)[OF x(1)] nonzero_sum by blast
  then show "x \<in> set []" using x(2) by linarith
qed (auto simp: sum_list_unitv)

lemma cd_inv_Nil: "cd_inv n M [] \<Longrightarrow> set M = Minimal_Solutions"
proof
  assume I: "cd_inv n M []"
  show "set M \<subseteq> Minimal_Solutions" using I by (simp add: cd_inv_def)
  show "Minimal_Solutions \<subseteq> set M"
  proof
    fix x assume x: "x \<in> Minimal_Solutions"
    show "x \<in> set M"
    proof (cases "sum_list x < n")
      case True then show ?thesis using I x by (simp add: cd_inv_def)
    next
      case False then show ?thesis using I x by (simp add: cd_inv_def not_less)
    qed
  qed
qed

lemma cd_step_inv:
  assumes I: "cd_inv n M P" and st: "cd_step q A M P = (M', P')"
  shows "cd_inv (Suc n) M' P'"
proof -
  let ?P0 = "filter (\<lambda>v. \<not> dominated M v) P"
  let ?Q = "filter (\<lambda>v. \<not> is_sol q A v) ?P0"
  have M': "M' = M @ filter (is_sol q A) ?P0"
    and P': "P' = remdups (concat (map (succs q A) ?Q))"
    using st by (auto simp: cd_step_def Let_def)
  from I have n0: "0 < n"
    and Pl: "\<And>v. v \<in> set P \<Longrightarrow> length v = q \<and> sum_list v = n"
    and Mmin: "set M \<subseteq> Minimal_Solutions" and Msz: "\<And>m. m \<in> set M \<Longrightarrow> sum_list m < n"
    and Mall: "\<And>x. x \<in> Minimal_Solutions \<Longrightarrow> sum_list x < n \<Longrightarrow> x \<in> set M"
    and Pcov: "\<And>x. x \<in> Minimal_Solutions \<Longrightarrow> n \<le> sum_list x \<Longrightarrow> \<exists>v \<in> set P. v \<le>\<^sub>v x"
    unfolding cd_inv_def by blast+
  text \<open>A frontier node below a minimal solution and not equal to it is expanded towards it.\<close>
  have expand: "\<exists>v' \<in> set P'. v' \<le>\<^sub>v x"
    if v: "v \<in> set P" "v \<le>\<^sub>v x" and x: "x \<in> Minimal_Solutions" "n < sum_list x" for v x
  proof -
    note xd = Minimal_SolutionsD[OF x(1)]
    have lv: "length v = q" "sum_list v = n" using Pl[OF v(1)] by auto
    have nzv: "nonzero v" using lv n0 by (simp add: nonzero_sum)
    have nsol: "\<not> is_sol q A v"
    proof
      assume "is_sol q A v"
      then have "v = x" using xd(4)[OF _ nzv v(2)] by (simp add: Solutions_def)
      then show False using lv x(2) by simp
    qed
    have ndom: "\<not> dominated M v"
    proof
      assume "dominated M v"
      then obtain m where m: "m \<in> set M" "m \<le>\<^sub>v v" by (auto simp: dominated_iff)
      have "m \<in> Minimal_Solutions" using m(1) Mmin by blast
      then have "m = x"
        using xd(4) Minimal_SolutionsD(1,2) m(2) v(2) order_vec.order_trans by blast
      then show False using Msz[OF m(1)] x(2) by simp
    qed
    have "\<exists>r \<in> set A. dot r v \<noteq> 0" using nsol lv by (auto simp: is_sol_def)
    then obtain j where j: "j < q" "v ! j < x ! j" "ip (img A v) (img A (unitv q j)) < 0"
      using cd_direction[OF v(2) xd(3)] xd(1) by (auto simp: in_Solutions_iff)
    have "bump v j \<in> set (succs q A v)"
      using j by (auto simp: succs_def)
    moreover have "v \<in> set ?Q" using v(1) nsol ndom by simp
    ultimately have "bump v j \<in> set P'" using P' by auto
    moreover have "bump v j \<le>\<^sub>v x" using bump_le[OF v(2)] j xd(3) by simp
    ultimately show ?thesis by blast
  qed
  show ?thesis
    unfolding cd_inv_def
  proof (intro conjI ballI impI)
    show "0 < Suc n" by simp
  next
    fix v' assume "v' \<in> set P'"
    then obtain v j where "v \<in> set P" "j < q" "v' = bump v j"
      using P' by (auto simp: succs_def)
    then show "length v' = q" using Pl by auto
  next
    fix v' assume "v' \<in> set P'"
    then obtain v j where "v \<in> set P" "j < q" "v' = bump v j"
      using P' by (auto simp: succs_def)
    then show "sum_list v' = Suc n" using Pl by (auto simp: sum_list_bump)
  next
    show "set M' \<subseteq> Minimal_Solutions"
    proof
      fix v assume "v \<in> set M'"
      then consider "v \<in> set M" | "v \<in> set P" "\<not> dominated M v" "is_sol q A v"
        using M' by auto
      then show "v \<in> Minimal_Solutions"
      proof cases
        case 1 then show ?thesis using Mmin by blast
      next
        case 2
        have lv: "length v = q" "sum_list v = n" using Pl[OF 2(1)] by auto
        have sv: "v \<in> Solutions" using 2(3) by (simp add: Solutions_def)
        have "\<not> (\<exists>y \<in> Solutions. nonzero y \<and> y <\<^sub>v v)"
        proof
          assume "\<exists>y \<in> Solutions. nonzero y \<and> y <\<^sub>v v"
          then obtain y where y: "y \<in> Solutions" "nonzero y" "y <\<^sub>v v" by blast
          then obtain m where m: "m \<in> Minimal_Solutions" "m \<le>\<^sub>v y"
            using minimal_below by blast
          have mv: "m <\<^sub>v v" by (rule order_vec.le_less_trans[OF m(2) y(3)])
          then have "sum_list m < n" using less_vec_sum_list_less[of m v] lv(2) by simp
          then have "m \<in> set M" by (rule Mall[OF m(1)])
          moreover have "m \<le>\<^sub>v v" using mv by (rule order_vec.less_imp_le)
          ultimately show False using 2(2) unfolding dominated_iff by blast
        qed
        then show ?thesis using sv lv n0 by (simp add: Minimal_Solutions_def nonzero_sum)
      qed
    qed
  next
    fix m assume "m \<in> set M'"
    then show "sum_list m < Suc n" using M' Msz Pl by (auto simp: less_Suc_eq)
  next
    fix x assume x: "x \<in> Minimal_Solutions" "sum_list x < Suc n"
    show "x \<in> set M'"
    proof (cases "sum_list x < n")
      case True then show ?thesis using Mall x(1) M' by simp
    next
      case False
      note xd = Minimal_SolutionsD[OF x(1)]
      obtain v where v: "v \<in> set P" "v \<le>\<^sub>v x" using Pcov[OF x(1)] False by (auto simp: not_less)
      then have "v = x" using Pl[OF v(1)] x(2) False by (intro le_sum_eq) auto
      have ndom: "\<not> dominated M x"
      proof
        assume "dominated M x"
        then obtain m where m: "m \<in> set M" "m \<le>\<^sub>v x" by (auto simp: dominated_iff)
        have mm: "m \<in> Minimal_Solutions" using m(1) Mmin by blast
        have "m = x"
          by (rule xd(4)[OF Minimal_SolutionsD(1)[OF mm] Minimal_SolutionsD(2)[OF mm] m(2)])
        then show False using Msz[OF m(1)] False by simp
      qed
      have "is_sol q A x" using xd(1) by (simp add: Solutions_def)
      then show ?thesis using M' v(1) \<open>v = x\<close> ndom by simp
    qed
  next
    fix x assume x: "x \<in> Minimal_Solutions" "Suc n \<le> sum_list x"
    then obtain v where "v \<in> set P" "v \<le>\<^sub>v x" using Pcov[OF x(1)] by auto
    then show "\<exists>v' \<in> set P'. v' \<le>\<^sub>v x" using expand x by simp
  qed
qed

lemma cd_loop_correct:
  assumes "cd_loop q A f M P = Some R" "cd_inv n M P"
  shows "set R = Minimal_Solutions"
  using assms
proof (induction f arbitrary: n M P)
  case 0
  then show ?case by (cases P) (auto dest: cd_inv_Nil)
next
  case (Suc f)
  show ?case
  proof (cases P)
    case Nil
    then show ?thesis using Suc.prems cd_inv_Nil by auto
  next
    case (Cons v P0)
    obtain M' P' where st: "cd_step q A M P = (M', P')" by (cases "cd_step q A M P")
    then have "cd_loop q A f M' P' = Some R" using Suc.prems(1) Cons by simp
    then show ?thesis using Suc.IH cd_step_inv[OF Suc.prems(2) st] by blast
  qed
qed

text \<open>Propositions 1 and 2: on success, the result is exactly the set of minimal solutions.\<close>

theorem cd_solve_correct: "cd_solve f q A = Some R \<Longrightarrow> set R = Minimal_Solutions"
  unfolding cd_solve_def using cd_loop_correct cd_inv_init by blast

end

end
