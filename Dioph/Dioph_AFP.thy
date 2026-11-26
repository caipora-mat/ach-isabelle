section \<open>A solver for linear Diophantine systems from the AFP solver for one equation\<close>

theory Dioph_AFP
  imports Dioph_Solver Diophantine_Eqns_Lin_Hom.Algorithm
begin

text \<open>
  The AFP entry \<^emph>\<open>Homogeneous Linear Diophantine Equations\<close> (Meßner, Parsert, Schöpf and
  Sternagel) computes the minimal solutions of one equation \<open>a \<bullet> x = b \<bullet> y\<close>. We show that they
  generate all solutions, solve one equation with integer coefficients by splitting it into its
  positive and negative part, and solve systems by successive elimination: the solutions of the
  first equation are \<open>y = \<Sum>\<^sub>i \<lambda>\<^sub>i b\<^sub>i\<close>, and the remaining equations become equations in \<open>\<lambda>\<close>.
\<close>

subsection \<open>Minimal solutions generate all solutions\<close>

text \<open>Any list containing the minimal solutions generates all solutions.\<close>

lemma (in hlde) Solutions_gen_by:
  assumes "(x, y) \<in> Solutions" "Minimal_Solutions \<subseteq> set S"
  shows "\<exists>ks. length ks = length S \<and>
    (\<forall>j < m + n. (x @ y) ! j = lc ks (map (\<lambda>(u, v). u @ v) S) j)"
  using assms
proof (induction "sum_list (x @ y)" arbitrary: x y rule: less_induct)
  case less
  let ?S = "map (\<lambda>(u, v). u @ v) S"
  have xy: "length x = m" "length y = n" "a \<bullet> x = b \<bullet> y"
    using less.prems by (auto simp: in_Solutions_iff)
  show ?case
  proof (cases "nonzero x")
    case False
    then have "nonzero y \<longleftrightarrow> False"
      using nonzero_Solutions_iff[OF less.prems(1)] by simp
    then have all0: "\<forall>e \<in> set (x @ y). e = 0"
      using False by (auto simp: nonzero_iff)
    have "(x @ y) ! j = lc (replicate (length ?S) 0) ?S j" if "j < m + n" for j
    proof -
      have "(x @ y) ! j \<in> set (x @ y)" using that xy by (intro nth_mem) simp
      then show ?thesis using all0 lc_zero[of ?S j] by simp
    qed
    then show ?thesis by (intro exI[of _ "replicate (length ?S) 0"]) simp
  next
    case True
    then obtain u v where uv: "u @ v \<le>\<^sub>v x @ y" "(u, v) \<in> Minimal_Solutions"
      using less.prems by (blast elim: minimize_nonzero_solution)
    have luv: "length u = m" "length v = n" "a \<bullet> u = b \<bullet> v" "nonzero u"
      using uv(2) by (auto simp: Minimal_Solutions_def in_Solutions_iff)
    have le: "u \<le>\<^sub>v x" "v \<le>\<^sub>v y"
      using uv(1) luv xy by (simp_all add: le_append)
    let ?x = "x -\<^sub>v u" and ?y = "y -\<^sub>v v"
    have lx: "length ?x = m" "length ?y = n"
      using xy by (simp_all add: vdiff_def)
    have "a \<bullet> ?x = ?x \<bullet> a" using lx by (simp add: dotprod_commute)
    also have "\<dots> = x \<bullet> a - u \<bullet> a" using le xy by (simp add: vdiff_dotprod_distr)
    also have "\<dots> = b \<bullet> y - b \<bullet> v" using xy luv by (simp add: dotprod_commute)
    also have "\<dots> = y \<bullet> b - v \<bullet> b" using xy luv by (simp add: dotprod_commute)
    also have "\<dots> = ?y \<bullet> b" using le xy by (simp add: vdiff_dotprod_distr)
    also have "\<dots> = b \<bullet> ?y" using lx by (simp add: dotprod_commute)
    finally have sol: "(?x, ?y) \<in> Solutions"
      using lx by (simp add: in_Solutions_iff)
    obtain e where "e \<in> set u" "e \<noteq> 0"
      using luv(4) by (auto simp: nonzero_iff)
    then have "0 < sum_list u"
      using member_le_sum_list[of e u] by simp
    then have "sum_list (?x @ ?y) < sum_list (x @ y)"
      using le le_sum_list_mono[OF le(1)] le_sum_list_mono[OF le(2)] by simp
    from less.hyps[OF this sol less.prems(2)] obtain ks where ks0: "length ks = length S"
      "\<forall>j < m + n. (?x @ ?y) ! j = lc ks ?S j" by (elim exE conjE)
    then have ks: "length ks = length ?S" "\<forall>j < m + n. (?x @ ?y) ! j = lc ks ?S j" by simp_all
    from uv(2) less.prems(2) obtain i where i: "i < length S" "S ! i = (u, v)"
      by (metis in_set_conv_nth subsetD)
    show ?thesis
    proof (intro exI conjI allI impI)
      show "length (ks[i := ks ! i + 1]) = length S" using ks by simp
    next
      fix j
      assume j: "j < m + n"
      have "(x @ y) ! j = (?x @ ?y) ! j + (u @ v) ! j"
        using j le xy luv by (auto simp: nth_append vdiff_def less_eq_def)
      also have "\<dots> = lc (ks[i := ks ! i + 1]) ?S j"
        using lc_update[of ks ?S i j] ks i j by simp
      finally show "(x @ y) ! j = lc (ks[i := ks ! i + 1]) ?S j" .
    qed
  qed
qed

lemma (in hlde) Solutions_gen:
  "(x, y) \<in> Solutions \<Longrightarrow> \<exists>ks. length ks = length (solve a b) \<and>
    (\<forall>j < m + n. (x @ y) ! j = lc ks (map (\<lambda>(u, v). u @ v) (solve a b)) j)"
  using Solutions_gen_by[of x y "solve a b"] by simp

subsection \<open>One-equation solvers\<close>

text \<open>
  A solver for one equation \<open>a \<bullet> x = b \<bullet> y\<close> returns solutions, among them all minimal ones.
  Definitions live in \<open>eq_solver_ops\<close> (no assumptions), so their equations are unconditional.
\<close>

locale eq_solver_ops =
  fixes sv :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat list) list"

locale eq_solver = eq_solver_ops +
  assumes sv_sol: "hlde a b \<Longrightarrow> set (sv a b) \<subseteq> hlde_ops.Solutions a b"
    and sv_min: "hlde a b \<Longrightarrow> hlde_ops.Minimal_Solutions a b \<subseteq> set (sv a b)"

text \<open>The AFP solver.\<close>

interpretation afp: eq_solver solve
  by unfold_locales (auto simp: hlde.solve dest: Minimal_Solutions_imp_Solutions)

subsection \<open>One equation with integer coefficients\<close>

text \<open>The position of an element in a list.\<close>

fun idx :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "idx [] y = 0"
| "idx (x # xs) y = (if x = y then 0 else Suc (idx xs y))"

lemma idx_less: "y \<in> set xs \<Longrightarrow> idx xs y < length xs"
  by (induction xs) auto

lemma nth_idx[simp]: "y \<in> set xs \<Longrightarrow> xs ! idx xs y = y"
  by (induction xs) auto

lemma idx_nth[simp]: "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> idx xs (xs ! i) = i"
  by (induction xs arbitrary: i) (auto simp: nth_Cons split: nat.splits)

text \<open>The coefficient of unknown \<open>j\<close> in row \<open>r\<close>; missing coefficients are \<open>0\<close>.\<close>

definition coef :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "coef r j = (if j < length r then r ! j else 0)"

definition pidx :: "nat \<Rightarrow> int list \<Rightarrow> nat list" where
  "pidx n r = filter (\<lambda>j. 0 < coef r j) [0..<n]"

definition nidx :: "nat \<Rightarrow> int list \<Rightarrow> nat list" where
  "nidx n r = filter (\<lambda>j. coef r j < 0) [0..<n]"

definition zidx :: "nat \<Rightarrow> int list \<Rightarrow> nat list" where
  "zidx n r = filter (\<lambda>j. coef r j = 0) [0..<n]"

definition ra :: "nat \<Rightarrow> int list \<Rightarrow> nat list" where
  "ra n r = map (\<lambda>j. nat (coef r j)) (pidx n r)"

definition rb :: "nat \<Rightarrow> int list \<Rightarrow> nat list" where
  "rb n r = map (\<lambda>j. nat (- coef r j)) (nidx n r)"

lemma hlde_ra_rb: "hlde (ra n r) (rb n r)"
  by unfold_locales (auto simp: ra_def rb_def pidx_def nidx_def)

lemma dot_coef: "length w = n \<Longrightarrow> dot r w = (\<Sum>j<n. coef r j * int (w ! j))"
proof -
  assume w: "length w = n"
  have "(\<Sum>j<n. coef r j * int (w ! j)) = (\<Sum>j<min (length r) n. coef r j * int (w ! j))"
    by (rule sum.mono_neutral_right) (auto simp: coef_def)
  also have "\<dots> = (\<Sum>j<min (length r) n. r ! j * int (w ! j))"
    by (rule sum.cong) (auto simp: coef_def)
  finally show ?thesis using w by (simp add: dot_conv)
qed

lemma int_dotprod_map:
  assumes "distinct L" "\<forall>j \<in> set L. 0 \<le> c j"
  shows "int (map (\<lambda>j. nat (c j)) L \<bullet> map g L) = (\<Sum>j \<in> set L. c j * int (g j))"
proof -
  have "int (map (\<lambda>j. nat (c j)) L \<bullet> map g L) = (\<Sum>i<length L. int (nat (c (L ! i)) * g (L ! i)))"
    by (simp add: dotprod_def)
  also have "\<dots> = (\<Sum>i<length L. c (L ! i) * int (g (L ! i)))"
    using assms(2) by (intro sum.cong) auto
  also have "\<dots> = sum_list (map (\<lambda>j. c j * int (g j)) L)"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>j \<in> set L. c j * int (g j))"
    using assms(1) by (simp add: sum_list_distinct_conv_sum_set)
  finally show ?thesis .
qed

text \<open>A row splits into its positive and its negative part.\<close>

lemma dot_split:
  assumes "length w = n"
  shows "dot r w = int (ra n r \<bullet> map (nth w) (pidx n r)) - int (rb n r \<bullet> map (nth w) (nidx n r))"
proof -
  let ?f = "\<lambda>j. coef r j * int (w ! j)"
  have P: "set (pidx n r) = {j \<in> {..<n}. 0 < coef r j}"
    and N: "set (nidx n r) = {j \<in> {..<n}. coef r j < 0}"
    by (auto simp: pidx_def nidx_def)
  have "dot r w = (\<Sum>j<n. ?f j)" using assms by (rule dot_coef)
  also have "\<dots> = (\<Sum>j \<in> {j \<in> {..<n}. 0 < coef r j}. ?f j) + (\<Sum>j \<in> {j \<in> {..<n}. coef r j < 0}. ?f j)"
  proof -
    have "(\<Sum>j<n. ?f j) = (\<Sum>j<n. (if 0 < coef r j then ?f j else 0) + (if coef r j < 0 then ?f j else 0))"
      by (intro sum.cong) auto
    then show ?thesis
      using sum.inter_filter[of "{..<n}" ?f "\<lambda>j. 0 < coef r j"]
        sum.inter_filter[of "{..<n}" ?f "\<lambda>j. coef r j < 0"]
      by (simp add: sum.distrib)
  qed
  also have "(\<Sum>j \<in> {j \<in> {..<n}. 0 < coef r j}. ?f j) = int (ra n r \<bullet> map (nth w) (pidx n r))"
    unfolding ra_def P[symmetric]
    by (subst int_dotprod_map) (auto simp: pidx_def)
  also have "(\<Sum>j \<in> {j \<in> {..<n}. coef r j < 0}. ?f j) = - int (rb n r \<bullet> map (nth w) (nidx n r))"
  proof -
    have "int (rb n r \<bullet> map (nth w) (nidx n r)) = (\<Sum>j \<in> set (nidx n r). - coef r j * int (w ! j))"
      unfolding rb_def by (subst int_dotprod_map) (auto simp: nidx_def)
    then show ?thesis unfolding N by (simp add: sum_negf)
  qed
  finally show ?thesis by simp
qed

text \<open>
  The generators of one row: the minimal solutions of its positive against its negative part,
  extended by \<open>0\<close>, and the unit vectors of the unknowns with coefficient \<open>0\<close>.
\<close>

definition emb :: "nat \<Rightarrow> int list \<Rightarrow> nat list \<times> nat list \<Rightarrow> nat list" where
  "emb n r xy = map (\<lambda>j. if 0 < coef r j then fst xy ! idx (pidx n r) j
     else if coef r j < 0 then snd xy ! idx (nidx n r) j else 0) [0..<n]"

definition (in eq_solver_ops) row_basis :: "nat \<Rightarrow> int list \<Rightarrow> nat list list" where
  "row_basis n r = map (emb n r) (sv (ra n r) (rb n r)) @ map (unitv n) (zidx n r)"

lemma distinct_idx[simp]: "distinct (pidx n r)" "distinct (nidx n r)" "distinct (zidx n r)"
  by (simp_all add: pidx_def nidx_def zidx_def)

lemma length_emb[simp]: "length (emb n r xy) = n"
  by (simp add: emb_def)

lemma map_nth_emb:
  assumes "length x = length (pidx n r)" "length y = length (nidx n r)"
  shows "map (nth (emb n r (x, y))) (pidx n r) = x" "map (nth (emb n r (x, y))) (nidx n r) = y"
proof -
  show "map (nth (emb n r (x, y))) (pidx n r) = x"
  proof (rule nth_equalityI)
    fix i
    assume "i < length (map (nth (emb n r (x, y))) (pidx n r))"
    then have i: "i < length (pidx n r)" by simp
    then have "pidx n r ! i < n" "0 < coef r (pidx n r ! i)"
      using nth_mem[OF i] by (auto simp: pidx_def)
    then show "map (nth (emb n r (x, y))) (pidx n r) ! i = x ! i"
      using i by (simp add: emb_def)
  qed (use assms in simp)
  show "map (nth (emb n r (x, y))) (nidx n r) = y"
  proof (rule nth_equalityI)
    fix i
    assume "i < length (map (nth (emb n r (x, y))) (nidx n r))"
    then have i: "i < length (nidx n r)" by simp
    then have "nidx n r ! i < n" "coef r (nidx n r ! i) < 0"
      using nth_mem[OF i] by (auto simp: nidx_def)
    then show "map (nth (emb n r (x, y))) (nidx n r) ! i = y ! i"
      using i by (simp add: emb_def)
  qed (use assms in simp)
qed

context eq_solver
begin

lemma minimal_lengths:
  assumes "(x, y) \<in> set (sv (ra n r) (rb n r))"
  shows "length x = length (pidx n r)" "length y = length (nidx n r)" "ra n r \<bullet> x = rb n r \<bullet> y"
proof -
  have "(x, y) \<in> Solutions (ra n r) (rb n r)"
    using assms sv_sol[OF hlde_ra_rb] by blast
  then show "length x = length (pidx n r)" "length y = length (nidx n r)" "ra n r \<bullet> x = rb n r \<bullet> y"
    by (auto simp: hlde_ops.in_Solutions_iff ra_def rb_def)
qed

lemma row_basis_sol:
  assumes "b \<in> set (row_basis n r)"
  shows "length b = n \<and> dot r b = 0"
proof -
  from assms consider (e) x y where "b = emb n r (x, y)" "(x, y) \<in> set (sv (ra n r) (rb n r))"
    | (u) j where "b = unitv n j" "j \<in> set (zidx n r)"
    unfolding row_basis_def by auto
  then show ?thesis
  proof cases
    case e
    then show ?thesis
      using minimal_lengths[OF e(2)] by (simp add: dot_split map_nth_emb)
  next
    case u
    note b = u(1) and j = u(2)
  have "(\<Sum>i<n. coef r i * int (if i = j then 1 else 0)) = (\<Sum>i<n. if i = j then coef r j else 0)"
    by (intro sum.cong) auto
  also have "\<dots> = 0"
    using j by (simp add: zidx_def)
  finally show ?thesis
    using b by (simp add: dot_coef unitv_def)
  qed
qed

lemma lc_unitv:
  assumes "j < n"
  shows "lc (map (nth y) (zidx n r)) (map (unitv n) (zidx n r)) j = (if coef r j = 0 then y ! j else 0)"
proof -
  let ?Z = "zidx n r"
  have "lc (map (nth y) ?Z) (map (unitv n) ?Z) j = (\<Sum>l<length ?Z. if ?Z ! l = j then y ! j else 0)"
  proof -
    have "?Z ! l < n" if "l < length ?Z" for l
      using nth_mem[OF that] by (simp add: zidx_def)
    then show ?thesis using assms by (simp add: lc_conv unitv_def) (intro sum.cong, auto)
  qed
  also have "\<dots> = sum_list (map (\<lambda>z. if z = j then y ! j else 0) ?Z)"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  also have "\<dots> = (\<Sum>z \<in> set ?Z. if z = j then y ! j else 0)"
    by (simp add: sum_list_distinct_conv_sum_set)
  also have "\<dots> = (if coef r j = 0 then y ! j else 0)"
    using assms by (simp add: zidx_def)
  finally show ?thesis .
qed

lemma lc_emb:
  assumes "j < n" "length ks = length (sv (ra n r) (rb n r))"
  defines "S \<equiv> map (\<lambda>(u, v). u @ v) (sv (ra n r) (rb n r))"
  shows "lc ks (map (emb n r) (sv (ra n r) (rb n r))) j =
    (if 0 < coef r j then lc ks S (idx (pidx n r) j)
     else if coef r j < 0 then lc ks S (length (pidx n r) + idx (nidx n r) j) else 0)"
proof -
  let ?P = "pidx n r" and ?N = "nidx n r" and ?S = "sv (ra n r) (rb n r)"
  have S: "S = map (\<lambda>(u, v). u @ v) ?S" by (simp add: S_def)
  show ?thesis
  proof (cases "0 < coef r j")
    case True
    then have "j \<in> set ?P" using assms(1) by (simp add: pidx_def)
    then have "emb n r b ! j = (\<lambda>(u, v). u @ v) b ! idx ?P j" if "b \<in> set ?S" for b
      using True assms(1) minimal_lengths[of "fst b" "snd b"] that idx_less[of j ?P]
      by (auto simp: emb_def nth_append split: prod.splits)
    from lc_map_cong[OF assms(2) this] show ?thesis using True S by simp
  next
    case False
    show ?thesis
    proof (cases "coef r j < 0")
      case True
      then have "j \<in> set ?N" using assms(1) by (simp add: nidx_def)
      then have "emb n r b ! j = (\<lambda>(u, v). u @ v) b ! (length ?P + idx ?N j)" if "b \<in> set ?S" for b
        using True assms(1) minimal_lengths[of "fst b" "snd b"] that
        by (auto simp: emb_def nth_append split: prod.splits)
      from lc_map_cong[OF assms(2) this] show ?thesis using True False S by simp
    next
      case False': False
      then have "emb n r b ! j = 0" for b
        using False assms(1) by (simp add: emb_def)
      then show ?thesis using False False' assms(2) by (simp add: lc_conv)
    qed
  qed
qed

lemma row_basis_gen:
  assumes "length y = n" "dot r y = 0"
  shows "\<exists>ks. length ks = length (row_basis n r) \<and> (\<forall>j < n. y ! j = lc ks (row_basis n r) j)"
proof -
  let ?P = "pidx n r" and ?N = "nidx n r" and ?Z = "zidx n r" and ?S = "sv (ra n r) (rb n r)"
  let ?x = "map (nth y) ?P" and ?y = "map (nth y) ?N"
  have "int (ra n r \<bullet> ?x) = int (rb n r \<bullet> ?y)"
    using dot_split[OF assms(1), of r] assms(2) by simp
  then have "(?x, ?y) \<in> Solutions (ra n r) (rb n r)"
    by (simp add: hlde_ops.in_Solutions_iff ra_def rb_def)
  from hlde.Solutions_gen_by[OF hlde_ra_rb this sv_min[OF hlde_ra_rb]] obtain ks where ks: "length ks = length ?S"
    "\<forall>i < length (ra n r) + length (rb n r). (?x @ ?y) ! i = lc ks (map (\<lambda>(u, v). u @ v) ?S) i"
    by (elim exE conjE)
  show ?thesis
  proof (intro exI conjI allI impI)
    show "length (ks @ map (nth y) ?Z) = length (row_basis n r)"
      using ks by (simp add: row_basis_def)
  next
    fix j
    assume j: "j < n"
    have "lc (ks @ map (nth y) ?Z) (row_basis n r) j =
        lc ks (map (emb n r) ?S) j + lc (map (nth y) ?Z) (map (unitv n) ?Z) j"
      using ks by (simp add: row_basis_def lc_append)
    also have "\<dots> = y ! j"
    proof (cases "0 < coef r j")
      case True
      then have jP: "j \<in> set ?P" using j by (simp add: pidx_def)
      have l: "length (ra n r) = length ?P" "length (rb n r) = length ?N"
        by (simp_all add: ra_def rb_def)
      have "lc ks (map (emb n r) ?S) j = lc ks (map (\<lambda>(u, v). u @ v) ?S) (idx ?P j)"
        using lc_emb[OF j ks(1)] True by simp
      also have "\<dots> = (?x @ ?y) ! idx ?P j"
        using ks(2) idx_less[OF jP] l by simp
      also have "\<dots> = y ! j"
        using idx_less[OF jP] jP by (simp add: nth_append)
      finally show ?thesis using True j by (simp add: lc_unitv)
    next
      case False
      show ?thesis
      proof (cases "coef r j < 0")
        case True
        then have jN: "j \<in> set ?N" using j by (simp add: nidx_def)
        have l: "length (ra n r) = length ?P" "length (rb n r) = length ?N"
          by (simp_all add: ra_def rb_def)
        have "lc ks (map (emb n r) ?S) j = lc ks (map (\<lambda>(u, v). u @ v) ?S) (length ?P + idx ?N j)"
          using lc_emb[OF j ks(1)] True False by simp
        also have "\<dots> = (?x @ ?y) ! (length ?P + idx ?N j)"
          using ks(2) idx_less[OF jN] l by simp
        also have "\<dots> = y ! j"
          using idx_less[OF jN] jN by (simp add: nth_append)
        finally show ?thesis using True j by (simp add: lc_unitv)
      qed (use False j ks in \<open>simp add: lc_emb lc_unitv\<close>)
    qed
    finally show "y ! j = lc (ks @ map (nth y) ?Z) (row_basis n r) j" by simp
  qed
qed

end

subsection \<open>Systems by successive elimination\<close>

text \<open>The vector \<open>\<Sum>\<^sub>i c\<^sub>i b\<^sub>i\<close> of length \<open>n\<close>.\<close>

definition combo :: "nat \<Rightarrow> nat list list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "combo n B c = map (lc c B) [0..<n]"

text \<open>
  The solutions of \<open>r # A\<close> are the combinations \<open>\<Sum>\<^sub>i \<lambda>\<^sub>i b\<^sub>i\<close> of the generators \<open>b\<^sub>i\<close> of \<open>r\<close>
  such that \<open>\<lambda>\<close> solves the rows \<open>r' \<in> A\<close> rewritten to \<open>\<Sum>\<^sub>i (r' \<cdot> b\<^sub>i) \<lambda>\<^sub>i = 0\<close>.
\<close>

context eq_solver_ops
begin

function dsys :: "nat \<Rightarrow> int list list \<Rightarrow> nat list list" where
  "dsys n [] = map (unitv n) [0..<n]"
| "dsys n (r # A) = (let B = row_basis n r in
     map (combo n B) (dsys (length B) (map (\<lambda>r'. map (dot r') B) A)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(n, A). length A)") auto

end

declare eq_solver_ops.row_basis_def [code] eq_solver_ops.dsys.simps [code]

lemma dot_combo:
  assumes "length c = length B" "\<forall>b \<in> set B. length b = n"
  shows "dot r (combo n B c) = dot (map (dot r) B) c"
proof -
  have "dot r (combo n B c) = (\<Sum>i<length B. int (c ! i) * dot r (B ! i))"
    unfolding combo_def using assms by (rule dot_lc)
  also have "\<dots> = dot (map (dot r) B) c"
    using assms(1) by (simp add: dot_conv mult.commute)
  finally show ?thesis .
qed

context eq_solver
begin

lemma dsys_sol: "b \<in> set (dsys n A) \<Longrightarrow> is_sol n A b"
proof (induction n A arbitrary: b rule: dsys.induct)
  case (1 n)
  then show ?case by (auto simp: is_sol_def unitv_def)
next
  case (2 n r A)
  let ?B = "row_basis n r"
  from "2.prems" obtain c where b: "b = combo n ?B c"
    and c: "c \<in> set (dsys (length ?B) (map (\<lambda>r'. map (dot r') ?B) A))"
    by (auto simp: Let_def)
  have sol: "is_sol (length ?B) (map (\<lambda>r'. map (dot r') ?B) A) c"
    using "2.IH"[OF refl c] .
  have lB: "\<forall>b \<in> set ?B. length b = n" and rB: "\<forall>b \<in> set ?B. dot r b = 0"
    using row_basis_sol by blast+
  have lc': "length c = length ?B" using sol by (simp add: is_sol_def)
  have "dot r b = dot (map (dot r) ?B) c"
    using b lc' lB by (simp add: dot_combo)
  also have "\<dots> = dot (map (\<lambda>_. 0) ?B) c"
    using rB by (metis map_eq_conv)
  also have "\<dots> = 0"
    using lc' by (simp add: dot_conv)
  finally have "dot r b = 0" .
  moreover have "dot r' b = 0" if "r' \<in> set A" for r'
    using b lc' lB sol that by (simp add: dot_combo is_sol_def)
  ultimately show ?case
    using b by (simp add: is_sol_def combo_def)
qed

lemma dsys_gen: "is_sol n A y \<Longrightarrow> \<exists>ks. length ks = length (dsys n A) \<and> (\<forall>j < n. y ! j = lc ks (dsys n A) j)"
proof (induction n A arbitrary: y rule: dsys.induct)
  case (1 n)
  have "y ! j = lc y (map (unitv n) [0..<n]) j" if "j < n" for j
  proof -
    have "lc y (map (unitv n) [0..<n]) j = (\<Sum>i<n. y ! i * (if j = i then 1 else 0))"
      using 1 that by (simp add: lc_conv unitv_def is_sol_def)
    also have "\<dots> = (\<Sum>i<n. if i = j then y ! i else 0)"
      by (intro sum.cong) auto
    finally show ?thesis using that by simp
  qed
  then show ?case using 1 by (auto simp: is_sol_def)
next
  case (2 n r A)
  let ?B = "row_basis n r"
  let ?A' = "map (\<lambda>r'. map (dot r') ?B) A"
  let ?C = "dsys (length ?B) ?A'"
  have y: "length y = n" "dot r y = 0" "\<forall>r' \<in> set A. dot r' y = 0"
    using "2.prems" by (simp_all add: is_sol_def)
  obtain l where l: "length l = length ?B" "\<forall>j < n. y ! j = lc l ?B j"
    using row_basis_gen[OF y(1,2)] by blast
  have lB: "\<forall>b \<in> set ?B. length b = n"
    using row_basis_sol by blast
  have yc: "combo n ?B l = y"
    using l y(1) by (intro nth_equalityI) (simp_all add: combo_def)
  have "is_sol (length ?B) ?A' l"
    using y(3) l(1) by (auto simp: is_sol_def dot_combo[OF l(1) lB, symmetric] yc)
  from "2.IH"[OF refl this] obtain ks where ks: "length ks = length ?C"
    "\<forall>i < length ?B. l ! i = lc ks ?C i" by blast
  have lC: "\<forall>c \<in> set ?C. length c = length ?B"
    using dsys_sol by (simp add: is_sol_def)
  show ?case
  proof (intro exI conjI allI impI)
    show "length ks = length (dsys n (r # A))" using ks by (simp add: Let_def)
  next
    fix j
    assume j: "j < n"
    have "y ! j = (\<Sum>i<length ?B. l ! i * ?B ! i ! j)"
      using l j by (simp add: lc_conv)
    also have "\<dots> = (\<Sum>i<length ?B. \<Sum>k<length ?C. ks ! k * ?C ! k ! i * ?B ! i ! j)"
      using ks by (simp add: lc_conv sum_distrib_right)
    also have "\<dots> = (\<Sum>k<length ?C. ks ! k * lc (?C ! k) ?B j)"
      using lC by (subst sum.swap) (simp add: lc_conv sum_distrib_left mult.assoc)
    also have "\<dots> = lc ks (dsys n (r # A)) j"
      using ks j by (simp add: Let_def lc_conv combo_def)
    finally show "y ! j = lc ks (dsys n (r # A)) j" .
  qed
qed

end

text \<open>With an empty side there is no minimal solution.\<close>

lemma (in hlde) Minimal_Solutions_empty:
  assumes "a = [] \<or> b = []"
  shows "Minimal_Solutions = {}"
proof -
  have False if xy: "(x, y) \<in> Minimal_Solutions" for x y
  proof -
    have sol: "(x, y) \<in> Solutions" "nonzero x"
      using xy by (simp_all add: Minimal_Solutions_def)
    have "x = [] \<or> y = []" using sol(1) assms by (auto simp: in_Solutions_iff)
    then show False
      using sol nonzero_Solutions_iff[OF sol(1)] by (auto simp: nonzero_iff)
  qed
  then show ?thesis by auto
qed

text \<open>The AFP solver, guarded against an empty side (where it evaluates \<open>Max {}\<close>).\<close>

definition solve0 :: "nat list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> nat list) list" where
  "solve0 a b = (if a = [] \<or> b = [] then [] else solve a b)"

interpretation afp0: eq_solver solve0
proof
  fix a b :: "nat list"
  assume h: "hlde a b"
  show "set (solve0 a b) \<subseteq> hlde_ops.Solutions a b"
    using h by (auto simp: solve0_def hlde.solve dest: Minimal_Solutions_imp_Solutions)
  show "hlde_ops.Minimal_Solutions a b \<subseteq> set (solve0 a b)"
    using h hlde.Minimal_Solutions_empty[OF h] by (auto simp: solve0_def hlde.solve)
qed

declare solve0_def [code]

text \<open>The successive elimination solver never gives up.\<close>

interpretation dioph_hlde: dioph_solver "\<lambda>n A. Some (afp0.dsys n A)"
  by unfold_locales (auto dest: afp0.dsys_sol afp0.dsys_gen)

end
