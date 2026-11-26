(*
Author: Guilherme Borges Brandão
*)

theory AC_Unif_Algorithm
  imports AC_Terms "../Dioph/Dioph_Solver"
begin

section ‹An AC-unification algorithm›

text ‹
  Stickel's AC-unification algorithm in the form certified in PVS by Ayala-Rincón, Fernández,
  Silva, Kutsia and Nantes-Sobrinho (∗‹Certified first-order AC-unification and
  applications›; FSCD 2022). The Diophantine equation of an AC step is solved by an arbitrary
  solver for homogeneous linear Diophantine systems (‹Dioph_Solver›) that returns a generating
  set of the solutions, e.g. the Contejean--Devie algorithm, instead of the bounded enumeration
  of PVS. Variables are natural numbers; ‹nv› is a bound on the variables in use, and fresh
  variables are ‹nv, nv + 1, …›.
›

type_synonym ('f, 'v) eqs = "(('f, 'v) term × ('f, 'v) term) list"

definition subst_eqs :: "('f, 'v) subst ⇒ ('f, 'v) eqs ⇒ ('f, 'v) eqs" where
  "subst_eqs σ P = map (λ(s, t). (s ⋅ σ, t ⋅ σ)) P"

definition vars_eqs :: "('f, 'v) eqs ⇒ 'v set" where
  "vars_eqs P = (⋃(s, t) ∈ set P. vars_term s ∪ vars_term t)"

lemma length_subst_eqs [simp]: "length (subst_eqs σ P) = length P"
  by (simp add: subst_eqs_def)

lemma subst_eqs_simps [simp]:
  "subst_eqs σ [] = []"
  "subst_eqs σ ((s, t) # P) = (s ⋅ σ, t ⋅ σ) # subst_eqs σ P"
  "subst_eqs σ (P @ Q) = subst_eqs σ P @ subst_eqs σ Q"
  by (simp_all add: subst_eqs_def)

lemma subst_eqs_compose: "subst_eqs (σ ∘⇩s τ) P = subst_eqs τ (subst_eqs σ P)"
  by (induction P) (auto simp: subst_eqs_def)

lemma vars_eqs_simps [simp]:
  "vars_eqs [] = {}"
  "vars_eqs ((s, t) # P) = vars_term s ∪ vars_term t ∪ vars_eqs P"
  "vars_eqs (P @ Q) = vars_eqs P ∪ vars_eqs Q"
  by (auto simp: vars_eqs_def)

text ‹Both sides are AC applications of the same AC symbol.›

fun ac_pair :: "('f ⇒ bool) ⇒ ('f, 'v) term × ('f, 'v) term ⇒ bool" where
  "ac_pair ac (Fun f [a, b], Fun g [c, d]) = (f = g ∧ ac f)"
| "ac_pair ac _ = False"

subsection ‹Instantiation of variables (PVS ‹instantiateStep›)›

text ‹
  Solve the variable equations of a problem from left to right. An equation ‹t ≈? Z› instantiates
  the right-hand side variable first, as in PVS: after an AC step the right-hand sides contain the
  new variables. Equations between non-variable terms are kept. The result is ‹None› if an
  occurs check fails.
›

function inst :: "('f, 'v) eqs ⇒ (('f, 'v) eqs × ('f, 'v) subst) option" where
  "inst [] = Some ([], Var)"
| "inst ((t, s) # E) =
    (if t = s then inst E
     else (case s of
       Var z ⇒ if z ∈ vars_term t then None
         else map_option (λ(R, θ). (R, Var(z := t) ∘⇩s θ)) (inst (subst_eqs (Var(z := t)) E))
     | Fun _ _ ⇒ (case t of
         Var x ⇒ if x ∈ vars_term s then None
           else map_option (λ(R, θ). (R, Var(x := s) ∘⇩s θ)) (inst (subst_eqs (Var(x := s)) E))
       | Fun _ _ ⇒ map_option (λ(R, θ). ((t ⋅ θ, s ⋅ θ) # R, θ)) (inst E))))"
  by pat_completeness auto
termination
  by (relation "measure length") auto

subsection ‹The AC step for one equation (PVS ‹solveAC›)›

text ‹The distinct elements of ‹xs› in ‹M›, with their multiplicity in ‹M›.›

definition grp :: "'a list ⇒ 'a multiset ⇒ ('a × nat) list" where
  "grp xs M = map (λu. (u, count M u)) (remdups (filter (λu. 0 < count M u) xs))"

text ‹Column ‹j› of the chosen solutions ‹D›, summed.›

definition col_sum :: "nat list list ⇒ nat ⇒ nat" where
  "col_sum D j = sum_list (map (λb. b ! j) D)"

text ‹
  The constraints of Fages on a choice ‹D› of solutions (PVS ‹extractSubmatrices›): every
  argument gets some new variable, and a non-variable argument gets exactly one, once.
›

definition valid_sub :: "('f, 'v) term list ⇒ nat list list ⇒ bool" where
  "valid_sub ws D ⟷ (∀j < length ws. 0 < col_sum D j ∧ (is_Fun (ws ! j) ⟶ col_sum D j = 1))"

text ‹Solution ‹i› of ‹D› is represented by the new variable ‹nv + i› (PVS ‹dioMatrix2acSol›).›

definition new_vars :: "nat ⇒ nat list list ⇒ nat ⇒ ('f, nat) term list" where
  "new_vars nv D j = concat (map (λi. replicate (D ! i ! j) (Var (nv + i))) [0..<length D])"

locale ac_unif = ac_sig ac + dioph_solver dsolve
  for ac :: "'f ⇒ bool" and dsolve :: "nat ⇒ int list list ⇒ nat list list option"
begin

definition sol_eqs :: "'f ⇒ nat ⇒ ('f, nat) term list ⇒ nat list list ⇒ ('f, nat) eqs" where
  "sol_eqs f nv ws D = map (λj. (ws ! j, mk_ac f (new_vars nv D j))) [0..<length ws]"

definition unifies :: "('f, 'v) subst ⇒ ('f, 'v) eqs ⇒ bool" where
  "unifies σ P ⟷ (∀(s, t) ∈ set P. s ⋅ σ ≈ t ⋅ σ)"

text ‹The generators of the solutions of ‹a ∙ x = b ∙ y›, without the zero vector.›

definition basis :: "nat list ⇒ nat list ⇒ nat list list" where
  "basis a b = (let k = length a + length b in
     case dsolve k [map int a @ map (λx. - int x) b] of
       None ⇒ []
     | Some B ⇒ filter (λv. length v = k ∧ 0 < sum_list v) B)"

text ‹
  The AC step on ‹t ≈? s›, both AC applications of ‹f›: eliminate the common arguments,
  group equal arguments, solve the Diophantine equation and return, for every admissible choice
  ‹D› of solutions, the equations between the arguments and sums of new variables.
›

text ‹The arguments of ‹t› that are not arguments of ‹s› (PVS ‹elimComArg›).›

definition dio_L :: "'f ⇒ ('f, 'v) term ⇒ ('f, 'v) term ⇒ ('f, 'v) term multiset" where
  "dio_L f t s = mset (args_ac f t) - mset (args_ac f s)"

text ‹Those arguments, each once, with their multiplicity: the coefficients of one side.›

definition dio_us :: "'f ⇒ ('f, 'v) term ⇒ ('f, 'v) term ⇒ (('f, 'v) term × nat) list" where
  "dio_us f t s = grp (args_ac f t) (dio_L f t s)"

text ‹The arguments associated with the unknowns of the Diophantine equation.›

definition dio_ws :: "'f ⇒ ('f, 'v) term ⇒ ('f, 'v) term ⇒ ('f, 'v) term list" where
  "dio_ws f t s = map fst (dio_us f t s) @ map fst (dio_us f s t)"

definition dio_basis :: "'f ⇒ ('f, 'v) term ⇒ ('f, 'v) term ⇒ nat list list" where
  "dio_basis f t s = basis (map snd (dio_us f t s)) (map snd (dio_us f s t))"

definition solve_ac :: "'f ⇒ ('f, nat) term ⇒ ('f, nat) term ⇒ nat ⇒ (('f, nat) eqs × nat) list" where
  "solve_ac f t s nv =
    (if dio_L f t s = {#} ∧ dio_L f s t = {#} then [([], nv)]
     else map (λD. (sol_eqs f nv (dio_ws f t s) D, nv + length D))
       (filter (valid_sub (dio_ws f t s)) (subseqs (dio_basis f t s))))"

subsection ‹The AC step for all equations (PVS ‹applyACStep›)›

text ‹
  Apply ‹solve_ac› and ‹inst› to the AC equations in turn. Arguments: the equations still to be
  processed, the equations obtained so far, the substitution computed so far and the next fresh
  variable.
›

function ac_round :: "('f, nat) eqs ⇒ ('f, nat) eqs ⇒ ('f, nat) subst ⇒ nat ⇒
    (('f, nat) eqs × ('f, nat) subst × nat) list" where
  "ac_round [] R σ nv = [(R, σ, nv)]"
| "ac_round ((t, s) # P) R σ nv =
    (case t of
      Fun f _ ⇒ concat (map (λ(C, nv').
          case inst C of
            None ⇒ []
          | Some (R', θ) ⇒ ac_round (subst_eqs θ P) (subst_eqs θ R @ R') (σ ∘⇩s θ) nv')
        (solve_ac f t s nv))
    | Var _ ⇒ ac_round P (R @ [(t, s)]) σ nv)"
  by pat_completeness auto
termination
  by (relation "measure (λ(P, R, σ, nv). length P)") auto

subsection ‹The algorithm (PVS ‹ACUnif›)›

text ‹
  The first equation that is not an AC pair is handled as in syntactic unification; only when
  all equations are AC pairs is the AC step applied (to all of them). Termination is proved in
  ‹AC_Unif_Termination›.
›

function (domintros) acunif :: "('f, nat) eqs ⇒ ('f, nat) subst ⇒ nat ⇒ ('f, nat) subst list" where
  "acunif P σ nv =
    (if P = [] then [σ]
     else (case find (λe. ¬ ac_pair ac e) P of
       None ⇒ concat (map (λ(P', σ', nv'). acunif P' σ' nv') (ac_round P [] σ nv))
     | Some (t, s) ⇒
         (let P1 = remove1 (t, s) P in
          if t = s then acunif P1 σ nv
          else (case t of
            Var x ⇒ if x ∈ vars_term s then []
              else acunif (subst_eqs (Var(x := s)) P1) (σ ∘⇩s Var(x := s)) nv
          | Fun f ts ⇒ (case s of
              Var x ⇒ if x ∈ vars_term t then []
                else acunif (subst_eqs (Var(x := t)) P1) (σ ∘⇩s Var(x := t)) nv
            | Fun g ss ⇒ if f = g ∧ length ts = length ss then acunif (zip ts ss @ P1) σ nv
                else [])))))"
  by pat_completeness auto

text ‹AC-unifiers of ‹s› and ‹t›.›

definition ac_unifiers :: "('f, nat) term ⇒ ('f, nat) term ⇒ ('f, nat) subst list" where
  "ac_unifiers s t = acunif [(s, t)] Var (Suc (Max (insert 0 (vars_term s ∪ vars_term t))))"

end

end
