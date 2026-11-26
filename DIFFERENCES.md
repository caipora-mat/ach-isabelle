# Formalization vs. dissertation

This note compares the Isabelle/HOL formalization in this repository with the dissertation
`GuilhermeBorgesBrandao_DISSERT.pdf`. It covers:

- every place where the formal development departs from the text, and why;
- the definitions that the formalization had to add.

Each item is labeled with one of these kinds:

| Label | Meaning |
|---|---|
| **Representation** | The same notion, encoded differently for Isabelle. |
| **Correction** | The text is wrong or underspecified, and the formal version fixes it. |
| **Generalization** | The original notion is a special case of the formal one. |
| **Needed for termination** | Required to make the termination argument go through. |
| **Made explicit** | An assumption or notion the text uses implicitly. |
| **New** | A notion with no counterpart in the dissertation. |

The theories, in dependency order:

| Theory | Content | Dissertation |
|---|---|---|
| `Equational_Theory.thy` | `=E` as an inductive congruence | Def. 1.11–1.12 |
| `AC_Unif/AC_Theory.thy` | Signature `+`; the AC axioms; n-ary sums | Sec. 1.4 |
| `ACh_Theory.thy` | Extends AC with `h`; the ACh axioms | Sec. 1.4 |
| `ACh_Normal_Form.thy` | Normal forms modulo ACh, `s ≈ACh t ⟷ nf s = nf t`, and h-height | Def. 1.21 (plus new material) |
| `Bounded_ACh_Unification.thy` | Triples, the rules of Fig. 2.2, soundness | Ch. 2, Sec. 3.3 |
| `Bounded_ACh_Completeness.thy` | Bounded solutions, completeness | Sec. 3.4 |
| `Bounded_ACh_Termination.thy` | Termination of flattening and of the strategy | Sec. 3.2 |
| `Bounded_ACh_Algorithm.thy` | Executable recursive algorithm `unify` | Algorithms 1 and 2 |

---

## 1. Foundations

### 1.1 Equational theory (`Equational_Theory.thy`) — Representation

**Text.** Def. 1.12 defines `=E` informally.

**Formalization.** `eq_theory E` is the least relation that:
- contains the instances of `E`;
- is reflexive, symmetric and transitive;
- is closed under contexts (`cong`).

The identities may use a variable type `'w` different from the term variables `'v`. The AC and
ACh axioms are given by the set of all their instances (e.g. every `s + t ≈ t + s`), so no
variables are fixed to state them.

### 1.2 Sums of several terms (`sum_terms`, `ACh_Theory.thy`) — Representation

**Text.** `+` is a binary symbol, but the text freely writes `X = X1 + … + Xn`.

**Formalization.** `sum_terms [t1, …, tn]` is the right-nested binary sum. A flat sum equation
(`flat_sum_eq`) is `X =? sum_terms (map Var ys)` with `length ys ≥ 2`.

**Why.**
- The terms come from the AFP `First_Order_Terms` library, where `+` is an ordinary binary
  `Fun`, so n-ary sums must be encoded.
- With one summand, `X = Y` is a variable–variable equation, which is treated separately.

### 1.3 Normal forms modulo ACh (`ACh_Normal_Form.thy`) — New

**Text.** Not in the dissertation.

**Formalization.**
- A term is normalized to a multiset of *atoms* `hⁿ(x)` / `hⁿ(f(…))`.
- The main theorem is `eq_ACh_iff_nf`: `s ≈ACh t ⟷ nf s = nf t`.

**Why.** The completeness proof (Lemma 3.6) relies on several facts that the text treats as
evident, and each of them needs a proof:
- injectivity of `h`;
- decomposition for free symbols;
- the clash cases;
- the Splitting equation (3.1);
- the occurs check modulo ACh.

All of them follow from the normal form.

### 1.4 h-height (`hh`, Def. 1.21) — Representation

**Text.** h-height is defined by recursion on the term.

**Formalization.** It is computed on normal forms.

**Why.** Definition 1.24 and the completeness proof need h-height to be invariant under `≈ACh`.
For example, `hh(h(x+y)) = 1 = hh(h(x)+h(y))`. With the recursive definition, that invariance
would need a separate proof over all equational derivations. Defined on normal forms, it holds
by construction (`hh_eq_ACh`).

The lemmas `hh_Var`, `hh_H`, `hh_Plus` and `hh_free` recover the equations of Def. 1.21.

---

## 2. Triples and rules (`Bounded_ACh_Unification.thy`)

### 2.1 Set triples — Representation

**Text (Sec. 2.1).** A triple `Γ ∥ Δ ∥ σ` has a *set* of equations Γ, a set of pairs Δ, and a
set of bindings σ.

**Formalization.** `triple = problem × depth_set × bindings` where:
- `Γ` is a **multiset** of equations;
- `Δ` is a partial map `'v ⇀ nat`;
- `σ` is a set of pairs.

**Why.**
- *Multisets:* the termination measures count equations (|Γ|, numbers of `+`-equations). With
  sets, rules like (Dec) can make two equations coincide, and the counts no longer behave as the
  proofs assume.
- *Partial map:* Δ is meant to hold at most one depth per variable. A partial map makes that
  hold by construction, and "updating the depth" becomes `Δ(y ↦ d)`.

### 2.2 Disjunctions of triples — Representation

**Text.** `Γ ∥ Δ ∥ σ ⇒ ⋁ᵢ (Γᵢ ∥ Δᵢ ∥ σᵢ)`, with `⊥` for failure.

**Formalization.** `S ↝ Ss`, where `Ss` is a *set* of triples:
- failure rules produce `{}`, the empty disjunction;
- (AC) produces one triple per unifier;
- every other rule produces a singleton.

On top of that, three notions describe derivations:

| Notion | Meaning | Dissertation |
|---|---|---|
| `step_one` / `↝*` | Follow one branch | `⇒*` |
| `tree S L` | Finite derivation tree from `S` with leaf set `L` | `⇒* ⋁ᵢ` |
| `reach S P` | Some tree from `S` has every leaf satisfying `P` | — |

**Why.** These make "applying rules exhaustively yields a disjunction" precise.

### 2.3 Rule-by-rule differences from Fig. 2.2

These are also documented in the text block before `inductive step`.

| Rule | Change | Kind | Reason |
|---|---|---|---|
| (FlFun) | Requires some argument to be a non-variable | Correction | Without this condition the rule applies forever to `f(X1,…,Xn)`. Lemma 3.1's proof already assumes `tᵢ ∉ V`. |
| (Clash) | Requires `f ≠ g` | Correction | As stated, it fires on `X = f(…), X = f(…)` for a free `f`, a case (Dec) must handle. That would make the system incomplete. |
| (OC) | Condition `X ∈ Var(f(t1,…,tn))` | Correction | The text's `Var(f(…)σ)` also applies σ. That is unnecessary, because (VE1)/(VE2) already apply each new binding to Γ, so bound variables never occur in Γ (`solved_inv`). The formal rule uses the standard [BN98] condition. |
| (AC) | Fresh variables | Correction | New variables of the AC-unifiers must be fresh for the whole triple. The AC algorithm receives the set of variables to avoid. |
| (AC) | New variables get depth 0 | Correction | The text only says that new variables "must be added to Δ". |
| (AC) | Requires `Ψ ≠ ∅` | Correction | As stated, (AC) applies even to `∅ ∥ Δ ∥ σ`, so no triple would ever be irreducible and "solved form" would be unreachable. |
| (AC) | Applies to any non-empty sub-multiset Ψ of *flat* `+`-equations | Needed for termination | The strategy applies (AC) one h-depth level at a time (see §4.3). Flatness is also what the AC-completeness assumption needs. |
| (Dec) | Arguments may be arbitrary terms, not only variables | Generalization | The text's version is a special case. |
| (UV) | **New rule:** for `X = Y`, raise `Δ(Y)` to `Δ(X)` | Needed for termination | Without it, eliminating X by (VE1) can move X's equations to a smaller depth, which breaks the level-wise measure. |
| (USum) | **New rule:** (UL)/(UR) for sums of any length | Needed for termination | (Split) and (AC) produce sums with n > 2 summands, and the text only gives update rules for `Y1 + Y2`. |
| (FU) | Gives the new variable depth 1 | — | This is the dissertation's improved version, not that of [EL20]. |

All other rules match the text: (FBS), (FL), (FR), (Uh), (UL), (UR), (VE1), (VE2), (Triv),
(Orient), (BC) and (Split).

### 2.4 The AC-unification algorithm as a parameter — Made explicit

**Text.** It uses Stickel's algorithm as formalized in PVS [AFSS22].

**Formalization.** `ac_unify :: 'v set ⇒ problem ⇒ unifier list` is a locale parameter, and
each part of the development assumes only the properties it uses:

| Locale | Assumption | Used for |
|---|---|---|
| `bounded_ach` | `ac_unify_sound`: each result is an AC-unifier of Ψ | Soundness |
| `bounded_ach_complete` | `ac_unify_complete`: every ACh-solution θ of flat Ψ extends to a solution θ' of `GetEqs(ρ)` for some result ρ, agreeing with θ on `Var(Ψ)`, with new variables not h-higher than old ones | Completeness (Lemma 3.6, case (AC)) |
| `bounded_ach_term` | `ac_fresh`: new variables avoid the given finite set | Termination |
| `bounded_ach_term` | `ac_shape`: Stickel shape — each variable of Ψ bound at most once, to a new variable or a sum of ≥ 2 new variables | Termination |

**Why.**
- No Isabelle formalization of Stickel's algorithm is available here.
- The h-height clause in `ac_unify_complete` is what the text uses silently when it says (AC)
  keeps bounded solutions bounded.
- The shape assumption is what makes the per-level counts drop after (AC).

### 2.5 Satisfiability and the computed substitution — Made explicit

- **Satisfaction of a triple.** `θ ⊨ (Γ, Δ, σ)` (`sat_triple`) is exactly the text's definition:
  θ ⊨ Γ, θ ⊨ σ, and MaxVal(Δ) ≤ κ.
- **Solved-form invariant.** `solved_inv` requires three things of σ:
  - each variable is bound at most once;
  - bound variables do not occur in bound terms;
  - bound variables do not occur in Γ.

  The proof of Corollary 3.2 says "obviously σᵢ ⊨ Γᵢ ∥ Δᵢ ∥ σᵢ". That holds only under this
  invariant, so the formalization proves that every rule preserves it (`step_solved_inv`).
- **Reading off the unifier.** `subst_of_bindings` turns a set of bindings into a substitution.

---

## 3. Completeness (`Bounded_ACh_Completeness.thy`)

### 3.1 Bounded solutions of triples (`bsol`) — Made explicit

**Formalization.** `bsol θ (Γ, Δ, σ)` holds when all of the following do:
- θ satisfies Γ and σ;
- every side of every equation of Γ, instantiated by θ, has h-height ≤ κ (Def. 1.24);
- `Δ x = Some d ⟹ d + hh(θ x) ≤ κ` (**depth consistency**).

**Why.** Depth consistency is left implicit in the text. The update rules raise depths, and
`θ ⊨ Γ ∥ Δ ∥ σ` alone does not ensure the raised depths stay ≤ κ. Depth consistency is preserved
by the update rules, so (BC) never discards a bounded solution. This is what the (BC) case of
Lemma 3.6 needs.

### 3.2 Lemma 3.6 / Theorem 3.3 — Generalization

**Formalization.**
- `step_complete`: *whichever* rule is applied to a triple with a bounded solution θ, some
  resulting triple has a bounded solution θ' that agrees with θ on the triple's variables.
- `tree_complete` lifts this to whole derivation trees.

**Why.** This is strategy-independent: it does not require choosing a rule, and it shows directly
that (OC), (Clash) and (BC) never fire on solvable triples. As a result, completeness of
`unify` needs no extra argument about the order in which the algorithm applies the rules.

### 3.3 Corollary 3.3 — Correction

**Text.** "for each ACh-unifier θ of Γ there is σⱼ ≲ θ".

**Formalization.** `completeness` and `completeness_bounded_unifier` require θ to be
**κ-bounded** (`hbounded`).

**Why.** Unbounded unifiers are legitimately cut off by (BC), so the unrestricted statement
is false.

The formalization also needs two side conditions that the text leaves implicit:
- `progress`: the variable type is infinite, so every non-empty finite triple can be reduced;
- Δ covers `Var(Γ)` and is finite.

---

## 4. Termination (`Bounded_ACh_Termination.thy`)

### 4.1 Flattening (Lemma 3.1) — as in the text

`flat_measure` is exactly the multiset M(Γ) of Lemma 3.1, and `flattening_terminates` proves
it is well founded.

The end-to-end phase (`flatten_phase`) also interleaves (Orient). (Orient) does not change M(Γ)
but decreases the number of equations with a non-variable left-hand side.

### 4.2 Theorem 3.1 is false as stated — Correction

**Text.** Theorem 3.1 claims that the measure of Def. 3.3,
`(κ − a, nX, |Sym(Γ)|, m, p, |Γ|, hd(Δ))`, decreases with **every** rule application.

**Counterexample (`VE2_increases_sym_count`).** Apply (VE2) to `{X = c, Y = g(X, X)}`. The
result is `{Y = g(c, c)}`:
- `|Sym|` grows from 2 to 3;
- the first two components are unchanged.

**Further problems.**
- **Lemma 3.2** says (AC) is applied at most κ times. It relies on Prop. 3.1 (AC-solved
  variables stay AC-solved), which excludes (VE1). But Algorithm 1 applies (VE1) after every
  step, and Example 3.2 itself shows (VE1) un-solving a variable.
- Applying (AC) to *all* `+`-equations at once can create new work at smaller h-depths.

**Consequence.** The rule system is not terminating rule by rule. What the formalization proves
is termination **of a strategy**: from every admissible input there is a *finite* derivation
tree whose leaves are all irreducible, `reach S irreducible`.

### 4.3 The new measure and strategy — New

**Measure.** `tmeasure (Γ, Δ, σ) = (nfree Γ, levels Γ Δ)`, ordered by
`term_rel = less_than <*lex*> lex R3`:
- `nfree`: the number of free-symbol equations;
- `levels`: for each depth level `l = 0..κ`, the triple of counts given by `counts`:
  1. the *excess* `+`-equations at level l (a variable heading k of them contributes k − 1);
  2. the number of `+`-equations at level l;
  3. the number of h-equations at level l.

**Strategy.** It works on states satisfying two invariants:
- `pnormal`: flat, Δ covers the variables, Δ is closed under the update rules, and Δ is bounded;
- `normal`: `pnormal` and no `X = Y` equations.

From a normal state, any variable heading two equations triggers one **macro step**, which ends
in a normal state again with a smaller measure:

| Pair of equations for X | Macro step |
|---|---|
| Two h-equations | (Dec), then merge |
| Two free equations | (Dec) or (Clash), then close Δ and merge |
| h-equation and sum | (Split) or (OC), then close Δ |
| Two sums | (AC) on all flat sums at level Δ(X), then close Δ and merge in every branch |
| Free symbol against h or `+` | (Clash) |

Once no variable heads two equations, `final_phase` applies (VE2), (Triv) and (OC) to empty the
problem.

**Helper definitions this needed.**
- `edge`, `closed`, `prot`, `potential`:
  - closing Δ under (Uh)/(UL)/(UR)/(USum)/(UV) terminates (`update_closure`), with potential
    `Σ (κ + 1 − Δ(x))`, the analogue of the text's `hd(Δ)`;
  - it doesn't disturb levels below the current one;
- `close_post`: packages the guarantees of closing Δ;
- `VV`, `merge_inv`, `ren`, `rename_eq`: merging `X = Y` equations by (VE1) plus closure, with
  the levels below unchanged (`merge_step`, `vv_closure`);
- `split_facts`, `ac_facts`, `dec_h_facts`: the per-macro-step facts, shared between the
  `reach` proofs and the executable algorithm.

### 4.4 Arities — Made explicit

**Formalization.** The locale `bounded_ach_term` fixes `arity` with `arity plus = 2` and
`arity hom = 1`, and inputs must satisfy `arity_ok_problem`.

**Why.** Def. 1.1 says symbols have fixed arity, but the rules never use it. Without arities, a
problem such as `X = f(a, b), X = f(c)` can be neither decomposed nor rejected, and
`X = f(a, b)` with `arity f = 1` is neither flat nor flattenable.

### 4.5 End-to-end statement

`ach_unification_terminates` assumes:
- `arity_ok_problem Γ`;
- Δ is finite and covers `Var(Γ)`;
- σ is finite.

It concludes `reach (Γ, Δ, σ) irreducible`. `ach_unification_terminates_initial` specializes
this to Algorithm 1's initial triple, where every variable has depth 0.

---

## 5. The algorithm (`Bounded_ACh_Algorithm.thy`)

### 5.1 Algorithm 1 vs. `unify` — Correction / Needed for termination

**Text.** Algorithm 1 is a single loop with fixed rule priorities:

> (a) Triv → (b) OC → (c) BC → (d) update → (e) Orient → (f) Split → (g) Clash → (h) Dec →
> (i) AC → (j) VE2

with (VE1) applied exhaustively after each step.

**Formalization.**

```
unify S = concat (map main_fun (concat (map merge_fun (close_fun (flatten S)))))
```

The phases are:

1. **`flatten`** applies the flattening rules and (Orient) until the problem is flat
   (Algorithm 2).
2. **`close_fun`** applies the update rules until Δ is closed, or fails by (BC). These are steps
   (c)–(d).
3. **`merge_fun`** removes all `X = Y` equations by (Triv), or by (VE1) followed by closing Δ.
4. **`main_fun`** repeats `macro` (§4.3) while some variable heads two equations, then calls
   `final_fun`.
5. **`final_fun`** applies (VE2), (Triv) and (OC). This is step (j).

**What changed and why.**
- (VE1) is followed by closing Δ, not applied blindly. Otherwise depths can drop (§2.3, (UV)).
- (AC) is applied to all `+`-equations **at one depth level**, not to all of them. This is what
  makes the level counts decrease (§4.2).
- There are no global rule priorities. `main_fun` picks the first pair of equations with the
  same left-hand variable and dispatches on their kinds. That is allowed because completeness
  is strategy-independent (§3.2).
- The result is not "a set of unifiers or ⊥". It is the **list of leaf triples**:
  - each leaf is `([], Δ', σ')`, whose `σ'` read as a substitution is a unifier;
  - an empty list means ⊥.

  By `progress`, every irreducible leaf with finitely many variables has an empty problem.

### 5.2 Definitions needed for executability — New

- **List triples** (`ltriple`, `abst`). Multisets, partial maps and sets are not executable as
  such. The algorithm works on `(eq list, (var × nat) list, binding list)`, and
  `abst (Γ, Δ, σ) = (mset Γ, map_of Δ, set σ)` connects it to the rule system.
- **Fresh variables** (locale `bounded_ach_alg`, parameter `fresh :: 'v list ⇒ 'v` with
  `fresh xs ∉ set xs`; `fresh_vars`; `used`).
  - The rules only *assume* a fresh variable exists; a function has to *produce* one.
  - `used S` lists every variable of the triple (`set_used`), and is also passed to `ac_unify`
    as the set to avoid.
- **Generalized trees** (`gtree`, `lsteps`).
  - Two different list triples can have the same abstraction but be processed differently, so
    the abstract leaves of the computation form a *union* of derivation trees.
  - `gtree` adds a `union` constructor, and `lsteps S Ls ≡ gtree (abst S) (abst ` set Ls)`.
  - `gtree_tree` extracts an ordinary `tree`, which is how `completeness` transfers, and
    `gtree_steps` gives `↝*` for `soundness`.
- **Executable tests.**

  | Executable | Proven equal to |
  |---|---|
  | `flat_eqb` | `flat_eq` |
  | `normal_l` | `normal` (`normal_l_iff`) |
  | `kind` | Classifies right-hand sides as `KH`, `KSum`, `KFree`, `KOther` |
  | `find_pair` | Finds a variable heading two equations |
  | `eq_edges`, `viol`, `bounded_l` | List versions of `edge`, an update violation, and `bounded_depths` |

- **The termination guard of `main_fun`.**
  - `main_fun` checks `normal_l` at every call and returns its argument when the check fails.
  - This lets the function package prove termination with
    `inv_image term_rel (tmeasure ∘ abst)` without carrying the invariant in the type.
  - On the actual inputs the guard always holds, but evaluating it at every iteration costs time.
- **Spec lemmas.** `close_fun_spec`, `merge_fun_spec`, `flatten_spec`, `macro_spec`,
  `main_fun_spec` and `final_fun_spec` each say that the function computes the leaves of a
  derivation with the postcondition the `reach` proofs promise. To avoid duplicating proofs,
  `Bounded_ACh_Termination.thy` was refactored to expose `split_facts`, `ac_facts`,
  `dec_h_facts` and `close_post`.

### 5.3 Main results

| Theorem | Statement |
|---|---|
| `unify_spec` | If `ready (abst S)`, then `lsteps S (unify S)`, and every output leaf is irreducible. |
| `unify_sound` | Every solved leaf `([], Δ', σ')` of `unify (Γ, Δ, [])` gives a unifier `subst_of_bindings (set σ')` of Γ. |
| `unify_complete` | In `bounded_ach_alg_complete`: every bounded solution θ of the input is an instance, modulo ACh on `Var(Γ)`, of some solved leaf. |

### 5.4 Executable instance

`global_interpretation ex: bounded_ach_alg 0 1 2 (λ_ _. []) ex_arity ex_fresh` sets up:
- natural numbers as symbols (0 = `+`, 1 = `h`, 2 = binary `f`, 3 = constant `a`) and as
  variables;
- κ = 2;
- `ex_fresh xs = Suc (max xs)`.

`value` reproduces the Triv/Dec/Clash/BC/Split examples. The AC algorithm in this instance
returns no unifiers. That is sound but **not complete**, so the instance does not exercise (AC).
A real instance needs an Isabelle implementation of Stickel's algorithm proven to satisfy
`ac_unify_sound`, `ac_unify_complete`, `ac_fresh` and `ac_shape`.

---

## 6. Summary of the dissertation's statements

| Dissertation | Formalization | Status |
|---|---|---|
| Lemma 3.1 (flattening terminates) | `flat_step_decreases`, `flattening_terminates` | As stated |
| Prop. 3.1, Lemma 3.2 | — | Not used; Lemma 3.2's argument fails (§4.2) |
| Def. 3.3, Theorem 3.1 | `tmeasure`, `main_loop_terminates` | Theorem false rule by rule; replaced by termination of a strategy |
| Corollary 3.1 | `ach_unification_terminates` | Proven for the strategy, assuming arities |
| Lemma 3.3–3.5, Theorem 3.2 | `step_sound`, `steps_sound` | As stated |
| Corollary 3.2 (soundness) | `soundness`, `unify_sound` | Proven with `solved_inv` made explicit |
| Lemma 3.6, Theorem 3.3 | `step_complete`, `tree_complete` | Stronger: holds for any rule (strategy-independent) |
| Corollary 3.3 (completeness) | `completeness`, `unify_complete` | Restricted to κ-bounded unifiers |
| Algorithms 1 and 2 | `unify` | Executable; level-wise (AC), (VE1) with closure |
