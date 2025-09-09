(* This file contains some implementation ideas and testing on ocaml
of some functions we might implement on Isabelle *)

(*  *)
type ('f , 'x) terms =
  | Var of 'x
  | Fn of 'f * (('f , 'x) terms) list

(* A tutorial on how to generate new fresh names. *)
(*
The problem of geenerating a new fresh name (or variable) is a common
in automated reasoning algorithms such as the
the unification algorithm we are working on.

Here, I will show how to understand this problem algorithmically,
with a programmer mindset in mind.
This is very useful in practice, since on a paper-and-paper discourse
we can just say "and v is a fresh variable" and we don't need to show
how to actually build this variable.

Some of the techniques:
  1. The split technique: basically, split the types of variables into two
  distinct possibilities, one for the input and one specific for the
  name generation.
  For instance, if variables are strings we can enforce that all input variables
  have names from a certein alphabet while the names generate are taken
  from another alphabet.

  (This is often annoying to keep track and forces the users of a function
  to respect too of an arbitrary rule on naming...)

  I wwon't show how to implement this because i don't like this solution.
*)

(* 2. The second solution the concrete one. *)
(* Let us use our definition of terms from above and specilialize its type to a concrete one. *)

type my_terms = (string, int) terms

(* Now function names are strings and variable names are integers.
Observe that choosing the variable names to be integers doesn't change how
the variables are presented to a person using the algorithm.
All we need is a function to_internal : string -> int
that collects the names given as input and map them to specific integers.]
This is a problem only when implementing unification (or extracting code)
to have a usable tool.

*)

(* Examples of terms*)

let my_tm_1 = Fn ("+", [Var 0 ; Var 0]) (* +(X,X) *)
let my_tm_2 = Fn ("+", [Var 0; Var 1]) (* +(X,Y) *)

(* Main ideas:
  - keep track of the biggest name used everytime a function is needed,
  and if any function creates a new name we update this record
  - pass the argument around to other functions
*)
(* This is somewhat abstract, and there are multiple ways of implementing this.
In ocaml for isntance:
  - we could use a reference type,
  - literally pass the argument around,
  - state monads,
  - modules.
The actual implementation will depend on the tools available in the target langauge.
I will do oen that is a bit annoying in practise but it will be a good didactic tool.
*)

(* First we define a renaming function on terms. *)
(* It receives a term and two names x and y and replaces x by y. *)
let rec rename (t : my_terms) (x : int) (y : int) : my_terms =
  match t with
  | Var z -> if (Int.equal x z) then Var y else Var z
  | Fn (f, args) ->
    Fn (f, (List.map (fun t -> rename t x y) args))
(* Notice that this function is the identity whenever x doesn't appear in the syntax of t.
In a formalization this would be a lemma, for instance.
*)

(* The very interesting part is then, generating a new name and calling the renaming. *)
(* So in this example, suppose we have a term t and a name x.
The goal of fresh is then to give us a new term t' such that x is replaced by a new variable 'x.
  1. collect the maximal name used (whic in this case it is the latest name used in the term)
  2. generate a new variable with a name greater than that one.
*)
(* Implementing 1 *)

let max_name t =
  let rec aux t acc =
    match t with
    | Var z ->
      if (z > acc) then z
      else
        acc
    | Fn (f, args) ->
        List.fold_left Int.max 0 (List.map (fun t -> aux t acc) args)
  in aux t (-1)

let fresh t z =
  let last_name = max_name t in
  match t with
  | Var x ->
    if x = z then Var (last_name + 1) else Var x
  | Fn (f, args) ->
    let new_args = List.map (fun t -> rename t z (last_name + 1)) args in
    Fn (f, new_args)


type fn_class = None | AC

type ('f, 'x) unifProb = {
  fn_eq : 'f -> 'f -> bool ;
  var_eq : 'x -> 'x -> bool ;
  label : 'f -> fn_class ;
  eq : (('f , 'x) terms * ('f, 'x) terms) list
}

(* regras : eq -> eq list *)
let rec fn_dec_aux ss ts =
  match (ss, ts) with
  | ([], []) -> []
  | (( x :: xs), (y :: ys)) -> (x, y) :: fn_dec_aux xs ys
  | _ -> exit 0

let fn_dec (p : ('f, 'x) unifProb) =
  match List.hd p.eq with
  (* | (FnAC ....) -> ... *)
  | (Fn (f, ts), Fn (g, ss)) ->
    if (p.fn_eq f g) && (p.label f == None) && (List.length ts == List.length ss) then
      let new_list = fn_dec_aux ts ss in
      let uni_prob = fun eq ->
      {
        fn_eq = p.fn_eq ;
        var_eq = p.var_eq ;
        label = p.label ;
        eq = eq
      } in
      List.map uni_prob new_list (* exercicio pro leitor: arrumar *)
    else
      exit 0
  | _ -> exit 0





(*

Inductive tm (F VS : Type) : Type :=
  | varTm : forall (x : VS), tm F VS
  | funTm : forall (f : F) (ts : list (tm F VS)), tm F VS.

Arguments varTm {_} {_} _.
Arguments funTm {_} {_} _ _.

Inductive SK := U | AC | H | INV.

Class sig (F : Type) `{isFinite F} := {
  ar : F -> nat ;
  label : F -> SK ;
  label_inj : forall ( f g : F), label f = label g -> f = g
}.

Fixpoint h_height
         {F VS : Type}
         `{sig F}
         (t : tm F VS)
  : nat.
Proof.
  refine
  match t with
  | varTm x => 0
  | funTm f ts =>
    match (label f) with
    | H => _
    | _ => _
    end
  end.






*)
