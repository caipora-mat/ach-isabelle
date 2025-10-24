theory TermAlgebra
  imports
    Main
    "First_Order_Terms.Term"

begin

(* Testing some concrete definitions of terms to check if importing the theory
First_Order_Terms actually works out.
*)
definition x :: "(string, nat) term"  where "x \<equiv> Var 0"
definition s :: "(string, nat) term"  where "s \<equiv> Fun ''f'' [x, x]" 

(* Computing with functions defined over terms...*)
value "vars_term s"

(*
First goals: test an architecture for implementing an algebra interpretation
for the theory of terms.
  - Deal with the abstract types for function symbols and variable names.
    Question: can i put typeclass constraints on those?
  - How does equality works on Isabelle? (Do i need an explicit equality relation over
    the inductive types?)
  - For instance: the type 'f should have decidable equality and
    the type for 'v should have decidable equality together with
    an structure to generate new names.

  - define a separate notion for carrier taking inspiration on how people
   have defined algebraic structures in Isabelle.
  (type classes? locales?)
*)

(* Decidable equality with computational \<open>eq\<close>. *)
class eq =
  fixes eq :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>


(* unlike coq, where i can define:

Class sig
  (F L : Type)
  `{isFinite F}
  `{isFinite L} := {
  ar : F -> nat ;
  label : F -> L ;
  label_inj : forall ( f g : F), label f = label g -> f = g
}.

type classes in Isabelle cannot relate two abstract types.
So a related definition in isabelle:
class labelled =
  fixes label :: "'a \<Rightarrow> 'b"
  assumes label_inj : "inj label"
produces an error.
This is a bit annoying... *)

(*
This limitation forces us to use a concrete type for labelling, like \<open>nat\<close>
Then a labelled structure (signature) could be defined as follows:
*)
class signature = eq +
  fixes ar :: \<open>'a \<Rightarrow> nat\<close>
  fixes label :: \<open>'a \<Rightarrow> int\<close>
  assumes label_inj : "inj label "

type_synonym ('f, 'v) tm = \<open>('f :: signature, 'v :: eq) term\<close>

text \<open>
  So a signature is a type \<open>'a\<close> that has a notion of equality, an arity function,
  and a label function which is injective.
  We can force our notion of terms to use this type class.
\<close>

text \<open>
  Okay, it seems that \<open>locales\<close> allow for more than one type variable in its
  definition.
  Then perhaps writing labelled structures as locales might be a better idea.

  Let us try that now.
\<close>

(* Locales allows for the usage of different type-variables but type variables
cannot be parametrized by terms (so no dependent types is present).
*)
locale lab_sig =
  fixes S :: "'f :: signature"
  fixes ar :: "'f \<Rightarrow> nat" (* it is possible to add type class constraints when definiting locales *)
  fixes label :: "'f \<Rightarrow> 'l"
  assumes inj_label : \<open>inj label\<close>

text \<open>Extending a locale such that the extension is aware of the type variables.\<close>

locale loc_a =
  fixes f :: \<open>'v list \<Rightarrow> 'v\<close>

locale extend_a = 
  loc_a f
  for f :: \<open>'v list \<Rightarrow> 'v\<close> +
  fixes g :: \<open>'v list\<close>
end