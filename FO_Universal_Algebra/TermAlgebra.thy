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

(* some testing *)
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

(* This limitation forces us to use a concrete type for labelling, like nat... 
Then a labelled structure (signature) could be defined as follows:
*)
class signature = eq +
  fixes ar :: \<open>'a \<Rightarrow> nat\<close>
  fixes label :: \<open>'a \<Rightarrow> nat\<close>
  assumes label_inj : "inj label "

text \<open>
  So a signature is a type \<open>'a\<close> that has a notion of equality, an arity function,
  and a label function which is injective.
  We can force our notion of terms to use this type class.
\<close>





end