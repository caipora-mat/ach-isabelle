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
    - For instance: the type 'f should have decidable equality and
      the type for 'v should have decidable equality together with
      an structure to generate new names.

  - define a separate notion for carrier taking inspiration on how people
   have defined algebraic structures in Isabelle.
  (type classes?)
*)






end