# Isabelle Mechanization of equational unification

This repo contains the files for our formalization of the bounded ACh-unification algorithm in Isabelle. For now, the main 2 files are:

- Freshness.thy: Defines a locale with a function to generate a fresh variable of a list. It also contains a proof of soundness of the procedure.
- Experiments.thy: Contains some prototype definitions of how an ACh term can be seen and what is an unification problem in its variable abstracted form. Also, it contains a definition that puts an application of an AC funciton symbol in its flattened form. This is just an experiment file to test new definitions. Once we feel those are well stablished, we intend to move them to their respective files.

The folder "FO_Universal_Algebra" just contains some testing of instantiation of the First-Order library into Universal Algebra to understand the Isabelle syntax and how to import other theories, we are not using this file in our formalization per se.

# To-Do
[] Define the variable abstracting rules;
[] Create a separate file for the Variable Abstracting procedure with its soundness proof;
[] Separate the file that works with ACh Terms and the flattening of an AC application;
[] Define the rules for the bounded ACh-unification algorithm;

## Useful links

- Isabelle Archive of Formal Proofs [https://www.isa-afp.org](https://www.isa-afp.org)
- The theory for first-order terms, [https://www.isa-afp.org/sessions/first_order_terms/#Term](https://www.isa-afp.org/sessions/first_order_terms/#Term)
- Paper, [https://arxiv.org/abs/1811.05602](https://arxiv.org/abs/1811.05602)

## Interesting Questions/Ideas

## Challanges of the formalization?
