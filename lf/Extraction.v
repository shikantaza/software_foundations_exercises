Require Coq.extraction.Extraction.
Extraction Language OCaml.

From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import ImpCEvalFun.

Extraction "/Users/Rajeshjayprakash/code/coq/software_foundations/lf/imp1.ml" ceval_step.

Extract Inductive bool => "bool" [ "true" "false" ].

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
  
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".

Extraction "/Users/Rajeshjayprakash/code/coq/software_foundations/lf/imp2.ml" ceval_step.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extract Inductive sumbool => "bool" ["true" "false"].

From LF Require Import Imp.
From LF Require Import ImpParser.
From LF Require Import Maps.

Extraction "/Users/Rajeshjayprakash/code/coq/software_foundations/lf/imp.ml" empty_st ceval_step parse.


