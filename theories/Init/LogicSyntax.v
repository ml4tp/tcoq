(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require Export Logic.

(** Symbolic notations for things in [Logic.v] *)

Notation "< P , Q > { p , q }" := (conj P Q p q) (at level 1).

Notation "~ x" := (not x) (at level 5, right associativity).
Notation "x = y" := (eq ? x y) (at level 5, no associativity).

Infix RIGHTA 6 "/\\" and.
Infix RIGHTA 7 "\\/" or.
Infix RIGHTA 8 "<->" iff.

Notation "'IF' c1 'then' c2 'else' c3" := (IF c1 c2 c3)
  (at level 1, c1, c2, c3 at level 8).

(* Order is important to give printing priority to fully typed ALL and EX *)

Notation All := (all ?).
Notation "'ALL' x | p"     := (all ? [x]p)   (at level 10, p at level 8).
Notation "'ALL' x : t | p" := (all t [x:t]p) (at level 10, p at level 8).

Notation Ex  := (ex ?).
Notation "'EX' x | p"      := (ex ? [x]p)    (at level 10, p at level 8).
Notation "'EX' x : t | p"  := (ex t [x:t]p)  (at level 10, p at level 8).

Notation Ex2 := (ex2 ?).
Notation "'EX' x | p & q"       := (ex2 ? [x]p [x]q)
  (at level 10, p, q at level 8).
Notation "'EX' x : t | p & q"   := (ex2 t [x:t]p [x:t]q)
  (at level 10, p, q at level 8).

(** Parsing only of things in [Logic.v] *)

Notation "< A > 'All' ( P )" := (all A P) (at level 1, only parsing).
Notation "< A > x = y" := (eq A x y) (at level 1, x at level 0, only parsing).
