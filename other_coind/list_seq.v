Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Require Import Arith.
Require Import List.
Import ListNotations.


(* Search Nat.div. *)


Fixpoint first_k {A} k (f:nat->list A) :=
    match k with
    | 0 => []
    | S m => first_k m f ++ f m 
    end.

(* Compute (first_k 3 (fun n => [n])). *)

Fixpoint conform_aux seq xs ys :=
    match xs 
Definition conform seq

Lemma cont_seq:
    forall k, conform seq (first_k k num_seq).

(* Lemma total_seq:
    forall n, sum (num_seq n) = n. *)