Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Require Import Arith.
Require Import List.
Import ListNotations.

Load LList.


Fixpoint appendListLList {A} (xs:list A) ys :=
    match xs with
    | [] => ys
    | x::xr => LCons x (appendListLList xr ys)
    end.

Fixpoint toLList {A} (xs:list A) :=
    match xs with
    | [] => LNil
    | x::xr => LCons x (toLList xr)
    end.

Goal forall {A} (xs:list A) ys,
    LAppend (toLList xs) ys = appendListLList xs ys.
Proof.
    induction xs;cbn;intros ys.
    - now rewrite LAppend_LNil.
    - rewrite LAppend_LCons.
      now rewrite IHxs.
Qed.

Inductive nelist (A:Type) :=
| nesingle (x:A) : nelist A
| necons (x:A) (xs:nelist A) : nelist A.

Fixpoint nelistToLList {A} (xs:nelist A) :=
    match xs with
    | nesingle x => LCons x LNil
    | necons x xr => LCons x (nelistToLList xr)
    end.

Fixpoint prependnelistLList {A} (xs:nelist A) ys :=
    match xs with
    | nesingle x => LCons x ys
    | necons x xr => LCons x (prependnelistLList xr ys)
    end.

    (* Check ne_list. *)

CoFixpoint concat_list {A} (f:nat -> nelist A) n :=
    prependnelistLList (f n) (concat_list f (S n)).




