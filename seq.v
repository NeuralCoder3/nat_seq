
Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Require Import Arith.
Require Import List.
Import ListNotations.

Require Import Lists.Streams.

Set Implicit Arguments.

Inductive nelist (A:Type) :=
| nesingle (x:A) : nelist A
| necons (x:A) (xs:nelist A) : nelist A.

Fixpoint prependnelistStream {A} (xs:nelist A) ys :=
    match xs with
    | nesingle x => Cons x ys
    | necons x xr => Cons x (prependnelistStream xr ys)
    end.

Definition ne_head {A} (xs:nelist A) :=
    match xs with
    | nesingle x
    | necons x _ => x
    end.

Fixpoint ne_to_list {A} (xs:nelist A) :=
    match xs with
    | nesingle x => [x]
    | necons x xr => x::ne_to_list xr
    end.

Definition ne_tail {A} (xs:nelist A) :=
    match xs with
    | nesingle _ => []
    | necons _ xr => ne_to_list xr
    end.

(* CoFixpoint concat_list {A} (f:nat -> nelist A) (n:nat) : Stream A.
Proof.
    cofix s.
    induction (f n).
    - apply (Cons x s).
    - apply (Cons x IHn0).
Defined. *)


Fixpoint prependListStream {A} (xs:list A) ys :=
    match xs with
    | [] => ys
    | x::xr => Cons x (prependListStream xr ys)
    end.

Unset Guard Checking.

(* CoFixpoint concat_list {A} (f:nat -> nelist A) n :=
    (fix g xs :=
    match xs with
    | nesingle x => Cons x (concat_list f (S n))
    | necons x xr => Cons x (g xr)
    end
    )
    (f n). *)
    (* Cons (ne_head (f n))
    (prependListStream (ne_tail (f n)) (concat_list f (S n))). *)
(* CoFixpoint concat_list {A} (f:nat -> nelist A) n :=
    let xs := f n in
    Cons (ne_head xs)
    (prependListStream (ne_tail xs) (concat_list f (S n))). *)
    (* prependnelistStream (f n) (concat_list f (S n)). *)

CoFixpoint concat_list {A} (f:nat -> nelist A) n :=
    let xs := f n in
    Cons (ne_head xs)
    (prependListStream (ne_tail xs) (concat_list f (S n))).

Set Guard Checking.

CoFixpoint seq := 
  Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 3 (Cons 2 seq))))).

(* Definition period := [1;2;3;4;3;2]. *)
Notation "[| x |]" := (nesingle x) : nelist_scope.
Notation "[| x ; y ; .. ; z ; u |]" := (necons x (necons y .. (necons z (nesingle u)) ..)) .
Definition period := [|1;2;3;4;3;2|].
Print period.

CoFixpoint seq2 :=
    prependnelistStream period seq2.

Goal EqSt seq seq2.
Proof.
    cofix CIH.
    do 6 constructor;trivial.
Qed.

Fixpoint sum (xs:nelist nat) :=
    match xs with
    | nesingle x => x
    | necons x xr => x+sum xr
    end.

Definition n_to_seq (n:nat) : {xs : nelist nat | sum xs = n}.
Proof.
    (* Search "div" "mod". *)
    (* Nat.divmod_spec. *)
    (* specialize (Nat.div_mod n 15) as H. *)
    assert(15 <> 0) as H15 by lia.
    pose proof(Nat.div_mod n 15 H15) as Hn.
    pose proof(Nat.mod_upper_bound n 15 H15) as Hr.
    remember (n/15) as q.
    remember (n mod 15) as r.
    refine(

    ).
Defined.