Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Require Import Arith.
Require Import List.
Import ListNotations.


(* Search Nat.div. *)



(* Lemma total_seq:
    forall n, sum (num_seq n) = n. *)

(* 
Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream. *)


Set Implicit Arguments.
CoInductive LList (A: Type) : Type := (* lazy lists *)
| LNil : LList A
| LCons : A -> LList A -> LList A.
Arguments LNil {A}.


CoFixpoint from (n:nat) : LList nat :=
LCons n (from (S n)).
Definition nat_stream := from 0.
CoFixpoint repeat (A:Type)(a: A) := LCons a (repeat a).

Definition LHead (A:Type) (l:LList A) : option A :=
match l with
| LNil => None
| LCons a l' => Some a
end.
Definition LTail (A:Type) (l:LList A) : LList A :=
match l with
| LNil => LNil
| LCons a l' => l'
end.


(* CoFixpoint filter (A:Type)(p:A->bool)(l:LList A) :=
match l with
LNil => LNil
| LCons a l' => if p a then LCons a (filter p l')
    else filter p l'
end.
 *)

CoFixpoint LAppend (A:Type) (u v:LList A) : LList A :=
match u with
| LNil => v
| LCons a u' => LCons a (LAppend u' v)
end.

CoFixpoint LMap(A B:Type)(f : A -> B)(u :LList A)
: LList B :=
match u with
| LNil => LNil
| LCons a u' => LCons (f a) (LMap f u')
end.

Inductive Finite(A:Type): LList A -> Prop :=
Finite_LNil : Finite LNil
|Finite_Lcons : forall a l, Finite l ->
Finite (LCons a l).
Lemma L123 : Finite (LCons 1 (LCons 2 (LCons 3 LNil))).
Proof.
repeat constructor.
Qed.

CoInductive Infinite(A:Type): LList A -> Prop :=
Infinite_LCons : forall a l, Infinite l ->
Infinite (LCons a l).

Lemma Tail_of_Infinite : forall (A:Type)(l : LList A),
Infinite l ->
Infinite (LTail l).
Proof.
destruct l.
intro H;inversion H.
intro H;inversion_clear H.
simpl;assumption.
Qed.


Definition frob A (s : LList A) : LList A :=
  match s with
    | LNil => LNil
    | LCons h t => LCons h t
  end.

Theorem frob_eq : forall A (s : LList A), s = frob s.
  destruct s; reflexivity.
Qed.

Lemma from_Infinite : forall n, Infinite (from n).
Proof.
cofix H.
intro n.
(* unwind (from n) (LCons n (from (S n))). *)
replace (from n) with (LCons n (from (S n))).
- constructor. auto.
- rewrite (frob_eq (from n)). now simpl.
Qed.

CoInductive LList_eq (A:Type)
: LList A -> LList A -> Prop :=
| LList_eq_LNil : LList_eq LNil LNil
| List_eq_LCons : forall a l l',
LList_eq l l' ->
LList_eq (LCons a l) (LCons a l').

(* Lemma LList_eq_LNth : forall A (l l': LList A),
LList_eq l l' <->
(forall n, LNth n l = LNth n l'). *)

Lemma Infinite_not_Finite : forall A (l:LList A),
Infinite l -> ~ Finite l.
Proof.
    intros A l H H0.
    revert H.
    (* generalize H. *)
    induction H0.
    - inversion 1.
    - inversion_clear 1.
      auto.
Qed.

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
    induction xs;cbn.
    - 

CoFixpoint concat_list {A} (f:nat -> list A) n :=
    appendListLList
    LCons n (from (S n)).




