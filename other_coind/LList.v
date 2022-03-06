Require Import List.
Require Import ArithRing.

Set Implicit Arguments.

(** Let us consider the following co-inductive definition *)

 CoInductive LList (A: Type) : Type := (* lazy lists *)
 |  LNil : LList A
 |  LCons : A -> LList A -> LList A.


Arguments LNil {A}.

Check (LCons 1 (LCons 2 (LCons 3 LNil))).


(* builds the infinite list n, 1+n, 2+n, 3+n, etc. *)

CoFixpoint from (n : nat) : LList nat := LCons n (from (S n)).

Definition nat_stream := from 0.



(* exercise 1 :

Build the infinite list  true_false_alter  which alternates the 
 boolean values :  true,false,true,false, ... 
*)

(* exercise 2 *)
(* generate the infinite list n_times_n  :
                   1,2,2,3,3,3,4,4,4,4, .... *)


(* exercise 3 :
 : Let A be any type and f : A -> A.
  define  "iterates f a" as the infinite list 
     a, f a , f (f a), f (f (f a), etc. 

  apply this functional for defining the sequence Exp2 of powers of 2 :
  1,2,4,8,16, etc.
*)


Definition isEmpty (A:Type) (l:LList A) : Prop :=
  match l with
  | LNil => True
  | LCons a l' => False
  end.

(* exercise 4: prove the following lemma *)

Lemma nat_stream_not_Empty : ~ isEmpty nat_stream.
Proof.
Admitted.


Definition LHead (A:Type) (l:LList A) : option A :=
  match l with
  | LNil => None 
  | LCons a l' => Some a
  end.

Eval compute in (LHead (LCons 1 (LCons 2 (LCons 3 LNil)))).

(* Exercise 5 : 
  prove the following lemma *)

Lemma Head_of_from : forall n, LHead (from n) = Some n.
Proof.
Admitted.

Definition LTail (A:Type) (l:LList A) : LList A :=
  match l with
  | LNil => LNil 
  | LCons a l' => l'
  end.

(* Exercise 6 :

 define a function Nth (A:Type)  (n:nat) (l:LList A) : option A
   such that (Nth n l) returns 
     - (Some a) if a is the n-th element of l (0-based)
     - None if l has less than n+1 elements


If your solution is good, you can make a simple test :

Eval compute in (LNth 5 Exp2).
Some 32 : option nat

*)




(* Exercise 7 :

   For this exercise (and perhaps another one) , you may use the 
   following tools  (but it's not mandatory) :
   
   Standard library's  theorem f_equal 
   tactic ring on natural numbers (from  the ArithRing module) : 


Proove the following theorem :

   
Lemma LNth_from : forall n p, LNth n (from p) = Some (n+p).
*)




(* exercise 8 : 
   define a function   list_inj (A:Type)(l : list A) : LList A
 
  which maps any (finite) list to a lazy list having the same elements
  in the same order
 *)


(* exercise 9 :

  in order to validate your function list_inj,
   prove the lemma list_inj_ok (which uses the following nth function on 
   finite lists).
 *)

Fixpoint nth (A:Type)  (n:nat) (l:list A)  {struct l} : option A :=
match n,l  with | _,nil => None
                | 0,a::_ =>  Some a
                | S p, _::l' => nth p l'
end.
           
(*
Lemma list_inj_Ok : forall (A:Type)(l : list A)(n:nat),
   nth n l  = LNth  n (list_inj l) .

*)

(* exercise 10 :
  Define a "reciprocal"  to list_inj :
   firsts (A:Type) n (l:LList A): list A
   returns the list of n-ths first elements of l

   if l is finite and too short, firsts returns the list of all elements of l

Here is a little test :

Eval compute in (firsts 6 Exp2).
    = 1 :: 2 :: 4 :: 8 :: 16 :: 32 :: nil
     : list nat

Eval compute in (firsts 10 n_times_n).
 = 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 4 :: 4 :: 4 :: 4 :: nil
     : list nat
*)


(* Exercise 11 (not so easy) :
 Prove that Exp2 truely contains the sequence of all powers of 2 *)



Inductive Finite(A:Type): LList A -> Prop :=
 Finite_LNil : Finite LNil
|Finite_Lcons : forall a l, Finite l -> Finite (LCons a l).

CoInductive Infinite(A:Type): LList A -> Prop :=
 Infinite_LCons : forall a l, Infinite l -> Infinite (LCons a l).

CoInductive LList_eq (A:Type): LList A -> LList A -> Prop :=
| LList_eq_LNil : LList_eq LNil LNil
| LList_eq_LCons : forall a l l', LList_eq l l' ->
                                  LList_eq (LCons a l) (LCons a l').

Definition LList_decomp (A:Type) (l:LList A) : LList A :=
  match l with
  | LNil => LNil
  | LCons a l' => LCons a l'
  end.

(* Eval simpl in (LList_decomp n_times_n). *)


Lemma LList_decompose : forall (A:Type) (l:LList A), l = LList_decomp l.
Proof.
 intros A l; case l; trivial.
Qed.

Ltac unwind_i := 
 match goal with | |- ?t1= ?t2  =>
          apply trans_equal with (1 := LList_decompose t1);auto
end.

Ltac unwind term1 term2 := 
  let eg := fresh "eg" in
  assert(eg : term1 = term2);
     [unwind_i|idtac].



(* Lemma bool_alternate_Infinite : forall b, Infinite (bool_alternate b).
Proof.
 cofix.
 intro b.
 unwind (bool_alternate b) (LCons b (bool_alternate (negb b))).
 rewrite eg.
 constructor.
 auto.
Guarded.
Qed. *)


(* exercise 12 : Prove the following lemmas

Lemma Exp2_Infinite : Infinite Exp2. 


Lemma bool_alternate_eqn : forall b, bool_alternate b =
                                     LCons b (bool_alternate (negb b)).
*)



CoFixpoint LAppend (A:Type) (u v:LList A) : LList A :=
  match u with
  | LNil => v
  | LCons a u' => LCons a (LAppend u' v)
  end.

Lemma LAppend_LNil : forall (A:Type) (v:LList A), LAppend LNil v = v.
Proof.
 intros A v.
 destruct v; unwind_i.
Qed.


Lemma LAppend_LCons :
  forall (A:Type) (a:A) (u v:LList A),
    LAppend (LCons a u) v = LCons a (LAppend u v).
Proof.
 intros A a u v.
 unwind_i.
Qed.
 
Hint Rewrite  LAppend_LNil LAppend_LCons : llists.



Lemma LAppend_Infinite_1 : forall (A:Type)(u v : LList A),
                             Infinite u -> Infinite (LAppend u v).
Proof.
 intro A. cofix LAppend_Infinite_1.
 destruct u.
 intros v H;inversion H.
 intros v H;rewrite LAppend_LCons.
constructor;auto.
 apply LAppend_Infinite_1.
 inversion H;auto.
Qed.

(* exercise 13 :
Prove the following lemma :

Lemma LAppend_Infinite_2 : forall (A:Type)(u v : LList A),
                           Infinite v -> Infinite (LAppend u v).
*)

(* exercise 14 :
Prove the following lemma :

Lemma LAppend_Infinite_3 : forall (A:Type)(u v : LList A),
                             Infinite (LAppend u v) -> 
                             Finite u ->  Infinite v.
*)
 

(* exercise 15 :
Prove the following lemma :
Lemma LAppend_absorbent : forall (A:Type)( u v: LList A),
                                       Infinite u -> 
                                       LList_eq u (LAppend u v).
*)





 
 
 


    