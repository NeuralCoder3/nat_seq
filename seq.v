
Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Require Import Arith.
Require Import List.
Import Nat.
Import ListNotations.

Require Import Lists.Streams.

Load util.

(** Auxiliary definitions **)

Fixpoint prependListStream {A} (xs:list A) ys :=
  match xs with
  | [] => ys
  | x::xr => Cons x (prependListStream xr ys)
  end.

Inductive ne_list (A:Type) : Type :=
| ne_single (a:A)
| ne_cons   (a:A) (xs:ne_list A).
Arguments ne_single {A}.
Arguments ne_cons {A}.

Definition prependNeListStream {A} (xs:ne_list A) ys :=
  (cofix prepend (xs : ne_list A) :=
  match xs with
  | ne_single x => Cons x ys
  | ne_cons x xr => Cons x (prepend xr)
  end) xs.

CoFixpoint concat_list {A} (f:nat -> ne_list A) n :=
  (prependNeListStream (f n) (concat_list f (S n))).

Definition to_ne_list {X} (xs:list X) (Hne:xs<>nil) : ne_list X.
Proof.
  induction xs.
  - congruence.
  - destruct xs.
    + exact (ne_single a).
    + refine (ne_cons a (IHxs _)).
    congruence.
Defined.








(** Main definitions **)

Definition period := [1;2;3;4;3;2].

CoFixpoint seq := prependListStream period seq.
CoFixpoint seq2 := Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 3 (Cons 2 seq2))))).


Definition offset r := 
  match r with
  |  0 =>  0
  |  1 =>  0
  |  2 =>  1
  |  3 =>  2
  |  4 =>  3
  |  5 =>  4
  |  6 =>  6
  |  7 =>  9
  |  8 => 11
  |  9 => 15
  | 10 => 18
  | 11 => 22
  | 12 => 27
  | 13 => 32
  | 14 => 37
  | _ => 0
  end.

Definition extra r := 
    match r with
    |  0 => []
    |  1 => [1]
    |  2 => [2]
    |  3 => [3]
    |  4 => [4]
    |  5 => [3;2]
    |  6 => [1;2;3]
    |  7 => [4;3]
    |  8 => [2;1;2;3]
    |  9 => [4;3;2]
    | 10 => [1;2;3;4]
    | 11 => [3;2;1;2;3]
    | 12 => [4;3;2;1;2]
    | 13 => [3;4;3;2;1]
    | 14 => [2;3;4;3;2]
    | _ => []
  end.

Definition qrseq (q:nat) (r:nat) : (list nat) * (list nat) :=
    (
      concat(repeat (rotate (offset r) period) q),
      extra r
    ).

Definition n_to_seq (n:nat) :=
  let (qseq,rseq) := qrseq (n/15) (n mod 15) in
  qseq ++ rseq.

Ltac solve_eqst_const :=
  match goal with
  | |- EqSt (Cons ?A ?B) (Cons ?C ?D) =>
      constructor;[auto|cbn [tl]]
  | _ => fail
  end.











(** Auxiliary proofs **)

Goal EqSt seq seq2.
Proof.
  cofix CIH.
  do 6 constructor;trivial.
Qed.

Lemma prepend_app {X} (xs ys:list X) s:
  prependListStream (xs++ys) s =
  prependListStream (xs) (prependListStream ys s).
Proof.
  induction xs;cbn.
  - reflexivity.
  - now rewrite IHxs.
Qed.

Lemma prepend_list_ne_list X (xs:list X) H S:
  prependListStream xs S =
  prependNeListStream (to_ne_list xs H) S.
Proof.
  induction xs as [|x [|y xs] IH].
  - congruence.
  - rewrite (unfold_Stream (prependNeListStream _ _));cbn.
    reflexivity.
  - cbn [prependListStream].
    rewrite (unfold_Stream (prependNeListStream _ _)).
    cbn. f_equal. apply IH.
Qed.

Lemma concat_list_unfold_list X f H n:
  let g n := @to_ne_list X (f n) (H n) in
  concat_list g n =
  prependListStream (f n) (concat_list g (S n)).
Proof.
  cbn.
  rewrite (unfold_Stream (concat_list _ _)).
  unfold concat_list at 1.
  fold (@concat_list X).
  rewrite prepend_list_ne_list.
  setoid_rewrite (unfold_Stream (prependNeListStream _ _)) at 2.
  reflexivity.
Qed.








(** Main proofs **)

Lemma qrseq_spec q r (Hr:r<15):
  let (ps,rs) := qrseq q r in
  sum ps = 15 * q /\
  sum rs = r.
Proof.
  destruct qrseq as [ps rs] eqn:H.
  revert H.
  do 15 try (destruct r as [|r]).
  16: lia.
  all: cbn;injection 1 as <- <-.
  all: rewrite repeat_sum;cbn;split;lia.
Qed.

Definition n_to_seq_spec (n:nat) : 
  n>0 ->
  let xs := n_to_seq n in
  sum xs = n /\ xs <> nil.
Proof.
  intros H0.
  assert(15 <> 0) as H15 by lia.
  pose proof(Nat.div_mod n 15 H15) as Hn.
  pose proof(Nat.mod_upper_bound n 15 H15) as Hr.
  unfold n_to_seq.
  remember (n/15) as q.
  remember (n mod 15) as r.
  pose proof(@qrseq_spec q r Hr) as H.
  destruct (@qrseq q r) as [qseq rseq] eqn: Hseq.
  destruct H as [Hqseq Hrseq].
  split.
  - now rewrite sum_app Hqseq Hrseq Hn.
  - destruct n;[lia|].
    do 15 try (destruct r as [|r]).
    16: lia.
    all: cbn in Hseq;injection Hseq as <- <-.
    2-15: now apply app_not_nil_r.
    assert(q>0) by lia.
    destruct q;[lia|].
    cbn;congruence.
Defined.

Lemma prependPeriod s:
EqSt s seq ->
EqSt (prependListStream period s) seq.
Proof.
  intros H.
  rewrite (unfold_Stream seq).
  do 6 constructor;[reflexivity|].
  apply H.
Qed.

Lemma prependRepeatPeriod n s:
EqSt s seq ->
EqSt (prependListStream (concat (repeat period n)) s) seq.
Proof.
  intros H.
  induction n.
  - apply H.
  - cbn [repeat concat].
    rewrite prepend_app.
    apply prependPeriod, IHn.
Qed.

Lemma prependPeriodSeq:
  prependListStream period seq = seq.
Proof.
  setoid_rewrite (unfold_Stream seq) at 2.
  now cbn.
Qed.

Definition n_to_ne_seq (n:nat) : ne_list nat.
Proof.
  apply (to_ne_list (n_to_seq (S n))).
  pose proof (n_to_seq_spec (S n)) as [_ H].
  1: {
    induction n.
    - do 2 constructor.
    - constructor;apply IHn.
  }
  exact H.
Defined.

Lemma seq_eq_k n k:
  k < 15 ->
  (S n) mod 15 = k ->
  EqSt (concat_list n_to_ne_seq (S n)) (prependListStream (drop (offset (S k) mod length period) period) seq) ->
  EqSt (concat_list n_to_ne_seq n) (prependListStream (drop (offset k mod length period) period) seq).
Proof.
  intros Hk Hr IH.
  rewrite concat_list_unfold_list.
  (* rewrite (unfold_Stream (concat_list _ _)). *)
  cbn [concat_list].
  unfold n_to_seq.
  rewrite Hr.
  cbn [qrseq].
  (* cbn offset period *)
  remember (_ / 15) as q.
  pose proof prependPeriodSeq as HP.
  cbn in HP.
  destruct q.
  - cbn [repeat concat app].

    do 15 try destruct k as [|k].
    all:
    try(
    cbn [offset extra skipn length period];
    vm_compute (_ mod 6);
    cbn [drop period];
    cbn [prependListStream];

    rewrite (unfold_Stream seq);cbn [seq];
    cbn [prependListStream period];
    first [
      rewrite <- unfold_Stream | 
      (cbn [prependListStream period];
      repeat solve_eqst_const)
    ];

    cbn [length period offset] in IH;
    vm_compute (_ mod 6) in IH;
    cbn [period drop offset] in IH;
    repeat rewrite prependPeriodSeq in IH;
    repeat rewrite HP in IH;
    repeat rewrite prependPeriodSeq;
    repeat rewrite HP;
    apply IH
    ).
  - rewrite repeat_rotate.

    do 15 try destruct k as [|k].

    all: 
    cbn [offset extra skipn length period];
    vm_compute (_ mod 6);
    cbn [drop period];
      repeat rewrite prepend_app;
    cbn [prependListStream];

    rewrite (unfold_Stream seq);cbn [seq];
    cbn [prependListStream period];
    first [
      rewrite <- unfold_Stream | 
      (cbn [prependListStream period];
      repeat solve_eqst_const)
    ];


    cbn [length period offset] in IH;
    vm_compute (_ mod 6) in IH;
    cbn [period drop offset] in IH;
    repeat rewrite prependPeriodSeq in IH;
    repeat rewrite HP in IH;
    repeat rewrite prependPeriodSeq;
    repeat rewrite HP;

      apply prependRepeatPeriod;
      cbn [take period];

      rewrite (unfold_Stream seq);cbn [seq];
      rewrite (unfold_Stream seq);cbn [seq];
      cbn [prependListStream period];
      first [
        rewrite <- unfold_Stream | 
        (cbn [prependListStream period];
        repeat solve_eqst_const)
      ];

      repeat rewrite prependPeriodSeq in IH;
      repeat rewrite HP in IH;
      repeat rewrite prependPeriodSeq;
      repeat rewrite HP;
      apply IH.
Defined.


Lemma seq_eq_large_step n:
  S n mod 15 = 1 ->
  EqSt (concat_list n_to_ne_seq (15 + n)) seq ->
  EqSt (concat_list n_to_ne_seq n) seq.
Proof.
  intros Hn CIH.
  assert(15<>0) as H0 by lia.
  pose proof (@local_mod_add (S n) 15 1 H0 Hn) as Hmod.

  pose proof (@seq_eq_k n 1) as Hk.
  rewrite prependPeriodSeq in Hk.
  apply Hk;[lia|auto|].
  clear Hk.

  do 13 (apply seq_eq_k;[lia|shelve|]).
  Unshelve.
  shelve.
  - apply (Hmod 1);lia.
  - apply (Hmod 2);lia.
  - apply (Hmod 3);lia.
  - apply (Hmod 4);lia.
  - apply (Hmod 5);lia.
  - apply (Hmod 6);lia.
  - apply (Hmod 7);lia.
  - apply (Hmod 8);lia.
  - apply (Hmod 9);lia.
  - apply (Hmod 10);lia.
  - apply (Hmod 11);lia.
  - apply (Hmod 12);lia.
  - apply (Hmod 13);lia.
  Unshelve.

  match goal with 
  | [ |- context G[concat_list _ ?N] ] =>
  replace N with (14+n) by reflexivity
  end.
  remember (14+n) as m.
  vm_compute (_ mod _).
  cbn [drop].
  rewrite prependPeriodSeq.
  
  pose proof (@seq_eq_k m 0) as Hk.
  rewrite prependPeriodSeq in Hk.
  apply Hk;[lia| | ].
  1: {
    subst. 
    change (S (14+n)) with (14+S n).
    rewrite (add_mod _ _ _ H0) Hn.
    setoid_rewrite mod_small at 2;[|lia].
    now rewrite (mod_same _ H0).
  }
  clear Hk.
  subst.
  apply CIH.
Defined.

Lemma seq_eq n:
  S n mod 15 = 1 ->
  EqSt (concat_list n_to_ne_seq n) seq.
Proof.
  (* unfold concat_list. *)
  revert n.
  cofix CIH.
  intros n H.
  apply seq_eq_large_step.
  1: apply H.
  apply CIH.
  change (S (15+n)) with (15+(S n)).
  assert(15<>0) as H0 by congruence.
  rewrite (add_mod _ _ _ H0) H.
  now rewrite (mod_same _ H0).
Qed.

Unset Guard Checking.

(* we will apply the cofix to "concat_list _ n+15" 
  so it is okay but Coq does not know it
*)
Lemma seq_eq n:
  S n mod 15 = 1 ->
  EqSt (concat_list n_to_ne_seq n) seq.
Proof.
  revert n.
  cofix CIH.
  intros n Hn.

  assert(15<>0) as H0 by lia.
  pose proof (@local_mod_add (S n) 15 1 H0 Hn) as Hmod.

  pose proof (@seq_eq_k n 1) as Hk.
  rewrite prependPeriodSeq in Hk.
  apply Hk;[lia|auto|].
  clear Hk.

  do 13 (apply seq_eq_k;[lia|shelve|]).
  Unshelve.
  shelve.
  - apply (Hmod 1);lia.
  - apply (Hmod 2);lia.
  - apply (Hmod 3);lia.
  - apply (Hmod 4);lia.
  - apply (Hmod 5);lia.
  - apply (Hmod 6);lia.
  - apply (Hmod 7);lia.
  - apply (Hmod 8);lia.
  - apply (Hmod 9);lia.
  - apply (Hmod 10);lia.
  - apply (Hmod 11);lia.
  - apply (Hmod 12);lia.
  - apply (Hmod 13);lia.
  Unshelve.

  match goal with 
  | [ |- context G[concat_list _ ?N] ] =>
  replace N with (14+n) by reflexivity
  end.
  remember (14+n) as m.
  vm_compute (_ mod _).
  cbn [drop].
  rewrite prependPeriodSeq.
  
  pose proof (@seq_eq_k m 0) as Hk.
  rewrite prependPeriodSeq in Hk.
  apply Hk;[lia| | ].
  1: {
    subst. 
    change (S (14+n)) with (14+S n).
    rewrite (add_mod _ _ _ H0) Hn.
    setoid_rewrite mod_small at 2;[|lia].
    now rewrite (mod_same _ H0).
  }
  clear Hk.

  apply CIH.
  subst.
  change (S(S (14+n))) with (15+S n).
  now rewrite (add_mod _ _ _ H0) (mod_same _ H0) (mod_mod _ _ H0);cbn [add].
Qed.



Set Guard Checking.

Corollary full_seq: EqSt (concat_list n_to_ne_seq 0) seq.
Proof.
  apply seq_eq.
  rewrite mod_small;lia.
Qed.