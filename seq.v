
Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Require Import Arith.
Require Import List.
Import Nat.
Import ListNotations.

Require Import Lists.Streams.

Set Implicit Arguments.


Fixpoint prependListStream {A} (xs:list A) ys :=
    match xs with
    | [] => ys
    | x::xr => Cons x (prependListStream xr ys)
    end.

Unset Guard Checking.

(* in theory non_empty lists are needed 
but it does not work either way, so lets go with lists
*)
CoFixpoint concat_list {A} (f:nat -> list A) n :=
    (prependListStream (f n) (concat_list f (S n))).

Set Guard Checking.

CoFixpoint seq := 
  Cons 1 (Cons 2 (Cons 3 (Cons 4 (Cons 3 (Cons 2 seq))))).

Definition period := [1;2;3;4;3;2].

CoFixpoint seq2 :=
    prependListStream period seq2.

Goal EqSt seq seq2.
Proof.
    cofix CIH.
    do 6 constructor;trivial.
Qed.

Definition sum := fold_right add 0.

Lemma sum_app xs ys:
    sum (xs ++ ys) = sum xs + sum ys.
Proof.
    induction xs;cbn;trivial.
    rewrite IHxs;lia.
Qed.

Lemma repeat_sum xs n :
    sum (concat (repeat xs n)) = n * sum xs.
Proof.
    induction n;cbn.
    - reflexivity.
    - now rewrite sum_app IHn.
Qed.

Fixpoint rotate {X} n (xs:list X) :=
    match n,xs with
    | _,[] => xs
    | 0,_ => xs
    | S m,x::xr => rotate m (xr++[x])
    end.


Definition qrseq (q:nat) (r:nat) : (list nat) * (list nat) :=
    let offset_period n :=
        concat(repeat (rotate n period) q) in
        match r with
        |  0 => (offset_period  0,          [])
        |  1 => (offset_period  0,         [1])
        |  2 => (offset_period  1,         [2])
        |  3 => (offset_period  2,         [3])
        |  4 => (offset_period  3,         [4])
        |  5 => (offset_period  4,       [3;2])
        |  6 => (offset_period  6,     [1;2;3])
        |  7 => (offset_period  9,       [4;3])
        |  8 => (offset_period 11,   [2;1;2;3])
        |  9 => (offset_period 15,     [4;3;2])
        | 10 => (offset_period 18,   [1;2;3;4])
        | 11 => (offset_period 22, [3;2;1;2;3])
        | 12 => (offset_period 27, [4;3;2;1;2])
        | 13 => (offset_period 32, [3;4;3;2;1])
        | 14 => (offset_period 37, [2;3;4;3;2])
        | _ => ([],[])
    end.

Lemma rotate_sum n xs:
    sum (rotate n xs) = sum xs.
Proof.
    induction n in xs |- *;destruct xs;trivial.
    rewrite IHn sum_app;cbn;lia.
Qed.

(* Lemma qrseq_spec q r (Hr:r<15) ps rs:
    @qrseq q r Hr = (ps,rs) -> *)
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

Lemma app_not_nil_r {X} (xs:list X) ys:
    ys <> [] -> xs++ys <> [].
Proof.
    destruct xs.
    - trivial.
    - intros _. cbn. congruence.
Qed.

Definition n_to_seq (n:nat) :=
    let (qseq,rseq) := qrseq (n/15) (n mod 15) in
    qseq ++ rseq.

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

Notation take := firstn.
Notation drop := skipn.
Definition rotate2 {A} (n : nat) (l : list A) : list A :=
  drop (n mod length l) l ++ take (n mod length l) l.

(* Goal forall
X n (xs ys : list X),
drop (n mod (length ys+length xs)) (ys ++ xs) ++ 
take (n mod (length ys+length xs)) (ys ++ xs) =
drop ((length xs+n) mod (length xs+length ys)) (xs ++ ys) ++ 
take ((length xs+n) mod (length xs+length ys)) (xs ++ ys).
Proof.
    intros.
    induction xs.
    - cbn [length add app]. rewrite add_0_r app_nil_r.
      reflexivity.
    - cbn [length add app].  *)

Lemma full_rotate {X} (xs:list X) :
    rotate (length xs) xs = xs.
Proof.
    induction xs;cbn.
    - reflexivity.
    -
Admitted.

Lemma rotate_mod {X} n (xs:list X):
    rotate n xs = rotate (n mod length xs) xs.
Proof.
    destruct xs.
    - now destruct n;cbn.
    - remember (x::xs) as ys.
      assert(length ys <> 0) as H0 by (subst;cbn;lia).
      pose proof (div_mod n (length ys) H0).
      remember (n/length ys) as q.
      induction q.
      + f_equal. lia.
      + 
Admitted.

Lemma rotate_alt {X} n (xs:list X):
    rotate n xs = rotate2 n xs.
Proof.
    induction n in xs |- *;cbn.
    - destruct xs;cbn;trivial.
      rewrite sub_diag. cbn.
      now rewrite app_nil_r.
    - destruct xs;trivial.  
      rewrite IHn.
      unfold rotate2.
      rewrite app_length.
      cbn [length].
      rewrite add_1_r.
      f_equal.
      + admit.
      + admit.
Restart.
    unfold rotate2.
    rewrite rotate_mod.
    (* remember (n mod length xs). *)
Admitted.

Lemma repeat_rotate {X} (xs:list X) n m:
    concat (repeat (rotate m xs) (S n)) =
    (drop (m mod length xs) xs) ++ concat(repeat xs n) ++ (take (m mod length xs) xs).
Proof.
    induction n in m,xs |- *.
    - cbn. rewrite app_nil_r rotate_alt.
      reflexivity.
    -   
        remember (S n) as n0.
        cbn.
        rewrite IHn.
        rewrite rotate_alt.
        unfold rotate2.
        rewrite <- app_assoc.
        f_equal.
        rewrite app_assoc.
        rewrite firstn_skipn.
        subst n0.
        cbn.
        now rewrite <- app_assoc.
Qed.

Lemma rotate_0 {X} (xs:list X):
    rotate 0 xs = xs.
Proof.
    now destruct xs;cbn.
Qed.

Lemma prepend_app {X} (xs ys:list X) s:
    prependListStream (xs++ys) s =
    prependListStream (xs) (prependListStream ys s).
Proof.
    induction xs;cbn.
    - reflexivity.
    - now rewrite IHxs.
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


Lemma local_mod_add n m c:
    m <> 0 ->
    n mod m = c ->
    forall k,
    k+c<m ->
    (k+n) mod m = (k+c).
Proof.
    intros.
    rewrite add_mod;[assumption|].
    rewrite H0.
    setoid_rewrite mod_small at 2. 2: lia.
    rewrite mod_small. 2: lia.
    assumption.
Qed.



(* Lemma seq_eq n:
    n mod 15 = 2 ->
    EqSt (concat_list n_to_seq n) (Cons 2 (Cons 3 (Cons 4 (Cons 3 (Cons 2 seq))))).
Proof.
    rewrite (unfold_Stream (concat_list _ _)).
    intros Hr.
    (* assert((S n) mod 15 = 2) as Hr by (apply (Hmod 1);lia). *)
    cbn [concat_list].
    unfold n_to_seq.
    rewrite Hr.
    cbn [qrseq].
    remember (_ / 15) as q.
    destruct q.
    - cbn [repeat concat app].

      cbn [prependListStream].
      constructor;[auto|cbn [tl]].
      admit.
    - rewrite repeat_rotate.
      (* Locate "_ mod _". *)
      replace (1 mod length period) with (1) by auto.
      cbn [drop length period take].
      do 3 rewrite prepend_app.
      cbn [prependListStream].
      do 5 (constructor;[reflexivity|]);cbn [tl].
      apply prependRepeatPeriod.
      rewrite (unfold_Stream seq).
      cbn [seq].
      do 2 (constructor;[reflexivity|]);cbn [tl]. *)


Lemma seq_eq n:
    n mod 15 = 1 ->
    EqSt (concat_list n_to_seq n) seq.
Proof.
    revert n.
    cofix CIH.
    intros n Hn.

    assert(15<>0) as H0 by lia.
    pose proof (@local_mod_add n 15 1 H0 Hn) as Hmod.
    clear H0.

    (* 0 *)

    rewrite (unfold_Stream (concat_list _ _)).
    cbn.
    unfold n_to_seq.
    rewrite Hn.
    cbn [qrseq].
    rewrite rotate_0.
    rewrite prepend_app.
    rewrite <- unfold_Stream.
    apply prependRepeatPeriod.

    cbn [prependListStream].
    rewrite (unfold_Stream seq).
    cbn [seq].
    
    constructor;[auto|].
    cbn [tl].
    (* rewrite (unfold_Stream (Cons _ _)). *)


    rewrite (unfold_Stream (concat_list _ _)).
    assert((S n) mod 15 = 2) as Hr by (apply (Hmod 1);lia).
    cbn [concat_list].
    rewrite Hr.
    cbn [qrseq].
    remember (_ / 15) as q.
    destruct q.
    - cbn [repeat concat app].

      cbn [prependListStream].
      constructor;[auto|cbn [tl]].
      admit.
    - rewrite repeat_rotate.
      (* Locate "_ mod _". *)
      replace (1 mod length period) with (1) by auto.
      cbn [drop length period take].
      do 3 rewrite prepend_app.
      cbn [prependListStream].
      do 5 (constructor;[reflexivity|]);cbn [tl].
      apply prependRepeatPeriod.
      rewrite (unfold_Stream seq).
      cbn [seq].
      do 2 (constructor;[reflexivity|]);cbn [tl].
      

Qed.

Goal EqSt (concat_list n_to_stream 1) seq.
Proof.
(* rewrite (unfold_Stream seq). *)
(* do 15 rewrite (unfold_Stream (concat_list _ _)). *)
rewrite (unfold_Stream (concat_list _ _)).