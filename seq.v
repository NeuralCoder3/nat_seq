
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


Definition qrseq (q:nat) (r:nat) (Hr:r<15) : (list nat) * (list nat).
    revert Hr.
    pose (offset_period n :=
        concat(repeat (rotate n period) q)
    ).
    refine(
        match r with
        |  0 => fun _ => (offset_period  0,          [])
        |  1 => fun _ => (offset_period  0,         [1])
        |  2 => fun _ => (offset_period  1,         [2])
        |  3 => fun _ => (offset_period  2,         [3])
        |  4 => fun _ => (offset_period  3,         [4])
        |  5 => fun _ => (offset_period  4,       [3;2])
        |  6 => fun _ => (offset_period  6,     [1;2;3])
        |  7 => fun _ => (offset_period  9,       [4;3])
        |  8 => fun _ => (offset_period 11,   [2;1;2;3])
        |  9 => fun _ => (offset_period 15,     [4;3;2])
        | 10 => fun _ => (offset_period 18,   [1;2;3;4])
        | 11 => fun _ => (offset_period 22, [3;2;1;2;3])
        | 12 => fun _ => (offset_period 27, [4;3;2;1;2])
        | 13 => fun _ => (offset_period 32, [3;4;3;2;1])
        | 14 => fun _ => (offset_period 37, [2;3;4;3;2])
        | _ => _
    end).
    lia.
Defined.

Lemma rotate_sum n xs:
    sum (rotate n xs) = sum xs.
Proof.
    induction n in xs |- *;destruct xs;trivial.
    rewrite IHn sum_app;cbn;lia.
Qed.

(* Lemma qrseq_spec q r (Hr:r<15) ps rs:
    @qrseq q r Hr = (ps,rs) -> *)
Lemma qrseq_spec q r (Hr:r<15):
    let (ps,rs) := @qrseq q r Hr in
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

Definition n_to_seq (n:nat) : 
    n>0 ->
    {xs : list nat | sum xs = n /\ xs <> nil }.
Proof.
    intros H0.
    assert(15 <> 0) as H15 by lia.
    pose proof(Nat.div_mod n 15 H15) as Hn.
    pose proof(Nat.mod_upper_bound n 15 H15) as Hr.
    remember (n/15) as q.
    remember (n mod 15) as r.
    pose proof(@qrseq_spec q r Hr) as H.
    destruct (@qrseq q r Hr) as [qseq rseq] eqn: Hseq.
    destruct H as [Hqseq Hrseq].
    exists (qseq ++ rseq).
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

Definition n_to_stream (n:nat) : list nat.
    remember n as m eqn:H.
    revert H.
    refine(match n with
    | 0 => fun _ => []
    | S k => fun H => _
    end).
    assert(m>0) as H0 by lia.
    exact(proj1_sig (@n_to_seq m H0)).
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

Lemma seq_eq n:
    n mod 15 = 1 ->
    EqSt (concat_list n_to_stream n) seq.
Proof.
    revert n.
    cofix CIH.
    intros n Hn.

    rewrite (unfold_Stream (concat_list _ _)).
    cbn.
    unfold n_to_stream.

Qed.

Goal EqSt (concat_list n_to_stream 1) seq.
Proof.
(* rewrite (unfold_Stream seq). *)
(* do 15 rewrite (unfold_Stream (concat_list _ _)). *)
rewrite (unfold_Stream (concat_list _ _)).