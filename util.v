Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Require Import Arith.
Require Import List.
Import Nat.
Import ListNotations.

Require Import Lists.Streams.





(** Definitions **)

Definition sum := fold_right add 0.

Notation take := firstn.
Notation drop := skipn.
Definition rotate {A} (n : nat) (l : list A) : list A :=
  drop (n mod length l) l ++ take (n mod length l) l.







(** Proof **)

Lemma sum_app xs ys:
  sum (xs ++ ys) = sum xs + sum ys.
Proof.
  induction xs;cbn;trivial.
  rewrite IHxs;lia.
Qed.

Lemma repeat_rotate {X} (xs:list X) n m:
  concat (repeat (rotate m xs) (S n)) =
  (drop (m mod length xs) xs) ++ concat(repeat xs n) ++ (take (m mod length xs) xs).
Proof.
  induction n in m,xs |- *.
  - cbn. rewrite app_nil_r.
    reflexivity.
  - remember (S n) as n0.
    cbn.
    rewrite IHn.
    unfold rotate.
    rewrite <- app_assoc.
    f_equal.
    rewrite app_assoc.
    rewrite firstn_skipn.
    subst n0.
    cbn.
    now rewrite <- app_assoc.
Qed.






(** common functions custom properties **)

Lemma app_not_nil_r {X} (xs:list X) ys:
  ys <> [] -> xs++ys <> [].
Proof.
  destruct xs.
  - trivial.
  - intros _. cbn. congruence.
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