
Definition le (x y : nat) : Prop :=
  exists k, x + k = y.

Notation "x <= y" := (le x y).
Notation "x < y" := (le (S x) y).

Definition dec (X : Prop) :=
  {X} + {~ X}.

Lemma origin x :
  0 <= x.
Proof.
  exists x. reflexivity.
Qed.

Lemma refl x :
  x <= x.
Proof.
  exists 0. lia.
Qed.

Lemma trans x y z :
  x <= y -> y <= z -> x <= z.
Proof.
  intros [k <-] [l <-].
  exists (k + l). lia.
Qed.

Lemma antisym x y :
  x <= y -> y <= x -> x = y.
Proof.
  intros [k Hk] [l Hl]. lia.
Qed.

Lemma shift x y :
  S x <= S y <-> x <= y.
Proof.
  split; intros [k Hk].
  - exists k. lia.
  - exists k. lia.
Qed.

Lemma strict x :
  ~ x < x.
Proof.
  intros [k Hk]. lia.
Qed.

Lemma minimum x :
  ~ x < 0.
Proof.
  intros [k Hk]. lia.
Qed.



(*** Exercise 9.2 ***)

Lemma add_sub_eq x y :
  x + y - x = y.
Proof.
  induction x as [|x IH]; cbn.
  - destruct y; reflexivity.
  - exact IH.
Qed.

Lemma le_add_sub x y :
  x <= y -> x + (y - x) = y.
Proof.
  intros [k <-]. rewrite add_sub_eq. reflexivity.
Qed.



(*** Exercise 9.3 ***)

Lemma linearity :
  forall n m, n <= m \/ m <= n.
Proof.
 induction n; destruct m.
 - left. exists 0. reflexivity.
 - left. exists (S m). reflexivity.
 - right. exists (S n). reflexivity.
 - destruct (IHn m) as [[k H]|[k H]].
   + left. exists k. lia.
   + right. exists k. lia.
Qed.

Lemma trichotomy : 
  forall n m, n < m \/ n = m \/ m < n.
Proof.
 induction n; destruct m.
 - right. left. reflexivity.
 - left. exists m. reflexivity.
 - right. right. exists n. reflexivity.
 - destruct (IHn m) as [[k H]|[H|[k H]]].
   + left. exists k. lia.
   + right. left. congruence.
   + right. right. exists k. lia.
Qed.

(* The stronger statements using + have (almost) the same proof scripts
   and of course imply the weaker statements using ∨. *)
  
Lemma linearity_sum :
  forall n m, {n <= m} + {m <= n}.
Proof.
 induction n; destruct m.
 - left. exists 0. reflexivity.
 - left. exists (S m). reflexivity.
 - right. exists (S n). reflexivity.
 - destruct (IHn m) as [H|H].
   + left. destruct H as [k H]. exists k. lia.
   + right. destruct H as [k H]. exists k. lia.
Qed.

Lemma trichotomy_sum :
  forall n m, {n < m} + {n = m} + {m < n}.
Proof.
 induction n; destruct m.
 - left. right. reflexivity.
 - left. left. exists m. reflexivity.
 - right. exists n. reflexivity.
 - destruct (IHn m) as [[H|H]|H].
   + left. left. destruct H as [k H]. exists k. lia.
   + left. right. congruence.
   + right. destruct H as [k H]. exists k. lia.
Qed.

Lemma not_lt_le x y :
  ~ (y < x) -> x <= y.
Proof.
  intros HX. destruct (trichotomy x y) as [H|[H|H]]; trivial.
  - destruct H as [k <-]. exists (S k). lia.
  - subst. apply refl.
  - contradiction.
Qed.

Lemma not_lt_eq x y :
  ~ (x < y) -> ~ (y < x) -> x = y.
Proof.
  intros H1 H2. apply antisym; now apply not_lt_le.
Qed.



(*** Exercise 9.4 ***)

Lemma le_iff x y :
  x <= y <-> x - y = 0.
Proof.
  split.
  - intros [k <-]. lia.
  - intros H. exists (y - x). lia.
Qed.

Lemma le_dec x y :
  dec (x <= y).
Proof.
  destruct (x - y) eqn : H.
  - left. now apply le_iff.
  - right. intros H' % le_iff.
    congruence.
Qed.

Lemma le_dec' x y :
  dec (x <= y).
Proof.
  revert y. induction x; intros [].
  - left. apply origin.
  - left. apply origin.
  - right. apply minimum.
  - destruct (IHx n) as [H|H].
    + left. now apply shift.
    + right. intros H'. now apply H, shift.
Qed.

Fixpoint le_bool (x y : nat) : bool :=
  match x, y with 
  | 0, y => true
  | S x, 0 => false
  | S x, S y => le_bool x y
  end.

Lemma le_bool_spec x y :
  x <= y <-> le_bool x y = true.
Proof.
  revert y. induction x; intros []; cbn.
  - split; trivial. intros _. apply refl.
  - split; trivial. intros _. apply origin.
  - split; try congruence. now intros H % minimum.
  - (* propositional equivalences can be used for rewriting: *)
    rewrite shift. apply IHx.
Qed.



(*** Exercise 9.5 ***)

Lemma nat_dec (x y : nat) :
  dec (x = y).
Proof.
  destruct (trichotomy_sum x y) as [[H|H]|H].
  - right. intros ->. now apply strict in H.
  - now left.
  - right. intros ->. now apply strict in H.
Qed.

End LE.


Lemma le_lt_dec x y :
  {x <= y} + {y < x}.
Proof.
  induction x as [|x IH] in y |-*.
  - left. lia.
  - destruct y as [|y].
    + right. lia.
    + specialize (IH y) as [IH|IH].
      * left. lia.
      * right. lia.
Qed.



(*** Exercise 9.8 ***)

Definition divides x y :=
  x <> 0 /\ exists k, y = k * x.

Lemma divides_dec x y :
  dec (divides x y).
Proof.
 destruct x.
 - right. intros [H _]. now apply H.
 - destruct (M y x) eqn : H.
   + left. split; try congruence. exists (D y x).
     rewrite (DM_spec1 y x) at 1. lia.
   + right. intros [_ [k H']].
     destruct (div_mod_unique x (D y x) (M y x) k 0).
     * apply DM_spec2.
     * lia.
     * rewrite <- (DM_spec1 y x). lia.
     * congruence.
Qed.

Definition cong x y k :=
  (x <= y /\ divides k (y - x)) \/ (y < x /\ divides k (x - y)).

Lemma cong_dec x y k :
  dec (cong x y k).
Proof.
  destruct (le_lt_dec x y) as [H|H].
  - destruct (divides_dec k (y - x)) as [H'|H'].
    + left. left. now split.
    + right. intros [[H1 H2]|[H1 H2]]; auto. lia.
  - destruct (divides_dec k (x - y)) as [H'|H'].
    + left. right. now split.
    + right. intros [[H1 H2]|[H1 H2]]; auto. lia.
Qed.



(*** Exercise 9.10 ***)

Definition spec_exp mu :=
  forall f n, (f (mu f n) = true -> mu f n <= n /\ forall k, k < mu f n -> f k = false)
         /\ (f (mu f n) = false -> mu f n = n /\ forall k, k <= n -> f k = false).

Definition wf X (R : X -> X -> Prop) :=
  forall f, (exists x, f x = true) -> exists x, f x = true /\ forall y, f y = true -> R x y.

Lemma nat_wf mu :
  spec_exp mu -> wf nat (fun x y => x <= y).
Proof.
  intros HM f [n Hn]. exists (mu f n). destruct (f (mu f n)) eqn : H.
  - split; trivial. intros n' Hn'. apply HM in H.
    destruct (le_lt_dec (mu f n) n'); trivial.
    apply H in l. congruence.
  - exfalso. apply HM in H as [_ H].
    assert (H' : n <= n) by lia.
    specialize (H n H'). congruence.
Qed.



(*** Exercise 9.11 ***)

Section S1.
  Variables (f: nat -> bool)
            (mu: nat -> nat)
            (R1: mu 0 = 0)
            (R2: forall n, mu (S n) = if f (mu n) then mu n else S n).

  Goal forall n, if f (mu n)
            then mu n <= n /\ forall k, k < mu n -> f k = false
            else mu n = n /\ forall k, k <= n -> f k = false.
  Proof.
    induction n as [|n IH].
    - rewrite R1. destruct (f 0) eqn:H1.
      + intuition. lia.
      + intuition. assert (k=0) as -> by lia. exact H1.
    - rewrite R2. destruct (f (mu n)) eqn:H1.
      + rewrite H1. intuition.
      + destruct (f (S n)) eqn:H2.
        * intuition.
        * intuition.
          assert (k = S n \/ k <= n) as [->|H4] by lia; auto.
  Qed.
  
  Variables (mu': nat -> nat)
            (R1': mu' 0 = 0)
            (R2': forall n, mu' (S n) = if f (mu' n) then mu' n else S n).

  Goal forall n, mu n = mu' n.
  Proof.
    induction n as [|n IH].
    - congruence.
    - rewrite R2, R2'. rewrite <-IH. reflexivity.
  Qed.
End S1.

Section S2.
  Variables (f: nat -> bool) (mu: nat -> nat).
  Variable (R: forall n, if f (mu n)
                    then mu n <= n /\ forall k, k < mu n -> f k = false
                    else mu n = n /\ forall k, k <= n -> f k = false ).
  
  Goal forall n, mu n <= n.
  Proof.
    intros *. generalize (R n). destruct (f (mu n)) eqn:H1; lia.
  Qed.

  Goal forall n k, k < mu n -> f k = false.
  Proof.
    intros *. generalize (R n).
    destruct (f (mu n)) eqn:H1; intuition.
  Qed.

  Goal forall n, mu n < n -> f (mu n) = true.
  Proof.
     intros *. generalize (R n).
     destruct (f (mu n)) eqn:H1; intuition.
  Qed.
End S2.

Section S3.
  Variables (f: nat -> bool) (mu: nat -> nat).
  Variables (R1: forall n, mu n <= n)
            (R2: forall n k, k < mu n -> f k = false)
            (R3: forall n, mu n < n -> f (mu n) = true).

  Lemma L1 n :
    ~ mu n < n -> mu n = n.
  Proof.
    specialize (R1 n). lia.
  Qed.

  Goal mu 0 = 0.
  Proof.
    generalize (R1 0). lia.
  Qed.

  Lemma not_lt_eq' x y :
    ~ x < y -> ~ y < x -> x = y.
  Proof.
    intros H1 H2. lia.
  Qed.

  Goal forall n, mu (S n) = if f (mu n) then mu n else S n.
  Proof.
    intros n. destruct (f (mu n)) eqn:H1.
    - apply not_lt_eq'; intros H2.
      + assert (H3: f (mu (S n)) = false) by eapply R2, H2.
        enough (f (mu (S n)) = true) by congruence.
        apply R3. specialize (R1 n). lia.
      + apply R2 in H2. congruence.
    - assert (H2: mu n = n).
      { apply L1. intros H2%R3. congruence. }
      apply L1. intros H3.
      assert (H4: f (mu (S n)) = true) by apply R3, H3.        
      assert (mu (S n) = n \/ mu (S n) < mu n) as [H5|H5] by lia.    
      + congruence.
      + apply R2 in H5. congruence.
  Qed.
End S3.



(*** Exercise 9.12 ***)

Section Challenge.

  Variable D M : nat -> nat -> nat.
  Hypothesis DM1 : forall x y, x = D x y * S y + M x y.
  Hypothesis DM2 : forall x y, M x y <= y.

  Goal forall x y, y < x -> D x y = S (D (x - S y) y).
  Proof.
    intros x y H. apply (div_mod_unique y (D x y) (M x y) (S (D (x - S y) y)) (M (x - S y) y)).
    - apply DM2.
    - apply DM2.
    - generalize (DM1 x y) (DM1 (x - S y) y). lia.
  Qed.

  Goal forall x y, x <= y -> D x y = 0.
  Proof.
    intros x y H. apply (div_mod_unique y (D x y) (M x y) 0 x).
    - apply DM2.
    - apply H.
    - cbn. symmetry. apply DM1.
  Qed.

End Challenge.
  
  







(*** Exercise 9.6 ***)

(* We now switch to the pre-defined x <= y and fully rely on lia. *)

Lemma size_induction X (f : X -> nat) (p : X -> Type) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof.
  intros H x. apply H.
  enough (G : forall n y, f y < n -> p y) by apply G.
  intros n. induction n; intros y Hy.
  - exfalso. lia.
  - apply H. intros z HZ. apply IHn. lia.
Qed.

Lemma complete_induction (p : nat -> Type) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  apply (size_induction nat (fun n => n)).
Qed.



(*** Exercise 9.7 ***)

Lemma div_mod_unique y a b a' b' :
  b <= y -> b' <= y -> a * S y + b = a' * S y + b' -> a = a' /\ b = b'.
Proof.
  intros H1 H2.
  (* the pattern "in a' |-*" generalises a' in the induction *)
  induction a as [|a IH] in a' |-*; destruct a'; cbn.
  - tauto.
  - intros ->. exfalso. lia.
  - intros <-. exfalso. lia.
  - (* the = in the intro pattern applies injectivity *)
    intros [= H3]. destruct (IH a') as [-> ->]; lia.
Qed.

Theorem div_mod x y :
  { a & { b & x = a * S y + b /\ b <= y}}.
Proof.
  induction x as [x IH] using complete_induction.
  destruct (le_lt_dec x y) as [H|H].
  - exists 0, x. split; trivial.
  - destruct (IH (x - S y)) as (a&b&H2&H3).
    + lia.
    + exists (S a), b. lia.
Qed.

Definition D (x y : nat) := projT1 (div_mod x y).
Definition M (x y : nat) := projT1 (projT2 (div_mod x y)).

Lemma DM_spec1 x y :
  x = D x y * S y + M x y.
Proof.
  apply (projT2 (projT2 (div_mod x y))).
Qed.

Lemma DM_spec2 x y :
  M x y <= y.
Proof.
  apply (projT2 (projT2 (div_mod x y))).
Qed.

