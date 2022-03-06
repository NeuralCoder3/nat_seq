# Number Sequence

We show that 1 2 3 4 3 2 1 2 3 4 3 2 1 ... can be split up into groups 
such that the sum of each group is the natural numbers in consecutive order.

The sequence is the numbers from one to four and back to one and so on.
Formally, it is [1;2;3;4;3;2] repeating.
In Haskell `let seq = 1:2:3:4:3:2:seq`.

One can observe:
* 1 = 1
* 2 = 2
* 3 = 3
* 4 = 4
* 5 = 3+2
* ...

The idea is that each number is put in a category according to its congruence group modulo 15 as 15 is the sum of the period.
Then the quotient `n/15` is how many periods are in the list of the number
and `n mod 15` is the rest before/after the period.

Formally, we will use an offset of the period and some rest which dictates the offset for the next number.

Every fifteen consecutive numbers form a full class of every modulo class.
These rest groups together form again full repetitions of the period.
To be precise, one has to not only should the correct number be there in the correct quantities but also in the correct order.

The formalization is done using streams which are a coinductive type representing infinite lists.

The important lemmas are:

```
Definition period := [1;2;3;4;3;2].
CoFixpoint seq := prependListStream period seq.

(* the group sums up to the number *)
Definition n_to_seq_spec (n:nat) : 
    n>0 ->
    let xs := n_to_seq n in
    sum xs = n /\ xs <> nil.

Lemma seq_eq n:
    n mod 15 = 1 ->
    EqSt (concat_list n_to_seq n) seq.
```

One has to strengthen `seq_eq` to `seq_eq_k`:
``` 
Lemma seq_eq_k n k:
    k < 15 ->
    n mod 15 = k ->
    EqSt (concat_list n_to_seq (S n)) (prependListStream (drop (offset (S k) mod length period) period) seq) ->
    EqSt (concat_list n_to_seq n) (prependListStream (drop (offset k mod length period) period) seq).
```

The main statement follows as a corollary:
```
(* all number groups from one onwards form the sequence *)
Corollary full_seq: EqSt (concat_list n_to_seq 1) seq.
```

