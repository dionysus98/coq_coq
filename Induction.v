(*? Induction: Proof by Induction *)

(* Separate Compilation * 
    # with MakeFile
    $ coq_makefile -f _CoqProject -o Makefile *.v

    # without MakeFile
    $ coqc -Q . FOUNDATIONS Basix.v
 *)

From FOUNDATIONS Require Export Basix.

Example add_0_1:
    forall n: nat,
        0 + n = n.
Proof. reflexivity. Qed.

Theorem add_0_r_first:
    forall n: nat,
        n + 0  = n.
Proof. 
    intros n. simpl. 
    (* reflexivity.  *)
    Abort.

Theorem add_0_r_sec:
    forall n: nat,
        n + 0  = n.
Proof. 
    intros [ | n'].
    - reflexivity.
    - simpl.
    Abort.

(*? Induction 
    - Let's say that [P(n)] is some proposition involving a natural number [n].
    - we want to show that [P] holds for _all_ numbers
        + [P(O)] holds
        + [P(n')] holds, then also [P(S n')]
        + Hence [P(n)]  holds for all [n].
*)

Theorem add_0_r:
    forall n: nat,
        n + 0  = n.
Proof.    
    intros n.
    induction n as [ | n' IHn'].
    - reflexivity.
    - simpl.
    rewrite -> IHn'.
    reflexivity.
    Qed.

Theorem minus_n_n:
    forall n,
        n - n = 0.
Proof.
    intros n.
    induction n as [ | k].
    - reflexivity.
    - simpl.
    rewrite -> IHk.
    reflexivity.
    Qed.

Theorem plus_a_Sb: 
    forall a b:nat,
        S (a + b) = a + S b.
Proof. 
    intros a b.
    induction a as [ | a'].
    - reflexivity.
    - simpl. rewrite IHa'. reflexivity.
    Qed.

Theorem add_comm:
    forall n m: nat,
        n + m = m + n.
Proof.
    intros n m.
    induction n as [ | n'].
    - simpl. rewrite add_0_r. reflexivity.    
    - simpl. rewrite IHn'. rewrite plus_a_Sb. reflexivity.
    Qed.

(* Proofs within Proofs  
    - Use the [assert] tactic.
 *)

Theorem mult_0_plus':
    forall n m: nat,
        (n + 0 + 0) * m = n * m.
Proof.
    intros n m.
    assert (H: n + 0 + 0 = n).
    - rewrite add_comm. simpl. rewrite add_comm. reflexivity.
    - rewrite H. reflexivity.
    Qed.

Theorem plus_rearrange_firsttry:
    forall n m p q: nat,
        (n + m) + (p + q) = (m + n) + (q + p).
Proof.
    intros n m p q.
    Set Printing Parentheses.
    rewrite add_comm.
    Abort.

Theorem plus_rearrange_firsttry:
    forall n m p q: nat,
        (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (H: n + m = m + n).
    - rewrite add_comm. reflexivity.
    - rewrite H. reflexivity.
    Qed.

(*? Formal vs. Informal proof  
    - Formal proofs are code.
    - Informal proof are algorithms
*)

Theorem add_assoc':
    forall n m p: nat,
        n + (m + p) = (n + m) + p.
Proof.
    intros n m p.
    induction n as [ | n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
    Qed.