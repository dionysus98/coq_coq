(* Lists *)

From FOUNDATIONS Require Export Induction.

(* Pairs of Numbers *)

Inductive natprod : Type :=
    | pair (n1 n1 : nat).

(* Check (pair 3 5) : natprod. *)

Definition fst (p: natprod) : nat :=
    match p with
    | pair x _ => x
    end.

Definition snd (p: natprod) : nat :=
    match p with
    | pair _ y => y
    end.

(* Compute fst (pair 3 5). *)

(* Nice Notation for pairs *)
Notation "( x , y )" := (pair x y).

(* Compute fst (3,5). *)

Definition fst' (p: natprod) : nat :=
    match p with
    | (x, _) => x
    end.

Definition snd' (p: natprod) : nat :=
    match p with
    |  (_, y) => y
    end.

Definition swap_pair (p: natprod) : natprod :=
    match p with
    |  (x, y) => (y, x)
    end.

Theorem surjective_pairing': 
    forall (n m : nat),
        (n, m) = (fst (n, m), snd (n, m)).
Proof. reflexivity. Qed.

Theorem surjective_pairing_abort: 
    forall (p : natprod),
        p = (fst p, snd p).
Proof. simpl. Abort.

Theorem surjective_pairing: 
    forall (p : natprod),
        p = (fst p, snd p).
Proof.
    intros [n m].  (* Destruct P as [n m] *)
    reflexivity.
    Qed.

(* LISTs of Numbers *)

Inductive natlist: Type :=
    | nil
    | cons (n :nat) (l : natlist).

(* (1, (2, (3, (4, nil)))) *)

Definition mine := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                        (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mine1 :=  1 :: ( 2 :: ( 3 :: nil)).
Definition mine2 :=  1 ::  2 ::  3 :: nil.
Definition mine3 :=  [1; 2; 3].