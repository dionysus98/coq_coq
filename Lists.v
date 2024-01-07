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

(* list functions *)

Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

(* Compute repeat 42 3. *)

Fixpoint length (xs: natlist) : nat :=
    match xs with
    | [] => O
    | _ :: t => S (length t)
    end.

(* Compute S (S (S O)). *)
(* Compute length [2;2;2;2]. *)

Fixpoint concat (xs ys: natlist) : natlist :=
    match xs with
    | [] => ys
    | h :: t => h :: (concat t ys)
    end.

(* Compute concat [3;2;1] [4;5;6]. *)

Notation "x ++ y" := 
    (concat x y)
    (right associativity, at level 60).

(* Compute [1;4;8] ++ [9;5]. *)

Example test_1:
     [1; 4; 8] ++ [9; 5] = [1; 4; 8; 9; 5].
Proof. simpl. reflexivity. Qed.

Definition hd' (default: nat) (l: natlist) : nat :=
    match l with
    | [] => default
    | h :: _ => h
    end.

Definition hd (l: natlist) : option nat  :=
    match l with
    | [] => None
    | h :: _ => Some(h)
    end.
