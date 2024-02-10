(* Polymorphism *)
(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Inductive list (X: Type) : Type :=
    | nil
    | cons (x: X) (l: list X).

Check nil.
Check cons nat 8 (cons nat 8 (nil nat)).

Fixpoint repeat (X: Type) (x : X) (count: nat) : list X :=
    match count with
    | 0 => nil X
    | S count' => cons X x (repeat X x count')
    end.

Check S(3).

Compute repeat nat 3 0.

Example test_repeat1:
    repeat bool true 2 = cons bool true (cons bool true (nil bool)).
Proof. simpl. reflexivity. Qed.

Module MumbleGrumble.

Inductive mumble : Type :=
    | a
    | b (x : mumble) (y: nat)
    | c.

Inductive grumble (X: Type) : Type :=
    | d (m: mumble)
    | e (x : X).

(* Check d (b a 5). *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)
Check c.

End MumbleGrumble.

(* Type Inference *)
Fixpoint repeat' X x count : list X :=
    match count with
    | O => nil X
    | S count' => cons X x (repeat' X x count')
    end.

(* Implicit Arguments *)
Arguments nil {X}.
Arguments cons {X}.
(* Arguments repeat' {X}. *)

Definition list123 := 
    cons 0 (cons 2 nil).

Check list123.

Fixpoint repeat'' {X: Type} (x: X) (count: nat) : list X :=
    match count with
    | O => nil
    | S count' => cons x (repeat'' x count')
    end.

Fixpoint app {X: Type} (l1 l2 : list X) : list X :=
    match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
    end.

Compute app (cons 1 (cons 2 nil)) 
            (cons 3 (cons 4 nil)).

Fixpoint rev {X: Type} (xs : list X) : list X :=
    match xs with
    | nil => nil
    | cons h t =>  app (rev t) (cons h nil) 
    end.

Compute rev (cons 1 (cons 2 (cons 3 nil))).


Fixpoint lengt {X: Type} (xs : list X) : nat :=
    match xs with
    | nil => O
    | cons _ t => S (lengt t)
    end.

Compute lengt (cons 1 (cons 2 (cons 3 nil))).

Example test_rev1:
      rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. simpl. reflexivity. Qed.

Example test_lengt1:
    lengt (cons true (cons false (cons true nil))) = 3.
Proof. simpl. reflexivity. Qed.

Fail Definition mynil := nil.
Definition mynil: list nat := nil.

(* we can force the implicit arguments to be explicit by prefixing the function name with @. *)
Check @nil : forall X: Type, list X.

Definition mynil' := @nil nat.
Check mynil'.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

