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