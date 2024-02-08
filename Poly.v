(* Polymorphism *)
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
