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

Definition list123''' := [1; 2; 3].
Check list123'''.

Theorem app_nil_r:
    forall X (l:list X),
        l ++ [] = l.
Proof.
  intros X l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
  Qed.

Theorem app_assoc: 
    forall A (l m n: list A),
        l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
  Qed.

Lemma app_length:
    forall X (l1 l2 : list X),
        lengt (l1 ++ l2) = lengt l1 + lengt l2.
Proof.
  intros X l1 l2.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite IHl1. simpl. reflexivity.
  Qed.

(* Polymorphic Pairs
   - often called products.*)
Inductive prod (X Y: Type) : Type :=
    | pair (x: X) (y: Y).

(* we make the type arguments implicit and define the familiar concrete notation. *)
Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
(* The annotation : type_scope tells Coq that this abbreviation should only be used when parsing types, not when parsing expressions. This avoids a clash with the multiplication symbol. *)

Definition fst {X Y : Type} (p: X * Y) : X :=
    match p with
    | (X, Y) => X
    end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y: Type} (xs: list X) (ys: list Y) : list (X * Y) :=
    match xs, ys with    
    | _, nil => nil
    | nil, _ => nil
    | cons xh xt, cons yh yt => 
        cons (pair xh yh) (combine xt yt)
    end.

Compute (combine [1;2] [false; true]).
Check combine.
Check @combine.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
    match l with
    | [] => (pair [] [])
    | (pair x y) :: t  => (pair (x :: (fst (split t)))
                                (y :: (snd (split t))))
    end.

Example test_split:
  split [(1, false); (2, false)] = ([1; 2], [false; false]).
Proof. simpl. reflexivity. Qed.

(* Poly Options *)

Module OptPlay.

Inductive option (X: Type) : Type :=
    | Some (x: X)
    | None.

Arguments Some {X}.
Arguments None {X}.

Fixpoint nth_error {X:Type} (xs: list X) (n: nat): option X :=
    match n, xs  with
    | _, []  => None
    | O, x :: _  => Some x
    | S n', _ :: xs' => nth_error xs' n'
    end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. simpl. reflexivity. Qed.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. simpl. reflexivity. Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
Proof. simpl. reflexivity. Qed.

Definition hd_error {X : Type} (xs : list X) : option X :=
    match xs with
    | [] => None
    | x :: _ => Some x
    end.

Check @hd_error : forall X, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. simpl. reflexivity. Qed.

End OptPlay.

(* Functions as Data 
    - functions are first-class citizens *)

Definition doit3times {X : Type} (f: X->X) (n:X) : X :=
    f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times (fun x => x - 2) 9 = 3.
Proof. simpl. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. simpl. reflexivity. Qed.

(* Filter *)
Fixpoint filter {X:Type} (pred: X->bool) (xs:list X) : list X :=
    match xs with
    | nil => nil
    | x :: xs' =>
        match pred x with
        | true => x :: filter pred xs'
        | false => filter pred xs'
        end
    end.

Fixpoint even (x:nat) : bool :=
    match x with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (xfn: X->Y) (xs:list X) : list Y :=
    match xs with
    | nil => nil
    | x :: xs' => xfn x :: map xfn xs'
    end.

Theorem rev_test:
    forall (X : Type) (x: X) (xs : list X),
        rev (x :: xs) = (rev xs) ++ [x].
Proof. 
    intros X x xs. 
    induction xs as [ | h t].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.