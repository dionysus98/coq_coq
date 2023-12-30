(* A datatype definition *)
Inductive day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

(* A function definition *)

Definition next_weekday (d:day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

(* Compute (next_weekday monday). *)
(* Compute (next_weekday (next_weekday monday)). *)

(* Proof: SIMPLIFICATION *)
Example test_next_weekday:
    (next_weekday (next_weekday monday)) = wednesday.

Proof. simpl. 
       reflexivity. (* Basically checks equality? *)
Qed.

(* BOOLEANS *)

Inductive B : Type :=
    | true
    | false.

Definition negb (b:B) : B :=
    match b with
    | true => false
    | false => true
    end.

Definition negb' (b:B) : B :=
    if b then false
    else true.

Definition andb (b1:B) (b2:B) : B :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition andb' (b1:B) (b2:B) : B :=
    if b1 then b2
    else false.

Definition orb (b1 b2 : B) : B :=
    match b1 with
    | true => true
    | false => b2
    end.

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_neg : (negb false) = true.
Proof. simpl. reflexivity. Qed.

Example test_and : (andb true false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_ornotation : false || true || false = true.
Proof. simpl. reflexivity. Qed.

(** **** Exercise: 1 star, standard (nandb)

    The command [Admitted] can be used as a placeholder for an
    incomplete proof.  We use it in exercises to indicate the parts
    that we're leaving for you -- i.e., your job is to replace
    [Admitted]s with real proofs.

    Remove "[Admitted.]" and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (I.e., fill in each proof, following the
    model of the [orb] tests above, and make sure Coq accepts it.) The
    function should return [true] if either or both of its inputs are
    [false].

    Hint: if [simpl] will not simplify the goal in your proof, it's
    probably because you defined [nandb] without using a [match]
    expression. Try a different definition of [nandb], or just
    skip over [simpl] and go directly to [reflexivity]. We'll
    explain this phenomenon later in the chapter. *)

Definition nandb (b1 b2 :B) : B :=
  match b1, b2 with
    | false, _ => true
    | _, false => true    
    | _, _ => false
  end.
  (* negb (andb b1 b2). *)

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* ================================================================= *)
(* TYPES *)
(* Check true : B. *)
(* Check negb. *)

Inductive rgb : Type :=
    | red
    | green
    | blue.

Inductive color : Type :=
    | black
    | white
    | primary (p: rgb).

Definition monochrome (c: color): B :=
    match c with
    | black => true
    | white => true
    | primary _ => false
    end.

Definition isRed (c: color): B :=
    match c with
    | primary red => true
    | _ => true
    end.

(* ================================================================= *)
(* MODULES *)

Module Playground.
    Definition b: rgb := blue.
End Playground.

Definition b: B := true.

(* Check Playground.b : rgb. *)
(* Check b : B. *)

(* ================================================================= *)
(* Numbers *)

Module NatPlayground.

    Inductive N : Type :=
        | O
        | S (n : N).

    Definition pred (n : N) : N :=
        match n with
        | S n' => n'
        | _ => n
        end.

End NatPlayground.

(* Check (S (S (S O))). *)

Definition minusTwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

(* Compute (minusTwo 8). *)

(* Recursion: The fixpoint keyword is used to define a rescurisve function *)
(* deduct two on each recursion until it reaches either 1 or 0 *)
Fixpoint even (n:nat) : B :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

Definition odd (n:nat) : B := negb (even n).

Example test_even: (even 2) = true.
Proof. simpl. reflexivity. Qed.

Module NatPlay2.
    Fixpoint plus (n m : nat) : nat :=
        match n with
        | O => m
        | S n' => S (plus n' m)
        end.

    (* Compute (plus 3 2). *)
    (* ===> 5 : nat *)
    
    (*      [plus 3 2]
       i.e. [plus (S (S (S O))) (S (S O))]
        ==> [S (plus (S (S O)) (S (S O)))]
              by the second clause of the [match]
        ==> [S (S (plus (S O) (S (S O))))]
              by the second clause of the [match]
        ==> [S (S (S (plus O (S (S O)))))]
              by the second clause of the [match]
        ==> [S (S (S (S (S O))))]
              by the first clause of the [match]
       i.e. [5]  *)    

    Fixpoint mult (n m : nat) : nat :=
        match n with
        | O => O
        | S n' => plus m (mult n' m)
        (* (1 + n')m = m + (n')m  *)
        end.

    (* Compute (mult 3 2). *)
    (* [mult 3 2]  *)
    (* i.e [mult (S (S (S O))) (S (S O))] *)
    (* => [plus (S (S O)) (mult (S (S O)) (S (S O)))] 
            ..... *)

    Example test_mult: mult 3 3 = 9.
    Proof. simpl. reflexivity. Qed.

    Fixpoint minus (n m : nat) : nat :=
        match n, m with
        | O, _ => O
        | _, O => n
        | S n', S m' => minus n' m'
        end.
    
    Example test_minus: minus 8 5 = 3.
    Proof. simpl. reflexivity. Qed.

    (* Notation "x + y" := (plus x y)
                            (at level 50, left associativity)
                            : nat_scope. *)

    Fixpoint eqb (n m : nat) : B :=
        match n, m with
        | O   , O => true
        | O   , S _ => false
        | S _ , O => false
        | S n', S m' => eqb n' m'
        end.

    Example test_is_equal: eqb 5 5 = true.
    Proof. simpl. reflexivity. Qed.
    
    Example test_isnot_equal: eqb 5 6 = false.
    Proof. simpl. reflexivity. Qed.

    Fixpoint leqb (n m : nat) : B :=
        match n, m with
        | O   ,  _ => true
        | S _ , O => false
        | S n', S m' => leqb n' m'
        end.

    Example test_less_than: leqb 8 8 = true.
    Proof. simpl. reflexivity. Qed.
        
End NatPlay2.