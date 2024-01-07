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

Notation "x =? y" := (NatPlay2.eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (NatPlay2.leqb x y) (at level 70) : nat_scope.


(*?  Proof by Simplification  *)

(* A general property of natural numbers *)

Theorem plus_O_n :
    forall n : nat, O + n = n.
Proof.
    intros n. simpl. reflexivity. Qed.

Theorem plus_1_n :
    forall n : nat, 1 + n = S n.
Proof.
    intros n. reflexivity. Qed.

(*?  Proof by Rewriting  *)

Theorem plud_id_example:
    forall n m : nat,
        n = m -> (* Logical implication *)
        n + m = m + n.
Proof.
    intros n m. (* move quantifiers into ctx *)
    intros H. (* move Hypothesis into ctx *)
    rewrite -> H. (* rewrite goal using H either left <- or right -> ; Here we rewite the contents of left *)
    reflexivity. Qed.

Theorem mult_n_0_m_0:
    forall n m : nat,
        n * 0 + m * 0 = 0.
Proof.
    intros n m.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    reflexivity. Qed.

(*? Proof by Case Analysis  *)

Theorem plus_1_neq_0_firsttry:
    forall n : nat,
        ((n + 1) =? 0) = false.
Proof.
    intros n.
    simpl.
    Abort. (*Wont work. so abort*)

Theorem plus_1_neq_0_secondtry:
    forall n : nat,
        ((n + 1) =? 0) = false.
Proof.
    intros n.
    destruct n as [ | n'] eqn:E.
    (* destruct n => [O | S n'] => [ | n'] *)
    - reflexivity.
    - reflexivity.
    Qed.

Theorem plus_1_neq_0:
    forall n : nat,
        ((n + 1) =? 0) = false.
Proof.
    intros [ | n'].
    - reflexivity.
    - reflexivity.
    Qed.

Theorem negb_involutive:
    forall b : B,
        negb (negb b) = b.
Proof.
    intros b. destruct b eqn:E.
    - reflexivity.
    - reflexivity.
    Qed.

Theorem andb_commutative:
    forall b c : B,
        andb b c = andb c b.
Proof.
    intros b c.
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
        + reflexivity.
        + reflexivity.
    -  destruct c eqn:Ec.
        + reflexivity.
        + reflexivity.
    Qed.

Theorem andb_commutative':
    forall b c : B,
        andb b c = andb c b.
Proof.
    intros b c.
    destruct b eqn:Eb.
    { destruct c eqn:Ec.
         { reflexivity. }
         { reflexivity. } }
    { destruct c eqn:Ec.
         { reflexivity. }
         { reflexivity. } }
    Qed.

Theorem andb_commutative'':
    forall b c : B,
        andb b c = andb c b.
Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    Qed.

(*? COQ syntax
    - Vernacular: Checkm Theorem, Proof, Qed..
    - Gallina: The func prog lang or logic..
    - Ltac: Language for tactics. intros, simpl, destruct..
 *)

(*? Lambda Calculus
    e ::= x | λx. e | e1 e2
    - Alpha equivalence: names don't matter
    - Beta reduction: application and substitution
        + call-by-value[cbv]: red app after redcing arg to val
        + call-by-name[cbn]: red before after redcing arg to val
        + Full: reduce any application any time any where
 *)

(*? Reduction tactics
    - [simpl]: `human readable` smart choices about reductions
    - [cbn]: modern, even smarter than [simpl]?
    - [cbv]: fully compute

    - [reflexivity]
        + finsihes proof 'by reflexivity of equality'
        + To prove [a = b], fully reduce [a] & [b]
            -- if alpha-equivalent then succeed
            -- else fail
 *)

(*? Gallina
    - Definition (delta reduction)
    - Inductive types, pattern matching, recursion (iota reduction)
    - let bindings (zeta reduction)

    - [cbv] takes flags to selectively enable each kind of reduction
    - [compute] is shorthand for [beta delta iota zeta]
 *)

(*? Convertibilty
    - [e1] & [e2] are definitionally equal aka convertible
        if they fully reduce to α-equivalent terms.
        + That's what the [=] means.

    - Converitibilty is decidable in COQ:
        + Gallina is strongly normalizing.
        + That's what the [reflexivity] do
 *)
