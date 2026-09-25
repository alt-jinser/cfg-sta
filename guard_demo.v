(* guard_demo.v -- teaching `finish_goal` a guard over a non-nat type.

   `finish_goal` comes with specialised arms for the guards the Mutex
   models use:

       Nat.eqb x y = true         ->  x = y            (substituted)
       nat_list_eqb xs ys = true  ->  xs = ys
       Nat.leb n m = true         ->  rewritten into the goal
       a boolean under an `if`    ->  split

   Any OTHER parameter type -- an enum, a string, a user-defined id --
   needs one line to join in:

       Hint Resolve mode_eqb_eq : finish_db.

   A hint database is consulted at call time and is shared across files,
   which is why it works here: Rocq resolves an Ltac name statically at
   definition time, so an Ltac hook redefined in a model file would never
   reach the library's `finish_goal`.  (Measured, not assumed.)

   Compiles with Rocq 9.1.1:  rocq compile guard_demo.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import protocol_lib.

(** A parameter type that is not [nat]. *)
Inductive mode := Fast | Slow.

Definition mode_eqb (a b : mode) : bool :=
  match a, b with
  | Fast, Fast | Slow, Slow => true
  | _, _ => false
  end.

Lemma mode_eqb_eq : forall a b, mode_eqb a b = true -> a = b.
Proof.
  destruct a; destruct b; simpl; intros H; try discriminate; reflexivity.
Qed.

(** The one line a model has to add. *)
Hint Resolve mode_eqb_eq : finish_db.

(** Without that line `finish_goal` cannot turn the guard into an
    equation, and a goal that needs `a = b` stays open -- there is no
    boolean `if` for the generic split arm to bite on either.  `Fail
    reflexivity` records that the goal was NOT closed, so this example
    starts failing loudly if the mechanism ever changes. *)
Example the_gap_without_the_hint :
  forall a b, mode_eqb a b = true -> Some a = Some b.
Proof.
  intros a b H. finish_goal.
  Fail reflexivity.
Abort.

(** With the hint, the same goal closes. *)
Example closes_with_the_hint :
  forall a b, mode_eqb a b = true -> Some a = Some b.
Proof. intros a b H. finish_goal. Qed.

(** A guard sitting under an `if` never needed the hint: the generic
    split arm turns it into `true = true` / `false = true`, and the
    latter is closed by `discriminate`. *)
Example if_guard_needs_no_hint :
  forall a b, mode_eqb a b = true -> (if mode_eqb a b then 0 else 1) = 0.
Proof. intros a b H. finish_goal. Qed.
