(* Bounded buffer (producer/consumer) -- the GENERALITY TEST.

   Every other model in this directory is a Mutex.  This one deliberately
   is not: a buffered channel in the file/queue domain, with a different
   vocabulary and a different shape (a terminal `Closed` state, a data
   payload in `Buffered`, no owner, no wakeup).

   The point is not the buffer.  The point is that this file supplies
   ONLY

       - the transition table                        (the STA side)
       - the event classes, defined without `step`   (the grammar side)
       - the 11 obligations of protocol_lib.Protocol

   and touches no line of protocol_lib.v.  If a non-lock protocol needs
   a library change, that change belongs in the library -- and this file
   is where we find out.

   States
       Uninitialized
       Buffered items             -- the queue payload
       Closed                     -- terminal, still live
       Error

   Abstractions (documented, not hidden):
     * `Get` on an empty buffer faults (guarded by `1 <= length items`),
       it is not modelled as a blocking wait.
     * `Flush` empties unconditionally, `Close` is final, and peeking a
       closed buffer is a no-op rather than an error.

   Classes: stutter = Peek; changes_to = Put, Get, Flush, Close.
   Note that `Flush` from an already-empty buffer does not change the
   state -- which is exactly why the library merged "advance" and
   "release" into one class: the name never carried any semantics.

   Compiles with Rocq 9.1.1:  rocq compile buffer.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.
Open Scope bool_scope.

Inductive State : Type :=
| Uninitialized
| Buffered (items : list nat)
| Closed
| Error.

Inductive Event : Type :=
| Setup
| Put    (x : nat)
| Get
| Peek
| Flush
| Close.

Definition Trace := list Event.

Definition is_live (s : State) : bool :=
  match s with Buffered _ | Closed => true | _ => false end.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** Removing the head; only ever called under the `1 <= length` guard. *)
Definition pop (items : list nat) : list nat :=
  match items with nil => nil | _ :: rest => rest end.

(** * The transition matrix *)
Definition step (s : State) (e : Event) : State :=
  match s, e with
  (* initialization *)
  | Uninitialized, Setup => Buffered nil
  | Uninitialized, _     => Error
  | Error, _             => Error
  | _, Setup             => Error

  (* the buffer *)
  | Buffered items, Put x  => Buffered (items ++ (x :: nil))
  | Buffered items, Get    =>
      if Nat.leb 1 (length items) then Buffered (pop items) else Error
  | Buffered items, Peek   => Buffered items
  | Buffered items, Flush  => Buffered nil
  | Buffered items, Close  => Closed

  (* terminal state: only a peek is harmless *)
  | Closed, Peek  => Closed
  | Closed, _     => Error
  end.

(** * Grammar side: the three event classes, defined without [step]. *)
Definition is_stutter (e : Event) : bool :=
  match e with Peek => true | _ => false end.

Definition changes (e : Event) (s s' : State) : bool :=
  match e, s, s' with
  (* the state-advancing step *)
  | Put x, Buffered items, Buffered items' =>
      nat_list_eqb items' (items ++ (x :: nil))
  (* the state-releasing steps *)
  | Get, Buffered items, Buffered items' =>
      Nat.leb 1 (length items) && nat_list_eqb items' (pop items)
  | Flush, Buffered items, Buffered items' =>
      nat_list_eqb items' nil
  | Close, Buffered _, Closed => true
  | _, _, _ => false
  end.

Definition starts (e : Event) (s : State) : bool :=
  match e, s with
  | Setup, Buffered items => nat_list_eqb items nil
  | _, _ => false
  end.

(** * The 11 obligations -- nine by [discharge], two by hand. *)
Ltac case_types := case_of State; case_of Event.

Lemma ob_live_not_fault : forall s, is_live s = true -> s <> Error.
Proof. discharge case_types. Qed.

Lemma ob_is_error_ok : forall s, is_err s = true <-> s = Error.
Proof. discharge case_types. Qed.

Lemma ob_init_ok : Uninitialized <> Error.
Proof. discharge case_types. Qed.

Lemma ob_start_ok : forall e s, starts e s = true -> step Uninitialized e = s.
Proof. discharge case_types. Qed.

Lemma ob_start_live : forall e s, starts e s = true -> is_live s = true.
Proof. discharge case_types. Qed.

Lemma ob_start_complete : forall e, step Uninitialized e <> Error ->
  exists s, starts e s = true.
Proof.
  intros e H. destruct e; simpl in H;
    [ exists (Buffered nil); reflexivity | contradiction .. ].
Qed.

Lemma ob_stutter_ok : forall s e,
  is_live s = true -> is_stutter e = true -> step s e = s.
Proof. discharge case_types. Qed.

Lemma ob_step_ok : forall s s' e, changes e s s' = true -> step s e = s'.
Proof. discharge case_types. Qed.

Lemma ob_step_live : forall s s' e, changes e s s' = true -> is_live s' = true.
Proof. discharge case_types. Qed.

Lemma ob_fault_absorbing : forall e, step Error e = Error.
Proof. discharge case_types. Qed.

(** Totality: every step out of a live state is a stutter, a state
    change, or a fault.  Only the `Get` guard needs a split. *)
Lemma ob_step_complete : forall s e, is_live s = true ->
    (is_stutter e = true /\ step s e = s)
    \/ (exists s', changes e s s' = true)
    \/ (step s e = Error).
Proof.
  intros s e Hl.
  destruct s as [| items | | ]; simpl in Hl;
    try (exfalso; discriminate Hl).
  - (* Buffered items *)
    destruct e; simpl;
      try solve [ left; split; reflexivity ];
      try solve [ right; left; exists (Buffered (items ++ (x :: nil)));
                  simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity ];
      (* the `Get` guard: [simpl] folded `Nat.leb 1 (length items)` into a
         match, so destruct whatever the goal's `if` is testing *)
      try solve [ match goal with |- context[if ?b then _ else _] => destruct b end;
                  [ right; left; exists (Buffered (pop items));
                    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
                  | right; right; reflexivity ] ];
      try solve [ right; left; exists (Buffered nil);
                  simpl; rewrite ?nat_list_eqb_refl; reflexivity ];
      try solve [ right; left; exists Closed; reflexivity ];
      try solve [ right; right; reflexivity ].
  - (* Closed *)
    destruct e; simpl;
      try solve [ left; split; reflexivity ];
      try solve [ right; right; reflexivity ].
Qed.

(** * Assemble the model *)
Definition P : Protocol :=
  {| st := State; ev := Event; live := is_live; init := Uninitialized;
     fault := Error; next := step; is_error := is_err;
     stutter := is_stutter; changes_to := changes;
     starts_to := starts;

     live_not_fault := ob_live_not_fault; is_error_ok := ob_is_error_ok;
     init_ok := ob_init_ok; start_ok := ob_start_ok;
     start_live := ob_start_live; start_complete := ob_start_complete;
     stutter_ok := ob_stutter_ok; changes_ok := ob_step_ok;
     changes_live := ob_step_live;
     fault_absorbing := ob_fault_absorbing;
     step_complete := ob_step_complete;
  |}.

(** * What a developer would ask for *)
Example producer_consumer_roundtrip : accepts P
  (Setup :: Put 1 :: Put 2 :: Peek :: Get :: Flush :: Close :: nil) = true.
Proof. reflexivity. Qed.

Example producer_consumer_generated : gen P
  (Setup :: Put 1 :: Put 2 :: Peek :: Get :: Flush :: Close :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

(* Taking from an empty buffer is an error. *)
Example get_from_empty : accepts P (Setup :: Get :: nil) = false.
Proof. reflexivity. Qed.

(* Everything after Close is an error. *)
Example put_after_close : accepts P (Setup :: Close :: Put 1 :: nil) = false.
Proof. reflexivity. Qed.

(* Peeking a closed buffer is a no-op, not an error. *)
Example peek_after_close : accepts P (Setup :: Close :: Peek :: nil) = true.
Proof. reflexivity. Qed.

(* Examples handed to a developer really are accepted. *)
Definition alphabet : list Event :=
  Setup :: Put 0 :: Get :: Peek :: Flush :: Close :: nil.

Example examples_upto_1 :
  examples_upto P alphabet 1 = nil :: (Setup :: nil) :: nil.
Proof. reflexivity. Qed.

Example enumerated_examples_are_accepted :
  forall tr, In tr (examples_upto P alphabet 2) -> accepts P tr = true.
Proof.
  intros tr H. unfold examples_upto in H.
  exact (examples_upto_sound P (traces_upto P alphabet 2) tr H).
Qed.
