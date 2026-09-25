(* Parameterized Mutex protocol, on top of protocol_lib.

   Two additions over mutex_grammar.v:

   1. IDENTITY.  Events carry a thread id and `Held` carries its owner, so
      the state space {Uninitialized} + {Unlocked} + {Held t | t : nat} +
      {Error} is INFINITE.  It is no longer a finite automaton -- which is
      why the grammar needs a *parameterized nonterminal* H(o) and a
      regular language will not do.

   2. NUMERIC CONSTRAINT.  TryLockCall t n is legal only when
      n <= MAX_RETRY (literally "参数 > 10").  The guard sits on the
      production, not in the alphabet.

       U    -> epsilon
             | LockCall(t) U | TryLockFail(t) U
             | TryLockCall(t,n) U         when n <= MAX_RETRY
             | LockAcquire(t) H(t) | TryLockSuccess(t) H(t)

       H(o) -> epsilon
             | LockCall(t) H(o) | TryLockFail(t) H(o)
             | TryLockCall(t,n) H(o)      when n <= MAX_RETRY
             | GuardDrop(o) U             <-- identity match

   This file owes protocol_lib only the transition matrix, the three event
   classes, and the 8 obligations.  The grammar and the equivalence come
   from the library.

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile mutex_param.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import protocol_lib.

Definition tid := nat.

(** The numeric guard: attempts above this budget are rejected. *)
Definition MAX_RETRY : nat := 10.

Inductive State : Type :=
| Uninitialized
| Unlocked
| Held (owner : tid)
| Error.

Inductive Event : Type :=
| Create
| LockCall       (t : tid)
| LockAcquire    (t : tid)
| TryLockCall    (t : tid) (n : nat)
| TryLockSuccess (t : tid)
| TryLockFail    (t : tid)
| GuardDrop      (t : tid).

Definition Trace := list Event.

Definition is_live (s : State) : bool :=
  match s with Unlocked | Held _ => true | _ => false end.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** The transition matrix: the STA side. *)
Definition step (s : State) (e : Event) : State :=
  match s, e with
  | Uninitialized, Create => Unlocked
  | Uninitialized, _ => Error
  | Unlocked, Create => Error
  | Unlocked, LockCall _ => Unlocked
  | Unlocked, TryLockFail _ => Unlocked
  | Unlocked, TryLockCall _ n => if Nat.leb n MAX_RETRY then Unlocked else Error
  | Unlocked, LockAcquire t => Held t
  | Unlocked, TryLockSuccess t => Held t
  | Unlocked, GuardDrop _ => Error
  | Held o, Create => Error
  | Held o, LockCall _ => Held o
  | Held o, TryLockFail _ => Held o
  | Held o, TryLockCall _ n => if Nat.leb n MAX_RETRY then Held o else Error
  | Held o, LockAcquire _ => Error
  | Held o, TryLockSuccess _ => Error
  | Held o, GuardDrop t => if Nat.eqb t o then Unlocked else Error
  | Error, _ => Error
  end.

(** * Grammar side: the three event classes, defined without [step]. *)
Definition is_stutter (e : Event) : bool :=
  match e with
  | LockCall _ | TryLockFail _ => true
  | TryLockCall _ n => Nat.leb n MAX_RETRY
  | _ => false
  end.

Definition changes (e : Event) (s s' : State) : bool :=
  match e, s, s' with
  (* the state-advancing steps *)
  | LockAcquire t, Unlocked, Held o => Nat.eqb t o
  | TryLockSuccess t, Unlocked, Held o => Nat.eqb t o
  (* the state-releasing step *)
  | GuardDrop t, Held o, Unlocked => Nat.eqb t o
  | _, _, _ => false
  end.

Definition starts (e : Event) (s : State) : bool :=
  match e, s with
  | Create, Unlocked => true
  | _, _ => false
  end.

(** * The 11 obligations

    Nine of the eleven are table-shaped and are discharged
    mechanically by `discharge case_types`.  Two -- `ob_start_complete`
    (whose goal ends in an existential) and `ob_step_complete` (the
    totality case split, below) -- are proved by hand.  The two nat
    facts used by the guards come from protocol_lib. *)
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
  (* Hand-written: after case analysis the goal simplifies to a bare
     `false = true`, which Rocq 9's `discriminate` does not close. *)
  intros e H. destruct e; simpl in H;
    [ exists Unlocked; reflexivity | contradiction .. ].
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


(** Totality of the transition table -- the backward-direction bridge.
    The two guarded events need an explicit case split on their guard. *)
Lemma ob_step_complete : forall s e, is_live s = true ->
    (is_stutter e = true /\ step s e = s)
    \/ (exists s', changes e s s' = true)
    \/ (step s e = Error).
Proof.
  intros s e Hl. destruct s as [| | o |]; simpl in Hl; try discriminate.
  all: destruct e; simpl;
    (* numeric guard: n <= MAX_RETRY *)
    try solve [ destruct (Nat.leb n MAX_RETRY);
                [ left; split; reflexivity
                | right; right; reflexivity ] ];
    (* identity guard: t =? o *)
    try solve [ destruct (Nat.eqb t o);
                [ right; left; exists Unlocked; reflexivity
                | right; right; reflexivity ] ];
    try solve [ left; split; reflexivity ];
    try solve [ right; left; exists (Held t); apply Nat.eqb_refl ];
    try solve [ right; right; reflexivity ].
Qed.

(** * Assemble the model.  Every definition above uses a name that does
    not clash with a Protocol field, otherwise the record literal below
    would fail with "Not a projection". *)
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

(** * Everything below is library-provided; these are just checks. *)

(** * ============================================================
    What the two new parameters actually buy you
    ============================================================ *)

(* --- the numeric guard, literally "参数 > 10" --- *)
Example retry_at_budget : accepts P (Create :: TryLockCall 0 10 :: nil) = true.
Proof. reflexivity. Qed.

Example retry_over_budget : accepts P (Create :: TryLockCall 0 11 :: nil) = false.
Proof. reflexivity. Qed.

Example retry_over_budget_not_generated : ~ gen P (Create :: TryLockCall 0 11 :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(* --- the identity guard: releasing someone else's lock is an error --- *)
Example drop_by_other_rejected :
  accepts P (Create :: LockAcquire 0 :: GuardDrop 1 :: nil) = false.
Proof. reflexivity. Qed.

Example drop_by_owner_accepted :
  accepts P (Create :: LockAcquire 0 :: GuardDrop 0 :: nil) = true.
Proof. reflexivity. Qed.

(* --- and the grammar agrees in both directions --- *)
Example gen_drop_by_owner : gen P (Create :: LockAcquire 0 :: GuardDrop 0 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example gen_retry_within_budget : gen P (Create :: TryLockCall 7 3 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example gen_retry_over_budget : ~ gen P (Create :: TryLockCall 7 11 :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(** The identity constraint cannot be expressed over a finite alphabet:
    the recognizer has infinitely many states [Held t].  Two traces that
    differ only in the owner are accepted or rejected differently, and no
    finite automaton over {create, lock, unlock, ...} can tell them apart. *)
Example owners_are_distinguished :
    accepts P (Create :: LockAcquire 0 :: GuardDrop 0 :: nil) = true
 /\ accepts P (Create :: LockAcquire 0 :: GuardDrop 1 :: nil) = false.
Proof. split; reflexivity. Qed.
