(* Grammar (generative) side of the Mutex protocol, on top of protocol_lib.

   This file now supplies ONLY what a model owes the library:

     - four event classes, defined without using `next`  (the grammar side)
     - the 11 obligations of protocol_lib.Protocol

   States, events and the transition matrix are NOT duplicated here: they
   come from mutex.v, together with its regression tests.  See
   `mutex_accepts_agree` below, which transfers those tests to the
   recognizer this file's theorem talks about.

   Everything else -- the grammar `genf`, the top level `gen`, the
   recognizer glue `run`/`accepts`, and THE headline theorem

       gen_iff_accepts : forall tr, gen tr <-> accepts tr = true

   ...comes from protocol_lib and is shared with mutex_param.v and
   mutex_waitqueue.v.

   Grammar (U = Unlocked, H = Held, nonterminals read as "starting in"):

       U -> epsilon
          | s U     for s in {lock-call, try-lock-call, try-lock-fail}
          | a H     for a in {lock-acquire, try-lock-success}

       H -> epsilon
          | s H     for s in {lock-call, try-lock-call, try-lock-fail}
          | d U     for d = guard-drop

       Program -> epsilon | create body      (body in U)

   U/H say nothing about the *final* state.  That is deliberate: it mirrors
   `accepts`, which accepts a trace that ends while the lock is still held
   (see `prefix_held`).  If the protocol were meant to be balanced instead,
   `balanced_is_not_equivalent` below is the machine-checked counterexample.

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile mutex_grammar.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
(* mutex.v owns the transition table.  Import it BEFORE protocol_lib so
   that the library's `run` / `accepts` / `next` win the unqualified
   names; reach mutex's own definitions through the `mutex.` qualifier. *)
Require Import mutex.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.

(** * Model: states, events and the transition matrix all come from
    mutex.v, together with its 7 regression tests (t_create, t_lock_unlock,
    t_accept_ok, ...).  Only the grammar-side event classes are defined
    here, independently of [next]. *)
Definition is_live (s : State) : bool :=
  match s with Unlocked | Held => true | _ => false end.

(** The STA side is [mutex.next] itself: one copy of the 4x7 table, not
    two.  [step] is only an alias, so the obligations below read exactly
    the same way as in the other two models. *)
Definition step : State -> Event -> State := mutex.next.

(** * Grammar side: the four event classes, defined without [step]. *)
Definition is_stutter (e : Event) : bool :=
  match e with
  | LockCall | TryLockCall | TryLockFail => true
  | _ => false
  end.

Definition changes (e : Event) (s s' : State) : bool :=
  match e, s, s' with
  (* the state-advancing steps *)
  | LockAcquire, Unlocked, Held => true
  | TryLockSuccess, Unlocked, Held => true
  (* the state-releasing steps *)
  | GuardDrop, Held, Unlocked => true
  | _, _, _ => false
  end.

Definition starts (e : Event) (s : State) : bool :=
  match e, s with
  | Create, Unlocked => true
  | _, _ => false
  end.

(** * The 11 obligations

    Nine of the eleven are table-shaped and are discharged mechanically
    by `discharge case_types`.  Two -- `ob_start_complete` (whose goal
    ends in an existential) and `ob_step_complete` (the totality case
    split over the transition table) -- are proved by hand, because each
    has to pick WHICH rule applies for each cell. *)
Ltac case_types := case_of State; case_of Event.

Lemma ob_live_not_fault : forall s, is_live s = true -> s <> Error.
Proof. discharge case_types. Qed.

Lemma ob_is_error_ok : forall s, mutex.is_error s = true <-> s = Error.
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
  (* Hand-written: the goal ends in an existential, and after case
     analysis it simplifies to a bare `false = true`, which Rocq 9's
     `discriminate` does not close. *)
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

(** Totality of the transition table: every step out of a live state is
    either a stutter, a state change, or a fault.  This is the
    backward-direction bridge. *)
Lemma ob_step_complete : forall s e, is_live s = true ->
    (is_stutter e = true /\ step s e = s)
    \/ (exists s', changes e s s' = true)
    \/ (step s e = Error).
Proof.
  intros s e Hl. destruct s; simpl in Hl; try discriminate.
  all: destruct e; simpl;
    try solve [ left; split; reflexivity ];
    try solve [ right; left; exists Held; reflexivity ];
    try solve [ right; left; exists Unlocked; reflexivity ];
    try solve [ right; right; reflexivity ].
Qed.

(** * Assemble the model.  Note: every definition above uses a name that
    does not clash with a Protocol field, otherwise the record literal
    below would fail with "Not a projection". *)
Definition P : Protocol :=
  {| st := State; ev := Event; live := is_live; init := Uninitialized;
     fault := Error; next := step; is_error := mutex.is_error;
     stutter := is_stutter; changes_to := changes;
     starts_to := starts;

     live_not_fault := ob_live_not_fault; is_error_ok := ob_is_error_ok;
     init_ok := ob_init_ok; start_ok := ob_start_ok;
     start_live := ob_start_live; start_complete := ob_start_complete;
     stutter_ok := ob_stutter_ok; changes_ok := ob_step_ok;
     changes_live := ob_step_live; fault_absorbing := ob_fault_absorbing;
     step_complete := ob_step_complete;
  |}.

(** * Agreement with mutex.v.

    The recognizer used here is the library's, built from [mutex.next];
    mutex.v's own uses a different [Fixpoint] over the same table.  These
    two lemmas make mutex.v's regression tests (t_create, t_lock_unlock,
    t_accept_ok, ...) apply to the recognizer `gen_iff_accepts` talks
    about -- one table, one meaning. *)
Lemma run_from_agree : forall tr s, run_from P s tr = mutex.run_from s tr.
Proof.
  intros tr; induction tr as [| e tr IH]; intros s; [ reflexivity | ].
  cbn [run_from]. cbn [mutex.run_from]. exact (IH (next P s e)).
Qed.

Lemma mutex_accepts_agree : forall tr, accepts P tr = mutex.accepts tr.
Proof.
  intros tr. unfold accepts, mutex.accepts. unfold run, mutex.run.
  rewrite run_from_agree. reflexivity.
Qed.

(** * Everything below is library-provided; these are just checks. *)

(* The acceptance criterion is prefix-closed: a trace may end while the
   lock is held.  The grammar accepts it too. *)
Example prefix_held : accepts P (Create :: LockAcquire :: nil) = true.
Proof. reflexivity. Qed.

Example balanced_ok : accepts P (Create :: LockAcquire :: GuardDrop :: nil) = true.
Proof. reflexivity. Qed.

Example drop_without_lock_bad : accepts P (Create :: GuardDrop :: nil) = false.
Proof. reflexivity. Qed.

(* Constructing a trace from the grammar constructors directly. *)
Example prefix_held_generated : gen P (Create :: LockAcquire :: nil).
Proof.
  apply (G_start P) with (s := Unlocked); [ reflexivity | ].
  apply (GF_chg P Unlocked Held LockAcquire nil);
    [ reflexivity | apply GF_nil; reflexivity ].
Qed.

Example drop_without_lock_not_generated : ~ gen P (Create :: GuardDrop :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(** * Example enumeration: what does this grammar actually generate?

    "Show me examples" is what a developer needs before confirming a
    generated grammar.  [examples_upto] lists every accepted trace over
    an alphabet, up to a given length. *)
Definition alphabet : list Event :=
  Create :: LockCall :: LockAcquire :: TryLockCall :: TryLockSuccess
    :: TryLockFail :: GuardDrop :: nil.

Example examples_upto_1 :
  examples_upto P alphabet 1 = nil :: (Create :: nil) :: nil.
Proof. reflexivity. Qed.

(** EVERY enumerated example is accepted -- not just the first one. *)
Example enumerated_examples_are_accepted :
  forall tr, In tr (examples_upto P alphabet 2) -> accepts P tr = true.
Proof.
  intros tr H. unfold examples_upto in H.
  exact (examples_upto_sound P (traces_upto P alphabet 2) tr H).
Qed.

(** * ============================================================
    The point of the whole exercise: the proof catches modelling
    mistakes and hands you a concrete counterexample.

    Suppose you read the protocol as *balanced* -- a trace must not end
    while the lock is still held -- and you add that to the grammar.
    Then the equivalence with `accepts` is not merely hard to prove; it
    is FALSE, and Rocq tells you exactly which trace breaks it.
    ============================================================ *)

Definition balanced (tr : Trace) : Prop := gen P tr /\ run P tr = Unlocked.

Lemma balanced_is_not_equivalent :
  ~ (forall tr, balanced tr <-> accepts P tr = true).
Proof.
  intro H.
  pose proof (H (Create :: LockAcquire :: nil)) as Hiff.
  destruct Hiff as [Hfwd Hback].
  assert (Hacc : accepts P (Create :: LockAcquire :: nil) = true) by reflexivity.
  assert (Hbal : balanced (Create :: LockAcquire :: nil))
    by (apply Hback; assumption).
  destruct Hbal as [_ Hrun].
  assert (Hheld : run P (Create :: LockAcquire :: nil) = Held) by reflexivity.
  congruence.
Qed.

Example counterexample_prefix :
    accepts P (Create :: LockAcquire :: nil) = true
 /\ run P (Create :: LockAcquire :: nil) = Held.
Proof. split; reflexivity. Qed.
