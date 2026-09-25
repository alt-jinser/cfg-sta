(* Grammar (generative) side of the Mutex protocol, on top of protocol_lib.

   This file now supplies ONLY what a model owes the library:

     - nonterminals, productions and the availability invariant
       (the grammar side, defined without [next])
     - the 7 obligations of protocol_lib.Protocol

   States, events and the transition matrix are NOT duplicated here:
   they come from mutex.v, together with its regression tests.  See
   `mutex_accepts_agree` below, which transfers those tests to the
   recognizer this file's theorem talks about.

   Everything else -- the derivability relation, the recognizer glue
   `run`/`accepts`, soundness, and THE headline theorem

       gen_iff_accepts : forall tr, gen tr <-> accepts tr = true

   ...comes from protocol_lib and is shared with mutex_param.v,
   mutex_waitqueue.v and buffer.v.

   Grammar (U = Unlocked, H = Held, nonterminals read as "starting in"):

       Program -> epsilon | Create U
       U -> epsilon | lock-call U | try-lock-call U | try-lock-fail U
                  | lock-acquire H | try-lock-success H
       H -> epsilon | lock-call H | try-lock-call H | try-lock-fail H
                  | guard-drop U

   U/H say nothing about the *final* state.  That is deliberate: it
   mirrors `accepts`, which accepts a trace that ends while the lock is
   still held (see `prefix_held`).  If the protocol were meant to be
   balanced instead, `balanced_is_not_equivalent` below is the
   machine-checked counterexample.

   Names: the model's definitions must not collide with a Protocol
   field, hence [productions] / [available] rather than [prod] / [inv].

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile mutex_grammar.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
(* mutex.v owns the transition table.  Import it BEFORE protocol_lib so
   that the library's `run` / `accepts` win the unqualified names;
   reach mutex's own definitions through the `mutex.` qualifier. *)
Require Import mutex.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.

(** * Grammar side *)
Inductive Nt := Program | U | H.

(** The STA side is [mutex.next] itself: one copy of the 4x7 table. *)
Definition step : State -> Event -> State := mutex.next.

Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nil  : productions Program nil
| PR_body : productions Program (Se Create :: Sn U :: nil)
| PU_nil  : productions U nil
| PU_call : productions U (Se LockCall :: Sn U :: nil)
| PU_tryc : productions U (Se TryLockCall :: Sn U :: nil)
| PU_tryf : productions U (Se TryLockFail :: Sn U :: nil)
| PU_acq  : productions U (Se LockAcquire :: Sn H :: nil)
| PU_succ : productions U (Se TryLockSuccess :: Sn H :: nil)
| PH_nil  : productions H nil
| PH_call : productions H (Se LockCall :: Sn H :: nil)
| PH_tryc : productions H (Se TryLockCall :: Sn H :: nil)
| PH_tryf : productions H (Se TryLockFail :: Sn H :: nil)
| PH_drop : productions H (Se GuardDrop :: Sn U :: nil).

(** Which nonterminal is available in which state: the invariant that
    ties the state machine to the grammar. *)
Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | Program, Uninitialized => true
  | U, Unlocked            => true
  | H, Held                => true
  | _, _                   => false
  end.

(** * The 7 obligations *)

Ltac case_types := case_of State; case_of Event.

Lemma ob_is_error_ok : forall s, mutex.is_error s = true <-> s = Error.
Proof. discharge case_types. Qed.

Lemma ob_init_fault_free : Uninitialized <> Error.
Proof. discharge case_types. Qed.

Lemma ob_inv_start : available Program Uninitialized = true.
Proof. reflexivity. Qed.

Lemma ob_prod_ok : forall A beta s,
    productions A beta -> available A s = true -> ok Error step available productions s beta.
Proof. discharge_prod productions case_types. Qed.

(** [Error] really is a sink -- used by the completeness proof below,
    which argues by contradiction from a faulting run. *)
Lemma run_from_error : forall tr, run_from step Error tr = Error.
Proof. apply run_from_sink. intros e; reflexivity. Qed.

(** The word-level predicate: a trace the machine accepts.  For a finite
    state machine with no counter there is no sharper structural form to
    give it -- and the content sits in [ob_word_ok_gen] anyway, which is
    where the contract says it belongs. *)
Definition wellformed (tr : list Event) : Prop :=
  run Uninitialized step tr <> Error.

Lemma ob_word_ok_run : forall tr,
    run Uninitialized step tr <> Error <-> wellformed tr.
Proof. intros tr. unfold wellformed. split; intro H; exact H. Qed.

(** Direction 2, at the grammar's own level: a safe run from a state
    where [A] is available is derivable from [A].  Right-linear
    productions make this a per-event induction -- each production
    consumes exactly one terminal, so the split of the word is forced
    and no decomposition lemma is needed (contrast rcu.v, whose
    [Read Body Drop Body] production does need one). *)
(** The two witnesses [gen_of_run] asks for.  The library owns the
    induction and the assembly of the derivation; all that is left
    here is choosing a production. *)
Lemma nil_prod : forall A, productions A nil.
Proof. intros A; destruct A; constructor. Qed.

Lemma step_prod : forall A s e,
    available A s = true -> step s e <> Error ->
    exists B, productions A (Se e :: Sn B :: nil) /\
              available B (step s e) = true.
Proof.
  intros A s e Hinv Hne.
  destruct A; case_types; simpl in *;
    try discriminate Hinv;
    try (exfalso; apply Hne; reflexivity).
  - (* Program / Uninitialized / Create *)
    exists U. split; [ exact PR_body | reflexivity ].
  - (* U / Unlocked / LockCall *)
    exists U. split; [ exact PU_call | reflexivity ].
  - (* U / Unlocked / LockAcquire *)
    exists H. split; [ exact PU_acq | reflexivity ].
  - (* U / Unlocked / TryLockCall *)
    exists U. split; [ exact PU_tryc | reflexivity ].
  - (* U / Unlocked / TryLockSuccess *)
    exists H. split; [ exact PU_succ | reflexivity ].
  - (* U / Unlocked / TryLockFail *)
    exists U. split; [ exact PU_tryf | reflexivity ].
  - (* H / Held / LockCall *)
    exists H. split; [ exact PH_call | reflexivity ].
  - (* H / Held / TryLockCall *)
    exists H. split; [ exact PH_tryc | reflexivity ].
  - (* H / Held / TryLockFail *)
    exists H. split; [ exact PH_tryf | reflexivity ].
  - (* H / Held / GuardDrop *)
    exists U. split; [ exact PH_drop | reflexivity ].
Qed.

Lemma ob_word_ok_gen : forall tr, wellformed tr -> gen productions Program tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run run_from_error nil_prod step_prod Program Uninitialized);
    [ reflexivity | exact H ].
Qed.

(** * Assemble the model. *)
Definition P : Protocol :=
  {| st := State; ev := Event; nt := Nt;
     init := Uninitialized; fault := Error; next := step;
     is_error := mutex.is_error;
     start := Program; prod := productions; inv := available;

     is_error_ok := ob_is_error_ok;
     init_fault_free := ob_init_fault_free;
     inv_start := ob_inv_start;
     prod_ok := ob_prod_ok;
     word_ok := wellformed;
     word_ok_run := ob_word_ok_run;
     word_ok_gen := ob_word_ok_gen;
  |}.

Notation runp := (run (init P) (next P)).
Notation acceptsp := (accepts (init P) (next P) (is_error P)).
Notation genp := (gen (prod P) (start P)).

(** * Agreement with mutex.v.

    The recognizer used here is the library's, built from [mutex.next];
    mutex.v's own uses a different [Fixpoint] over the same table.  These
    two lemmas make mutex.v's regression tests (t_create, t_lock_unlock,
    t_accept_ok, ...) apply to the recognizer `gen_iff_accepts` talks
    about -- one table, one meaning. *)
Lemma run_from_agree : forall tr s, run_from (next P) s tr = mutex.run_from s tr.
Proof.
  intros tr; induction tr as [| e tr IH]; intros s; [ reflexivity | ].
  cbn [run_from]. cbn [mutex.run_from]. exact (IH (next P s e)).
Qed.

Lemma mutex_accepts_agree : forall tr, acceptsp tr = mutex.accepts tr.
Proof.
  intros tr. unfold accepts. unfold mutex.accepts.
  unfold run, mutex.run.
  rewrite run_from_agree. reflexivity.
Qed.

(** * Everything below is library-provided; these are just checks. *)

(* The acceptance criterion is prefix-closed: a trace may end while the
   lock is held.  The grammar accepts it too. *)
Example prefix_held : acceptsp (Create :: LockAcquire :: nil) = true.
Proof. reflexivity. Qed.

Example balanced_ok : acceptsp (Create :: LockAcquire :: GuardDrop :: nil) = true.
Proof. reflexivity. Qed.

Example drop_without_lock_bad : acceptsp (Create :: GuardDrop :: nil) = false.
Proof. reflexivity. Qed.

(* Constructing a trace from the productions directly. *)
Example prefix_held_generated : genp (Create :: LockAcquire :: nil).
Proof.
  apply (derives_sn productions Program (Se Create :: Sn U :: nil)
           (Create :: LockAcquire :: nil) PR_body).
  apply derives_se.
  apply (derives_sn productions U (Se LockAcquire :: Sn H :: nil)
           (LockAcquire :: nil) PU_acq).
  apply derives_se.
  apply (derives_sn productions H nil nil PH_nil).
  apply derives_nil.
Qed.

Example drop_without_lock_not_generated : ~ genp (Create :: GuardDrop :: nil).
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
  forall tr, In tr (examples_upto P alphabet 2) -> acceptsp tr = true.
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

Definition balanced (tr : Trace) : Prop := genp tr /\ runp tr = Unlocked.

Lemma balanced_is_not_equivalent :
  ~ (forall tr, balanced tr <-> acceptsp tr = true).
Proof.
  intro H.
  pose proof (H (Create :: LockAcquire :: nil)) as Hiff.
  destruct Hiff as [Hfwd Hback].
  assert (Hacc : acceptsp (Create :: LockAcquire :: nil) = true) by reflexivity.
  assert (Hbal : balanced (Create :: LockAcquire :: nil))
    by (apply Hback; assumption).
  destruct Hbal as [_ Hrun].
  assert (Hheld : runp (Create :: LockAcquire :: nil) = Held) by reflexivity.
  congruence.
Qed.

Example counterexample_prefix :
    acceptsp (Create :: LockAcquire :: nil) = true
 /\ runp (Create :: LockAcquire :: nil) = Held.
Proof. split; reflexivity. Qed.
