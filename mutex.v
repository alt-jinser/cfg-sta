(* Mutex state machine, ported from mutex.rkt (Redex) to Rocq/Coq.
   Fixes applied vs. original .rkt:
   - F1: guard-drop rule had missing parens: (held guard-drop E ...)
         -> corrected to (held (guard-drop E ...)).
   - F2: double-create was stuck (no rule) -> now goes to error.
   - F3: evaluation is a total function, so stuck configs cannot
         raise "no clauses matched"; all 4x7 combinations are covered.
   - F4 (aligned with vostd ostd/specs/sync/mutex_protocol.rs, which wins):
         uninitialized + lock_call/try_lock_call/try_lock_fail -> error
         (the .rkt stuttered); double-create -> error in all live states.
   Tested with Rocq 9.1.1 (rocq compile). *)

Require Import Corelib.Lists.ListDef.

(** * Syntax: states and events *)
Inductive State : Type :=
  | Uninitialized
  | Unlocked
  | Held
  | Error.

Inductive Event : Type :=
  | Create
  | LockCall
  | LockAcquire
  | TryLockCall
  | TryLockSuccess
  | TryLockFail
  | GuardDrop.

Definition Trace := list Event.
Definition Config := (State * Trace)%type.

(** * Small-step: one event *)
(** Total transition function. Covers the full 4x7 matrix. *)
Definition next (s : State) (e : Event) : State :=
  match s, e with
  (* uninitialized: any use before create is an error (.rs wins) *)
  | Uninitialized, Create         => Unlocked
  | Uninitialized, LockAcquire    => Error
  | Uninitialized, LockCall       => Error
  | Uninitialized, TryLockCall    => Error
  | Uninitialized, TryLockSuccess => Error
  | Uninitialized, TryLockFail    => Error
  | Uninitialized, GuardDrop      => Error
  (* unlocked *)
  | Unlocked, Create         => Error        (* F2: .rkt had no rule, stuck *)
  | Unlocked, LockAcquire    => Held
  | Unlocked, LockCall       => Unlocked
  | Unlocked, TryLockCall    => Unlocked
  | Unlocked, TryLockSuccess => Held
  | Unlocked, TryLockFail    => Unlocked  (* QUESTIONABLE: spurious fail on unlocked; kept from .rkt *)
  | Unlocked, GuardDrop      => Error
  (* held *)
  | Held, Create         => Error            (* F2: .rkt had no rule, stuck *)
  | Held, LockAcquire    => Error
  | Held, LockCall       => Held
  | Held, TryLockCall    => Held
  | Held, TryLockSuccess => Error
  | Held, TryLockFail    => Held
  | Held, GuardDrop      => Unlocked         (* F1: .rkt rule was dead due to missing parens *)
  (* error sink *)
  | Error, _ => Error
  end.

(** Relational form, one-to-one with the Redex reduction-relation. *)
Inductive step : Config -> Config -> Prop :=
  | Step : forall s e s' rest,
      next s e = s' ->
      step (s, e :: rest) (s', rest).

(** Multi-step (reflexive-transitive closure over remaining trace). *)
Inductive steps : Config -> Config -> Prop :=
  | StepsRefl  : forall c, steps c c
  | StepsTrans : forall c1 c2 c3,
      step c1 c2 -> steps c2 c3 -> steps c1 c3.

(** * Trace evaluation *)
Fixpoint run_from (s : State) (tr : Trace) : State :=
  match tr with
  | nil       => s
  | e :: es => run_from (next s e) es
  end.

Definition run (tr : Trace) : State :=
  run_from Uninitialized tr.

Definition is_error (s : State) : bool :=
  match s with Error => true | _ => false end.

Definition accepts (tr : Trace) : bool :=
  negb (is_error (run tr)).

(** * Regression tests mirroring mutex.rkt module+ test *)
Example t_create : run (Create :: nil) = Unlocked.
Proof. reflexivity. Qed.

Example t_lock_unlock :
  run (Create :: LockAcquire :: GuardDrop :: nil) = Unlocked.
Proof. reflexivity. Qed.

Example t_drop_unlocked_err :
  run (Create :: GuardDrop :: nil) = Error.
Proof. reflexivity. Qed.

Example t_accept_ok :
  accepts (Create :: LockAcquire :: GuardDrop :: nil) = true.
Proof. reflexivity. Qed.

Example t_accept_bad :
  accepts (Create :: GuardDrop :: nil) = false.
Proof. reflexivity. Qed.

Example t_double_create_err :
  run (Create :: Create :: nil) = Error.
Proof. reflexivity. Qed.

Example t_try_seq :
  run (Create :: LockAcquire :: TryLockFail :: GuardDrop :: nil) = Unlocked.
Proof. reflexivity. Qed.

(** * Properties *)

(** Error is absorbing (corresponds to redex-check err-sink property). *)
Theorem error_absorbing : forall tr,
  run_from Error tr = Error.
Proof.
  intros tr. induction tr as [| e es IH].
  - reflexivity.
  - simpl. destruct e; apply IH.
Qed.

Corollary error_sink_step : forall e rest,
  step (Error, e :: rest) (Error, rest).
Proof.
  intros e rest. apply Step. destruct e; reflexivity.
Qed.

(** Determinism: the relation is functional. *)
Theorem step_deterministic : forall c c1 c2,
  step c c1 -> step c c2 -> c1 = c2.
Proof.
  intros c c1 c2 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  congruence.
Qed.

(** Function-relation agreement on one step. *)
Theorem step_next_agree : forall s e rest,
  step (s, e :: rest) (next s e, rest).
Proof. intros. apply Step. reflexivity. Qed.

(** run_from agrees with multi-step reduction to empty trace. *)
Theorem run_steps : forall s tr,
  steps (s, tr) (run_from s tr, nil).
Proof.
  intros s tr. generalize dependent s.
  induction tr as [| e es IH]; intros s.
  - simpl. apply StepsRefl.
  - simpl. eapply StepsTrans.
    + apply Step. reflexivity.
    + apply IH.
Qed.
