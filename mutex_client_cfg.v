(* A client-driven CFG for the real Asterinas Mutex lookup client:
     ../asterinas/kernel/core/src/device/registry/char.rs::lookup

   The function evaluates
       DEVICE_REGISTRY.lock().get(&id.to_raw()).cloned()
   The temporary MutexGuard is released at the end of the expression.
   The client grammar describes any finite sequence of calls to this
   helper; `Access` abstracts the protected map lookup and is erased when
   projecting to the Mutex protocol alphabet.

   Client -> epsilon | Acquire Lookup Release Client
   Lookup -> Access

   The API side below is `mutex_grammar.P`, whose transition table is
   sourced from vostd/ostd/specs/sync/mutex_protocol.rs.  The claim is
   inclusion of this client language in the API language, not equality.
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.
Require Import mutex.
Require Import mutex_grammar.

Inductive ClientEvent : Type := Acquire | Access | Release.

Inductive Lookup : list ClientEvent -> Prop :=
| Lookup_access : Lookup (Access :: nil).

Inductive Client : list ClientEvent -> Prop :=
| Client_nil : Client nil
| Client_call : forall body tail,
    Lookup body -> Client tail ->
    Client (Acquire :: body ++ Release :: tail).

Definition client_step (s : mutex.State) (e : ClientEvent) : mutex.State :=
  match s with
  | mutex.Unlocked =>
      match e with
      | Acquire => mutex.Held
      | Access => mutex.Error
      | Release => mutex.Error
      end
  | mutex.Held =>
      match e with
      | Acquire => mutex.Error
      | Access => mutex.Held
      | Release => mutex.Unlocked
      end
  | mutex.Uninitialized => mutex.Error
  | mutex.Error => mutex.Error
  end.

Fixpoint run_client_from (s : mutex.State) (tr : list ClientEvent) : mutex.State :=
  match tr with
  | nil => s
  | e :: rest => run_client_from (client_step s e) rest
  end.

Definition run_client (tr : list ClientEvent) :=
  run_client_from mutex.Unlocked tr.

Lemma run_client_from_app : forall a b s,
    run_client_from s (a ++ b) = run_client_from (run_client_from s a) b.
Proof.
  induction a as [| e a IH]; intros b s; simpl; [ reflexivity | ].
  apply IH.
Qed.

Lemma lookup_runs_while_held : forall body,
    Lookup body -> run_client_from mutex.Held body = mutex.Held.
Proof. intros body H. inversion H; reflexivity. Qed.

Theorem lookup_client_returns_unlocked : forall tr,
    Client tr -> run_client tr = mutex.Unlocked.
Proof.
  intros tr H. induction H as [| body tail Hbody Htail IHtail].
  - reflexivity.
  - unfold run_client. cbn [run_client_from client_step].
    rewrite run_client_from_app.
    rewrite (lookup_runs_while_held body Hbody).
    cbn [run_client_from client_step].
    exact IHtail.
Qed.

Fixpoint project_to_mutex (tr : list ClientEvent) : list mutex.Event :=
  match tr with
  | nil => nil
  | Acquire :: rest => mutex.LockAcquire :: project_to_mutex rest
  | Access :: rest => project_to_mutex rest
  | Release :: rest => mutex.GuardDrop :: project_to_mutex rest
  end.

Lemma project_to_mutex_app : forall a b,
    project_to_mutex (a ++ b) = project_to_mutex a ++ project_to_mutex b.
Proof.
  induction a as [| e a IH]; intros b; simpl; [ reflexivity | ].
  destruct e; simpl; rewrite IH; reflexivity.
Qed.

Lemma lookup_projects_away : forall body,
    Lookup body -> project_to_mutex body = nil.
Proof. intros body H. inversion H; reflexivity. Qed.

Theorem client_projects_to_mutex_unlocked : forall tr,
    Client tr ->
    protocol_lib.run_from mutex.next mutex.Unlocked
      (project_to_mutex tr) = mutex.Unlocked.
Proof.
  intros tr H. induction H as [| body tail Hbody Htail IHtail].
  - reflexivity.
  - cbn [project_to_mutex].
    rewrite project_to_mutex_app.
    rewrite (lookup_projects_away body Hbody).
    cbn [protocol_lib.run_from mutex.next].
    exact IHtail.
Qed.

Theorem client_trace_accepted_by_mutex_spec : forall tr,
    Client tr ->
    protocol_lib.accepts mutex.Uninitialized mutex.next mutex.is_error
      (mutex.Create :: project_to_mutex tr) = true.
Proof.
  intros tr H. unfold protocol_lib.accepts, protocol_lib.run.
  cbn [protocol_lib.run_from mutex.next].
  rewrite (client_projects_to_mutex_unlocked tr H).
  reflexivity.
Qed.

Theorem client_cfg_included_in_protocol_cfg : forall tr,
    Client tr ->
    gen (prod mutex_grammar.P) (start mutex_grammar.P)
      (mutex.Create :: project_to_mutex tr).
Proof.
  intros tr H.
  apply (proj2 (gen_iff_accepts mutex_grammar.P
                  (mutex.Create :: project_to_mutex tr))).
  apply client_trace_accepted_by_mutex_spec.
  exact H.
Qed.

(** The spec permits a prefix that this completed helper-call grammar does
    not generate: API behaviors strictly contain this client's behaviors. *)
Example mutex_spec_accepts_held_prefix :
    protocol_lib.accepts mutex.Uninitialized mutex.next mutex.is_error
      (mutex.Create :: mutex.LockAcquire :: nil) = true.
Proof. reflexivity. Qed.

Example lookup_client_does_not_return_with_guard :
    ~ Client (Acquire :: Access :: nil).
Proof.
  intro H.
  pose proof (lookup_client_returns_unlocked
                (Acquire :: Access :: nil) H) as Hrun.
  discriminate Hrun.
Qed.
