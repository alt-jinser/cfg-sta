(* A client-driven CFG for the loop in
     ../asterinas/kernel/libs/xarray/src/test.rs::init_continuous_with_arc

   The source loop repeatedly evaluates
       xarray.lock().store(i, value)
   The temporary LockedXArray (and its SpinLockGuard field) is dropped at
   the end of the statement.  `Store` is a client operation protected by
   that guard; it is not an event in spin.v's lock-only alphabet.

   Client grammar:
       Client -> epsilon | Acquire Body Release Client
       Body   -> epsilon | Store Body

   This is a client language, so it is intentionally a subset of the
   SpinLock protocol language.  In particular, spin.v accepts a trace
   ending while held; this complete-client CFG does not.
*)

Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.
Require Import spin.

Inductive ClientEvent : Type := Acquire | Store | Release.

(** A specialized yield semantics for the two CFG nonterminals above. *)
Inductive Body : list ClientEvent -> Prop :=
| Body_nil : Body nil
| Body_store : forall tr, Body tr -> Body (Store :: tr).

Inductive Client : list ClientEvent -> Prop :=
| Client_nil : Client nil
| Client_iter : forall body tail,
    Body body -> Client tail ->
    Client (Acquire :: body ++ Release :: tail).

(** The client/API product state.  Store is legal only while the guard is
    live.  The lock transitions agree with spin.v; Store is a stutter in
    the API lock state, but is checked against the client state here. *)
Definition client_step (s : spin.State) (e : ClientEvent) : spin.State :=
  match s with
  | spin.Free =>
      match e with
      | Acquire => spin.Locked
      | Store => spin.Error
      | Release => spin.Error
      end
  | spin.Locked =>
      match e with
      | Acquire => spin.Error
      | Store => spin.Locked
      | Release => spin.Free
      end
  | spin.Error => spin.Error
  end.

Fixpoint run_client_from (s : spin.State) (tr : list ClientEvent) : spin.State :=
  match tr with
  | nil => s
  | e :: rest => run_client_from (client_step s e) rest
  end.

Definition run_client (tr : list ClientEvent) :=
  run_client_from spin.Free tr.

Lemma run_client_from_app : forall a b s,
    run_client_from s (a ++ b) = run_client_from (run_client_from s a) b.
Proof.
  induction a as [| e a IH]; intros b s; simpl; [ reflexivity | ].
  apply IH.
Qed.

Lemma body_runs_while_held : forall body,
    Body body -> run_client_from spin.Locked body = spin.Locked.
Proof.
  intros body H. induction H; simpl; [ reflexivity | exact IHBody ].
Qed.

(** Top-level client property: every completed generated execution ends
    with the lock available.  The stronger Store-under-guard condition is
    checked by [client_step] and the body lemma above. *)
Theorem client_returns_unlocked : forall tr,
    Client tr -> run_client tr = spin.Free.
Proof.
  intros tr H. induction H as [| body tail Hbody Htail IHtail].
  - reflexivity.
  - unfold run_client. cbn [run_client_from client_step].
    rewrite run_client_from_app.
    rewrite (body_runs_while_held body Hbody).
    cbn [run_client_from client_step].
    exact IHtail.
Qed.

Theorem client_store_is_guarded : forall body,
    Body body -> run_client_from spin.Locked body = spin.Locked.
Proof. apply body_runs_while_held. Qed.

(** Erase data operations to compare the client trace with the existing
    SpinLock API protocol alphabet. *)
Fixpoint project_to_spin (tr : list ClientEvent) : list spin.Event :=
  match tr with
  | nil => nil
  | Acquire :: rest => spin.Lock :: project_to_spin rest
  | Store :: rest => project_to_spin rest
  | Release :: rest => spin.Unlock :: project_to_spin rest
  end.

Lemma project_to_spin_app : forall a b,
    project_to_spin (a ++ b) = project_to_spin a ++ project_to_spin b.
Proof.
  induction a as [| e a IH]; intros b; simpl; [ reflexivity | ].
  destruct e; simpl; rewrite IH; reflexivity.
Qed.

Lemma body_projects_away : forall body,
    Body body -> project_to_spin body = nil.
Proof.
  intros body H. induction H; simpl; [ reflexivity | exact IHBody ].
Qed.

Theorem client_projects_to_accepted_spin_trace : forall tr,
    Client tr -> run spin.Free spin.step (project_to_spin tr) = spin.Free.
Proof.
  intros tr H. induction H as [| body tail Hbody Htail IHtail].
  - reflexivity.
  - cbn [project_to_spin].
    rewrite project_to_spin_app.
    rewrite (body_projects_away body Hbody).
    cbn [protocol_lib.run protocol_lib.run_from spin.step].
    exact IHtail.
Qed.

Corollary client_is_accepted_by_spin_protocol : forall tr,
    Client tr ->
    accepts spin.Free spin.step spin.is_err (project_to_spin tr) = true.
Proof.
  intros tr H. unfold accepts.
  rewrite (client_projects_to_accepted_spin_trace tr H).
  reflexivity.
Qed.

(** Client traces form a strict subset: the protocol permits a held prefix,
    but the complete xarray helper returns after each statement. *)
Example spin_accepts_held_prefix :
    accepts spin.Free spin.step spin.is_err (spin.Lock :: nil) = true.
Proof. reflexivity. Qed.

Example client_does_not_return_held_prefix :
    ~ Client (Acquire :: nil).
Proof.
  intro H.
  pose proof (client_returns_unlocked (Acquire :: nil) H) as Hrun.
  discriminate Hrun.
Qed.
