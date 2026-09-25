(* Wait-queue Mutex protocol: API alphabet plus INTERNAL labels, with a
   REAL FIFO wait queue.

   Motivation: mutex_grammar.v / mutex_param.v model only API-level events.
   The owner's release and the waiter's wakeup are folded together, so a
   trace cannot say WHO was woken, or whether anyone was queued at all.
   That is exactly the gap the regular-language model cannot close (see
   docs/sync-protocol/mutex-regular-language.md: identities are projected
   away).  This model exposes two internal labels:

       Wait t   -- t found the lock held and enqueued itself (tail)
       Wake t   -- the holder released, and t (the queue HEAD) takes over

   States
       Uninitialized
       Unlocked                     -- free, queue empty (only after Create)
       Held o w                     -- held by o, FIFO queue w of waiters
       Waking w                     -- just released; w is the remaining queue
       Error

   The release step always goes to `Waking w` (never straight to
   `Unlocked`), so that the queue survives the release window -- that is
   what makes `Wake` meaningful, and what makes waking nobody an error.

   Abstractions (documented, not hidden):
     * Enqueue is FIFO with no duplicate check: `Wait t` appends even if t
       is already queued.
     * A newcomer may barge past the queue (`LockAcquire` while
       `Waking w` hands the lock over and keeps w queued), matching
       examples/mutex_tla.rs, whose pre_check_lock only looks at `locked`.
     * `Unlocked` and `Waking nil` are both "free with an empty queue";
       they differ only in history.

   Classification for protocol_lib (classes are a partition of the
   transition relation; the names are the library's):
     stutter    = LockCall, TryLockFail, TryLockCall(n <= MAX_RETRY)
     changes_to = LockAcquire, TryLockSuccess, GuardDrop, Wake, and Wait
                  (the library used to split this into an "advance"
                   class and a "release" class, but both produce the
                   same grammar rule -- and `Wait` fitted neither name.
                   Merging them removed that awkwardness entirely.)

   Obligations: 8 of 11 are discharged by `discharge case_types`.  The
   other three are hand-written because `case_of` cannot destructure a
   list in a bounded way -- `destruct q` on `list tid` introduces another
   `list tid`, so a `repeat` would not terminate.  Those three break the
   queue open themselves, once, at the top of their proof.

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile mutex_waitqueue.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import protocol_lib.
Open Scope bool_scope.

Definition tid := nat.

(** The numeric guard, as in mutex_param.v: 参数 > 10. *)
Definition MAX_RETRY : nat := 10.

Inductive State : Type :=
| Uninitialized
| Unlocked
| Held (owner : tid) (waiters : list tid)
| Waking (queue : list tid)
| Error.

Inductive Event : Type :=
| Create
| LockCall       (t : tid)
| LockAcquire    (t : tid)
| TryLockCall    (t : tid) (n : nat)
| TryLockSuccess (t : tid)
| TryLockFail    (t : tid)
| GuardDrop      (t : tid)
(* internal *)
| Wait           (t : tid)
| Wake           (t : tid).

Definition Trace := list Event.

Definition is_live (s : State) : bool :=
  match s with Unlocked | Held _ _ | Waking _ => true | _ => false end.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** The queue head decides the wakeup.  Kept OUT of the [step] pattern on
    purpose: if a match arm destructures the queue, Coq's match compiler
    splits on it for every `Waking` arm, and the residual
    `match queue with nil | _ => X end` is not convertible for a symbolic
    queue -- no closer in finish_goal can discharge it. *)
Definition wake_info (q : list tid) (t : tid) : option (list tid) :=
  match q with
  | h :: tl => if Nat.eqb t h then Some tl else None
  | nil => None
  end.

(** * The transition matrix *)
Definition step (s : State) (e : Event) : State :=
  match s, e with
  (* initialization *)
  | Uninitialized, Create     => Unlocked
  | Uninitialized, _          => Error
  | Error, _                  => Error
  | _, Create                 => Error

  (* LockCall is a pure call: it stutters in every live state. *)
  | Unlocked, LockCall _      => Unlocked
  | Held o w, LockCall _      => Held o w
  | Waking q, LockCall _      => Waking q

  (* acquisition: fast path, or barging past the queue (queue kept) *)
  | Unlocked, LockAcquire t        => Held t nil
  | Unlocked, TryLockSuccess t     => Held t nil
  | Waking q, LockAcquire t        => Held t q
  | Waking q, TryLockSuccess t     => Held t q
  | Held _ _, LockAcquire _        => Error
  | Held _ _, TryLockSuccess _     => Error

  (* numeric-guarded stutters *)
  | Unlocked, TryLockCall _ n => if Nat.leb n MAX_RETRY then Unlocked else Error
  | Held o w, TryLockCall _ n => if Nat.leb n MAX_RETRY then Held o w else Error
  | Waking q, TryLockCall _ n => if Nat.leb n MAX_RETRY then Waking q else Error
  | Unlocked, TryLockFail _   => Unlocked
  | Held o w, TryLockFail _   => Held o w
  | Waking q, TryLockFail _   => Waking q

  (* INTERNAL: a blocked thread enqueues itself at the tail *)
  | Held o w, Wait t          => Held o (w ++ (t :: nil))
  | Unlocked, Wait _          => Error
  | Waking _, Wait _          => Error

  (* release: the queue survives into Waking *)
  | Held o w, GuardDrop t     => if Nat.eqb t o then Waking w else Error
  | Unlocked, GuardDrop _     => Error
  | Waking _, GuardDrop _     => Error

  (* INTERNAL: the head of the queue is woken and takes the lock *)
  | Waking q, Wake t =>
      match wake_info q t with
      | Some tl => Held t tl
      | None => Error
      end
  | Unlocked, Wake _          => Error
  | Held _ _, Wake _          => Error
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
  | LockAcquire t, Unlocked, Held o w => Nat.eqb t o && nat_list_eqb w nil
  | TryLockSuccess t, Unlocked, Held o w => Nat.eqb t o && nat_list_eqb w nil
  | LockAcquire t, Waking q, Held o w => Nat.eqb t o && nat_list_eqb w q
  | TryLockSuccess t, Waking q, Held o w => Nat.eqb t o && nat_list_eqb w q
  | Wait t, Held o w, Held o' w' => Nat.eqb o o' && nat_list_eqb w' (w ++ (t :: nil))
  | Wake t, Waking q, Held o w =>
      match wake_info q t with
      | Some tl => Nat.eqb o t && nat_list_eqb w tl
      | None => false
      end
  (* the state-releasing step *)
  | GuardDrop t, Held o w, Waking qs => Nat.eqb t o && nat_list_eqb qs w
  | _, _, _ => false
  end.

Definition starts (e : Event) (s : State) : bool :=
  match e, s with
  | Create, Unlocked => true
  | _, _ => false
  end.

(** * The 11 obligations

    Eight are discharged mechanically.  `ob_step_ok`,
    `ob_start_complete` and `ob_step_complete` are proved by hand: the
    first because the `Wake` cell inspects the queue, the second because
    its goal ends in an existential, the third because it has to pick
    WHICH rule applies for each cell. *)
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
    [ exists Unlocked; reflexivity | contradiction .. ].
Qed.

Lemma ob_stutter_ok : forall s e,
  is_live s = true -> is_stutter e = true -> step s e = s.
Proof. discharge case_types. Qed.

(** Hand-written: the `Wake` cell of `changes` inspects the queue, so the
    queue must be broken open (once) before that arm can reduce. *)
Lemma ob_step_ok : forall s s' e, changes e s s' = true -> step s e = s'.
Proof.
  intros s s' e H.
  destruct s as [| | o w | q |];
  [ destruct e; destruct s'; simpl in H; discriminate H
  | destruct e; destruct s'; finish_goal
  | destruct e; destruct s'; finish_goal
  | destruct q as [| h tl];
    [ destruct e; destruct s'; finish_goal
    | destruct e; destruct s'; finish_goal ]
  | destruct e; destruct s'; simpl in H; discriminate H ].
Qed.

Lemma ob_step_live : forall s s' e, changes e s s' = true -> is_live s' = true.
Proof. discharge case_types. Qed.

Lemma ob_fault_absorbing : forall e, step Error e = Error.
Proof. discharge case_types. Qed.

(** Totality: every step out of a live state is a stutter, a state
    change, or a fault.  The guarded cells need an explicit split, and
    the queue must be opened for the `Wake` cells. *)
Lemma ob_step_complete : forall s e, is_live s = true ->
    (is_stutter e = true /\ step s e = s)
    \/ (exists s', changes e s s' = true)
    \/ (step s e = Error).
Proof.
  intros s e Hl.
  destruct s as [| | o w | q |]; simpl in Hl;
    try (exfalso; discriminate Hl).
  - (* Unlocked *)
    destruct e; simpl;
      try solve [ destruct (Nat.leb n MAX_RETRY);
                  [ left; split; reflexivity | right; right; reflexivity ] ];
      try solve [ left; split; reflexivity ];
      try solve [ right; left; exists (Held t nil);
                  simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity ];
      try solve [ right; right; reflexivity ].
  - (* Held o w *)
    destruct e; simpl;
      try solve [ destruct (Nat.leb n MAX_RETRY);
                  [ left; split; reflexivity | right; right; reflexivity ] ];
      try solve [ destruct (Nat.eqb t o);
                  [ right; left; exists (Waking w);
                    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
                  | right; right; reflexivity ] ];
      try solve [ left; split; reflexivity ];
      try solve [ right; left; exists (Held o (w ++ (t :: nil)));
                  simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity ];
      try solve [ right; right; reflexivity ].
  - (* Waking q *)
    destruct q as [| h tl];
      (destruct e; simpl;
        try solve [ destruct (Nat.leb n MAX_RETRY);
                    [ left; split; reflexivity | right; right; reflexivity ] ];
        (* the queue head decides whether `Wake` advances or faults *)
        try solve [ destruct (Nat.eqb t h) eqn:Hw;
                    [ rewrite Nat.eqb_eq in Hw; subst;
                      right; left; exists (Held h tl);
                      simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
                    | right; right; reflexivity ] ];
        try solve [ left; split; reflexivity ];
        try solve [ right; left; exists (Held t nil);
                    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity ];
        try solve [ right; left; exists (Held t (h :: tl));
                    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity ];
        try solve [ right; right; reflexivity ]).
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

(** * ============================================================
    What the internal labels buy you
    ============================================================ *)

(* A full contended hand-off, FIFO, with the internal steps visible:
   0 takes the lock; 1 and 2 call, find it held and enqueue themselves;
   0 releases (state -> Waking [1;2]); 1 is woken and takes over; then 2. *)
Example contended_handoff : accepts P
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1
   :: LockCall 2 :: Wait 2
   :: GuardDrop 0
   :: Wake 1 :: GuardDrop 1
   :: Wake 2 :: GuardDrop 2 :: nil) = true.
Proof. reflexivity. Qed.

Example contended_handoff_generated : gen P
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1
   :: LockCall 2 :: Wait 2
   :: GuardDrop 0
   :: Wake 1 :: GuardDrop 1
   :: Wake 2 :: GuardDrop 2 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

(* FIFO order is enforced: 2 is queued behind 1, so waking 2 first fails.
   The API-level alphabet cannot even express this -- it has no Wake. *)
Example wake_out_of_order : accepts P
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1 :: LockCall 2 :: Wait 2
   :: GuardDrop 0 :: Wake 2 :: nil) = false.
Proof. reflexivity. Qed.

Example wake_out_of_order_not_generated : ~ gen P
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1 :: LockCall 2 :: Wait 2
   :: GuardDrop 0 :: Wake 2 :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(* Waking nobody is an error -- nothing was queued. *)
Example wake_without_waiter : accepts P
  (Create :: LockAcquire 0 :: GuardDrop 0 :: Wake 1 :: nil) = false.
Proof. reflexivity. Qed.

(* Waiting on a free lock is an error: there is nothing to wait for. *)
Example wait_on_free_lock : accepts P (Create :: Wait 0 :: nil) = false.
Proof. reflexivity. Qed.

(* The numeric guard carries over unchanged. *)
Example retry_over_budget : accepts P (Create :: TryLockCall 0 11 :: nil) = false.
Proof. reflexivity. Qed.

Example retry_at_budget : accepts P (Create :: TryLockCall 0 10 :: nil) = true.
Proof. reflexivity. Qed.
