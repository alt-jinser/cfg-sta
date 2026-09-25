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

   Grammar: THE NONTERMINAL CARRIES THE QUEUE.  A production is
   state-independent, so a queue-free nonterminal would derive `Wake t`
   whenever a `Wake` appeared, even with an empty queue -- the machine
   rejects that, and [prod_ok] would fail at exactly that cell.  The
   nonterminal type is therefore infinite (a list per state shape),
   which the contract allows precisely so that queue-shaped protocols
   can be written at all.

       Program -> epsilon | Create U
       U       -> epsilon | lock-call t U | try-lock-fail t U
                      | try-lock-call t U          when n <= MAX_RETRY
                      | lock-acquire t H(t,nil) | try-lock-success t H(t,nil)
       H(o,w)  -> epsilon | lock-call t H(o,w) | try-lock-fail t H(o,w)
                      | try-lock-call t H(o,w)     when n <= MAX_RETRY
                      | wait t H(o, w++[t])
                      | guard-drop o W(w)          <-- tied to the owner
       W(q)    -> epsilon | lock-call t W(q) | try-lock-fail t W(q)
                      | try-lock-call t W(q)       when n <= MAX_RETRY
                      | lock-acquire t H(t,q) | try-lock-success t H(t,q)
                      | wake t H(t,tl)             when q = t :: tl

   This file owes protocol_lib the transition matrix, the
   nonterminals/productions/invariant, and the 7 obligations.  The
   equivalence comes from the library.

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

(** * Grammar side *)

Inductive Nt := Program | U | H (o : tid) (w : list tid) | W (q : list tid).

Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nil  : productions Program nil
| PR_body : productions Program (Se Create :: Sn U :: nil)
(* Unlocked *)
| PU_nil  : productions U nil
| PU_call : forall t, productions U (Se (LockCall t) :: Sn U :: nil)
| PU_tryf : forall t, productions U (Se (TryLockFail t) :: Sn U :: nil)
| PU_tryc : forall t n, Nat.leb n MAX_RETRY = true ->
    productions U (Se (TryLockCall t n) :: Sn U :: nil)
| PU_acq  : forall t, productions U (Se (LockAcquire t) :: Sn (H t nil) :: nil)
| PU_succ : forall t,
    productions U (Se (TryLockSuccess t) :: Sn (H t nil) :: nil)
(* Held o w *)
| PH_nil  : forall o w, productions (H o w) nil
| PH_call : forall o w t,
    productions (H o w) (Se (LockCall t) :: Sn (H o w) :: nil)
| PH_tryf : forall o w t,
    productions (H o w) (Se (TryLockFail t) :: Sn (H o w) :: nil)
| PH_tryc : forall o w t n, Nat.leb n MAX_RETRY = true ->
    productions (H o w) (Se (TryLockCall t n) :: Sn (H o w) :: nil)
| PH_wait : forall o w t,
    productions (H o w) (Se (Wait t) :: Sn (H o (w ++ (t :: nil))) :: nil)
| PH_drop : forall o w,
    productions (H o w) (Se (GuardDrop o) :: Sn (W w) :: nil)
(* Waking q *)
| PW_nil  : forall q, productions (W q) nil
| PW_call : forall q t, productions (W q) (Se (LockCall t) :: Sn (W q) :: nil)
| PW_tryf : forall q t,
    productions (W q) (Se (TryLockFail t) :: Sn (W q) :: nil)
| PW_tryc : forall q t n, Nat.leb n MAX_RETRY = true ->
    productions (W q) (Se (TryLockCall t n) :: Sn (W q) :: nil)
| PW_acq  : forall q t,
    productions (W q) (Se (LockAcquire t) :: Sn (H t q) :: nil)
| PW_succ : forall q t,
    productions (W q) (Se (TryLockSuccess t) :: Sn (H t q) :: nil)
| PW_wake : forall h tl t, Nat.eqb t h = true ->
    productions (W (h :: tl)) (Se (Wake t) :: Sn (H t tl) :: nil).

(* Queue-shaped tables need equality on lists of nats -- only this
   model needs it, so it lives here (registered with [finish_db]). *)
Fixpoint nat_list_eqb (a b : list nat) : bool :=
  match a, b with
  | nil, nil => true
  | x :: xs, y :: ys => Nat.eqb x y && nat_list_eqb xs ys
  | _, _ => false
  end.

Lemma nat_list_eqb_true : forall a b, nat_list_eqb a b = true -> a = b.
Proof.
  induction a as [| x xs IH]; destruct b as [| y ys]; simpl; intros H;
    try discriminate; try reflexivity.
  rewrite Bool.andb_true_iff in H; destruct H as [Hxy Hrest].
  rewrite Nat.eqb_eq in Hxy; subst. apply IH in Hrest; subst. reflexivity.
Qed.

Lemma nat_list_eqb_refl : forall a, nat_list_eqb a a = true.
Proof.
  induction a as [| x xs IH]; simpl; [ reflexivity | ].
  rewrite Nat.eqb_refl; rewrite IH; reflexivity.
Qed.

Hint Resolve nat_list_eqb_true nat_list_eqb_refl : finish_db.
Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | Program, Uninitialized  => true
  | U, Unlocked             => true
  | H o w, Held owner wait  => Nat.eqb o owner && nat_list_eqb w wait
  | W q, Waking queue       => nat_list_eqb q queue
  | _, _                    => false
  end.

(** * The 7 obligations *)

Ltac case_types := case_of State; case_of Event.

Lemma ob_is_error_ok : forall s, is_err s = true <-> s = Error.
Proof. discharge case_types. Qed.

Lemma ob_init_fault_free : Uninitialized <> Error.
Proof. discharge case_types. Qed.

Lemma ob_inv_start : available Program Uninitialized = true.
Proof. reflexivity. Qed.

Lemma ob_prod_ok : forall A beta s,
    productions A beta -> available A s = true ->
    ok Error step available productions s beta.
Proof.
  discharge_prod productions case_types.
  (* Re-establishing [available] at the target nonterminal needs this
     model's own reflexivity lemma -- the library no longer knows the
     data type.  Same shape as buffer's two [available] cleanups. *)
  all: try (rewrite nat_list_eqb_refl; reflexivity).
  (* The [Wake] cell, by hand: [simpl] folded
     [nat_list_eqb (h :: tl) queue] into a match on the queue, and both
     of its conjuncts read [wake_info] -- a match, not an [if], so the
     automation above never saw a guard here. *)
  all: (destruct queue as [| y ys];
        [ simpl in H1; discriminate H1 | ]).
  all: (simpl in H1 |- *;
        destruct (Nat.eqb h y) eqn:Hw;
        [ | simpl in H1; discriminate H1 ]).
  all: finish_goal.
  (* ...including the conjunct the [Wake] split leaves behind. *)
  all: try (rewrite nat_list_eqb_refl; reflexivity).
Qed.

(** [Error] is a sink in this table; [run_from_sink] turns that into
    the recognizer-level fact the completeness proof argues from. *)
Lemma run_from_error : forall tr, run_from step Error tr = Error.
Proof. apply run_from_sink. intros e; reflexivity. Qed.

Definition wellformed (tr : list Event) : Prop :=
  run Uninitialized step tr <> Error.

Lemma ob_word_ok_run : forall tr,
    run Uninitialized step tr <> Error <-> wellformed tr.
Proof. intros tr. unfold wellformed. split; intro H; exact H. Qed.

(** Direction 2.  The chain mirrors mutex_param's, plus one extra step:
    [available] here is a conjunction of two equalities, so it is split
    and both are pushed into the GOAL (not [subst]ed) -- rewriting keeps
    the nonterminal in the state's own variable names, which is what the
    case proofs below then read.

    The queue itself is NOT destructed here: [case_of] must not touch a
    [list tid] (a `repeat` would not terminate), so the one cell that
    needs the queue -- `Waking q, Wake t` -- opens it by hand. *)
(** The two witnesses [gen_of_run] asks for; the library owns the
    induction. *)
Lemma nil_prod : forall A, productions A nil.
Proof. intros A; destruct A; constructor. Qed.

Lemma step_prod : forall A s e,
    available A s = true -> step s e <> Error ->
    exists B, productions A (Se e :: Sn B :: nil) /\
              available B (step s e) = true.
Proof.
  intros A s e Hinv Hne.
  destruct A as [| | o w | q]; case_types;
    cbn [run_from step available] in *;
    (* [available] is a conjunction of two reflected equalities:
       split it, then push both into the goal. *)
    repeat match goal with
           | [ H : _ && _ = true |- _ ] =>
               rewrite Bool.andb_true_iff in H; destruct H
           end;
    repeat match goal with
           | [ H : Nat.eqb ?x ?y = true |- _ ] =>
               rewrite Nat.eqb_eq in H; rewrite H; clear H
           | [ H : nat_list_eqb ?x ?y = true |- _ ] =>
               apply nat_list_eqb_true in H; rewrite H; clear H
           end;
    try discriminate Hinv;
    (* the guards live in [Hne] and in the goal's [step s e] *)
    repeat match goal with
           | [ H : context[if ?b then _ else _] |- _ ] =>
               destruct b eqn:Hb; cbn [run_from step] in *
           | |- context[if ?b then _ else _] =>
               destruct b eqn:Hb; cbn [run_from step] in *
           end;
    try (exfalso; apply Hne; reflexivity).
  - (* Program / Uninitialized / Create *)
    exists U. split; [ exact PR_body | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* U / Unlocked / LockCall *)
    exists U. split; [ exact (PU_call t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* U / Unlocked / LockAcquire *)
    exists (H t nil). split; [ exact (PU_acq t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* U / Unlocked / TryLockCall, within budget *)
    exists U. split; [ exact (PU_tryc t n Hb) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* U / Unlocked / TryLockSuccess *)
    exists (H t nil). split; [ exact (PU_succ t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* U / Unlocked / TryLockFail *)
    exists U. split; [ exact (PU_tryf t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* H owner waiters / Held / LockCall *)
    exists (H owner waiters). split; [ exact (PH_call owner waiters t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* H owner waiters / Held / TryLockCall, within budget *)
    exists (H owner waiters). split;
      [ exact (PH_tryc owner waiters t n Hb) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* H owner waiters / Held / TryLockFail *)
    exists (H owner waiters). split; [ exact (PH_tryf owner waiters t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* H owner waiters / Held / GuardDrop, by the owner: the
       production's terminal is [GuardDrop owner], so the event's id
       has to be aligned first. *)
    pose proof (proj1 (Nat.eqb_eq t owner) Hb) as Hte. rewrite Hte.
    exists (W waiters). split; [ exact (PH_drop owner waiters) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* H owner waiters / Held / Wait *)
    exists (H owner (waiters ++ t :: nil)). split;
      [ exact (PH_wait owner waiters t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* W queue / Waking / LockCall *)
    exists (W queue). split; [ exact (PW_call queue t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* W queue / Waking / LockAcquire (barging keeps the queue) *)
    exists (H t queue). split; [ exact (PW_acq queue t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* W queue / Waking / TryLockCall, within budget *)
    exists (W queue). split; [ exact (PW_tryc queue t n Hb) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* W queue / Waking / TryLockSuccess *)
    exists (H t queue). split; [ exact (PW_succ queue t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* W queue / Waking / TryLockFail *)
    exists (W queue). split; [ exact (PW_tryf queue t) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
  - (* W queue / Waking / Wake t -- the queue decides, and it has to
       be opened by hand: [wake_info] is a match, not an [if], so the
       chain above never saw a guard in this cell. *)
    destruct queue as [| h tl];
      [ simpl in Hne; exfalso; apply Hne; reflexivity | ].
    simpl in *.
    destruct (Nat.eqb t h) eqn:Hb; simpl in *;
      [ | exfalso; apply Hne; reflexivity ].
    exists (H t tl). split; [ exact (PW_wake h tl t Hb) | ].
    simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity.
Qed.

Lemma ob_word_ok_gen : forall tr, wellformed tr -> gen productions Program tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run run_from_error nil_prod step_prod Program Uninitialized); [ reflexivity | exact H ].
Qed.

(** * Assemble the model *)
Definition P : Protocol :=
  {| st := State; ev := Event; nt := Nt;
     init := Uninitialized; fault := Error; next := step;
     is_error := is_err;
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

(** * ============================================================
    What the internal labels buy you
    ============================================================ *)

(* A full contended hand-off, FIFO, with the internal steps visible:
   0 takes the lock; 1 and 2 call, find it held and enqueue themselves;
   0 releases (state -> Waking [1;2]); 1 is woken and takes over; then 2. *)
Example contended_handoff : acceptsp
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1
   :: LockCall 2 :: Wait 2
   :: GuardDrop 0
   :: Wake 1 :: GuardDrop 1
   :: Wake 2 :: GuardDrop 2 :: nil) = true.
Proof. reflexivity. Qed.

Example contended_handoff_generated : genp
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1
   :: LockCall 2 :: Wait 2
   :: GuardDrop 0
   :: Wake 1 :: GuardDrop 1
   :: Wake 2 :: GuardDrop 2 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

(* FIFO order is enforced: 2 is queued behind 1, so waking 2 first fails.
   The API-level alphabet cannot even express this -- it has no Wake. *)
Example wake_out_of_order : acceptsp
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1 :: LockCall 2 :: Wait 2
   :: GuardDrop 0 :: Wake 2 :: nil) = false.
Proof. reflexivity. Qed.

Example wake_out_of_order_not_generated : ~ genp
  (Create :: LockCall 0 :: LockAcquire 0
   :: LockCall 1 :: Wait 1 :: LockCall 2 :: Wait 2
   :: GuardDrop 0 :: Wake 2 :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(* Waking nobody is an error -- nothing was queued. *)
Example wake_without_waiter : acceptsp
  (Create :: LockAcquire 0 :: GuardDrop 0 :: Wake 1 :: nil) = false.
Proof. reflexivity. Qed.

(* Waiting on a free lock is an error: there is nothing to wait for. *)
Example wait_on_free_lock : acceptsp (Create :: Wait 0 :: nil) = false.
Proof. reflexivity. Qed.

(* The numeric guard carries over unchanged. *)
Example retry_over_budget : acceptsp (Create :: TryLockCall 0 11 :: nil) = false.
Proof. reflexivity. Qed.

Example retry_at_budget : acceptsp (Create :: TryLockCall 0 10 :: nil) = true.
Proof. reflexivity. Qed.
