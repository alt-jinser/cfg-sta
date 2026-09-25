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

Definition Trace := list Event.

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
Qed.

(** [Error] really is a sink -- used by the completeness proof below to
    argue from a faulting run.  A fact about this table, so it lives
    here rather than in the contract. *)
Lemma step_error_sink : forall e, step Error e = Error.
Proof. intros e; reflexivity. Qed.

Lemma run_from_error : forall tr, run_from step Error tr = Error.
Proof.
  induction tr as [| e tr IH]; [ reflexivity | ].
  change (run_from step (step Error e) tr = Error).
  rewrite step_error_sink. exact IH.
Qed.

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
Lemma gen_of_run : forall A s tr,
    available A s = true -> run_from step s tr <> Error ->
    derives productions (Sn A :: nil) tr.
Proof.
  intros A s tr. revert A s.
  induction tr as [| e tr IH]; intros A s Hinv Hrun.
  - destruct A as [| | o w | q].
    + exact (derives_sn productions Program nil nil PR_nil
               (derives_nil productions)).
    + exact (derives_sn productions U nil nil PU_nil
               (derives_nil productions)).
    + exact (derives_sn productions (H o w) nil nil (PH_nil o w)
               (derives_nil productions)).
    + exact (derives_sn productions (W q) nil nil (PW_nil q)
               (derives_nil productions)).
  - cbn [run_from step] in Hrun.
    assert (Hne : step s e <> Error).
    { intro Hf. rewrite Hf in Hrun. rewrite run_from_error in Hrun.
      exact (Hrun eq_refl). }
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
      (* the guards live in [Hrun] -- the goal is a [derives] statement
         and has no [if] -- so the split must look at hypotheses too *)
      repeat match goal with
             | [ H : context[if ?b then _ else _] |- _ ] =>
                 destruct b eqn:Hb; cbn [run_from step] in *
             | |- context[if ?b then _ else _] =>
                 destruct b eqn:Hb; cbn [run_from step] in *
             end;
      try (exfalso; apply Hrun; apply run_from_error).
    + (* Program / Uninitialized / Create *)
      refine (derives_sn productions Program (Se Create :: Sn U :: nil)
                (Create :: tr) PR_body _).
      apply derives_se.
      apply (IH U Unlocked); [ reflexivity | exact Hrun ].
    + (* U / Unlocked / LockCall *)
      refine (derives_sn productions U (Se (LockCall t) :: Sn U :: nil)
                (LockCall t :: tr) (PU_call t) _).
      apply derives_se.
      apply (IH U Unlocked); [ reflexivity | exact Hrun ].
    + (* U / Unlocked / LockAcquire *)
      refine (derives_sn productions U
                (Se (LockAcquire t) :: Sn (H t nil) :: nil)
                (LockAcquire t :: tr) (PU_acq t) _).
      apply derives_se.
      apply (IH (H t nil) (Held t nil));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* U / Unlocked / TryLockCall, within budget *)
      refine (derives_sn productions U
                (Se (TryLockCall t n) :: Sn U :: nil)
                (TryLockCall t n :: tr) (PU_tryc t n Hb) _).
      apply derives_se.
      apply (IH U Unlocked); [ reflexivity | exact Hrun ].
    + (* U / Unlocked / TryLockSuccess *)
      refine (derives_sn productions U
                (Se (TryLockSuccess t) :: Sn (H t nil) :: nil)
                (TryLockSuccess t :: tr) (PU_succ t) _).
      apply derives_se.
      apply (IH (H t nil) (Held t nil));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* U / Unlocked / TryLockFail *)
      refine (derives_sn productions U (Se (TryLockFail t) :: Sn U :: nil)
                (TryLockFail t :: tr) (PU_tryf t) _).
      apply derives_se.
      apply (IH U Unlocked); [ reflexivity | exact Hrun ].
    + (* H owner waiters / Held / LockCall *)
      refine (derives_sn productions (H owner waiters)
                (Se (LockCall t) :: Sn (H owner waiters) :: nil)
                (LockCall t :: tr) (PH_call owner waiters t) _).
      apply derives_se.
      apply (IH (H owner waiters) (Held owner waiters));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* H owner waiters / Held / TryLockCall, within budget *)
      refine (derives_sn productions (H owner waiters)
                (Se (TryLockCall t n) :: Sn (H owner waiters) :: nil)
                (TryLockCall t n :: tr) (PH_tryc owner waiters t n Hb) _).
      apply derives_se.
      apply (IH (H owner waiters) (Held owner waiters));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* H owner waiters / Held / TryLockFail *)
      refine (derives_sn productions (H owner waiters)
                (Se (TryLockFail t) :: Sn (H owner waiters) :: nil)
                (TryLockFail t :: tr) (PH_tryf owner waiters t) _).
      apply derives_se.
      apply (IH (H owner waiters) (Held owner waiters));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* H owner waiters / Held / GuardDrop, by the owner.
         The production's terminal is [GuardDrop owner], so the event's
         thread id has to be aligned with the owner first. *)
      rewrite Nat.eqb_eq in Hb. rewrite Hb.
      refine (derives_sn productions (H owner waiters)
                (Se (GuardDrop owner) :: Sn (W waiters) :: nil)
                (GuardDrop owner :: tr) (PH_drop owner waiters) _).
      apply derives_se.
      apply (IH (W waiters) (Waking waiters));
        [ simpl; rewrite ?nat_list_eqb_refl; reflexivity | exact Hrun ].
    + (* H owner waiters / Held / Wait *)
      refine (derives_sn productions (H owner waiters)
                (Se (Wait t) :: Sn (H owner (waiters ++ (t :: nil))) :: nil)
                (Wait t :: tr) (PH_wait owner waiters t) _).
      apply derives_se.
      apply (IH (H owner (waiters ++ (t :: nil)))
                (Held owner (waiters ++ (t :: nil))));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* W queue / Waking / LockCall *)
      refine (derives_sn productions (W queue)
                (Se (LockCall t) :: Sn (W queue) :: nil)
                (LockCall t :: tr) (PW_call queue t) _).
      apply derives_se.
      apply (IH (W queue) (Waking queue));
        [ simpl; rewrite ?nat_list_eqb_refl; reflexivity | exact Hrun ].
    + (* W queue / Waking / LockAcquire (barging keeps the queue) *)
      refine (derives_sn productions (W queue)
                (Se (LockAcquire t) :: Sn (H t queue) :: nil)
                (LockAcquire t :: tr) (PW_acq queue t) _).
      apply derives_se.
      apply (IH (H t queue) (Held t queue));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* W queue / Waking / TryLockCall, within budget *)
      refine (derives_sn productions (W queue)
                (Se (TryLockCall t n) :: Sn (W queue) :: nil)
                (TryLockCall t n :: tr) (PW_tryc queue t n Hb) _).
      apply derives_se.
      apply (IH (W queue) (Waking queue));
        [ simpl; rewrite ?nat_list_eqb_refl; reflexivity | exact Hrun ].
    + (* W queue / Waking / TryLockSuccess *)
      refine (derives_sn productions (W queue)
                (Se (TryLockSuccess t) :: Sn (H t queue) :: nil)
                (TryLockSuccess t :: tr) (PW_succ queue t) _).
      apply derives_se.
      apply (IH (H t queue) (Held t queue));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
    + (* W queue / Waking / TryLockFail *)
      refine (derives_sn productions (W queue)
                (Se (TryLockFail t) :: Sn (W queue) :: nil)
                (TryLockFail t :: tr) (PW_tryf queue t) _).
      apply derives_se.
      apply (IH (W queue) (Waking queue));
        [ simpl; rewrite ?nat_list_eqb_refl; reflexivity | exact Hrun ].
    + (* W queue / Waking / Wake t -- the queue decides, and it has to be
         opened by hand: [wake_info] is a match, not an [if], so the
         chain above never saw a guard in this cell. *)
      destruct queue as [| h tl];
        [ simpl in Hrun; exfalso; apply Hrun; apply run_from_error | ].
      simpl in Hrun.
      destruct (Nat.eqb t h) eqn:Hb; simpl in Hrun;
        [ | exfalso; apply Hrun; apply run_from_error ].
      refine (derives_sn productions (W (h :: tl))
                (Se (Wake t) :: Sn (H t tl) :: nil)
                (Wake t :: tr) (PW_wake h tl t Hb) _).
      apply derives_se.
      apply (IH (H t tl) (Held t tl));
        [ simpl; rewrite ?Nat.eqb_refl, ?nat_list_eqb_refl; reflexivity
        | exact Hrun ].
Qed.

Lemma ob_word_ok_gen : forall tr, wellformed tr -> gen productions Program tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run Program Uninitialized); [ reflexivity | exact H ].
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
