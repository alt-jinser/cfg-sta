(* Parameterized Mutex protocol, on top of protocol_lib.

   Two additions over mutex_grammar.v:

   1. IDENTITY.  Events carry a thread id and `Held` carries its owner, so
      the state space {Uninitialized} + {Unlocked} + {Held t | t : nat} +
      {Error} is INFINITE.  It is no longer a finite automaton -- which
      is why the grammar needs a *parameterized nonterminal* H(o) and a
      regular language will not do.

   2. NUMERIC CONSTRAINT.  TryLockCall t n is legal only when
      n <= MAX_RETRY (literally "参数 > 10").  The guard sits on the
      production, not in the alphabet.

       Program -> epsilon | Create U

       U    -> epsilon
             | LockCall(t) U | TryLockFail(t) U
             | TryLockCall(t,n) U         when n <= MAX_RETRY
             | LockAcquire(t) H(t) | TryLockSuccess(t) H(t)

       H(o) -> epsilon
             | LockCall(t) H(o) | TryLockFail(t) H(o)
             | TryLockCall(t,n) H(o)      when n <= MAX_RETRY
             | GuardDrop(o) U             <-- identity match

   This file owes protocol_lib only the transition matrix, the
   nonterminals/productions/invariant, and the 7 obligations.  The
   equivalence comes from the library.

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile mutex_param.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
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

(** * Grammar side *)

Inductive Nt := Program | U | H (owner : tid).

Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nil  : productions Program nil
| PR_body : productions Program (Se Create :: Sn U :: nil)
| PU_nil  : productions U nil
| PU_call : forall t, productions U (Se (LockCall t) :: Sn U :: nil)
| PU_tryf : forall t, productions U (Se (TryLockFail t) :: Sn U :: nil)
| PU_tryc : forall t n, Nat.leb n MAX_RETRY = true ->
    productions U (Se (TryLockCall t n) :: Sn U :: nil)
| PU_acq  : forall t, productions U (Se (LockAcquire t) :: Sn (H t) :: nil)
| PU_succ : forall t, productions U (Se (TryLockSuccess t) :: Sn (H t) :: nil)
| PH_nil  : forall o, productions (H o) nil
| PH_call : forall o t, productions (H o) (Se (LockCall t) :: Sn (H o) :: nil)
| PH_tryf : forall o t, productions (H o) (Se (TryLockFail t) :: Sn (H o) :: nil)
| PH_tryc : forall o t n, Nat.leb n MAX_RETRY = true ->
    productions (H o) (Se (TryLockCall t n) :: Sn (H o) :: nil)
| PH_drop : forall o, productions (H o) (Se (GuardDrop o) :: Sn U :: nil).

(** The invariant is PRECISE about the owner: [H o] is available in
    [Held o'] only when [o = o'], because the production [H(o) ->
    GuardDrop(o) U] would otherwise derive a release the machine
    rejects. *)
Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | Program, Uninitialized => true
  | U, Unlocked            => true
  | H o, Held o'           => Nat.eqb o o'
  | _, _                   => false
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
Proof. discharge_prod productions case_types. Qed.

(** [Error] really is a sink -- used below to argue from a faulting
    run.  Proved here rather than carried by the contract: only the
    completeness proof needs it, and it is a fact about this table. *)
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

(** Direction 2: a safe run from an available nonterminal is derivable
    from it.  Same shape as mutex_grammar's, plus two guard splits (the
    retry budget and the owner match) which the chain peels off before
    the cases are read -- ten cases survive, one per real transition. *)
Lemma gen_of_run : forall A s tr,
    available A s = true -> run_from step s tr <> Error ->
    derives productions (Sn A :: nil) tr.
Proof.
  intros A s tr. revert A s.
  induction tr as [| e tr IH]; intros A s Hinv Hrun.
  - destruct A as [| | o].
    + exact (derives_sn productions Program nil nil PR_nil
               (derives_nil productions)).
    + exact (derives_sn productions U nil nil PU_nil
               (derives_nil productions)).
    + exact (derives_sn productions (H o) nil nil (PH_nil o)
               (derives_nil productions)).
  - simpl in Hrun.
    assert (Hne : step s e <> Error).
    { intro Hf. rewrite Hf in Hrun. rewrite run_from_error in Hrun.
      exact (Hrun eq_refl). }
    destruct A as [| | o]; case_types; simpl in *;
      try (rewrite Nat.eqb_eq in Hinv; subst);
      try discriminate Hinv;
      (* The guards live in Hrun (the goal is a [derives] statement, it
         has no [if]), so the split has to look at hypotheses too. *)
      repeat match goal with
             | [ H : context[if ?b then _ else _] |- _ ] =>
                 destruct b eqn:Hb; simpl in *
             | |- context[if ?b then _ else _] =>
                 destruct b eqn:Hb; simpl in *
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
                (Se (LockAcquire t) :: Sn (H t) :: nil)
                (LockAcquire t :: tr) (PU_acq t) _).
      apply derives_se.
      apply (IH (H t) (Held t)); [ simpl; apply Nat.eqb_refl | exact Hrun ].
    + (* U / Unlocked / TryLockCall, within budget *)
      refine (derives_sn productions U
                (Se (TryLockCall t n) :: Sn U :: nil)
                (TryLockCall t n :: tr) (PU_tryc t n Hb) _).
      apply derives_se.
      apply (IH U Unlocked); [ reflexivity | exact Hrun ].
    + (* U / Unlocked / TryLockSuccess *)
      refine (derives_sn productions U
                (Se (TryLockSuccess t) :: Sn (H t) :: nil)
                (TryLockSuccess t :: tr) (PU_succ t) _).
      apply derives_se.
      apply (IH (H t) (Held t)); [ simpl; apply Nat.eqb_refl | exact Hrun ].
    + (* U / Unlocked / TryLockFail *)
      refine (derives_sn productions U (Se (TryLockFail t) :: Sn U :: nil)
                (TryLockFail t :: tr) (PU_tryf t) _).
      apply derives_se.
      apply (IH U Unlocked); [ reflexivity | exact Hrun ].
    + (* H owner / Held owner / LockCall *)
      refine (derives_sn productions (H owner)
                (Se (LockCall t) :: Sn (H owner) :: nil)
                (LockCall t :: tr) (PH_call owner t) _).
      apply derives_se.
      apply (IH (H owner) (Held owner)); [ simpl; apply Nat.eqb_refl | exact Hrun ].
    + (* H owner / Held owner / TryLockCall, within budget *)
      refine (derives_sn productions (H owner)
                (Se (TryLockCall t n) :: Sn (H owner) :: nil)
                (TryLockCall t n :: tr) (PH_tryc owner t n Hb) _).
      apply derives_se.
      apply (IH (H owner) (Held owner)); [ simpl; apply Nat.eqb_refl | exact Hrun ].
    + (* H owner / Held owner / TryLockFail *)
      refine (derives_sn productions (H owner)
                (Se (TryLockFail t) :: Sn (H owner) :: nil)
                (TryLockFail t :: tr) (PH_tryf owner t) _).
      apply derives_se.
      apply (IH (H owner) (Held owner)); [ simpl; apply Nat.eqb_refl | exact Hrun ].
    + (* H owner / Held owner / GuardDrop owner *)
      pose proof (proj1 (Nat.eqb_eq t owner) Hb) as Hte.
      rewrite Hte.
      refine (derives_sn productions (H owner)
                (Se (GuardDrop owner) :: Sn U :: nil)
                (GuardDrop owner :: tr) (PH_drop owner) _).
      apply derives_se.
      apply (IH U Unlocked); [ reflexivity | exact Hrun ].
Qed.

Lemma ob_word_ok_gen : forall tr, wellformed tr -> gen productions Program tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run Program Uninitialized); [ reflexivity | exact H ].
Qed.

(** * Assemble the model. *)
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
    What the two new parameters actually buy you
    ============================================================ *)

(* --- the numeric guard, literally "参数 > 10" --- *)
Example retry_at_budget : acceptsp (Create :: TryLockCall 0 10 :: nil) = true.
Proof. reflexivity. Qed.

Example retry_over_budget : acceptsp (Create :: TryLockCall 0 11 :: nil) = false.
Proof. reflexivity. Qed.

Example retry_over_budget_not_generated : ~ genp (Create :: TryLockCall 0 11 :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(* --- the identity guard: releasing someone else's lock is an error --- *)
Example drop_by_other_rejected :
  acceptsp (Create :: LockAcquire 0 :: GuardDrop 1 :: nil) = false.
Proof. reflexivity. Qed.

Example drop_by_owner_accepted :
  acceptsp (Create :: LockAcquire 0 :: GuardDrop 0 :: nil) = true.
Proof. reflexivity. Qed.

(* --- and the grammar agrees in both directions --- *)
Example gen_drop_by_owner : genp (Create :: LockAcquire 0 :: GuardDrop 0 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example gen_retry_within_budget : genp (Create :: TryLockCall 7 3 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example gen_retry_over_budget : ~ genp (Create :: TryLockCall 7 11 :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(** The identity constraint cannot be expressed over a finite alphabet:
    the recognizer has infinitely many states [Held t].  Two traces that
    differ only in the owner are accepted or rejected differently, and no
    finite automaton over {create, lock, unlock, ...} can tell them apart. *)
Example owners_are_distinguished :
    acceptsp (Create :: LockAcquire 0 :: GuardDrop 0 :: nil) = true
 /\ acceptsp (Create :: LockAcquire 0 :: GuardDrop 1 :: nil) = false.
Proof. split; reflexivity. Qed.
