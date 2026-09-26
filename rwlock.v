(* rwlock.v -- read-write lock discipline (v1), on top of protocol_lib.

   Provenance: ostd/src/sync/rwlock.rs.  Four guard-level events; the
   writer/reader exclusion is that file's own core invariant:

       &&& !(active_writer && (active_read_guards +
             if active_upgrade_guard { 1int } else { 0 }) > 0)

   NO protocol spec exists for rwlock -- ostd/specs/sync/ holds only
   mutex_protocol.rs, rcu/ and the mutex examples.  Both sides of the
   equivalence are therefore derived from the implementation: the
   table from its control flow, the grammar from the API docs and the
   Verus invariant above (separate artifacts, same file).  That is
   weaker independence than mutex_grammar has (table from mutex.rkt,
   grammar from the discipline prose) and is exactly the open question
   1 of PIPELINE.md -- read it before trusting this theorem.

   Modelling choice, stated because it changes what [accepts] means:
   here [fault] = the call cannot complete immediately (contention) or
   would break the invariant.  For mutex the error state is API misuse;
   for rwlock the equivalent "bad step" is a call that has to wait, so
   [accepts] means "this trace drives the lock without ever waiting".
   The API docs are explicit that waiting carries no ordering guarantee
   ("There is no guarantee for the order in which other readers or
   writers waiting simultaneously will obtain the lock"), so -- unlike
   the wait-queue mutex -- there is NO queue in this protocol.

   Scope (v1): upgrade / upreader machinery, try_read / try_write, and
   MAX_READER overflow are out of scope, the way grace periods are out
   of scope for rcu.v.  The reader count is idealized to [nat] exactly
   as rcu.v idealizes RCU_READER_SLOTS = 1 << 60.

   ------------------------------------------------------------
   PREDICTION, written from the transition semantics BEFORE any
   grammar exists (this file's first commit is the pre-registration;
   the verdict is at the end of this header).

   Applied to the three-step criterion of PIPELINE.md:

   1. Does [next] inspect unbounded data to decide a step?  YES -- the
      reader count (kept in READER bits, bounded by MAX_READER in the
      code, idealized to [nat]).  So the count must enter the grammar
      somehow.
   2. Stack-like?  The read/drop discipline is a pairing discipline
      with no identities (a pure counter), and there is no queue (see
      the API quote above).  A counter is expressible both ways:
      nesting, as rcu.v does, or a nonterminal parameter.
   3. Both work, so prefer the right-linear one -- it gets obligation 7
      from the library.

   PREDICTED MODEL SHAPE: modes {free, write} plus one
   count-parameterized nonterminal for readers; every production
   right-linear (one terminal, one nonterminal); obligation 4
   mechanical; obligation 7 discharged by gen_of_run's two witnesses;
   no Z-valued net measure (unlike rcu.v).

   VERDICT (written after the model compiled): CONFIRMED at the level
   the criterion claims.  The model is exactly the predicted shape --
   {RwRead n, RwWrite}, every production right-linear, obligation 4
   mechanical, obligation 7 the two witnesses handed to the library's
   gen_of_run, and no net measure (no Z, no reach_positive-style
   lemma, unlike rcu.v).  Two details the criterion does not cover,
   both about HOW the count is split rather than WHETHER it enters the
   grammar: the transition matrix has to be written nested, because a
   flat matrix lets the `Readers` row's split on [n] leak into the
   [Read] arm and leave a residual match that [cbn] cannot collapse;
   and step_prod opens [n] by hand in the two cells that need it, the
   way wait-queue opens the queue.

   Compiles with Rocq 9.1.1:  rocq compile rwlock.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.
Open Scope bool_scope.

(** * STA side *)

Inductive State : Type :=
| Readers (n : nat)        (* [Readers 0] is the free lock *)
| Writer
| Error.

Inductive Event : Type :=
| Read
| ReadDrop
| Write
| WriteDrop.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** The transition matrix.  [Error] stands for "the call cannot
    complete immediately" -- a writer in the way of [read], any reader
    or writer in the way of [write], or a release that no guard
    accounts for.

    The two count cases are written as PATTERNS rather than as [if]s
    on [n], deliberately: in [prod_ok] the availability equation
    substitutes the state's count with the nonterminal's, leaving a
    structurally [S _]-shaped state that fires the pattern directly,
    whereas an [if] would split the goal before that equation can be
    used.  [step_prod] pays for it by opening [n] in the two affected
    cells -- same trade, and the same place wait-queue opens the
    queue. *)
Definition step (s : State) (e : Event) : State :=
  match s with
  | Readers n =>
      match e with
      | Read => Readers (S n)
      (* release a read guard: never below zero *)
      | ReadDrop => match n with 0 => Error | S m => Readers m end
      (* write: exclusive -- no reader, no writer *)
      | Write => match n with 0 => Writer | _ => Error end
      | WriteDrop => Error
      end
  | Writer =>
      match e with
      | Read | ReadDrop | Write => Error
      | WriteDrop => Readers 0
      end
  | Error => Error
  end.

(** * CFG side *)

Inductive Nt : Type :=
| RwRead (n : nat)     (* [RwRead 0] is the free lock *)
| RwWrite.

(** Productions are right-linear, and their guards are structural:
    [PR_drop] only applies to [RwRead (S n)], so an underflowing drop
    cannot be derived at all -- where buffer.v has to carry that guard
    as a side condition on the production. *)
Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nilR : forall n, productions (RwRead n) nil
| PR_nilW : productions RwWrite nil
| PR_read : forall n,
    productions (RwRead n) (Se Read :: Sn (RwRead (S n)) :: nil)
| PR_drop : forall n,
    productions (RwRead (S n)) (Se ReadDrop :: Sn (RwRead n) :: nil)
| PR_write : productions (RwRead 0) (Se Write :: Sn RwWrite :: nil)
| PR_wdrop : productions RwWrite (Se WriteDrop :: Sn (RwRead 0) :: nil).

Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | RwRead n, Readers m => Nat.eqb n m
  | RwWrite, Writer     => true
  | _, _                => false
  end.

(** * The 7 obligations *)

Ltac case_types := case_of State; case_of Event.

Lemma ob_is_error_ok : forall s, is_err s = true <-> s = Error.
Proof. discharge case_types. Qed.

Lemma ob_init_fault_free : Readers 0 <> Error.
Proof. discriminate. Qed.

Lemma ob_inv_start : available (RwRead 0) (Readers 0) = true.
Proof. reflexivity. Qed.

Lemma ob_prod_ok : forall A beta s,
    productions A beta -> available A s = true ->
    ok Error step available productions s beta.
Proof.
  discharge_prod productions case_types.
  (* [simpl] folds [Nat.eqb (S n) n0] into a match on the state's count,
     which the closer cannot use; open it once (the PR_drop cell). *)
  all: (destruct n0 as [| n1]; [ simpl in H0; discriminate H0 | ]).
  all: finish_goal.
Qed.

Lemma run_from_error : forall tr, run_from step Error tr = Error.
Proof. apply run_from_sink. intros e; reflexivity. Qed.

Definition wellformed (tr : list Event) : Prop :=
  run (Readers 0) step tr <> Error.

Lemma ob_word_ok_run : forall tr,
    run (Readers 0) step tr <> Error <-> wellformed tr.
Proof. intros tr. unfold wellformed. split; intro H; exact H. Qed.

(** The two witnesses [gen_of_run] asks for. *)
Lemma nil_prod : forall A, productions A nil.
Proof. intros A; destruct A; constructor. Qed.

Lemma step_prod : forall A s e,
    available A s = true -> step s e <> Error ->
    exists B, productions A (Se e :: Sn B :: nil) /\
              available B (step s e) = true.
Proof.
  intros A s e Hinv Hne.
  destruct A as [k|]; case_types; cbn [run_from step available] in *;
    repeat match goal with
           | [ H : Nat.eqb ?x ?y = true |- _ ] =>
               rewrite Nat.eqb_eq in H; rewrite H; clear H
           end;
    try discriminate Hinv;
    try (exfalso; apply Hne; reflexivity).
  - (* readers n / Read: one more reader *)
    exists (RwRead (S n)). split; [ exact (PR_read n) | ].
    simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* readers n / ReadDrop -- the table matches on [n], so open it
       once; the grammar is structural here instead ([RwRead (S m)]). *)
    destruct n as [| m].
    + exfalso; simpl in Hne; apply Hne; reflexivity.
    + exists (RwRead m). split; [ exact (PR_drop m) | ].
      simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* readers n / Write -- exclusive, so n = 0 *)
    destruct n as [| m].
    + exists RwWrite. split; [ exact PR_write | ].
      simpl; rewrite ?Nat.eqb_refl; reflexivity.
    + exfalso; simpl in Hne; apply Hne; reflexivity.
  - (* writer / WriteDrop *)
    exists (RwRead 0). split; [ exact PR_wdrop | ].
    simpl; rewrite ?Nat.eqb_refl; reflexivity.
Qed.

Lemma ob_word_ok_gen : forall tr,
    wellformed tr -> gen productions (RwRead 0) tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run run_from_error nil_prod step_prod
           (RwRead 0) (Readers 0)); [ reflexivity | exact H ].
Qed.

(** * Assemble the model *)

Definition P : Protocol :=
  {| st := State; ev := Event; nt := Nt;
     init := Readers 0; fault := Error; next := step;
     is_error := is_err;
     start := RwRead 0; prod := productions; inv := available;

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

(** * What the model says *)

Example two_readers : acceptsp (Read :: Read :: nil) = true.
Proof. reflexivity. Qed.

Example writer_while_reading : acceptsp (Read :: Write :: nil) = false.
Proof. reflexivity. Qed.

Example reader_while_writing : acceptsp (Write :: Read :: nil) = false.
Proof. reflexivity. Qed.

Example release_without_guard : acceptsp (ReadDrop :: nil) = false.
Proof. reflexivity. Qed.

Example balanced_generated :
    genp (Read :: Read :: ReadDrop :: ReadDrop :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example contention_not_generated : ~ genp (Read :: Write :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.
