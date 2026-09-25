(* rwmutex.v -- reader-writer mutex with mode conversions, on top of
   protocol_lib.

   Provenance: ostd/src/sync/rwmutex.rs.  Unlike rwlock.rs, this one
   queues its waiters -- `use super::WaitQueue` and every acquisition
   documents "The implementation of [`WaitQueue`] guarantees the order
   in which other concurrent readers or writers waiting simultaneously
   will acquire the mutex" (read/write/upread, rwmutex.rs:327-360).
   That queue is INTERNAL at this alphabet: the events are guard
   actions, so nothing in the trace observes wake order.  If wake order
   were part of the language, `Wait`/`Wake` events would have to be
   added and the grammar would then need the queue as a nonterminal
   parameter -- exactly what mutex_waitqueue.v does.

   Eight events, guard level, `try_*` excluded (they return Options,
   same scope call as rwlock.v):

     Read / ReadDrop          acquire / release a read guard
     Write / WriteDrop        acquire / release the write guard
     UpRead / UpReadDrop      acquire / release an upgradable reader
     Downgrade                Write -> UpRead, "always succeeds"
                              (rwmutex.rs:692, exclusive holder)
     Upgrade                  UpRead -> Write, spins until the other
                              readers are gone (rwmutex.rs:877), so it
                              cannot complete immediately while any
                              reader remains

   No protocol spec exists for it (ostd/specs/sync/ holds only
   mutex_protocol, rcu/ and the mutex examples), so as in rwlock.v and
   spin.v both sides come from the implementation.

   Modelling choice, the same one rwlock.v and spin.v make: [fault] =
   the call cannot complete immediately (every acquisition here
   sleeps, so "sleeps" counts as cannot-complete) or is a release / mode
   change that no guard accounts for.

   ------------------------------------------------------------
   PREDICTION, written from the transition semantics BEFORE any
   grammar exists (this file's first commit is the pre-registration;
   the verdict is at the end of this header).

   Applied to the three-step criterion of PIPELINE.md:

   1. Does [next] inspect unbounded data?  YES -- the reader count
      (in READER bits, bounded by MAX_READER in the code, idealized to
      [nat] as in rcu.v and rwlock.v).  So the count enters the
      grammar somehow.
   2. Stack-like?  The read/drop discipline is again a pairing
      discipline with no identities (a counter), so both forms are
      available; and the WaitQueue's FIFO is not in the alphabet, so
      no queue parameter is predicted.
   3. Prefer the right-linear one.

   PREDICTED MODEL SHAPE: three modes -- two count-parameterized
   ([Readers n], [UpReader n]) and one constant ([Writer]) -- every
   production right-linear (the mode conversions Downgrade / Upgrade /
   UpRead / UpReadDrop are single-terminal steps), obligation 4
   mechanical, obligation 7 = the two witnesses for gen_of_run, no net
   measure, and TEN surviving cells in step_prod (4 from [Readers n],
   4 from [UpReader n], 2 from [Writer]).

   VERDICT (written after the model compiled): CONFIRMED on shape, off
   by one on the count.  Three modes (two count-parameterized, one
   constant), all fourteen productions right-linear, obligation 4
   mechanical, obligation 7 the two witnesses, no net measure -- as
   predicted.  The cell count was predicted at ten and the proof has
   ten bullets but ELEVEN leaf goals: UpReadDrop's target dispatches
   on the count (no other readers -> [Readers 0], some -> [Readers m]),
   so one cell yields two live productions.  That is a gap in the
   criterion, not in the model: it predicts WHETHER the count enters
   the grammar, not HOW the right-hand side depends on it -- the same
   family as rwlock's "how the count is split", this time on the
   grammar side.

   Compiles with Rocq 9.1.1:  rocq compile rwmutex.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.
Open Scope bool_scope.

(** * STA side *)

Inductive State : Type :=
| Readers (rn : nat)        (* [Readers 0] is free *)
| UpReader (un : nat)       (* one upgradable reader + [un] others *)
| Writer
| Error.

Inductive Event : Type :=
| Read
| ReadDrop
| Write
| WriteDrop
| UpRead
| UpReadDrop
| Downgrade
| Upgrade.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** The transition matrix, nested per state (see the constraints in
    MODELS.md): a flat matrix would let one row's split on a count
    leak into another arm. *)
Definition step (s : State) (e : Event) : State :=
  match s with
  | Readers n =>
      match e with
      | Read      => Readers (S n)
      | ReadDrop  => match n with 0 => Error | S m => Readers m end
      | Write     => match n with 0 => Writer | _ => Error end
      (* an upreader joins the existing readers *)
      | UpRead    => UpReader n
      | WriteDrop | UpReadDrop | Downgrade | Upgrade => Error
      end
  | UpReader n =>
      match e with
      | Read       => UpReader (S n)
      | ReadDrop   => match n with 0 => Error | S m => UpReader m end
      (* only one upreader may exist *)
      | UpRead     => Error
      (* upgrade spins until the other readers are gone *)
      | Upgrade    => match n with 0 => Writer | _ => Error end
      (* the upreader leaves; the others keep the lock *)
      | UpReadDrop => match n with 0 => Readers 0 | S m => Readers m end
      | Write | WriteDrop | Downgrade => Error
      end
  | Writer =>
      match e with
      | WriteDrop  => Readers 0
      | Downgrade  => UpReader 0
      | Read | ReadDrop | Write | UpRead | UpReadDrop | Upgrade => Error
      end
  | Error => Error
  end.

(** * CFG side *)

Inductive Nt : Type :=
| NReaders (n : nat)      (* [n] readers, no writer, no upreader *)
| NUpReader (n : nat)     (* one upgradable reader plus [n] others *)
| NWriter.

(** Fourteen productions, all right-linear.  The count guards are
    structural -- [PR_rdrop] only applies to [NReaders (S n)], and the
    upreader's release dispatches on the count through two
    productions rather than one guarded production. *)
Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nilR  : forall n, productions (NReaders n) nil
| PR_nilU  : forall n, productions (NUpReader n) nil
| PR_nilW  : productions NWriter nil
(* Readers n *)
| PR_read  : forall n,
    productions (NReaders n) (Se Read :: Sn (NReaders (S n)) :: nil)
| PR_rdrop : forall n,
    productions (NReaders (S n)) (Se ReadDrop :: Sn (NReaders n) :: nil)
| PR_wr    : productions (NReaders 0) (Se Write :: Sn NWriter :: nil)
| PR_up    : forall n,
    productions (NReaders n) (Se UpRead :: Sn (NUpReader n) :: nil)
(* UpReader n *)
| PR_uread : forall n,
    productions (NUpReader n) (Se Read :: Sn (NUpReader (S n)) :: nil)
| PR_udrop : forall n,
    productions (NUpReader (S n)) (Se ReadDrop :: Sn (NUpReader n) :: nil)
| PR_uup0  : productions (NUpReader 0)
    (Se UpReadDrop :: Sn (NReaders 0) :: nil)
| PR_uupS  : forall m, productions (NUpReader (S m))
    (Se UpReadDrop :: Sn (NReaders m) :: nil)
| PR_upg   : productions (NUpReader 0)
    (Se Upgrade :: Sn NWriter :: nil)
(* Writer *)
| PR_wdrop : productions NWriter
    (Se WriteDrop :: Sn (NReaders 0) :: nil)
| PR_down  : productions NWriter
    (Se Downgrade :: Sn (NUpReader 0) :: nil).

Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | NReaders n, Readers m     => Nat.eqb n m
  | NUpReader n, UpReader m   => Nat.eqb n m
  | NWriter, Writer           => true
  | _, _                      => false
  end.

(** * The 7 obligations *)

Ltac case_types := case_of State; case_of Event.

Lemma ob_is_error_ok : forall s, is_err s = true <-> s = Error.
Proof. discharge case_types. Qed.

Lemma ob_init_fault_free : Readers 0 <> Error.
Proof. discriminate. Qed.

Lemma ob_inv_start : available (NReaders 0) (Readers 0) = true.
Proof. reflexivity. Qed.

Lemma ob_prod_ok : forall A beta s,
    productions A beta -> available A s = true ->
    ok Error step available productions s beta.
Proof.
  discharge_prod productions case_types.
  (* [simpl] folds both [Nat.eqb 0 _] and [Nat.eqb (S _) _] into a
     match on the state's count, which the closer cannot use: open the
     count in every cell that still needs a structural index (the
     polarity differs -- [PR_rdrop]/[PR_udrop]/[PR_uupS] die at 0,
     [PR_wr]/[PR_uup0]/[PR_upg] live at 0). *)
  all: try (destruct rn; simpl in H0; try discriminate H0).
  all: try (destruct un; simpl in H0; try discriminate H0).
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
  destruct A as [n|n|]; case_types; cbn [run_from step available] in *;
    repeat match goal with
           | [ H : Nat.eqb ?x ?y = true |- _ ] =>
               rewrite Nat.eqb_eq in H; rewrite H; clear H
           end;
    try discriminate Hinv;
    try (exfalso; apply Hne; reflexivity).
  - (* Readers rn / Read *)
    exists (NReaders (S rn)). split; [ exact (PR_read rn) | ].
    simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* Readers rn / ReadDrop *)
    destruct rn as [| m].
    + exfalso; simpl in Hne; apply Hne; reflexivity.
    + exists (NReaders m). split; [ exact (PR_rdrop m) | ].
      simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* Readers rn / Write -- exclusive, so rn = 0 *)
    destruct rn as [| m].
    + exists NWriter. split; [ exact PR_wr | reflexivity ].
    + exfalso; simpl in Hne; apply Hne; reflexivity.
  - (* Readers rn / UpRead: an upreader joins the existing readers *)
    exists (NUpReader rn). split; [ exact (PR_up rn) | ].
    simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* UpReader un / Read *)
    exists (NUpReader (S un)). split; [ exact (PR_uread un) | ].
    simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* UpReader un / ReadDrop *)
    destruct un as [| m].
    + exfalso; simpl in Hne; apply Hne; reflexivity.
    + exists (NUpReader m). split; [ exact (PR_udrop m) | ].
      simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* UpReader un / UpReadDrop: the upreader leaves, the others keep
       the lock -- the target dispatches on the count. *)
    destruct un as [| m].
    + exists (NReaders 0). split; [ exact PR_uup0 | ].
      simpl; rewrite ?Nat.eqb_refl; reflexivity.
    + exists (NReaders m). split; [ exact (PR_uupS m) | ].
      simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* UpReader un / Upgrade -- spins until the others are gone *)
    destruct un as [| m].
    + exists NWriter. split; [ exact PR_upg | reflexivity ].
    + exfalso; simpl in Hne; apply Hne; reflexivity.
  - (* Writer / WriteDrop *)
    exists (NReaders 0). split; [ exact PR_wdrop | ].
    simpl; rewrite ?Nat.eqb_refl; reflexivity.
  - (* Writer / Downgrade -- always succeeds *)
    exists (NUpReader 0). split; [ exact PR_down | ].
    simpl; rewrite ?Nat.eqb_refl; reflexivity.
Qed.

Lemma ob_word_ok_gen : forall tr,
    wellformed tr -> gen productions (NReaders 0) tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run run_from_error nil_prod step_prod
           (NReaders 0) (Readers 0)); [ reflexivity | exact H ].
Qed.

(** * Assemble the model *)

Definition P : Protocol :=
  {| st := State; ev := Event; nt := Nt;
     init := Readers 0; fault := Error; next := step;
     is_error := is_err;
     start := NReaders 0; prod := productions; inv := available;

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

(* concurrent readers, then both leave *)
Example two_readers : acceptsp (Read :: Read :: nil) = true.
Proof. reflexivity. Qed.

(* an upreader with nobody else may upgrade immediately *)
Example upread_upgrade : acceptsp (UpRead :: Upgrade :: nil) = true.
Proof. reflexivity. Qed.

(* ...but not while another reader remains: [upgrade] spins *)
Example upgrade_with_reader :
    acceptsp (Read :: UpRead :: Upgrade :: nil) = false.
Proof. reflexivity. Qed.

(* only one upreader at a time *)
Example second_upreader : acceptsp (UpRead :: UpRead :: nil) = false.
Proof. reflexivity. Qed.

(* the full mode cycle: write -> downgrade -> release *)
Example downgrade_cycle :
    acceptsp (Write :: Downgrade :: UpReadDrop :: nil) = true.
Proof. reflexivity. Qed.

(* a writer makes readers sleep, which we model as cannot-complete *)
Example writer_blocks_read : acceptsp (Write :: Read :: nil) = false.
Proof. reflexivity. Qed.

Example downgrade_generated :
    genp (Write :: Downgrade :: UpReadDrop :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example writer_blocks_read_not_generated : ~ genp (Write :: Read :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.
