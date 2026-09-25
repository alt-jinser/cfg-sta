(* spin.v -- spin-lock discipline, on top of protocol_lib.

   Provenance: ostd/src/sync/spin.rs.  The lock state is a single
   boolean -- `is (locked: bool, resource: Option<SpinLockResource>)`
   -- and the two events are its two transitions:

     * `SpinLock::lock()` (spin.rs:270) acquires and returns a
       `SpinLockGuard`;
     * `SpinLockGuard::drop(self)` (spin.rs:588) releases.  The
       ordinary `Drop` impl is commented out with the note "VERUS
       LIMITATION: We implement `drop` and call it manually because
       Verus's support for `Drop` is incomplete for now", so the
       release path is an explicit call -- that is what `Unlock` below
       refers to.

   No protocol spec exists (ostd/specs/sync/ holds only mutex_protocol,
   rcu/ and the mutex examples), so as in rwlock.v both sides come from
   the implementation.

   Modelling choice, the same one rwlock.v makes: [fault] = the call
   cannot complete immediately (a second [lock] would spin until the
   release) or is a release no guard accounts for.  `try_lock()`
   returns an Option and is out of scope, as try_read/try_write are for
   rwlock.v.

   ------------------------------------------------------------
   PREDICTION, written from the transition semantics BEFORE any
   grammar exists (this file's first commit is the pre-registration;
   the verdict is at the end of this header).

   Applied to the three-step criterion of PIPELINE.md:

   1. Does [next] inspect unbounded data to decide a step?  NO -- the
      state is one boolean.  Step 1 predicts: finite nonterminals, no
      parameters, the `mutex_grammar` branch.
   2. (not reached: it is about what to do with unbounded data)
   3. Trivially right-linear.

   PREDICTED MODEL SHAPE: two finite modes, every production
   right-linear (one terminal, one nonterminal), obligation 4
   mechanical, obligation 7 = the two witnesses for the library's
   gen_of_run, no net measure -- and the smallest model so far: two
   surviving cells in step_prod.

   VERDICT (written after the model compiled): CONFIRMED.  Two finite
   modes, four productions, all right-linear; obligation 4 mechanical;
   obligation 7 the two witnesses, step_prod with exactly the predicted
   two cells; no net measure.  Step 1 of the criterion gets its second
   data point -- `next` reads no unbounded data, the grammar carries no
   parameter, same branch as mutex_grammar.

   Compiles with Rocq 9.1.1:  rocq compile spin.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.
Open Scope bool_scope.

(** * STA side *)

Inductive State : Type :=
| Free
| Locked
| Error.

Inductive Event : Type :=
| Lock
| Unlock.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** The transition matrix, nested per state (see the constraints in
    MODELS.md). *)
Definition step (s : State) (e : Event) : State :=
  match s with
  | Free =>
      match e with
      | Lock   => Locked
      | Unlock => Error    (* releasing a lock no guard holds *)
      end
  | Locked =>
      match e with
      | Lock   => Error     (* would spin until the release *)
      | Unlock => Free
      end
  | Error => Error
  end.

(** * CFG side *)

Inductive Nt : Type :=
| NFree
| NHeld.

Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nilF   : productions NFree nil
| PR_nilH   : productions NHeld nil
| PR_lock   : productions NFree (Se Lock :: Sn NHeld :: nil)
| PR_unlock : productions NHeld (Se Unlock :: Sn NFree :: nil).

Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | NFree, Free   => true
  | NHeld, Locked => true
  | _, _          => false
  end.

(** * The 7 obligations *)

Ltac case_types := case_of State; case_of Event.

Lemma ob_is_error_ok : forall s, is_err s = true <-> s = Error.
Proof. discharge case_types. Qed.

Lemma ob_init_fault_free : Free <> Error.
Proof. discriminate. Qed.

Lemma ob_inv_start : available NFree Free = true.
Proof. reflexivity. Qed.

Lemma ob_prod_ok : forall A beta s,
    productions A beta -> available A s = true ->
    ok Error step available productions s beta.
Proof. discharge_prod productions case_types. Qed.

Lemma run_from_error : forall tr, run_from step Error tr = Error.
Proof. apply run_from_sink. intros e; reflexivity. Qed.

Definition wellformed (tr : list Event) : Prop :=
  run Free step tr <> Error.

Lemma ob_word_ok_run : forall tr,
    run Free step tr <> Error <-> wellformed tr.
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
  destruct A; case_types; cbn [run_from step available] in *;
    try discriminate Hinv;
    try (exfalso; apply Hne; reflexivity).
  - (* free / Lock *)
    exists NHeld. split; [ exact PR_lock | reflexivity ].
  - (* held / Unlock *)
    exists NFree. split; [ exact PR_unlock | reflexivity ].
Qed.

Lemma ob_word_ok_gen : forall tr,
    wellformed tr -> gen productions NFree tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run run_from_error nil_prod step_prod NFree Free);
    [ reflexivity | exact H ].
Qed.

(** * Assemble the model *)

Definition P : Protocol :=
  {| st := State; ev := Event; nt := Nt;
     init := Free; fault := Error; next := step;
     is_error := is_err;
     start := NFree; prod := productions; inv := available;

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

(* acquisition, then release *)
Example lock_unlock : acceptsp (Lock :: Unlock :: nil) = true.
Proof. reflexivity. Qed.

(* the trace may end while the lock is held *)
Example held_prefix : acceptsp (Lock :: nil) = true.
Proof. reflexivity. Qed.

(* a second acquisition would spin until the release *)
Example double_lock : acceptsp (Lock :: Lock :: nil) = false.
Proof. reflexivity. Qed.

(* releasing a lock no guard holds is the misuse case *)
Example unlock_while_free : acceptsp (Unlock :: nil) = false.
Proof. reflexivity. Qed.

Example lock_unlock_generated : genp (Lock :: Unlock :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example double_lock_not_generated : ~ genp (Lock :: Lock :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.
