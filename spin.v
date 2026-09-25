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

(** * Model side, to follow: the grammar, the seven obligations and
    the verdict on the prediction above. *)
