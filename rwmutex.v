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
| Readers (n : nat)        (* [Readers 0] is free *)
| UpReader (n : nat)       (* one upgradable reader + [n] others *)
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

(** * Model side, to follow: the grammar, the seven obligations and
    the verdict on the prediction above. *)
