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
   the verdict is filled in after the model is written).

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
    accounts for. *)
Definition step (s : State) (e : Event) : State :=
  match s, e with
  (* read: always possible without a writer; one more reader *)
  | Readers n, Read  => Readers (S n)
  | Writer, Read     => Error
  (* release a read guard: never below zero *)
  | Readers (S n), ReadDrop => Readers n
  | Readers 0, ReadDrop     => Error
  | Writer, ReadDrop        => Error
  (* write: exclusive -- no reader, no writer *)
  | Readers 0, Write => Writer
  | Readers _, Write  => Error
  | Writer, Write    => Error
  (* release the write guard *)
  | Writer, WriteDrop    => Readers 0
  | Readers _, WriteDrop => Error
  (* the fault state absorbs *)
  | Error, _             => Error
  end.

(** * Model side, to follow: the grammar, the seven obligations and
    the verdict on the prediction above. *)
