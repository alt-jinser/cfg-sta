# Provenance, audited

Every non-trivial element of the eight models, checked against the
whole source set: `ostd/src/`, `ostd/specs/`, both `docs/` subtrees,
the git histories of this repository and of `vostd`, and `research/`.
A source is a path a reader can open; a *stated idealization* is a
deliberate simplification recorded in the model's own header.

## Sources that exist

| artifact | role |
|---|---|
| `specs/sync/mutex_protocol.rs` | authoritative 4-state table for `create` (per `mutex-regular-language.md`) |
| `docs/sync-protocol/mutex-inventory.md` | API-boundary scope; one `Mutex<T>` per trace; lists the specs; asks for kernel traces |
| `docs/sync-protocol/mutex-regular-language.md` | strict alphabet + FSM + `L+_core = create (A F* D)*`; `L+_mutex` = run never enters ERROR |
| `docs/sync-protocol/mutex-fsm.md` | identity refinement: `wrong_owner_unlock`; ownership kept *because* the guard is `!Send` |
| `specs/sync/examples/mutex_tla.rs` | wait queue, wakers, FIFO/barging |
| `specs/sync/examples/mutex_verussync.rs` | state-machine wait queue (`enqueue_waker`, `wake_one`, ...) |
| `specs/sync/examples/abstract_lock_tla.rs` | program-level mutual exclusion (`start/lock/cs/unlock`); no read/write semantics (0 hits) |
| `mutex.rkt` (Redex) | this repo's git history only: added `ec1202f`, dropped `cda871b` |
| `ostd/src/sync/*.rs` | implementation -- the only source for rwlock, spin, rcu |
| `asterinas/kernel` | client call sites; a different tree (all 12 `sync/` files differ) |

## Matrix

| model | table side | grammar side | verdict |
|---|---|---|---|
| `mutex_grammar` | `mutex.rkt` (git) + `mutex_protocol.rs` | `mutex-regular-language.md` -- its `L+_core` regex matches the U/H language exactly | two artifacts, both named |
| `mutex_param` | as above, plus identity | `mutex-fsm.md`; `m`/`g` erased per `mutex-inventory.md`'s single-instance scope | sourced |
| `mutex_waitqueue` | as above | `mutex_tla.rs` + `mutex_verussync.rs` + `wait.rs` (`enqueue`:244, `wake_one`:146, `wake_up`:449) | three artifacts; `Wait`/`Wake` are model-chosen names for spec-described steps |
| `buffer` | none: declared "the non-lock test of the contract"; no buffer protocol under `specs/` or `docs/` | -- | synthetic, stated in its header |
| `rcu` | `src/sync/rcu` (`RCU_READER_SLOTS = 1 << 60`, `mod.rs:56`); `specs/sync/rcu/` defers reader protection | same file | single source; gap report, documented |
| `rwlock` | `rwlock.rs` + Verus invariant (`:235`), quote re-checked | same file | single source; no spec under `specs/` or `docs/` |
| `spin` | `spin.rs:223/270/588` -- line references land exactly | same file | single source; no spec |
| `rwmutex` | `rwmutex.rs:327-360/692/877` -- line references land exactly | same file | single source; no spec |

## Layer coverage

Which evidence layers each protocol actually has (mutex's full stack
is the reference):

| protocol | inventory / API scope | language or FSM doc | identity / queue spec | Verus spec | implementation | client traces |
|---|---|---|---|---|---|---|
| `mutex` | `mutex-inventory.md` | `mutex-regular-language.md` | `mutex-fsm.md`, `mutex_tla.rs`, `mutex_verussync.rs` | `specs/sync/mutex_protocol.rs` | `src/sync/mutex.rs` | `asterinas/kernel` -- the inventory asks for these |
| `rwlock` | -- | -- | -- | -- | `src/sync/rwlock.rs` + invariant | `asterinas/kernel` (pilot 3) |
| `spin` | -- | -- | -- | -- | `src/sync/spin.rs` | `asterinas/kernel` (pilot 1) |
| `rwmutex` | -- | -- | -- | -- | `src/sync/rwmutex.rs` | `asterinas/kernel` (pilot 3) |
| `rcu` | -- | -- | -- | partial: `specs/sync/rcu/` defers reader protection -- the documented gap | `src/sync/rcu/` | `asterinas/kernel`: 2 files, all four events (`Rcu::new`, `.read()`, `.update()`, scope-end release) (pilot 4) |

Three of the five real protocols have exactly two layers --
implementation, plus the client view this audit supplied -- so their
equivalence rests on those two, and writing the missing layers is
1.1-shaped gap work.  One open item vostd flags itself:
`mutex-inventory.md` calls `abstract_lock_tla.rs`'s unlock
precondition (no `locked == true`, no owner) "a candidate for
differential checking, not yet a confirmed specification bug".

## What the audit changed

* Line references in model headers were re-checked and are exact;
  `mutual_exclusion`/`starvation_free` exist
  (`mutex_verussync.rs:213`, `abstract_lock_tla.rs:198/:225`).
* Two dangling references were found.  `mutex.rkt` was cited as a
  file; it lives only in git history and is now cited that way.
  `DECISIONS.md` cited "the plan's variants, F1/F3", which nothing in
  the workspace defines -- the F1-F3 in `mutex.v` are that port's
  three *fixes*, something else entirely.  The sentence and its two
  inheritors are gone.
* The retry budget (`MAX_RETRY = 10`) had no source in any location
  above and was removed; `DECISIONS.md` records the search.

## Client traces

`mutex-inventory.md` notes that its checkout has no `kernel/` and
that "kernel-side traces need to be added later from the
corresponding source tree".  The two pilots in `PIPELINE.md` supply
exactly that from `asterinas/kernel`.
