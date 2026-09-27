# What a code → grammar pipeline must produce

Task 1.1's loop is *client → top-level property → verify against the
existing API spec → spec-gap report* (`research/task-1.1-*.md`). A CFG
can describe the client interaction language and make the required
property explicit. The key check is whether the client-generated
behaviors are supported by the API spec and whether the property follows;
language equality between a client CFG and a protocol recognizer is not
the general goal. Client behaviors are normally a subset of all protocol
behaviors, and a client may intentionally require balanced completion
while the API permits a trace to end with a guard held.

The repository's original protocol models remain useful as machine-
checked API-language representations and counterexample tools. They do
not synthesize top-level properties from clients by themselves. The first
client-side links are documented in `CLIENT_CFG_CASE.md`. The stronger
pilot, `mutex_client_cfg.v`, abstracts a real Asterinas registry lookup
and proves its CFG traces are accepted by the mutex spec. The companion
`xarray_client_cfg.v` targets SpinLock, for which no independent formal
spec exists in `vostd/ostd/specs/sync/`; that result is client-to-model
evidence only.

The functional COW pilot is the one-page path in Asterinas'
`cow_copy_pt_basic` test. Its source assertions ask for physical-frame
identity, read-only COW permissions, and child-mapping persistence after a
parent unmap. The contract audit in `CLIENT_CFG_CASE.md` finds relevant
clauses in the local `Cursor` map/query specs. The embedding now proves
cursor continuity, Query-to-Map handle flow, and the metadata and view
postconditions of Unmap. The embedding contains a result-bearing one-page RAM
COW trace: FindNext, Query, child-specific write protection, Jump, Map, and
parent Unmap. This trace still relies on trusted embedding mirrors. Path
accounting now uses multiset semantics, so the same path under distinct
page-table roots can contribute multiple references. The executable Map API
proves exact base-page path insertion and its `+1` length effect. The abstract
store accounting now includes pending/in-flight TLB-retained frames, and
model-level Unmap proves path/TLB conservation. The runtime-backed Unmap store
bridge, Rocq state refinement, and production COW loop remain open. The last
completed full Vostd verification run fails at `CursorMut::unmap`'s
`unmap_spec` postcondition (1575 verified, 1 error); the preceding full run
passed (1576 verified, 0 errors). Verification still includes the embedding
axioms.
`mm_cow_client_cfg.v` compiles a projection of those embedding actions
into the client CFG, including the parent-unmap suffix. The projection
does not prove that Rocq's candidate transition semantics refine the
Verus store contracts. Several operations still use trusted store-level
embedding axioms; `run` for arbitrary traces still preserves only
`VmStore.inv()`. The production loop, MMIO behavior, and general callback
semantics remain open. Details and trust boundaries are in
`CLIENT_CFG_CASE.md`.

For mutex, existing top-level properties in
`vostd/ostd/specs/sync/examples/mutex_tla.rs` include
`mutual_exclusion` and `starvation_free`; these are candidate properties
for a richer client-driven case. `gen_iff_accepts` remains valuable for
checking an API-language model against its grammar, but it does not
replace the client-property proof obligation.

Two mismatch shapes are already demonstrated in this repository:

* **documented stricter than spec** -- putting "the trace must be
  balanced" into a grammar makes `gen` and prefix-closed `accepts`
  disagree, with `Create :: LockAcquire :: nil` as the witness
  (`mutex_grammar.v`, `balanced_is_not_equivalent`);
* **alphabet too narrow** -- a public-API-only alphabet cannot express
  FIFO wakeup order at all, which is why the wait-queue model needs the
  internal labels `Wait`/`Wake` (`mutex_waitqueue.v`'s header).

## The six outputs, and how much of each is mechanical

Measured across the eight models (detail in `MODELS.md`):

| output | mechanized? | evidence |
|---|---|---|
| **alphabet (events)** | **no -- hand-written per model** | public verbs come from the API surface (acquire / release / downgrade), so that part is mechanizable in principle (rust-analyzer); it would MISS internal (non-API) labels, which only `mutex_waitqueue` has (`Wait`, `Wake` -- model-chosen names for steps that `wait.rs`, `mutex_tla.rs` and `mutex_verussync.rs` describe) -- and hand-written alphabets also miss real operations: the `spin` alphabet had no event for `disable_irq().lock()` though the kernel calls it 37 times -- the client view caught it, and the model was amended (`DisableIrq`) |
| transition table + error flag | taken from the existing spec -- or, where none exists (`rwlock.v`), from the implementation | -- |
| obligations 1–3 (glue) | fully mechanical | 8/8 |
| obligation 4 (`prod_ok`) | mechanical | 7/8; the eighth needs the net measure |
| **grammar: `nt` / `prod` / `inv`** | **no -- design work** | the count, the queue and the owner had to be carried by the nonterminal |
| obligation 7 (grammar completeness) | partly | the library assembles the right-linear case from two witnesses (7 of 8); non-right-linear is hand-written (`rcu.v`) |
| counterexample enumeration | mechanical | provided by the library (`examples_upto`) |

**Conclusion:** every remaining difficulty sits in *grammar synthesis*;
everything downstream of the grammar is obligation discharge, and even
the induction behind right-linear completeness now lives in the library
(`gen_of_run`).  If 1.1 is to generate protocol models automatically,
the research question is how to synthesize the grammar (the
nonterminals and their parameters), not how to discharge the
obligations.

## Open questions

1. **Input: spec or code?**  Taking the spec (a state machine) makes
   grammar-as-documentation vs machine-as-spec a meaningful comparison;
   taking code reintroduces the circularity 1.1 names as its largest
   risk (properties must come from outside the repository's own spec).
   Provenance is measurable across the three protocols, and only one of
   them separates cleanly: `mutex_grammar` takes its table from
   `mutex.rkt` (the Redex prototype; only in git history now -- added
   `ec1202f`, dropped `cda871b`) and its grammar from
   `ostd/docs/sync-protocol/mutex-regular-language.md`, the document
   that defines that exact alphabet and table -- two artifacts.
   `mutex_param.v`'s identity parameter cites `mutex-fsm.md` in the
   same directory.  The element-by-element audit of all eight models
   is `PROVENANCE.md`.  `rcu.v` takes both sides from the implementation, and
   the reason was checked rather than assumed: `ostd/specs/sync/rcu/`
   exists but covers allocation registration and publication identity
   only, and `root.rs` says outright that "physical ownership, reader
   protection, and detachment evidence must be supplied by the RCU
   protocol" -- which no spec file states (0 hits for `load_read_token`
   or `RCU_READER_SLOTS` under `specs/`).  So the property rcu.v
   formalizes -- a guard dropped that no read is outstanding for -- has
   no spec clause behind it; it exists only in code, and our grammar is
   the first written form of the discipline.  That is a gap report in
   1.1's own vocabulary.  `rwlock.v` has no spec at all (checked
   under `specs/` and `docs/`), so both sides
   come from implementation + Verus invariant.  The equivalence is only
   as informative as that separation.

   **Pilot, done** -- deriving `spin`'s side from real call sites in
   `asterinas/kernel` (131 `SpinLock` mentions; sampled at futex,
   console, uart, virtio):

   * *The alphabet was incomplete.*  `disable_irq().lock()` -- the
     `PreemptDisabled -> LocalIrqDisabled` mode cast -- occurs 37
     times and had no event in `spin.v`; the model now carries it as
     `DisableIrq`, a stutter in both modes.  Conversely the decision
     to exclude `try_lock` is upheld: 0 real uses (the one apparent
     hit is a `Mutex`, not a `SpinLock`).
   * *The grammar's oddity is confirmed.*  9 client functions return
     a `SpinLockGuard`, so real traces do end while holding the lock
     -- exactly the prefix closure `spin.v` allows, which the original
     `mutex.rkt` reading did not.
   * *Provenance must name the tree.*  Clients exercise
     `asterinas/ostd`, our material comes from `vostd/ostd`, and all
     12 files under `sync/` differ between the two -- including
     `SpinLockGuard`'s `Drop` (present there; commented out here as a
     Verus limitation).  Independence is thus stronger than "different
     file" -- it is different code -- and version drift becomes a risk
     to state rather than an assumption.

   **Pilot 2, done** -- the same pass over `mutex` (170 `Mutex<`
   mentions in `asterinas/kernel`):

   * *Usage confirms the shape again.*  6 client functions return a
     `MutexGuard`, one of them storing it in a struct field
     (`process/mod.rs:195`), and `mutex.rs:262` comments out
     `impl Drop` exactly as `spin.rs` does -- so `GuardDrop` is the
     live release path.
   * *No spin-shaped gap.*  `mutex.rs` has no mode cast (0 hits), and
     `try_lock` has exactly 1 real use, single-shot -- corroborating
     the removal of this repository's retry budget (`DECISIONS.md`).
   * *Two public verbs stay out of the alphabet:* `get_mut` and
     `MutexGuard::get_lock` touch no pairing and are guarded by
     `&mut self` / the borrow checker -- out of scope the way
     `try_lock` is for `rwlock.v`.
   * *Lesson for provenance searches:* the discipline documents live
     under `ostd/docs/sync-protocol/`, not `specs/` -- a source audit
     that stops at `specs/` reports false gaps (this one did).  The
     same check under `docs/` keeps `rwlock.v`'s and `rcu.v`'s
     "no protocol spec" claims intact; `docs/sync-protocol/README.md`
     calls mutex "the first complete synchronization-protocol
     result".

   **Pilot 3, done** -- `rwlock` and `rwmutex` (49 / 45 `RwLock<` /
   `RwMutex<` mentions, plus 80 `WaitQueue`):

   * *The pattern holds again.*  15 client functions return a read or
     write guard (prefix closure, third confirmation); `try_read` /
     `try_write` have 0 real uses, so the Option exclusion stands for
     the second time; `impl Drop` is commented out in `rwlock.rs`
     (`:858`, `:1091`) and absent from `rwmutex.rs`, while clients
     call `drop(guard)` explicitly (`input_core.rs:167`) -- manual
     release is the live path in all four guard files.
   * *The declared scope gap is exercised, not hypothetical:*
     `upread()` has 18 real call sites and `upgrade()` runs at
     `softirq/src/lock.rs:195` on an `RwLock`, so rwlock.v's
     "upgrade / upreader machinery out of scope" excludes what
     clients actually do.
   * *The `get_mut` class is three models wide:* `rwlock.rs:624` and
     `rwmutex.rs:520` add it to mutex's two verbs -- same
     no-pairing / `&mut self` argument, still unlisted in the models'
     own scope notes.

   **Pilot 4, done** -- `rcu`, the last protocol: `Rcu<` appears in
   2 kernel files (console, cgroupfs) exercising every model event --
   `Rcu::new` (x5), `.read()` (x6), `.update()` (x4), release at
   scope end.  No explicit `.drop()` anywhere, and none is owed at
   runtime: the guard's only runtime protection field
   (`DisabledPreemptGuard`) is field-dropped, while the manual `drop`
   (marked VERUS LIMITATION) returns the *ghost* token that verified
   callers owe.  The model's `Drop` event = the end of the read
   section on both sides.
2. **When does a protocol need parameters, and when a non-right-linear
   production?**  Draft criterion -- a hypothesis to be validated, not
   a result:

   * *Read off what `next` inspects to decide whether a step faults.*
     Nothing unbounded ⇒ finite nonterminals, no parameters
     (`mutex_grammar`, `spin`).
   * *If it does inspect something unbounded, is the discipline
     stack-like?*  Pairing / LIFO ⇒ nesting suffices: a non-right-linear
     production over finite nonterminals (`rcu`).  Not stack-like -- a
     queue, or a value the machine resets (`Flush`) ⇒ the data has to
     become a nonterminal parameter (`mutex_waitqueue`, `buffer`,
     `mutex_param`).  The `{ww}` reduction in `DECISIONS.md` is the
     proof that FIFO cannot be dodged this way.
   * *If both would work, prefer the one that stays right-linear*, since
     a right-linear grammar gets obligation 7 from the library
     (measured: 7 of 8 models).
   * *When the count decides the TARGET nonterminal rather than only
     whether a step is allowed, the production must dispatch
     structurally on it -- one production per case, not a guarded
     one.*  `rwmutex.v`'s `UpReadDrop` is the instance: the prediction
     counted one cell, the proof needed two.

   Validation: done three times -- `rwlock.v`, `spin.v`, `rwmutex.v`.  Each prediction
   was committed before any grammar existed (the first commit of that
   file) and the verdict is in its header -- the shape-level prediction
   held all three times; what the criterion does not cover is *how* the
   count gets split into the table (see the constraints in
   `MODELS.md`).
3. **Scope.**  Language equivalence only.  Temporal/fairness properties
   stay out, per 1.1's risk 7 ("safety first, fairness later").
