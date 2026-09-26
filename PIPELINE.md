# What a code → grammar pipeline must produce

Task 1.1's loop is *client → property → verify against the existing
contracts → spec-gap report* (`research/task-1.1-*.md`).  The protocol
work occupies one cell of it: **the documented usage grammar and the
spec's state machine denote the same language**, so `gen_iff_accepts`
is the checker for that cell -- a mismatch is a spec gap with a named
witness.  The state machines it would be checked against already exist
(`vostd/ostd/specs/sync/mutex_protocol.rs`,
`vostd/ostd/specs/sync/examples/mutex_tla.rs`, whose
`mutual_exclusion`/`starvation_free` are the fairness samples 1.1 defers
to).

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
| **alphabet (events)** | **no -- hand-written per model** | public verbs come from the API surface (acquire / release / downgrade), so that part is mechanizable in principle (rust-analyzer); it would MISS invented internal labels, which only `mutex_waitqueue` has (`Wait`, `Wake`) -- and hand-written alphabets also miss real operations: the `spin` pilot found 37 `disable_irq().lock()` sites with no event in `spin.v` | |
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
   `mutex.rkt` and its grammar from the discipline prose -- two
   artifacts.  `rcu.v` takes both sides from the implementation, and
   the reason was checked rather than assumed: `ostd/specs/sync/rcu/`
   exists but covers allocation registration and publication identity
   only, and `root.rs` says outright that "physical ownership, reader
   protection, and detachment evidence must be supplied by the RCU
   protocol" -- which no spec file states (0 hits for `load_read_token`
   or `RCU_READER_SLOTS` under `specs/`).  So the property rcu.v
   formalizes -- a guard dropped that no read is outstanding for -- has
   no spec clause behind it; it exists only in code, and our grammar is
   the first written form of the discipline.  That is a gap report in
   1.1's own vocabulary.  `rwlock.v` has no spec at all, so both sides
   come from implementation + Verus invariant.  The equivalence is only
   as informative as that separation.

   **Pilot, done** -- deriving `spin`'s side from real call sites in
   `asterinas/kernel` (131 `SpinLock` mentions; sampled at futex,
   console, uart, virtio):

   * *The alphabet is incomplete.*  `disable_irq().lock()` -- the
     `PreemptDisabled -> LocalIrqDisabled` mode cast -- occurs 37
     times and has no event in `spin.v`.  Conversely the decision to
     exclude `try_lock` is upheld: 0 real uses (the one apparent hit
     is a `Mutex`, not a `SpinLock`).
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
