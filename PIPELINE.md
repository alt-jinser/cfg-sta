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

Measured across the five models (detail in `MODELS.md`):

| output | mechanized? | evidence |
|---|---|---|
| transition table + error flag | taken from the existing spec | -- |
| obligations 1–3 (glue) | fully mechanical | 5/5 |
| obligation 4 (`prod_ok`) | mechanical | 4/5; the fifth needs the net measure |
| **grammar: `nt` / `prod` / `inv`** | **no -- design work** | count and queue had to be carried by the nonterminal |
| obligation 7 (grammar completeness) | no | 5/5 hand-written; right-linear ⇒ per-event induction, non-right-linear ⇒ a word cut |
| counterexample enumeration | mechanical | provided by the library (`examples_upto`) |

**Conclusion:** every remaining difficulty sits in *grammar synthesis*;
everything downstream of the grammar is obligation discharge and can be
handed to automation.  If 1.1 is to generate protocol models
automatically, the research question is how to synthesize the grammar
(the nonterminals and their parameters), not how to discharge the
obligations.

## Open questions

1. **Input: spec or code?**  Taking the spec (a state machine) makes
   grammar-as-documentation vs machine-as-spec a meaningful comparison;
   taking code reintroduces the circularity 1.1 names as its largest
   risk (properties must come from outside the repository's own spec).
2. **When is a non-right-linear production necessary?**  Nesting (RCU's
   read/drop pairing) needs one; counts and queues can be carried by
   parameterized nonterminals instead.  The criterion for choosing is
   not written down anywhere yet.
3. **Scope.**  Language equivalence only.  Temporal/fairness properties
   stay out, per 1.1's risk 7 ("safety first, fairness later").
