# Design decisions

What was chosen, what it rules out, and where the argument lives.

**Productions, not predicates over transitions.** Each model defines
`prod : nt -> list (sym nt ev) -> Prop` without touching the
transition table; the only bridge to the machine is `inv`. This
replaces the earlier `stutter` / `changes_to` / `starts_to` classes:
the grammar rule for an advance and for a release is literally the
same term, so the class names carried no semantics. We are on F1 of
the plan's variants; F3 remains the documented fallback.

**Derivability in yield form** (`D_base` / `D_se` / `D_sn`), not a
rewriting relation. The rule records where the word splits between a
nonterminal and its continuation -- which is exactly the state at
which the continuation runs. A rewriting relation drops the split, so
every proof needs a decomposition lemma to recover it.

**Completeness is a model obligation** (5–7), not a library proof: a
state-indexed version is false, since `safe 1 [Drop]` holds while no
production derives `[Drop]` (`rcu.v`). Soundness (3–4) is proved once
in the library.

**A nonterminal's tail is checked at every state it can reach**, not
at the current one -- the nonterminal consumes input before the tail
runs. `Reach` quantifies over fault-free endpoints only; this does not
hide the conclusion, because soundness establishes non-fault
separately before applying the clause, while the top-level instance
stays trivially dischargeable.

**`nt : Type` may be infinite.** FIFO with identities is not
context-free: `Wait t1..tn .. Wake t1..tn` reduces to `{ww}` by
regular intersection and homomorphism, so `mutex_waitqueue.v` indexes
nonterminals by the queue. With finite `nt` the contract is a
classical CFG. The reduction is standard language theory and is not
yet mechanized.

**Rewritten in place, no parallel contract.** While the contract is
an experiment, two side by side double the proof surface and add no
evidence; `protocol_lib.v` is the single contract.

Arguments: headers of `protocol_lib.v` and `rcu.v`; facts and gates in
`MODELS.md`.
