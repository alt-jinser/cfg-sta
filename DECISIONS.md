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
production derives `[Drop]` (`rcu.v`). For right-linear grammars the
library nevertheless owns the induction (`gen_of_run`): the model owes
two witnesses -- an epsilon production per nonterminal, and a
production per safe step -- because which production applies then
depends only on (nonterminal, state, event); `rcu.v` cannot use it and
proves completeness itself. Soundness (3–4) is proved once in the
library.

**A nonterminal's tail is checked at every state it can reach**, not
at the current one -- the nonterminal consumes input before the tail
runs. `Reach` quantifies over fault-free endpoints only; this does not
hide the conclusion, because soundness establishes non-fault
separately before applying the clause, while the top-level instance
stays trivially dischargeable.

**`nt : Type` may be infinite.** FIFO with identities is not
context-free, so `mutex_waitqueue.v` indexes nonterminals by the queue;
with finite `nt` the contract is a classical CFG. Reduction, in full so
it can be checked: let R be the regular set

    Create LockAcquire 0 Wait* GuardDrop 0 (Wake _ GuardDrop _)*

and h the homomorphism `Wait t ↦ t`, `Wake t ↦ t`, everything else
`↦ ε`. The machine accepts a trace of shape R exactly when its two id
sequences agree (a mismatched `Wake` faults, `wake_info` returns
`None`), so `h(L ∩ R) = { ww | w ∈ tid* }`; restricting `w` to the
tids {1, 2} (0 is the owner) yields the classical `{ww}`, which is not
context-free. CFLs are closed under regular intersection and
homomorphism, so L is not CFL either. Standard language theory; not
mechanized.

The converse bound matters just as much: with an infinite `nt` and
`prod` as a relation the grammar family is *strictly* larger than CFL
-- one nonterminal per machine configuration and one production per
transition already encodes arbitrary computation. So `gen_iff_accepts`
is a CFG equivalence only in the finite-`nt` case; in general the
contract guarantees that two relations agree, and says nothing about
the family being context-free.

**Rewritten in place, no parallel contract.** While the contract is
an experiment, two side by side double the proof surface and add no
evidence; `protocol_lib.v` is the single contract.

**`wait` is not modelable under F1.** The contract's events are
guarded protocol operations with a misuse reading, and
`ostd/src/sync/wait.rs` offers none: `wake_one → false` is legal
(`:153`), `wait_until` re-loops until the deadline (`:124-142`), and
`waiter_wake_twice` asserts the second wake returns false -- blocking
is the call's function, not a failure, and every report is a
bool/Option (the file's 17 `assert!`s serve Verus proofs and tests,
not a client-facing fault). An event would have to invent a fault the
implementation does not have, which is the independence risk 1.1
names. Extending the contract to observable outcomes -- reports, not
just faults -- would let it in; that is a contract change and stays
open.

**No numeric retry budget.**  `mutex_param.v` and `mutex_waitqueue.v`
carried `n <= MAX_RETRY = 10` on `TryLockCall`, cited as "literally
参数 > 10".  No artifact has it: `mutex_protocol.rs` and both
`docs/sync-protocol/` models give the event with no counter, the
Redex prototype (git `ec1202f`) has no bound, the implementation
retries without one (`wait_until(|| try_lock())`), and research notes
and history contain no such number -- while `mutex_waitqueue.v` cited
`mutex_param.v`, which is circular.  Removed: the guard, the counter
parameter, and the tests for them; the events now match the
documented alphabet exactly.

Arguments: headers of `protocol_lib.v` and `rcu.v`; facts and gates in
`MODELS.md`.
