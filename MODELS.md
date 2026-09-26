# The contract and its eight models

`protocol_lib.v` proves one theorem, and every model reuses it:

```coq
gen_iff_accepts : forall tr, gen tr <-> accepts tr = true
```

`gen tr` is "the trace is derivable from the grammar's start
nonterminal" (yield-form derivability, `D_base`/`D_se`/`D_sn`);
`accepts tr = true` is "the transition table does not fault on it".
It occurs **exactly once in the repository** -- in the library.

## What a model supplies

Fields (`st ev nt init fault next is_error start prod inv`) and seven
obligations, listed with their type in the header of `protocol_lib.v`:

| # | obligation | the direction it carries |
|---|---|---|
| 1 | `is_error_ok` | glue: boolean error flag ≡ the fault state |
| 2 | `init_fault_free` | glue: the initial state is not the fault state |
| 3 | `inv_start` | → : the start nonterminal is available initially |
| 4 | `prod_ok` | → : a production is safe where it sits |
| 5 | `word_ok` | a predicate on traces (the model's choice) |
| 6 | `word_ok_run` | ← : the recognizer's safety ≡ `word_ok` |
| 7 | `word_ok_gen` | ← : `word_ok` ⇒ derivable |

Direction → (`gen → accepts`) is proved **once** in the library, from
3 and 4. Direction ← (`accepts → gen`) is assembled by the library
from 5–7; its content lives in the model, because a state-indexed
statement of completeness is *false* in general (see the header of
`protocol_lib.v`, and `rcu.v` for the concrete counterexample:
`safe 1 [Drop]` holds, no production derives `[Drop]`).

## The models

| file | lines | nonterminals | productions | grammar shape |
|---|---|---|---|---|
| `mutex_grammar.v` | 320 | `Program`, `U`, `H` | 13 | right-linear, finite |
| `mutex_param.v` | 323 | `Program`, `U`, `H(o)` | 13 | parameterized; retry-budget guard on two productions |
| `mutex_waitqueue.v` | 527 | `Program`, `U`, `H(o,w)`, `W(q)` | 21 | parameterized by a **queue**; `wake_info` reads the head |
| `buffer.v` | 307 | `Program`, `Buf(n)`, `Cl` | 10 | parameterized by the **count**; `Get` guarded by `1 <= n` |
| `rcu.v` | 566 | `Program`, `Body` | 6 | **non-right-linear** (`Body -> Read Body Drop Body`) |
| `rwlock.v` | 281 | `RwRead n`, `RwWrite` | 4 (+2 ε) | count-parameterized, right-linear; **no protocol spec exists**, so both sides come from the implementation (see `PIPELINE.md`, open question 1) |
| `spin.v` | 249 | `NFree`, `NHeld` | 6 (+2 ε) | finite, right-linear; **no protocol spec** (implementation only) |
| `rwmutex.v` | 350 | `NReaders n`, `NUpReader n`, `NWriter` | 14 (+3 ε) | count-parameterized ×2, right-linear mode conversions; **no protocol spec** (implementation only) |

Two of these parameters are forced, not decorative:

* `Buf(n)` in `buffer.v` -- a production is state-independent, so a
  count-free nonterminal would derive `Get` from an empty buffer, and
  `prod_ok` would fail at that cell.
* `H(o,w)` / `W(q)` in `mutex_waitqueue.v` -- likewise for `Wake`: a
  queue-free nonterminal would wake a waiter when nobody is queued.
  `rcu.v`'s header records the same argument for its grammar.

## How each model discharges the obligations

`mech` = closed by `discharge`/`discharge_prod` (case analysis over the
model's own types plus `finish_goal`); `1-line` = a definition or a
one-tactic proof; `witness` = two lemmas handed to the library's
completeness induction (`gen_of_run`); `hand` = proof written out.

| model | 1–3 | 4 `prod_ok` | 5–6 `word_ok`/`word_ok_run` | 7 `word_ok_gen` |
|---|---|---|---|---|
| `mutex_grammar` | mech, mech, 1-line | mech (all 13) | 1-line + 1-line | **witness**: `nil_prod` + `step_prod`, 10 cases |
| `mutex_param` | mech, mech, 1-line | mech (guards split by `finish_goal`) | 1-line + 1-line | **witness**: 10 cases, 2 guard splits |
| `mutex_waitqueue` | mech, mech, 1-line | mech + `available` reflexivity cleanup + manual `Wake` cell (2 goals) | 1-line + 1-line | **witness**: 17 cases; `Wake` cell opened by hand |
| `buffer` | mech, mech, 1-line | mech + 2 length cleanups | 1-line + 1-line | **witness**: 7 cases |
| `rcu` | hand, 1-line, 1-line | **hand**: 4 cases; `PB_cs` needs `reach_positive` | 1-line + 1-line | **hand**: `body_complete` + `dip_split` |
| `rwlock` | mech, 1-line, 1-line | mech + 1 availability cleanup | 1-line + 1-line | **witness**: 4 cases |
| `spin` | mech, 1-line, 1-line | mech | 1-line + 1-line | **witness**: 4 cases |
| `rwmutex` | mech, 1-line, 1-line | mech + count cleanup | 1-line + 1-line | **witness**: 10 cells, 11 leaves |

Obligation 4 is mechanical for seven of the eight models.  Obligation 7
is assembled by the library for those seven: the model hands it
`nil_prod` and `step_prod`, whose case count is the number of real
transitions; only `rcu.v` (non-right-linear) proves completeness
itself, because there the choice of production depends on where in the
word the count bottoms out.  It remains the obligation whose difficulty
tracks the grammar.

Constraints on the automation, for anyone adding a model with a
list- or guard-carrying nonterminal:

* Do not point `case_of` at a `list tid`: `destruct` on a list
  introduces another list, so the `repeat` would not terminate.  The
  queue is opened once, by hand, in the cells that read it
  (`mutex_waitqueue.v`, `rcu.v`).
* `simpl` folds `Nat.leb 1 (length items)` into a raw match on
  `length items`, which loses the production's guard; normalise with
  `cbn [run_from step available]` instead (`buffer.v`).
* Write `step` NESTED per state rather than as one flat matrix: a flat
  matrix lets a state row's split on a count leak into another arm and
  leaves a residual match `cbn` cannot collapse (`rwlock.v`, measured).
* A model-specific reflected equality (a table keyed by lists, say)
  does **not** get an arm in `finish_goal`: register it with
  `Hint Resolve ... : finish_db` and close its reflexive goals on the
  model side (`mutex_waitqueue.v`).  The closer stays generic.

## Build and gates

```sh
cd AES/working
make          # build all eight files
make check    # build, then the gates below
```

| gate | expected |
|---|---|
| all eleven files above | compile clean, no warnings |
| `grep "Theorem gen_iff_accepts" *.v` | exactly one hit, `protocol_lib.v` |
| `grep "Admitted\|admit()\|assume()\|external_body" *.v` | no hits |
| `git -C ../../vostd status --porcelain` | no tracked change (vostd is read-only for this work) |

`mutex.v` supplies the transition table and seven regression tests and
does not depend on the library; `guard_demo.v` only exercises the
`finish_goal`/`finish_db` automation.
