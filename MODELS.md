# The contract and its five models

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
one-tactic proof; `hand` = proof written out.

| model | 1–3 | 4 `prod_ok` | 5–6 `word_ok`/`word_ok_run` | 7 `word_ok_gen` |
|---|---|---|---|---|
| `mutex_grammar` | mech, mech, 1-line | mech (all 13) | 1-line + 1-line | **hand**: `gen_of_run`, 10 cases |
| `mutex_param` | mech, mech, 1-line | mech (guards split by `finish_goal`) | 1-line + 1-line | **hand**: 10 cases, 2 guard splits |
| `mutex_waitqueue` | mech, mech, 1-line | mech + manual `Wake` cell (2 goals) | 1-line + 1-line | **hand**: 17 cases; `Wake` cell opened by hand |
| `buffer` | mech, mech, 1-line | mech + 2 length cleanups | 1-line + 1-line | **hand**: 7 cases |
| `rcu` | hand, 1-line, 1-line | **hand**: 4 cases; `PB_cs` needs `reach_positive` | 1-line + 1-line | **hand**: `body_complete` + `dip_split` |

Obligation 4 is mechanical for four of the five models; obligation 7 is
hand-written in all five, and is the only obligation whose difficulty
tracks the grammar (right-linear ⇒ per-event induction; non-right-linear
⇒ a word cut).

Two constraints on the automation, for anyone adding a model with a
list- or guard-carrying nonterminal:

* Do not point `case_of` at a `list tid`: `destruct` on a list
  introduces another list, so the `repeat` would not terminate.  The
  queue is opened once, by hand, in the cells that read it
  (`mutex_waitqueue.v`, `rcu.v`).
* `simpl` folds `Nat.leb 1 (length items)` into a raw match on
  `length items`, which loses the production's guard; normalise with
  `cbn [run_from step available]` instead (`buffer.v`).

## Build and gates

```sh
cd AES/working
nix develop ./nix -c bash -c '
  rocq compile protocol_lib.v && rocq compile mutex.v &&
  rocq compile mutex_grammar.v && rocq compile mutex_param.v &&
  rocq compile mutex_waitqueue.v && rocq compile buffer.v &&
  rocq compile guard_demo.v && rocq compile rcu.v'
```

| gate | expected |
|---|---|
| all eight files above | compile clean, no warnings |
| `grep "Theorem gen_iff_accepts" *.v` | exactly one hit, `protocol_lib.v` |
| `grep "Admitted\|admit()\|assume()\|external_body" *.v` | no hits |
| `git -C ../../vostd status --porcelain` | no tracked change (vostd is read-only for this work) |

`mutex.v` supplies the transition table and seven regression tests and
does not depend on the library; `guard_demo.v` only exercises the
`finish_goal`/`finish_db` automation.
