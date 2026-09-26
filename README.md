# CFG ⇔ STA equivalence, proved once and reused

One theorem, proved once in Rocq and shared by every protocol model
in this directory:

```coq
gen_iff_accepts : forall tr, gen tr <-> accepts tr = true
```

`gen tr` = the trace derives from a context-free grammar; `accepts
tr = true` = the transition table never faults on it.  A model
supplies a table, a grammar and seven obligations, and gets the
equivalence for free.  The library states the theorem exactly once --
a gate checks it.  Proofs and documentation only; no production code.

## Reading map

| start here | what it holds |
|---|---|
| `MODELS.md` | the contract a model owes, the eight models, obligation by obligation, build + gates |
| `protocol_lib.v` header | the contract's design points, each with its reasoning |
| `PROVENANCE.md` | element-by-element audit of where every model part comes from; evidence layers per protocol |
| `PIPELINE.md` | what an automated code → grammar pipeline must produce: the shape criterion, four client-side pilots, open questions |
| `DECISIONS.md` | what was chosen, and what each choice rules out |

The other `.v` files: `mutex.v` (transition table + regression tests
only), `guard_demo.v` (automation demo), and eight self-contained
models.  Every model header carries its provenance, a pre-registered
shape prediction, and the verdict.

## Sources -- all read-only

| path | role |
|---|---|
| `../vostd` | the Verus-verified OSTD: implementations, `ostd/specs/`, `docs/sync-protocol/` -- must stay clean (gated) |
| `../asterinas` | the kernel and its own `ostd`: real client call sites, from a *different tree* -- the models' independent side |
| `../research` | task 1.1 research notes |

## Build

```sh
make        # compile all 11 files (nix + Rocq 9.1.1)
make check  # build, then the gates: exactly one `gen_iff_accepts`,
            # no Admitted/admit()/assume()/external_body, vostd untouched
```

Commits: conventional type, title only.

## Status

8 models / 6 protocols (5 real; `buffer` is synthetic).  Obligations
1-3: 8/8 mechanical.  Obligation 4: 7/8 (rcu needs a net measure).
Obligation 7: 7/8 from the library.  The shape criterion was
pre-registered and validated on rwlock, spin and rwmutex -- the
rwmutex run corrected it (target dispatch must be structural).  The
four pilots put real kernel call sites behind every real protocol.
Open questions live in `PIPELINE.md`; scope decisions in
`DECISIONS.md`.
