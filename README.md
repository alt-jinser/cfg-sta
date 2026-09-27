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
| `CLIENT_CFG_CASE.md` | two proved protocol pilots and a functional mm client/spec-gap audit |
| `DECISIONS.md` | what was chosen, and what each choice rules out |

The other `.v` files: `mutex.v` (transition table + regression tests
only), `guard_demo.v` (automation demo), eight self-contained protocol
models, and three client CFG examples: `mutex_client_cfg.v` connects an
Asterinas Mutex client to the formal mutex spec, `xarray_client_cfg.v`
connects an XArray client to the SpinLock model, and
`mm_cow_client_cfg.v` checks the one-page COW property under explicit
candidate contracts.
Every protocol model header carries its provenance, a pre-registered
shape prediction, and the verdict.

## Source repositories

| path | role |
|---|---|
| `../vostd` | the Verus-verified OSTD: implementations, `ostd/specs/`, `docs/sync-protocol/`; the current COW embedding work modifies its spec/model files |
| `../asterinas` | the kernel and its own `ostd`: real client call sites, from a *different tree* -- the models' independent side |
| `../research` | task 1.1 research notes |

## Build

```sh
make        # compile all 14 files (nix + Rocq 9.1.1)
make check  # build, then the gates: exactly one `gen_iff_accepts`,
            # no Admitted/admit()/assume()/external_body
```

Commits: conventional type, title only.

## Status

8 protocol models / 6 protocols (5 real; `buffer` is synthetic), plus
two proved protocol-client pilots and one functional-property candidate
client model. Obligations
1-3: 8/8 mechanical.  Obligation 4: 7/8 (rcu needs a net measure).
Obligation 7: 7/8 from the library.  The shape criterion was
pre-registered and validated on rwlock, spin and rwmutex -- the
rwmutex run corrected it (target dispatch must be structural).  The
four pilots put real kernel call sites behind every real protocol.
Open questions live in `PIPELINE.md`; scope decisions in
`DECISIONS.md`.

The current COW integration status is in `CLIENT_CFG_CASE.md`: the path
accounting model now uses a multiset, so identical `TreePath` values under
separate page-table roots count as separate references. The runtime-backed
Map API proves exact base-page path insertion, including its `+1` multiset
length effect. The store-integrated Map/Unmap bridge, Rocq state refinement,
and production COW loop remain open. The last completed full Vostd run fails
at `CursorMut::unmap`'s `unmap_spec` postcondition (1575 verified, 1 error);
the preceding full run passed (1576 verified, 0 errors). Verification still
includes trusted embedding axioms. The Rocq client CFG
includes the matching action projection. The refinement from Rocq's
candidate transitions to the Verus store contracts, and the production
copy loop/MMIO cases, are still open.
