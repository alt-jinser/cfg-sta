# Client-driven CFG pilots

## Spec-backed Mutex client: character-device lookup

The primary anchor is `../asterinas/kernel/core/src/device/registry/char.rs`,
`lookup` (around line 46):

```rust
pub(super) fn lookup(id: DeviceId) -> Option<Arc<dyn Device>> {
    DEVICE_REGISTRY.lock().get(&id.to_raw()).cloned()
}
```

The temporary `MutexGuard` protects the map lookup and is released when the
expression completes. Repeated calls to this helper are described by the
CFG in `mutex_client_cfg.v`:

```text
Client -> ε | Acquire Lookup Release Client
Lookup -> Access
```

The client product model proves that `Access` occurs while the lock is held
and that each completed call returns with the lock unlocked. Erasing the
client-only `Access` event and adding the one-time `Create` event projects
every generated trace into the language of `mutex_grammar.P`. That model's
transition table comes from the Verus mutex protocol spec at
`../vostd/ostd/specs/sync/mutex_protocol.rs`.

This is inclusion, not equality. The API spec accepts a prefix ending after
`LockAcquire`; a completed lookup call does not. Both facts are checked in
Rocq. The result meets the narrow client-to-formal-spec part of the plan:
the CFG describes a real client usage family and its lock traces satisfy
the existing mutex protocol spec.

The evidence is limited to lock discipline. `Access` is erased because the
mutex protocol spec does not model map contents, so this proof does not
establish that lookup returns the correct device, nor does this single-lock
trace prove global mutual exclusion across interleavings. It finds no spec
gap; it shows the client family is supported by the current lock spec.

## Implementation-only SpinLock client: XArray insertion loop

## Source client

The anchor is `../asterinas/kernel/libs/xarray/src/test.rs`,
`init_continuous_with_arc` (line 19):

```rust
for i in 0..item_num {
    let value = Arc::new(i);
    xarray.lock().store(i as u64, value);
}
```

`XArray::lock` constructs a `LockedXArray` holding a `SpinLockGuard`
(`../asterinas/kernel/libs/xarray/src/lib.rs`). `LockedXArray::store`
requires `&mut self`; the temporary locked wrapper is dropped at the end
of the statement. This gives the client interaction pattern
`Acquire · Store* · Release` per loop iteration. The indices, values, and
loop bound are abstracted away because this pilot concerns the guard
protocol only.

## CFG and property

The CFG is written directly as the two recursive trace relations in
`xarray_client_cfg.v`:

```text
Client -> ε | Acquire Body Release Client
Body   -> ε | Store Body
```

The client-level transition relation rejects `Store` when the lock is
free. Rocq proves:

- each generated body runs from `Locked` back to `Locked`, so each `Store`
  occurs while the guard is live;
- every complete generated client trace returns in `Free`;
- erasing the client-only `Store` events projects every CFG trace to a
  trace accepted by the existing SpinLock protocol model.

This is a **language inclusion** result: complete executions of this
client are allowed by the lock model. Equality would be the wrong claim.
The SpinLock protocol accepts the held prefix `Lock`, while this CFG
describes a helper that completes each statement and returns with its
temporary guard released. Rocq checks both facts.

## Evidence and limits

This is a manually derived, source-anchored CFG example, not an automatic
grammar synthesizer. It abstracts one single-threaded loop and omits
concurrent clients, fairness, data values, and XArray functional
correctness. The Asterinas call site is in a different checkout from the
Verus implementation, and the current SpinLock protocol model is derived
from implementation behavior: there is no independent formal SpinLock
spec in `vostd/ostd/specs/sync/` to test for sufficiency. Thus this pilot
demonstrates that a client-derived CFG can state and prove a useful usage
property against an API model, but it does **not** yet establish a spec
gap (or prove the authoritative API spec sufficient). The gap-reporting
part of the intended workflow remains open.

The experiment also clarifies the role of the broader CFG models in this
repository: they are API/protocol languages and proof infrastructure;
they are not, by themselves, top-level properties synthesized from
clients. This file is the first client-side link, with explicit
provenance and a deliberately narrow claim.

## Reproduce

```sh
make check
```

## Functional-property pilot in progress: copy-on-write page-table copy

### Client and CFG

The next source anchor is the real Asterinas regression test
`../asterinas/kernel/core/src/vm/vmar/vmar_impls/fork.rs::test::cow_copy_pt_basic`
(around line 144). It supplies a small instance of the production
`cow_copy_pt` loop: one parent mapping is copied into a child page table,
then the parent mapping is removed.

For the one-page RAM case, the client interaction CFG is:

```text
Scenario -> MapParent CheckParent CopyToChild CheckBoth
            UnmapParent CheckChild
CopyToChild -> FindNext QueryParent ProtectParent JumpChild MapChild
```

`CheckParent` and the later checks stand for client assertions, not API
operations. The source asserts that the original mapping has physical
address `paddr` and RW flags; after `cow_copy_pt`, parent and child both map
`paddr`; after unmapping the parent, the child still maps `paddr` with R
flags. This is a manually extracted one-iteration CFG, not yet a
full implementation proof. `mm_cow_client_cfg.v` machine-checks the
one-page grammar and assertions against an abstract state whose operation
semantics encode the candidate postconditions below. Its theorems quantify
over the physical address instead of fixing a sample frame. It does not
encode address validity or ownership, model the full loop (which also
handles MMIO and arbitrary ranges), or establish that the Verus
implementation satisfies those candidate postconditions.

### Source-to-verified-API alignment

The selected Asterinas `kernel/` checkout and this Vostd checkout have
different `VmSpace` API shapes. The one-page RAM CFG is an extraction from
the former, not a verified invocation of the latter. The following mapping
is the proposed normalization; each mismatch remains an explicit proof
obligation.

| Source event | Asterinas call (`fork.rs`) | Vostd / embedding status |
|---|---|---|
| `FindNext` | `src.find_next(remain_size)` guards the loop with `Some(mapped_va)` (:92) | Vostd has `find_next(len) -> Option<Vaddr>`. A verified runtime store wrapper now calls it against the tracked `CursorEntry` in place and proves the store invariant. The proof-only `lemma_step_find_next` still uses the older store-level trusted axiom; its precondition requires page-aligned `len` within the cursor range. |
| `QueryParent` | `src.query()` returns `VmQueriedItem::MappedRam { frame, prop }` (:93-100) | Vostd returns `MappedItem { frame: UFrame, prop }`, without that enum split. `cursor_query_store_api` now runs real Query against a tracked cursor entry. It registers a returned handle at a fresh Frame ID and proves store structure/accounting, or preserves frames/accounting when the result is `None`. The proof-only generic `lemma_step_query` remains a trusted store-level mirror and is not yet connected to the runtime wrapper. |
| `ProtectParent` | `op` mutates `&mut PageFlags` and `&mut CachePolicy`; `protect_next` advances the source cursor (:88-102, :116-117) | The general `Op::ProtectNext` remains callback-free. A client-specific `CowProtectNext` embedding action represents the one-page callback that removes W, returns the protected range, and changes exactly the selected mapping under `protect_mapping_update_at`. This is a trusted store-level mirror. |
| `JumpChild` / `MapChild` | `dst.jump(mapped_va)` then `dst.map(frame, prop)` (:104-106) | The runtime trace requires the destination cursor to already point at `mapped_va`, so Jump is an identity step and is omitted. `cursor_map_store_api` now consumes the Query-registered `FrameId`, borrows the source cursor's tracked `EntryOwner`, and calls real `CursorMut::map` into an absent base-page slot. Its contract proves the target view's `map_spec` transition and preserves `VmStore::inv()`. The generic proof-only Map step remains a trusted mirror. |
| `UnmapParent` | A fresh parent cursor calls `unmap(map_range.len())` after the copy (:198-202) | Vostd's exec contract has `CursorView::unmap_spec`. A new `cursor_entry_unmap_api` invokes runtime `CursorMut::unmap` and proves the cursor/view and safety invariants. Its metadata accounting effects are not yet exposed, so the store-level Unmap bridge and client wiring still rely on the trusted mirror. The latest full Vostd verification fails at the `CursorMut::unmap` proof of `unmap_spec`; trusted embedding axioms also remain. |
| MMIO branch | `MappedIoMem`, `find_iomem_by_paddr`, `map_iomem` (:110-124) | `mm_cow_client_cfg.v` now has a separate candidate trace that preserves the parent's permissions, maps the same PA into the child, then checks child persistence after parent unmap. It has no Vostd action projection: this Vostd `VmSpace` interface has no IoMem handle or `map_iomem` operation. |

Cursor-position detail: successful `protect_next` and `map` advance the cursor
past the protected or mapped range. The runtime Map contract records the
destination view's `map_spec` transition at the original VA while the cursor
advances by one page. The later parent Unmap path still uses its own cursor
positioning step.

The source test's functional assertions are at `fork.rs:161-165`,
`:176-195`, and `:204-207`. The proposed RAM path additionally assumes
successful cursor opens, `FindNext`, `Query`, `ProtectNext`, and `Jump` at
the points where the source unwraps or pattern-matches their results.

### Contract audit and current result

The API has relevant pieces. `ostd/specs/mm/vm_space.rs::map_item_ensures`
states that mapping transforms the cursor view by `map_spec`; and
`Cursor::query_success_ensures` relates a successful query's returned item
and range to `CursorView::query_item_spec`. These can express local
map/query facts. At the lower view level, `CursorView::unmap_spec` also
states that mappings outside the unmapped interval are preserved in that
same view.

The one-page client path now reaches a functional Vostd store theorem in
`embedding/trace.rs::cow_ram_copy_then_parent_unmap`. Starting from one RW
base-page mapping in the source and an empty child view, it composes:

```text
FindNext -> Query -> CowProtectNext -> Jump(child) -> Map(child) -> Unmap(parent)
```

On the successful path, the returned `(VA, PA)` is tied to the original
source mapping. Before unmap, both parent and child views query that PA with
the write bit cleared; after unmap, the parent is absent at the VA and the
child still queries the same PA with the same COW property. The proof uses
`CursorView::unmap_spec`, the cursor-isolation postcondition of the store
step, and the mapped-frame handle created by Query. It assumes distinct
source/destination cursors, a single base-page source mapping, an empty child,
and a destination cursor range covering that page. These are the selected
regression case's scope, not the full loop's general case.

The Asterinas MMIO branch is represented separately in the Rocq candidate
CFG: it does not protect the parent mapping, preserves the queried PA and
permissions in the child, and checks that the child remains mapped after
parent unmap. The missing IoMem operations in Vostd mean this branch is not
connected to a Vostd trace.

The runtime prefix `cow_ram_runtime_find_query_protect_map` executes
FindNext, Query, COW protection, and Map through real cursor APIs and the
shared `VmStore`; a preceding full Verus run passed with 1576 verified, 0
errors. The latest completed full run fails in the strengthened Unmap proof
(1575 verified, 1 error). This is not yet the complete client proof: generic FindNext, Query,
Map, and `CowProtectNext` still have trusted store-level mirrors, and this
driver has not been composed with executable Unmap or the Rocq observation
bridge. Exec `protect_next` also proves that success advances the concrete
cursor to the returned range end. The RAM trace uses the explicit
`CowProtectNext` action because the general callback-taking API cannot yet be
represented in `Op`. The generic `run` theorem still proves
only invariant preservation for arbitrary precondition-valid operations. The
unmap embedding additionally exposes metadata path/refcount accounting and
preserves other cursor entries.

The x86 COW property-preservation lemma is now proved: removing W preserves
`PageProperty::inv`, the read bit, and the cache condition in
`PageTableEntryTrait::new_page_req`. The callback trackedness requirement has
also been tightened across `Entry::protect`, `Cursor::protect_cur_entry`,
`Cursor::protect_next`, and `CursorMut::protect_next`: it now applies only
when the old raw item is well formed. This excludes invalid option encodings
that the cursor cannot obtain from a valid owner, and the complete Verus run
still passes.

A direct `CursorMut::protect_current` operation is now exposed at both the
page-table cursor and `VmSpace::CursorMut` API layers. It protects the frame at
the cursor without calling `find_next_impl`, so its mapping update is
unconditional under the current-entry frame precondition. `protect_next` now
calls this same operation after its search. This removes the search-success
obstacle for a client that already has a current-frame proof. The operation
leaves cursor position unchanged. A generic `cursor_entry_protect_current_api`
now executes this verified operation against the runtime cursor and paired
tracked `CursorEntry`, proving entry invariants, region preservation, callback
property postconditions, and the mapping update. A generic
`cursor_protect_current_store_api` composes that bridge with a mutable borrow
of `VmStore.cursors[c]`; it proves `VmStore::inv` and leaves regions, frame
accounting, and unrelated store entries unchanged. `VmSpace::CursorMut::advance_current`
exposes the verified underlying `move_forward` transition, including guard
transfer, and `cursor_advance_store_api` proves the corresponding store
transition. The specialized `cursor_cow_protect_next_store_api` now composes
the executable W-clearing callback, protection, and advance. Its postconditions
establish the one-page range, cursor movement, unchanged mapping geometry and
PA, and the final read-only property under
`protect_mapping_update_at`. This replaces the dedicated COW protect-and-advance
store mirror for this one-page path. It does not yet connect this runtime
wrapper to the proof-only trace or discharge Rocq's candidate transition.

`VmStore` stores ghost `CursorOwner` values, while exec methods require
runtime `Cursor` / `CursorMut` handles tied to an RCU guard. Per-operation
wrappers can now accept both the runtime handle and the corresponding tracked
store entry, but the proof-only trace does not retain or pass those runtime
handles. Three Jump bridge layers exist in Vostd's `embedding/cursor.rs`:
`cursor_jump_api` calls verified exec `CursorMut::jump` with a runtime cursor
and its tracked owner, regions, and guards; `cursor_entry_jump_api` carries
those resources inside a tracked `CursorEntry` and requires the runtime
cursor's barrier range to match the entry range; `cursor_jump_store_api`
borrows the entry in place from `VmStore.cursors`, calls the runtime API, and
proves the store invariants afterward. Full Vostd verification proves all
three wrappers. The proof-only `lemma_step_jump` still goes through the
existing `lemma_cursor_jump_embedded` axiom, so the abstract `Op` trace has
not yet been switched to this runtime path. A `cursor_entry_find_next_api`
now similarly calls the verified runtime `find_next` using a tracked
`CursorEntry` and its metadata regions. The store-level
`cursor_find_next_store_api` borrows the entry in place, proves the store
invariants, and exposes the full single-step transition facts: unrelated
store resources and cursors are unchanged, the selected mapping view and
locked range are preserved, the result agrees with both the runtime VA and
tracked owner VA, and the scan neither skips an earlier mapping nor advances
less than `len` on `None`. FindNext can materialize metadata slot permissions
while visiting page-table nodes: its verified contract preserves the
`slot_owners` map and all pre-existing slot permissions, while allowing the
slots map to grow. The wrapper transports `metaregion_sound` for every
unrelated cursor across that monotonic growth. The proof-only
`lemma_step_find_next` still uses `cursor_find_next_store_embedded`; the
remaining mismatch is architectural—the abstract proof trace has only ghost
`CursorEntry` values and no runtime cursor handle to pass to this wrapper.
The same runtime-entry layer now exists for Query:
`cursor_entry_query_api` calls the real `CursorMut::query` with the tracked
entry's owner, metadata regions, and guards, and verifies the exec query
postconditions, owner cursor position/view preservation, entry invariant, and
regions invariant. It also proves that a returned `Some(item)` corresponds to
a present view mapping and that `item.frame`'s physical address matches that
mapping. The verified exec `Cursor::query` contract now also exposes the exact
single-slot `inc_frame_reference_region_spec` transition for the returned
tracked frame. Its proof composes the local `clone_item` contract with the
query-loop facts that preserve the `slots` map and the `slot_owners` map before
the clone; the full Vostd run verifies this contract and the entry bridge.
The bridge returns the real optional `MappedItem`, including its cloned frame
handle. `cursor_query_store_api` now handles both Query results. When a mapping
is present, it registers a fresh `FrameEntry`, transports the exact one-slot
reference increment across unrelated cursor owners, and proves both
`structural_inv` and `accounting_inv`. When Query returns `None`, the exec
contract proves both metadata-region maps unchanged, allowing the wrapper to
preserve all cursor soundness and store accounting. `UserPtConfig` ties a
present UFrame permission to a `PageUsage::Frame` slot, and the clone contracts
preserve that fact for the returned handle. The full Vostd run verifies both
branches. The abstract `lemma_step_query` remains a trusted mirror and is not
wired to this runtime wrapper because the abstract trace carries no runtime
cursor handle. Store-level COW protection, Map, and Unmap bridges also remain
before connecting the runtime sequence to the Rocq CFG.
Until then, those operations' store-level claims remain trusted even where
their exec methods have useful verified postconditions.

The attempted next step, a runtime cursor-open wrapper, exposes a deeper
ownership mismatch. `VmSpace::cursor_mut` forwards a `PageTableOwner` by
value to `PageTable::cursor_mut`; `CursorMut::new` consumes that owner and
returns a `CursorOwner` whose page-table view is that same owner. In contrast,
`VmStore.vm_spaces[vs]` retains its `page_table_owner`, and the trusted
`vm_space_cursor_mut_embedded` contract both preserves that VM-space owner and
creates a cursor owner. A wrapper cannot call the runtime API from the stored
owner while also keeping the same tracked resource in the VM-space entry.
Therefore opening a cursor is not yet connected to an executable client
sequence. The next design step is to model an explicit ownership transfer or
split at open, and the corresponding return/merge on cursor close, before
replacing the open axiom. There is a concrete close-side building block:
`CursorContinuation::tracked_restore` can reassemble a child subtree into its
parent, and `CursorOwner::as_page_table_owner` specifies the reconstructed
tree. The missing piece is a tracked `CursorOwner` close operation that
performs the full continuation restoration, reconciles the returned guards
with the VM-space state, and makes the root owner available again. Treating
the cursor owner as a clone of the VM-space owner would duplicate linear
ownership and is not a valid bridge.

`mm_cow_client_cfg.v` separately proves the candidate state property for the
one-page CFG. It now also defines the projection from the normalized
Vostd-action sequence to the CFG event sequence and proves that projection
is exactly the recorded scenario trace. The three assertion events are
executable state checks, and a further Rocq theorem proves that the projected
trace passes them and ends with the parent absent and the child retaining the
same read-only PA. This checks event alignment and the candidate model's
assertions; a negative regression also shows that skipping parent write
protection is rejected at `CheckBoth`. The Rocq `State` transition relation
remains a candidate contract and is not extracted from the Verus execution
theorem. There is still no
formal theorem that discharges the Rocq candidate operations from the Verus
trusted mirrors.
At this intermediate stage, the full Vostd run reported `1551 verified, 1
error`; the cursor address-overflow proof was subsequently resolved.
`embedding/trace.rs::run` continues to ensure only the store invariant.

The generic query event also remains result-free: `lemma_step_query` returns
the handle and paddr, and the specialized COW trace consumes them, while the
generic `lemma_step` dispatcher discards that observation. General clients
would need result-bearing operations rather than this scenario-specific
composition.

The exec-side `find_next` contract now carries additional results through
`Cursor::find_next`, `CursorMut::find_next`, and
`VmSpace::CursorMut::find_next`: `Some(va)` identifies a frame at the final
cursor position, with `owner@.present()` and the existing frame-property
preservation relation; `None` preserves the abstract mapping set. These
facts come from `find_next_impl` and `lemma_cur_entry_frame_present`.
The public contract also carries the scan guarantee that no mapping starting
between the old and final cursor addresses was skipped; `None` moves at
least `len` bytes. `cow_find_next_at_mapped_start` proves from those clauses
that the selected base-page mapping at the starting address must yield
`Some(va)`. The embedding step now returns `Option<Vaddr>`, updates the
observed cursor position, and `cow_ram_cursor_path` branches on the returned
address. Its store-level trusted axiom preserves the client-visible mapping
set, Frame handles, VM-space/TLB state, unrelated cursors, and Frame-slot
owners. It does not claim every metadata slot is unchanged: page-table
traversal can materialize additional non-Frame metadata slot permissions.
The runtime FindNext store wrapper proves the store invariant under this
monotonic slot growth; the proof-only trace still uses the trusted mirror.
The FindNext transition remains within the latest Vostd run, which currently
has one unrelated cursor address-overflow proof failure.

The COW client's single-page RAM behavior has a Verus-checked candidate
embedding trace and a Rocq event projection, but the Map mirror audit below
means the trace is not yet sound evidence for runtime behavior. The COW
protection-plus-advance
operation is now an executable verified store wrapper, but the proof-only
trace still invokes the older trusted embedded operation. This is an
architectural limitation in the current embedding: `cow_ram_cursor_path` is a
proof function and cannot call the runtime wrapper, which requires a real
`CursorMut`; `CursorEntry` stores only its ghost `CursorOwner` and guards.
`FrameEntry` records a paddr while the queried `UFrame` is returned to the
caller. A runtime-backed driver can carry these handles as explicit arguments,
but must keep each runtime handle paired with its store id and synchronize
ownership across API calls. Other store-level mirrors remain axioms, and
Rocq's candidate state steps are not proved from the Verus execution
contracts. `mm_cow_client_cfg.v` now states the missing observation bridge:
`PageViewObservation` records the selected mapping's PA, writable bit, and
RAM/IoMem kind; `state_refines_observation` erases a pair of those observations
to the Rocq `State`. The `ApiObservationPost` relation spells out the
one-page operation facts needed for MapParent, ProtectParent, MapChild, and
UnmapParent. Rocq proves that each such postcondition simulates the CFG state
step, and that a trace of these postconditions simulates `run`. These are
explicit premises, not facts derived from the current Vostd wrappers. The
`cow_scenario_has_api_observation_witness` lemma constructs these premises for
the selected COW witness, and `cow_api_observation_trace_matches_cfg` proves
that its abstract final observation erases to the candidate final state. The
remaining bridge must extract the one-page observations from actual
`CursorView` states and prove each `ApiObservationPost` from its executable
operation contract. These gaps remain before claiming an end-to-end
client-to-authoritative-spec theorem.

### Map mirror audit finding and repair status

`MetaSlotOwner.paths_in_pt` now uses the `PtPaths` wrapper over a multiset.
`TreePath` still records only page-table indices, but inserting the same path
from another page-table root increments its multiplicity. Removing one mapping
decrements only one occurrence, and `len()` counts aliases separately for
`accounting_inv`. This repairs the specific Set-idempotence mismatch identified
in the COW audit.

The generic proof-only Map/Unmap store transitions remain trusted mirrors.
For the empty base-page Map case, the runtime
executable `CursorMut::map` contract now proves exact insertion of the
continuation path for an absent base-page slot, and
`cursor_entry_map_api` exposes both that multiset equality and its `len() + 1`
effect. `PtPaths::lemma_len_insert` states the occurrence-count rule directly.
The Vostd cursor-owner proof now transfers `metaregion_sound` across this path
insertion while allowing unrelated slots to transition from unused non-MMIO
slots to newly allocated page-table nodes. `cursor_map_store_api` consumes the
stored `FrameId`, borrows the stored cursor entry in place, and invokes
`cursor_entry_map_api` with the caller's tracked `EntryOwner`. Its verified
postcondition includes the full `VmStore::inv()`. The proof shows that removing
one frame handle balances the one inserted path occurrence, the target
refcount is preserved, and the other cursors remain structurally sound. For the leaf-level
absent-slot case, the executable Map contract also proves that every
non-target slot owner and the metadata-slot map are unchanged; at the target,
permissions, usage, and slot address are preserved. `cursor_entry_unmap_api`
now invokes the real `CursorMut::unmap` and verifies its cursor-view transition,
but executable unmap does not yet expose the per-slot path/refcount relation
required to prove store accounting. The gap is in the current TLB boundary:
unmap passes removed frames to `TlbFlusher::issue_tlb_flush_with`, while
`OpsStack.page_keeper` is commented out and `dispatch_tlb_flush` is
`external_body` with no `MetaRegionOwners` argument. `TlbModel` records pending
flush operations but not the frames held for those flushes or their eventual
metadata-reference release. Its dispatch spec previously applied only the
last pending operation, while one `CursorMut::unmap` call can queue several
flushes before a single dispatch. The dispatch spec now applies the entire
queue in order; `Address` invalidates all covering mappings and `Range`
invalidates every intersecting mapping. The subset lemmas prove that this
preserves the TLB invariant. The full Vostd run passes with 1560 verified, 0
errors.

The `TlbModel` carries pending and in-flight frame addresses. The
`issue_tlb_flush_with` contract records the consumed frame address; dispatch
moves those records to the in-flight queue, and the `sync_tlb_flush` contract
clears them only at completion. `tlb_frame_count` counts these retained
references per metadata slot, and `VmStore::slot_resource_count` now includes
that count in the Frame reference equation. `slot_accounting_inv` also rules
out TLB-held references to UNUSED slots and requires referenced slots to remain
Frame or PageTable metadata. The store-level Unmap postcondition conserves
page-table paths plus TLB-held references while preserving the region
refcount. Segment operations, Frame allocation, and store-integrated Map have
proofs maintaining this invariant. The full Vostd verifier passes with 1565
verified, 0 errors.

The abstract store `Map` step is restricted to a view with no mapping at the
current cursor address. Mapping over an existing leaf issues a TLB flush in the
runtime `CursorMut::map` implementation, so its retained old-frame reference
must be modeled as a separate replacement transition before general Map can be
claimed. The runtime-backed `cursor_map_store_api` additionally requires the
tracked current page-table entry to be absent; the current abstract COW trace
does not yet prove that lower-level condition from its view state.

This closes the TLB-count-to-store-accounting proof obligation at the abstract
`VmStore` layer. Some transitions still depend on trusted embedding axioms,
including the metadata effects of `cursor_mut_regions_step`; this does not
establish that runtime TLB dispatch retains and releases real `Frame` handles.

The fragment-address validity chain is now explicit. `Frame::into_dyn` preserves
`ptr_inv` and the physical address across metadata erasure. Cursor map
replacement exposes well-formedness of a returned mapped item, while
`take_next` exposes mapped-item well-formedness and `ptr_inv` for the stray
page-table frame. `issue_tlb_flush_with` now requires `ptr_inv`, and
`TlbModel::inv` requires valid addresses in both pending and in-flight queues.
The full Vostd verifier passes with 1565 verified, 0 errors.

Runtime `dispatch_tlb_flush` is still an `external_body` and its implementation
is commented out in this checkout. In the source design, dispatch can return
before remote CPUs finish; `sync_tlb_flush` is the completion boundary.
`OpsStack.page_keeper`, which should retain `Frame` handles across that
interval, is commented out, as is its transfer to per-CPU queues and its
release after flushing. Thus the verified contracts establish the intended
abstract lifetime at trusted boundaries, but not from executable runtime
code. An attempt to put the expected per-slot relation directly on executable
`CursorMut::unmap` still does not expose its metadata effects through a
runtime-backed store API. The store-level `lemma_step_unmap` now proves the
path/TLB conservation relation, but its cursor metadata transition still uses
a trusted embedding axiom. Runtime `dispatch_tlb_flush` and `sync_tlb_flush`
also remain external/trusted boundaries, and the `page_keeper` storage is
commented out. The proof-only `lemma_step_map` and `lemma_step_unmap` remain
trusted mirrors, and the COW trace is not wired end-to-end to runtime APIs. The
full Vostd run at this stage passed (1565 verified, 0 errors); this includes the
existing embedding axioms and is not, by itself, consistency evidence for
them.

The low-level path removal has an explicit multiset-length lemma, and the
huge-page split path uses it to prove that removing one `TreePath` occurrence
decreases the slot's path count by one. `take_next` now exports this exact
count change for a scoped case: when the search starts at a present base-page
mapping and returns a `Mapped` fragment, that mapping's PA slot loses exactly
one path occurrence. This does not yet cover a `StrayPageTable` fragment,
huge-page splitting, or the complete runtime Unmap/TLB handoff.

The `find_next_impl` contract closes one specific search gap: if
the pre-state contains a mapping whose start lies in the requested scan window,
the result must be `Some`. This is derived from the loop's end condition and
the fact that a `None` result proves the scanned interval contains no mapping
start. It lets callers rule out a false `None` for a mapping in range, but does
not determine whether a returned `take_next` fragment is a mapped frame or a
stray page-table subtree.

`take_next` inherits that foundness guarantee: any pre-state mapping
whose start is inside its scan window forces a `Some` fragment. The guarantee
is proved through the call to `find_next_impl`; it rules out the no-result
branch for mapped input without conflating a frame fragment with a whole
subtree fragment.

`replace_cur_entry` states and proves that a returned `Mapped` fragment keeps
its PA slot's `paths_in_pt` multiset unchanged during replacement. Combined
with the search contract and the local multiset-removal lemma, `take_next`
proves that the pre-search view mapping's PA loses one path occurrence in the
base-page case. The condition is view-based: the mapping must be present at
the scan start, have `PAGE_SIZE`, and the result must be `Mapped`. This avoids
assuming that an arbitrary initial raw entry PA equals a later returned
fragment PA. It now also guarantees that this returned fragment denotes exactly
the queried pre-search mapping. For a one-page search that returns
`StrayPageTable`, it also proves that the fragment starts at that mapping and
contains exactly one mapped frame; for either fragment variant, `take_next`
advances exactly one page. The full Vostd run passes (1566 verified, 0 errors).
The outer `CursorMut::unmap` contract now proves that this case returns one.
The loop invariant records the fixed concrete start VA and its relation to
`end_va`, while a saved `remaining_len` makes the one-page `take_next`
precondition explicit. The one-page invariant covers both `Mapped` and
`StrayPageTable` results; the `None` branch is contradicted using the
pre-call mapping and cursor snapshot because `take_next(None)` has already
advanced the current view. The full Vostd run passes (1566 verified, 0 errors).

This closes the scoped one-page return-count obligation. The general range
contract remains open across arbitrary mappings, absent gaps, and huge-page
boundary splits. `CursorView::unmap_spec` now relates `num_unmapped` to
`unmap_count(len)` for a present base mapping at the cursor when `len` is one
page and the exclusive end address is representable. The helper lemma proves
that this normalized count is one by using view non-overlap and the mapping
fragment normalizer. The separate one-page return-count clause remains. The
exclusive-end guard matters because the current count interface stores the end
as `Vaddr`, so a range ending at the top of the address space wraps there.
`CursorView::unmap_count` defines the recursive count per
old mapping through `unmap_mapping_fragments` and combines them into
`unmap_fragments_set`; `unmap_count` is the normalized set's cardinality.
Disjoint mappings contribute no fragments, fully covered mappings contribute
one, and partially covered huge mappings recurse into their next-level
children. Thus a huge mapping fully inside the interval counts once; only
partial overlaps split recursively. This matches the runtime behavior, where
`take_next` enables huge-page splitting and may return either one mapped entry
or a whole stray subtree. Verus now proves the base fragment lemmas and the
one-page count lemma, and a full run passes (1569 verified, 0 errors). The
remaining obligation is to prove that the loop's `removed` set refines this
measure for general ranges. The `unmap` implementation previously used an
overflow `assume` for `cursor_va + len` (issue #3159). It now checks
`cursor_va <= barrier.end` and `len <= barrier.end - cursor_va` before adding,
which makes the range check itself overflow-safe and proves the later end
calculation safe. A full Vostd verification passes (1569 verified, 0 errors).
A first
no-boundary range-count invariant
was rejected because `take_next` can change `adjusted_base` by splitting a
huge mapping, and the attempted cursor-prefix removal invariant does not hold
on the `None` break path. A frame-kind postcondition on `find_next_impl` was
also tried but does not follow from the current view-only condition. A direct
recursive split equation for the normalizer also remains unproved: even when
its preconditions force the partial-overlap recursive branch, revealing one
unfolding does not establish equality with the child-fragment union. Repeating
the branch conditions exactly as Boolean preconditions has the same result.
That equation is needed to relate runtime huge-page splits to the normalized set.
Factoring that union into a spec helper called by the recursive normalizer
creates a mutual-recursion cycle, which Verus rejects for lack of a decreases
clause; no such helper was retained. Making the depth function `closed` and
revealing it explicitly did not discharge the equation and also broke an
unrelated embedding postcondition, so the function remains `open`.

For a present base-page mapping at the scan start, `find_next_impl` also proves
that the search leaves mappings and metadata owners unchanged. Its loop
invariant tracks metadata preservation until an actual huge-page split occurs.
This gives the caller a stable view and metadata snapshot for the `Mapped`
path-count postcondition.

There is an implementation-side reason the general postcondition is
nontrivial: `find_next_impl` can split a huge mapping, making the protected
sub-mapping absent from the original view. The current public contract uses
`old(owner)@.split_while_huge(size)` as its pre-protection baseline. The
selected regression case maps one base page; the general contract must
still account for splitting. The underlying
`find_next_impl` contract already states, in the `res is Some && split_huge`
case, that the post-view equals
`old(owner)@.split_while_huge(page_size(final(self).level))`; this gives the
precise pre-protection view used by the verified
`protect_mapping_update_at` relation.

For the test's base-page case, the verified `protect_next` clause handles the
selected mapping after splitting any huge page. Given
`old_view` containing `(va, paddr, PAGE_SIZE, prop)`, with `va` the current
cursor address and `len == PAGE_SIZE`, require a callback result `prop'`
such that `op.requires((prop,))` and `op.ensures((prop,), prop')`. The
post-view contains `(va, paddr, PAGE_SIZE, prop')`, preserves every
mapping outside `[va, va + PAGE_SIZE)`, and contain no writable mapping for
that page when the callback ensures `prop'.flags == PageFlags::R`. The
separate child view remains unchanged in the pure two-view composition theorem.
After mapping that same frame/property into the child, `map_item_ensures`
gives the child's mapping; after parent unmap, the child-view equality plus
the child query contract gives the persistence assertion. This is the
smallest useful contract target; a generic range postcondition can follow.

### Remaining concrete steps

1. **Runtime Map prefix verified; Unmap integration remains.** The
   `cow_ram_runtime_find_query_protect_map` driver executes FindNext, Query,
   source COW protection, and destination Map over two actual `CursorMut`
   handles sharing one `VmStore`. Query registers the cloned frame under a
   fresh `FrameId`; Map consumes that handle and borrows the source cursor's
   tracked `EntryOwner`, avoiding permission reconstruction. The target must
   be empty, at level 1, and have a guard level above 1; its locked range must
   cover the base page. Map's `map_spec` advances the destination cursor by one
   page and records the mapping at the original VA. A previous full Verus run
   passed (1576 verified, 0 errors). The last completed full run fails at the `unmap_spec`
   postcondition in `CursorMut::unmap` (1575 verified, 1 error).

   A subsequent attempt to prove the base-page count directly added special
   first-iteration reasoning to the loop. That attempt did not verify: interval
   arithmetic, loop invariants, and a split-locality precondition failed. The
   experimental special case was removed. The previous full-gate result above
   is the last completed verification result; this cleanup was checked with
   `git diff --check` but was not followed by another full verification run.

   `cursor_entry_unmap_api` now requires the runtime cursor VA to equal the
   tracked owner's current VA, matching the position condition already used by
   the query and protect wrappers. It still exposes cursor/view refinement,
   `metaregion_sound`, and TLB invariant preservation, but not the store's
   per-slot accounting transition. A verified `CursorView` lemma now states
   that two mappings covering the same VA in a non-overlapping view are equal;
   it passed with the full Verus gate, but has not yet been wired into Unmap.
   The lower-level `take_next` contract exports a path-count decrement for its
   current mapping, and the TLB model exports retained-frame counts. Those
   aggregate facts are sufficient in shape for slot-resource conservation;
   identifying the individual path is not required. The missing link is to
   carry a stable mapping witness through `take_next` and its TLB flush, then
   use the same physical-frame index in the store accounting proof. The
   attempted direct one-page postcondition did not verify, so no new Unmap
   accounting contract was retained.

   Remaining work is to connect executable Unmap's TLB-held frames and
   per-slot metadata effects to `VmStore::accounting_inv`, replace the
   proof-only Unmap mirror, and compose this runtime prefix with the abstract
   COW trace. FindNext, Query, Map, and COW protection still have trusted
   store-level mirrors; the Rocq observation bridge is also open. Keep the
   callback-free generic `ProtectNext` limitation explicit.
2. **Abstraction relation identified; operation bridge remains open.** Rocq
   now proves candidate-state simulation from `ApiObservationPost` and gives a
   witness trace. Prove each premise from the executable Vostd operation
   contracts by relating actual `CursorView` mappings to `PageViewObservation`.
   The event projection and conditional state simulation are checked; the
   Verus-to-Rocq postcondition bridge is not.
3. Redesign cursor creation/lifetime in `VmStore` to represent transfer of
   `page_table_owner` into the active cursor and its return on close; only
   then replace the open/drop axioms with runtime-backed wrappers. The model
   must retain the VM-space invariant while the cursor is active without
   duplicating linear ownership. After the runtime-backed driver and lifetime
   transfer are established, expand beyond the one-page RAM regression case
   to arbitrary ranges, huge-page splits, MMIO handling, and the production
   loop. The independent Asterinas source tree remains the client side of that
   expansion.
