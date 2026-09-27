(* Contract-level CFG for the one-page RAM path in
     Asterinas::vmar_impls::fork::test::cow_copy_pt_basic.

   This is deliberately a candidate-contract model.  ProtectParent's step
   keeps the physical address and clears writable; MapChild copies that
   frame into a separate child view; UnmapParent changes only the parent.
   The Vostd embedding now has a result-bearing one-page RAM trace through
   FindNext, Query, COW protection, child Map, and parent Unmap. The action
   projection below checks that this normalized trace has the client CFG
   shape. The abstract State semantics remain candidate contracts; the
   trusted Verus embedding axioms are recorded in CLIENT_CFG_CASE.md.
   A separate IoMem candidate trace captures the source branch which maps
   device memory without write-protecting the parent; it has no Vostd action
   projection because the Vostd API has no matching IoMem mapping operation.
*)

Require Import Corelib.Init.Nat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Lists.List.

Import ListNotations.

Inductive Event : Type :=
| MapParent
| MapParentIoMem
| CheckParent
| FindNext
| QueryParent
| ProtectParent
| SkipProtectParent
| JumpChild
| MapChild
| MapIoMemChild
| CheckBoth
| CheckIoMemBoth
| UnmapParent
| CheckChild
| CheckIoMemChild.

(* Normalized Vostd embedding actions for the selected single-page case.
   Cursor creation is a precondition of the Verus trace; assertions are
   client observations between API calls. *)
Inductive EmbeddingAction : Type :=
| OpenSourceCursor
| OpenDestinationCursor
| CopyFindNext
| CopyQuery
| CopyCowProtectNext
| CopyJumpChild
| CopyMapChild
| AssertBothMappings
| CopyUnmapParent
| AssertChildMapping.

Definition project_embedding_action (op : EmbeddingAction) : list Event :=
  match op with
  | OpenSourceCursor | OpenDestinationCursor => []
  | CopyFindNext => [FindNext]
  | CopyQuery => [QueryParent]
  | CopyCowProtectNext => [ProtectParent]
  | CopyJumpChild => [JumpChild]
  | CopyMapChild => [MapChild]
  | AssertBothMappings => [CheckBoth]
  | CopyUnmapParent => [UnmapParent]
  | AssertChildMapping => [CheckChild]
  end.

Definition vostd_one_page_embedding_trace : list EmbeddingAction :=
  [OpenSourceCursor; OpenDestinationCursor; CopyFindNext; CopyQuery;
   CopyCowProtectNext; CopyJumpChild; CopyMapChild; AssertBothMappings;
   CopyUnmapParent; AssertChildMapping].

Definition projected_vostd_one_page_trace : list Event :=
  [MapParent; CheckParent] ++
  flat_map project_embedding_action vostd_one_page_embedding_trace.

Inductive CopyBody : list Event -> Prop :=
| CopyBody_one_page :
    CopyBody [FindNext; QueryParent; ProtectParent; JumpChild; MapChild].

Inductive Scenario : list Event -> Prop :=
| Scenario_one_page : forall body,
    CopyBody body ->
    Scenario ([MapParent; CheckParent] ++ body ++ [CheckBoth; UnmapParent; CheckChild]).

Inductive PageKind := Ram | IoMem.
Record Page := mkPage { paddr : nat; writable : bool; page_kind : PageKind }.
Record State := mkState {
  parent_view : option Page;
  child_view : option Page
}.

Definition initial_state : State := mkState None None.

Definition step (pa : nat) (s : State) (e : Event) : State :=
  match e with
  | MapParent => mkState (Some (mkPage pa true Ram)) (child_view s)
  | MapParentIoMem => mkState (Some (mkPage pa true IoMem)) (child_view s)
  | ProtectParent =>
      match parent_view s with
      | Some p => mkState (Some (mkPage (paddr p) false (page_kind p))) (child_view s)
      | None => s
      end
  | MapChild =>
      match parent_view s with
      | Some p => mkState (parent_view s)
          (Some (mkPage (paddr p) (writable p) (page_kind p)))
      | None => s
      end
  | MapIoMemChild =>
      match parent_view s with
      | Some p => mkState (parent_view s) (Some (mkPage (paddr p) (writable p) IoMem))
      | None => s
      end
  | UnmapParent => mkState None (child_view s)
  | _ => s
  end.

(* Assertions in the client trace are executable checks, not silent labels. *)
Definition event_ok (pa : nat) (s : State) (e : Event) : bool :=
  match e with
  | CheckParent =>
      match parent_view s with
      | Some p => Nat.eqb (paddr p) pa && writable p
      | None => false
      end
  | CheckBoth =>
      match parent_view s, child_view s with
      | Some p, Some c =>
          Nat.eqb (paddr p) pa && Nat.eqb (paddr c) pa &&
          negb (writable p) && negb (writable c)
      | _, _ => false
      end
  | CheckIoMemBoth =>
      match parent_view s, child_view s with
      | Some p, Some c =>
          Nat.eqb (paddr p) pa && Nat.eqb (paddr c) pa &&
          (match page_kind p, page_kind c with IoMem, IoMem => true | _, _ => false end) &&
          writable p && writable c
      | _, _ => false
      end
  | CheckChild =>
      match parent_view s, child_view s with
      | None, Some c => Nat.eqb (paddr c) pa && negb (writable c)
      | _, _ => false
      end
  | CheckIoMemChild =>
      match parent_view s, child_view s with
      | None, Some c => Nat.eqb (paddr c) pa &&
          (match page_kind c with IoMem => true | Ram => false end) && writable c
      | _, _ => false
      end
  | _ => true
  end.

Fixpoint run_checked (pa : nat) (s : State) (tr : list Event)
  : option State :=
  match tr with
  | [] => Some s
  | e :: rest =>
      if event_ok pa s e
      then run_checked pa (step pa s e) rest
      else None
  end.

Fixpoint run (pa : nat) (s : State) (tr : list Event) : State :=
  match tr with
  | [] => s
  | e :: rest => run pa (step pa s e) rest
  end.

Definition scenario_trace : list Event :=
  [MapParent; CheckParent; FindNext; QueryParent; ProtectParent;
   JumpChild; MapChild; CheckBoth; UnmapParent; CheckChild].

Definition iomem_scenario_trace : list Event :=
  [MapParentIoMem; CheckParent; FindNext; QueryParent; JumpChild;
   MapIoMemChild; CheckIoMemBoth; UnmapParent; CheckIoMemChild].

Definition unprotected_copy_trace : list Event :=
  [MapParent; CheckParent; FindNext; QueryParent; SkipProtectParent;
   JumpChild; MapChild; CheckBoth; UnmapParent; CheckChild].

Inductive IoMemScenario : list Event -> Prop :=
| IoMemScenario_one_page : IoMemScenario iomem_scenario_trace.

Lemma scenario_trace_in_cfg : Scenario scenario_trace.
Proof.
  unfold scenario_trace.
  change (Scenario ([MapParent; CheckParent] ++
    [FindNext; QueryParent; ProtectParent; JumpChild; MapChild] ++
    [CheckBoth; UnmapParent; CheckChild])).
  econstructor. constructor.
Qed.

Lemma project_vostd_one_page_trace_exact :
  projected_vostd_one_page_trace = scenario_trace.
Proof. reflexivity. Qed.

Theorem vostd_one_page_trace_in_client_cfg :
  Scenario projected_vostd_one_page_trace.
Proof. rewrite project_vostd_one_page_trace_exact. apply scenario_trace_in_cfg. Qed.

Theorem projected_vostd_one_page_checks_pass : forall pa,
  run_checked pa initial_state projected_vostd_one_page_trace =
    Some (mkState None (Some (mkPage pa false Ram))).
Proof. intros pa. rewrite project_vostd_one_page_trace_exact.
  cbv [run_checked event_ok step initial_state scenario_trace
    parent_view child_view paddr writable page_kind].
  repeat rewrite Nat.eqb_refl. reflexivity. Qed.

Theorem unprotected_copy_is_rejected : forall pa,
  run_checked pa initial_state unprotected_copy_trace = None.
Proof.
  intros pa. cbv [run_checked event_ok step initial_state unprotected_copy_trace
    parent_view child_view paddr writable page_kind].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem iomem_scenario_in_cfg : IoMemScenario iomem_scenario_trace.
Proof. constructor. Qed.

Theorem iomem_copy_checks_pass : forall pa,
  run_checked pa initial_state iomem_scenario_trace =
    Some (mkState None (Some (mkPage pa true IoMem))).
Proof.
  intros pa. cbv [run_checked event_ok step initial_state iomem_scenario_trace
    parent_view child_view paddr writable page_kind].
  repeat rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem cow_copy_observed_after_copy : forall pa,
  let s := run pa initial_state
    [MapParent; CheckParent; FindNext; QueryParent; ProtectParent; JumpChild; MapChild] in
  parent_view s = Some (mkPage pa false Ram) /\
  child_view s = Some (mkPage pa false Ram).
Proof. intros pa. split; reflexivity. Qed.

Theorem child_mapping_survives_parent_unmap : forall pa tr,
  Scenario tr ->
  let s := run pa initial_state tr in
  parent_view s = None /\
  child_view s = Some (mkPage pa false Ram).
Proof.
  intros pa tr H. inversion H; subst. inversion H0; subst. split; reflexivity.
Qed.

(* The state relation needed to connect this candidate model to Vostd.
   A Verus CursorView is reduced to an optional observation of the mapping at
   the client's one-page VA. Establishing this reduction from the actual
   CursorView postconditions is a separate bridge obligation. *)
Record PageViewObservation := mkViewObs {
  observed_pa : nat;
  observed_writable : bool;
  observed_kind : PageKind
}.

Record VerusObservation := mkVerusObs {
  observed_parent : option PageViewObservation;
  observed_child : option PageViewObservation
}.

Definition erase_page_view (v : PageViewObservation) : Page :=
  mkPage (observed_pa v) (observed_writable v) (observed_kind v).

Definition erase_view (v : option PageViewObservation) : option Page :=
  option_map erase_page_view v.

Definition erase_verus_observation (v : VerusObservation) : State :=
  mkState (erase_view (observed_parent v)) (erase_view (observed_child v)).

Definition state_refines_observation (s : State) (v : VerusObservation) : Prop :=
  s = erase_verus_observation v.

Definition client_neutral_event (e : Event) : Prop :=
  match e with
  | MapParent | MapParentIoMem | ProtectParent | MapChild | MapIoMemChild
  | UnmapParent => False
  | _ => True
  end.

(* These are the one-page observation contracts required from the Vostd
   operations. They intentionally do not assert that the current embedding
   proves these contracts as a group. *)
Inductive ApiObservationPost (pa : nat) :
    VerusObservation -> Event -> VerusObservation -> Prop :=
| ApiNeutral : forall v e,
    client_neutral_event e ->
    ApiObservationPost pa v e v
| ApiMapParent : forall v,
    observed_parent v = None ->
    ApiObservationPost pa v MapParent
      (mkVerusObs (Some (mkViewObs pa true Ram)) (observed_child v))
| ApiMapParentIoMem : forall v,
    observed_parent v = None ->
    ApiObservationPost pa v MapParentIoMem
      (mkVerusObs (Some (mkViewObs pa true IoMem)) (observed_child v))
| ApiProtectParent : forall v p,
    observed_parent v = Some p ->
    ApiObservationPost pa v ProtectParent
      (mkVerusObs
        (Some (mkViewObs (observed_pa p) false (observed_kind p)))
        (observed_child v))
| ApiProtectAbsentParent : forall v,
    observed_parent v = None ->
    ApiObservationPost pa v ProtectParent v
| ApiMapChild : forall v p,
    observed_parent v = Some p ->
    ApiObservationPost pa v MapChild
      (mkVerusObs (observed_parent v)
        (Some (mkViewObs (observed_pa p) (observed_writable p) (observed_kind p))))
| ApiMapAbsentChild : forall v,
    observed_parent v = None ->
    ApiObservationPost pa v MapChild v
| ApiMapIoMemChild : forall v p,
    observed_parent v = Some p ->
    ApiObservationPost pa v MapIoMemChild
      (mkVerusObs (observed_parent v)
        (Some (mkViewObs (observed_pa p) (observed_writable p) IoMem)))
| ApiMapIoMemAbsentChild : forall v,
    observed_parent v = None ->
    ApiObservationPost pa v MapIoMemChild v
| ApiUnmapParent : forall v,
    ApiObservationPost pa v UnmapParent
      (mkVerusObs None (observed_child v)).

Lemma api_observation_post_simulates_cfg_step : forall pa v e v' s,
  ApiObservationPost pa v e v' ->
  state_refines_observation s v ->
  state_refines_observation (step pa s e) v'.
Proof.
  intros pa v e v' s Hpost.
  induction Hpost; intros Hrel; unfold state_refines_observation in Hrel; subst s.
  - destruct e; simpl in *; try contradiction; reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (observed_parent v) as [p0|] eqn:Hp; simpl in *.
    + inversion H; subst p0. rewrite Hp. reflexivity.
    + discriminate.
  - destruct (observed_parent v) as [p0|] eqn:Hp; simpl in *.
    + discriminate.
    + rewrite Hp. reflexivity.
  - destruct (observed_parent v) as [p0|] eqn:Hp; simpl in *.
    + inversion H; subst p0. rewrite Hp. reflexivity.
    + discriminate.
  - destruct (observed_parent v) as [p0|] eqn:Hp; simpl in *.
    + discriminate.
    + rewrite Hp. reflexivity.
  - destruct (observed_parent v) as [p0|] eqn:Hp; simpl in *.
    + inversion H; subst p0. rewrite Hp. reflexivity.
    + discriminate.
  - destruct (observed_parent v) as [p0|] eqn:Hp; simpl in *.
    + discriminate.
    + rewrite Hp. reflexivity.
  - reflexivity.
Qed.

Inductive ApiObservationTrace (pa : nat) :
    VerusObservation -> list Event -> VerusObservation -> Prop :=
| ApiTraceNil : forall v,
    ApiObservationTrace pa v [] v
| ApiTraceCons : forall v e v1 tr v2,
    ApiObservationPost pa v e v1 ->
    ApiObservationTrace pa v1 tr v2 ->
    ApiObservationTrace pa v (e :: tr) v2.

Theorem api_observation_trace_simulates_cfg : forall pa v tr v' s,
  ApiObservationTrace pa v tr v' ->
  state_refines_observation s v ->
  run pa s tr = erase_verus_observation v'.
Proof.
  intros pa v tr v' s Htrace.
  revert s.
  induction Htrace; intros s Hrel.
  - unfold state_refines_observation in Hrel. subst. reflexivity.
  - simpl. eapply IHHtrace.
    eapply api_observation_post_simulates_cfg_step; eauto.
Qed.

Definition empty_verus_observation : VerusObservation := mkVerusObs None None.

Definition cow_final_observation (pa : nat) : VerusObservation :=
  mkVerusObs None (Some (mkViewObs pa false Ram)).

Lemma cow_scenario_has_api_observation_witness : forall pa,
  ApiObservationTrace pa empty_verus_observation scenario_trace
    (cow_final_observation pa).
Proof.
  intros pa. unfold scenario_trace, empty_verus_observation, cow_final_observation.
  eapply ApiTraceCons.
  - apply ApiMapParent. reflexivity.
  - eapply ApiTraceCons.
    + constructor. simpl. exact I.
    + eapply ApiTraceCons.
      * constructor. simpl. exact I.
      * eapply ApiTraceCons.
        -- constructor. simpl. exact I.
        -- eapply ApiTraceCons.
           ++ apply ApiProtectParent. reflexivity.
           ++ eapply ApiTraceCons.
              ** constructor. simpl. exact I.
              ** eapply ApiTraceCons.
                 --- apply ApiMapChild. reflexivity.
                 --- eapply ApiTraceCons.
                     +++ constructor. simpl. exact I.
                     +++ eapply ApiTraceCons.
                         *** apply ApiUnmapParent.
                         *** eapply ApiTraceCons.
                             ---- constructor. simpl. exact I.
                             ---- apply ApiTraceNil.
Qed.

Theorem cow_api_observation_trace_matches_cfg : forall pa,
  run pa initial_state scenario_trace =
    erase_verus_observation (cow_final_observation pa).
Proof.
  intros pa.
  eapply api_observation_trace_simulates_cfg.
  - apply cow_scenario_has_api_observation_witness.
  - reflexivity.
Qed.
