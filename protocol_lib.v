(* protocol_lib.v -- reusable library: CFG <-> STA equivalence.

   The claim this library formalizes:

       Prove the equivalence ONCE, for any protocol of this shape.
       A new model then only has to supply its tables and discharge
       11 small obligations -- the grammar, the recognizer glue, and
       `gen_iff_accepts` itself all come from here.

   A model supplies
     - transition table   next  : st -> ev -> st            (the STA side)
     - three event classes, defined WITHOUT using next       (the grammar side)
         stutter    e        : state-preserving event
         changes_to e s s'   : e carries s into s'
         starts_to  e s      : the event(s) that leave the initial state
     - is_error, live, init, fault

   and discharges 11 obligations:

     1  live_not_fault : live s = true                            -> s <> fault
     2  is_error_ok    : is_error s = true                        <-> s = fault
     3  init_ok        : init                                     <> fault
     4  start_ok       : starts_to e s = true                     -> next init e = s
     5  start_live     : starts_to e s = true                     -> live s = true
     6  start_complete : next init e <> fault                     -> exists s, starts_to e s = true
     7  stutter_ok     : live s = true -> stutter e = true        -> next s e = s
     8  changes_ok     : changes_to e s s' = true                 -> next s e = s'
     9  changes_live   : changes_to e s s' = true                 -> live s' = true
     10 fault_absorbing: next fault e = fault
     11 step_complete  : live s = true ->
             (stutter e = true /\ next s e = s)
         \/  (exists s', changes_to e s s' = true)
         \/  (next s e = fault)

   Why TWO step classes and not three (advance / release)?  The grammar
   rule for an advance and for a release is literally the same term --
       changes_to e s s' = true -> genf s' ts -> genf s (e :: ts)
   -- so the class name carried no semantics.  buffer.v's `Flush` is
   classified as a release yet leaves an empty buffer untouched, and the
   proof does not care.  Merging them turns 13 obligations into 11.

   The grammar itself is defined here as an inductive family indexed by
   the starting state -- it never mentions `next`.  Obligations 7/8/9 are
   the forward bridge, 11 is the backward bridge.  `genf` and `next` are
   therefore two genuinely independent descriptions, which is what makes
   the equivalence meaningful rather than a tautology.

   Compiles with Rocq 9.1.1:  rocq compile protocol_lib.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
(* Stdlib (registered by nix/flake.nix through ROCQPATH): Nat.eqb_eq /
   Nat.eqb_refl, Bool.andb_true_iff, and In / filter / map / flat_map. *)
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Open Scope bool_scope.

Record Protocol : Type := mk {
  st : Type;
  ev : Type;
  live : st -> bool;
  init : st;
  fault : st;
  next : st -> ev -> st;
  is_error : st -> bool;

  stutter : ev -> bool;
  changes_to : ev -> st -> st -> bool;
  starts_to : ev -> st -> bool;

  live_not_fault : forall s, live s = true -> s <> fault;
  is_error_ok : forall s, is_error s = true <-> s = fault;
  init_ok : init <> fault;
  start_ok : forall e s, starts_to e s = true -> next init e = s;
  start_live : forall e s, starts_to e s = true -> live s = true;
  start_complete : forall e, next init e <> fault -> exists s, starts_to e s = true;
  stutter_ok : forall s e, live s = true -> stutter e = true -> next s e = s;
  changes_ok : forall s s' e, changes_to e s s' = true -> next s e = s';
  changes_live : forall s s' e, changes_to e s s' = true -> live s' = true;
  fault_absorbing : forall e, next fault e = fault;
  step_complete : forall s e, live s = true ->
      (stutter e = true /\ next s e = s)
      \/ (exists s', changes_to e s s' = true)
      \/ (next s e = fault);
}.

(** * ============================================================
    Automation: table-shaped obligations are discharged by [discharge].

    The nat / bool / list facts come from the Stdlib; only
    [nat_list_eqb] below is ours, because the Stdlib has no equality on
    lists of nats. *)
(** Queue-shaped tables need equality on lists of nats. *)
Fixpoint nat_list_eqb (a b : list nat) : bool :=
  match a, b with
  | nil, nil => true
  | x :: xs, y :: ys => Nat.eqb x y && nat_list_eqb xs ys
  | _, _ => false
  end.

Lemma nat_list_eqb_true : forall a b, nat_list_eqb a b = true -> a = b.
Proof.
  induction a as [| x xs IH]; destruct b as [| y ys]; simpl; intros H;
    try discriminate; try reflexivity.
  rewrite Bool.andb_true_iff in H; destruct H as [Hxy Hrest].
  rewrite Nat.eqb_eq in Hxy; subst. apply IH in Hrest; subst. reflexivity.
Qed.

Lemma nat_list_eqb_refl : forall a, nat_list_eqb a a = true.
Proof.
  induction a as [| x xs IH]; simpl; [ reflexivity | ].
  rewrite Nat.eqb_refl; rewrite IH; reflexivity.
Qed.

(** Case analysis over one of the model's own types.  A model wires this
    up once, e.g.
        Ltac case_types := case_of State; case_of Event.
    Types that must NOT be destructed (nat, tid, ...) are simply left out. *)
Ltac case_of T :=
  repeat match goal with | [ v : T |- _ ] => destruct v end.

(** The common tail: normalise, push boolean equalities into the goal,
    and close it.  Every attempt is wrapped so a failure backtracks.

    NOTE (measured on Rocq 9): bare `discriminate` and `congruence` fire
    only on a goal of the form `t1 <> t2`, or on a *hypothesis* of the
    form `t1 = t2`.  They do NOT close a bare equation goal such as
    `false = true`.  An obligation whose goal simplifies to one of those
    (the ones ending in an existential) is therefore proved by hand;
    every other table obligation carries a discriminating hypothesis. *)
Ltac finish_goal :=
  simpl in *;
  repeat match goal with
         (* A boolean guard sitting in the GOAL (e.g. a queue-head test
            that only reduces once the queue is known) must be split
            BEFORE the hypothesis arms: those consume their equation by
            substitution, and the resulting `false` branch would then have
            no discriminating hypothesis left -- and Rocq 9's bare
            `discriminate` cannot close an equation goal such as
            `Error = Unlocked`.  Splitting first turns it into
            `false = true`, which it can. *)
         | |- context[if Nat.eqb ?a ?b then _ else _] =>
             destruct (Nat.eqb a b); simpl in *
         | [ H : _ && _ = true |- _ ] =>
             rewrite Bool.andb_true_iff in H; destruct H
         | [ H : nat_list_eqb _ _ = true |- _ ] =>
             apply nat_list_eqb_true in H; subst
         | [ H : Nat.eqb _ _ = true |- _ ] =>
             (* prefer substitution over rewriting: both sides must end up
                syntactically equal, otherwise a later `reflexivity` on
                `if Nat.eqb x y then ...` cannot fire *)
             first [ rewrite Nat.eqb_eq in H; subst | rewrite H; clear H ]
         | [ H : Nat.leb _ _ = true |- _ ] => rewrite H; clear H
         (* Fallback for a guard that [simpl] has already reduced into a
            match -- e.g. `Nat.leb 1 (length items)` folds to
            `match length items with … end` because the first argument is
            a literal, so neither the Nat.leb hypothesis arm nor the
            Nat.eqb goal arm above recognises it. *)
         | |- context[if ?b then _ else _] => destruct b; simpl in *
         (* Any other reflected equality (an enum, a string, ...): ask the
            hint database.  Deliberately LAST: on a goal that still has a
            boolean `if`, splitting it first turns the guard into
            `true = true` / `false = true` in the hypothesis, which is
            cheaper than substituting and losing that equation. *)
         | [ H : ?f ?a ?b = true |- _ ] =>
             assert (a = b) by eauto with finish_db; subst; clear H
         end;
  try rewrite Nat.eqb_refl;
  try discriminate;
  try congruence;
  (* Rocq 9: bare `discriminate`/`congruence` will not close an *equation*
     goal such as `Error = Unlocked` -- they only fire on `t1 <> t2` or on
     a discriminating hypothesis.  After `subst` has consumed the
     hypothesis, `auto` is what is left. *)
  try auto;
  try reflexivity;
  try contradiction;
  try (split; intros; solve [ discriminate | congruence | reflexivity ]).

(** Guards whose parameters are not [nat] (an enum, a string, ...) are
    turned into equations through this hint database.  A model adds its
    own reflection lemma:

        Hint Resolve string_eqb_eq : finish_db.

    and [finish_goal] can then substitute `string_eqb x y = true` just
    like it does `Nat.eqb x y = true`.  A hint database is used at call
    time and is shared across files -- unlike an Ltac hook, which Rocq
    resolves statically at definition time. *)
Create HintDb finish_db.

(** Discharge a table-shaped obligation. *)
Ltac discharge cases :=
  intros;
  cases;
  finish_goal.


Section WithP.

Variable p : Protocol.

Notation State := (st p).
Notation Event := (ev p).

(** * Recognizer *)
Fixpoint run_from (s : State) (tr : list Event) : State :=
  match tr with
  | nil => s
  | e :: es => run_from (next p s e) es
  end.

Definition run (tr : list Event) : State := run_from (init p) tr.

Definition accepts (tr : list Event) : bool :=
  negb (is_error p (run tr)).

Lemma run_from_fault : forall tr, run_from (fault p) tr = fault p.
Proof.
  intros tr; induction tr as [| e tr IH]; [ reflexivity | ].
  cbn [run_from]. rewrite (fault_absorbing p e). exact IH.
Qed.

Lemma run_from_ne : forall s tr, run_from s tr <> fault p -> s <> fault p.
Proof.
  intros s tr H Hs. subst s.
  rewrite run_from_fault in H. apply H. reflexivity.
Qed.

Lemma accepts_iff : forall tr, accepts tr = true <-> run tr <> fault p.
Proof.
  intros tr. unfold accepts. split; intro H.
  - intro Hf.
    assert (Hi : is_error p (run tr) = true)
      by (apply (proj2 (is_error_ok p (run tr))); exact Hf).
    rewrite Hi in H. simpl in H. discriminate H.
  - destruct (is_error p (run tr)) eqn:Hi; [ | reflexivity ].
    exfalso. apply H.
    apply (proj1 (is_error_ok p (run tr))). exact Hi.
Qed.

(** * Grammar: defined by constructors over the trace, never via [next]. *)
Inductive genf : State -> list Event -> Prop :=
| GF_nil  : forall s, live p s = true -> genf s nil
| GF_st   : forall s e ts,
    stutter p e = true -> genf s ts -> genf s (e :: ts)
| GF_chg  : forall s s' e ts,
    changes_to p e s s' = true -> genf s' ts -> genf s (e :: ts).

(** Top level: the initial state and its first event. *)
Inductive gen : list Event -> Prop :=
| G_nil    : gen nil
| G_start  : forall s e ts,
    starts_to p e s = true -> genf s ts -> gen (e :: ts).

(** * Forward: generated traces do not fault. *)
Lemma genf_run : forall s ts, genf s ts -> live p s = true -> run_from s ts <> fault p.
Proof.
  intros s ts Hg.
  induction Hg as [s Hnil
                  | s e ts Hs Hg IH
                  | s s' e ts Hc Hg IH];
    intros Hliv; cbn [run_from].
  - apply (live_not_fault p s Hliv).
  - rewrite (stutter_ok p s e Hliv Hs). apply IH; exact Hliv.
  - rewrite (changes_ok p s s' e Hc).
    apply IH. exact (changes_live p s s' e Hc).
Qed.

(** * Backward: a non-faulting run from a live state is generated. *)
Lemma run_genf : forall ts s, live p s = true -> run_from s ts <> fault p -> genf s ts.
Proof.
  intros ts. induction ts as [| e ts IH]; intros s Hliv Hrun;
    cbn [run_from] in Hrun.
  - apply GF_nil; exact Hliv.
  - destruct (step_complete p s e Hliv)
      as [Hst | [ [s' Hc] | Hf ] ].
    + rewrite (proj2 Hst) in Hrun.
      apply GF_st; [ exact (proj1 Hst) | apply IH; assumption ].
    + rewrite (changes_ok p s s' e Hc) in Hrun.
      eapply GF_chg; [ exact Hc | apply IH;
                      [ exact (changes_live p s s' e Hc) | exact Hrun ] ].
    + rewrite Hf in Hrun. rewrite run_from_fault in Hrun. contradiction.
Qed.

Lemma genf_iff_run : forall s ts,
  live p s = true ->
  (genf s ts <-> run_from s ts <> fault p).
Proof.
  intros s ts Hliv. split; intro H.
  - exact (genf_run s ts H Hliv).
  - exact (run_genf ts s Hliv H).
Qed.

(** * Forward for whole traces. *)
Lemma gen_run : forall tr, gen tr -> run tr <> fault p.
Proof.
  intros tr H. destruct H as [| s e ts Hs Hg].
  - unfold run. cbn [run_from]. exact (init_ok p).
  - unfold run. cbn [run_from]. rewrite (start_ok p e s Hs).
    apply (genf_run s ts Hg). exact (start_live p e s Hs).
Qed.

(** * The headline theorem.  Free for every model. *)
Theorem gen_iff_accepts : forall tr, gen tr <-> accepts tr = true.
Proof.
  intros tr. split; intro H.
  - apply accepts_iff. exact (gen_run tr H).
  - apply accepts_iff in H.
    destruct tr as [| e ts].
    + constructor.
    + unfold run in H. cbn [run_from] in H.
      assert (Hne : next p (init p) e <> fault p)
        by (apply (run_from_ne (next p (init p) e) ts); exact H).
      destruct (start_complete p e Hne) as [s Hst].
      apply G_start with (s := s); [ exact Hst | ].
      apply (run_genf ts s);
        [ exact (start_live p e s Hst)
        | rewrite (start_ok p e s Hst) in H; exact H ].
Qed.

(** * Example enumeration.

    A grammar is only useful to a developer if they can SEE what it
    generates.  [examples_upto] enumerates every trace over an alphabet
    up to a given length and keeps the accepted ones -- the primitive
    behind "expand an example" in the confirmation workflow. *)

(** Every trace over [alphabet] of length at most [n]. *)
Fixpoint traces_upto (alphabet : list Event) (n : nat) :
  list (list Event) :=
  match n with
  | 0 => nil :: nil
  | S k =>
      let shorter := traces_upto alphabet k in
      shorter ++ flat_map (fun e => map (fun t => e :: t) shorter) alphabet
  end.

Definition examples_upto (alphabet : list Event) (n : nat) :
  list (list Event) :=
  filter accepts (traces_upto alphabet n).

(** Whatever comes back really is accepted -- what a developer sees when
    the generator is asked for examples. *)
Lemma examples_upto_sound : forall l tr,
  In tr (filter accepts l) -> accepts tr = true.
Proof.
  intros l tr H. rewrite filter_In in H. destruct H as [_ H]. exact H.
Qed.


End WithP.
