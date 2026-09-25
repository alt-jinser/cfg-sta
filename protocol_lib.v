(* protocol_lib.v -- reusable library: CFG <-> STA equivalence.

   The claim this library formalizes:

       Prove the equivalence ONCE, for any protocol of this shape.
       A new model then only has to supply its grammar, its invariant
       and two word-level lemmas -- the recognizer glue, the soundness
       proof, and `gen_iff_accepts` itself all come from here.

   A model supplies

     - transition table   next : st -> ev -> st            (STA side)
     - is_error, init, fault
     - nonterminals       nt, start                         (CFG side)
     - productions        prod : nt -> list (sym nt ev) -> Prop
     - an availability invariant
                          inv : nt -> st -> bool

   and discharges 7 obligations:

      1  is_error_ok      : is_error s = true              <-> s = fault
      2  init_fault_free  : init                            <> fault
      3  inv_start        : inv start init                  = true
      4  prod_ok          : prod A beta = true-shaped       ->
                            inv A s = true                  -> ok s beta
      5  word_ok          : list ev -> Prop                 (a predicate)
      6  word_ok_run      : run tr <> fault                 <-> word_ok tr
      7  word_ok_gen      : word_ok tr                      -> gen tr

   Where the two directions live, and why they are not symmetric:

   DIRECTION 1 (soundness, gen -> accepts) is fully generic.  It runs
   through [ok s alpha], the judgment that a form is safe to expand and
   run from [s].  Its nonterminal clause checks the TAIL at every state
   the nonterminal can reach -- checking it only at [s] would be wrong,
   because expanding a nonterminal makes it consume input first, so the
   tail is really run from a later state.  Obligation 4 is the content;
   in practice most of its cases close by reflexivity and discriminate.
   The library proof uses [fix] rather than [induction] on the
   derivation, because an [induction] replaces the head nonterminal's
   sub-derivation by an induction hypothesis and the tail clause needs
   that sub-derivation.

   DIRECTION 2 (completeness, accepts -> gen) has NO generic proof
   over this contract, and that is a theorem, not a shortfall.  From a
   count above zero the machine accepts an extra step that no
   production can derive, so any statement of the form "same state,
   same conclusion" is simply false: a state-indexed induction has
   nothing to induct on.  Choosing which production applies, and where
   its word ends, is word-level structure that [prod] and [inv] do not
   determine -- witnessed by the Dyck grammar in rcu.v, where the
   [Read] case of completeness needs the first position at which the
   count bottoms out.  Obligations 5-7 are therefore the honest split:
   the model characterizes its own accepted words, and proves its own
   grammar complete for them.  For a right-linear grammar (one
   terminal per production) that is a direct per-event induction; for
   a nesting grammar it needs a decomposition lemma.

   Why TWO step classes are gone (they were merged earlier): the
   grammar rule for an advance and for a release is literally the same
   term, so the class name carried no semantics.  Under this contract
   the notion disappears outright -- productions ARE the grammar side.

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

(** * ============================================================
    CFG syntax.  A symbol is either a nonterminal or a terminal (an
    event); a production's right-hand side is a list of symbols. *)
Inductive sym (N E : Type) :=
| Sn (n : N)
| Se (e : E).

(* Without this [Se e] would be read as [Se (N := e)]: constructors of a
   parameterized inductive take the parameters first, and elaboration
   tries the arguments before the expected type fixes them. *)
Arguments Sn {N E} _.
Arguments Se {N E} _.

(** * ============================================================
    Recognizer, derivability, and the safety judgment.

    These are defined BEFORE [Record Protocol], because [prod_ok] is a
    field of that record and mentions [ok].  Everything is therefore
    parameterized over the pieces a model supplies; the record fields
    are plugged in at the field's type. *)
Section WithTypes.

Variables (St E Nt : Type).
Variable init : St.
Variable fault : St.
Variable next : St -> E -> St.
Variable is_error : St -> bool.
Variable inv : Nt -> St -> bool.
Variable prod : Nt -> list (sym Nt E) -> Prop.
Variable start : Nt.

(** * Recognizer *)
Fixpoint run_from (s : St) (tr : list E) : St :=
  match tr with
  | nil => s
  | e :: es => run_from (next s e) es
  end.

Definition run (tr : list E) : St := run_from init tr.

Definition accepts (tr : list E) : bool := negb (is_error (run tr)).

(** * Grammar: derivability in YIELD form.

    A derivation records how the word splits between a nonterminal and
    its continuation.  This is not cosmetic: with a rewriting-style
    relation the split is never recorded, and the state at which the
    continuation runs is exactly the information every proof then has
    to go and recover. *)
Inductive derives : list (sym Nt E) -> list E -> Prop :=
| D_base : derives nil nil
| D_se   : forall (e : E) (alpha : list (sym Nt E)) (tr : list E),
    derives alpha tr -> derives (Se e :: alpha) (e :: tr)
| D_sn   : forall (A : Nt) (beta : list (sym Nt E)) (tr1 tr2 : list E)
             (alpha : list (sym Nt E)),
    prod A beta -> derives beta tr1 -> derives alpha tr2 ->
    derives (Sn A :: alpha) (tr1 ++ tr2).

(** One nonterminal step, as a derived form of [D_sn]. *)
Lemma derives_sn : forall A beta tr,
    prod A beta -> derives beta tr -> derives (Sn A :: nil) tr.
Proof.
  intros A beta tr Hp Hd.
  assert (H : derives (Sn A :: nil) (tr ++ nil))
    by exact (D_sn A beta tr nil nil Hp Hd D_base).
  rewrite app_nil_r in H. exact H.
Qed.

(** Terminal steps, as derived forms of the constructors.  Models only
    ever BUILD derivations (the library does the reasoning), and the
    constructors of a parameterized [Inductive] carry the parameters as
    extra arguments once the section is closed -- so they go through
    these lemmas, whose arguments are declared below. *)
Lemma derives_nil : derives nil nil.
Proof. constructor. Qed.

Lemma derives_se : forall e alpha tr,
    derives alpha tr -> derives (Se e :: alpha) (e :: tr).
Proof. intros e alpha tr H. constructor. exact H. Qed.

Definition gen (tr : list E) : Prop := derives (Sn start :: nil) tr.

(** States reachable by running some word derived from [A], WITHOUT
    faulting on the way.

    Restricting to non-faulting endpoints is deliberate, not a way of
    hiding the conclusion: the soundness proof only ever applies this
    clause after it has separately established that the endpoint does
    not fault (from obligation 4), so nothing is assumed that is not
    also proved -- while the top-level instance stays trivially
    dischargeable instead of demanding a word-level lemma before the
    proof can even start. *)
Definition Reach (s : St) (A : Nt) (s' : St) : Prop :=
  exists tr, derives (Sn A :: nil) tr /\ run_from s tr = s' /\ s' <> fault.

(** [ok s alpha]: [alpha] is safe to expand and run from [s].

    The clause for a nonterminal checks its TAIL at every state the
    nonterminal can reach, not at [s] -- see the header. *)
Fixpoint ok (s : St) (alpha : list (sym Nt E)) {struct alpha} : Prop :=
  match alpha with
  | nil           => s <> fault
  | Se e :: rest  => next s e <> fault /\ ok (next s e) rest
  | Sn A :: rest  => inv A s = true /\ (forall s', Reach s A s' -> ok s' rest)
  end.

End WithTypes.

(* The types are inferred from the model's own fields, so the record
   reads [ok fault next inv prod s beta] rather than repeating them. *)
Arguments run_from {St E} _ _ _.
Arguments run {St E} _ _ _.
Arguments accepts {St E} _ _ _ _.
Arguments derives {E Nt} _ _ _.
Arguments derives_sn {E Nt} _ _ _ _ _ _.
Arguments derives_nil {E Nt} _.
Arguments derives_se {E Nt} _ _ _ _ _.
Arguments gen {E Nt} _ _ _.
Arguments Reach {St E Nt} _ _ _ _ _ _.
Arguments ok {St E Nt} _ _ _ _ _ _.

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

(** * The contract *)
Record Protocol : Type := mk {
  st : Type;
  ev : Type;
  nt : Type;

  init : st;
  fault : st;
  next : st -> ev -> st;
  is_error : st -> bool;

  start : nt;
  prod : nt -> list (sym nt ev) -> Prop;
  inv : nt -> st -> bool;

  is_error_ok : forall s, is_error s = true <-> s = fault;
  init_fault_free : init <> fault;
  inv_start : inv start init = true;
  prod_ok : forall A beta s,
      prod A beta -> inv A s = true -> ok fault next inv prod s beta;

  word_ok : list ev -> Prop;
  word_ok_run : forall tr, run init next tr <> fault <-> word_ok tr;
  word_ok_gen : forall tr, word_ok tr -> gen prod start tr
}.

(** * ============================================================
    Automation: case analysis over one of the model's own types.

    A model wires this up once, e.g.
        Ltac case_types := case_of State; case_of Event.
    Types that must NOT be destructed (nat, tid, ...) are simply left
    out. *)
Ltac case_of T :=
  repeat match goal with | [ v : T |- _ ] => destruct v end.

(** The common tail: normalise, push boolean equalities into the goal,
    and close it.  Every attempt is wrapped so a failure backtracks.

    NOTE (measured on Rocq 9): bare `discriminate` and `congruence` fire
    only on a goal of the form `t1 <> t2`, or on a *hypothesis* of the
    form `t1 = t2`.  They do NOT close a bare equation goal such as
    `false = true`; and `simpl` will often turn `x <> y` into
    `x = y -> False`, which `discriminate` then refuses -- hence the
    `intro H; discriminate` idiom used throughout. *)
Ltac finish_goal :=
  simpl in *;
  repeat match goal with
         (* A boolean guard sitting in the GOAL must be split BEFORE
            the hypothesis arms: those consume their equation by
            substitution, and the resulting `false` branch would then
            have no discriminating hypothesis left. *)
         | |- context[if Nat.eqb ?a ?b then _ else _] =>
             destruct (Nat.eqb a b); simpl in *
         | [ H : _ && _ = true |- _ ] =>
             rewrite Bool.andb_true_iff in H; destruct H
         | [ H : nat_list_eqb _ _ = true |- _ ] =>
             apply nat_list_eqb_true in H; subst
         | [ H : Nat.eqb _ _ = true |- _ ] =>
             first [ rewrite Nat.eqb_eq in H; subst | rewrite H; clear H ]
         | [ H : Nat.leb _ _ = true |- _ ] => rewrite H; clear H
         (* Fallback for a guard that [simpl] has already reduced into a
            match -- e.g. `Nat.leb 1 (length items)` folds to
            `match length items with ... end` because the first argument
            is a literal. *)
         | |- context[if ?b then _ else _] => destruct b; simpl in *
         (* Any other reflected equality (an enum, a string, ...): ask
            the hint database.  Deliberately LAST. *)
         | [ H : ?f ?a ?b = true |- _ ] =>
             assert (a = b) by eauto with finish_db; subst; clear H
         end;
  (* The tail after a nonterminal, once [simpl] has reduced [ok s' nil]
     to [s' <> fault]: [Reach] carries exactly that fact. *)
  try (intros s' Hr; destruct Hr as [? [? [? Hne]]]; exact Hne);
  try rewrite Nat.eqb_refl;
  try discriminate;
  try congruence;
  try auto;
  try reflexivity;
  try contradiction;
  try (split; intros; solve [ discriminate | congruence | reflexivity ]);
  (* `<>` goals that [simpl] turned into implications. *)
  try (intro H; discriminate).

(** Guards whose parameters are not [nat] are turned into equations
    through this hint database (used at call time, shared across
    files -- unlike an Ltac hook, which Rocq resolves statically):

        Hint Resolve string_eqb_eq : finish_db. *)
Create HintDb finish_db.

(** Discharge [prod_ok]: split the production (the relation is passed
    in, since the model names its own), split the model's own types,
    then peel the right-nested conjunction all the way down and hand
    every conjunct to [finish_goal].  Peeling without solving first is
    deliberate: if the head conjunct needs a model-specific rewrite,
    solving it would stop the peel and leave the tail bundled with it. *)
Ltac discharge_prod rel cases :=
  intros;
  repeat match goal with [ H : rel _ _ |- _ ] => destruct H end;
  cases;
  repeat split;
  finish_goal.

(** Discharge a table-shaped obligation (kept for models that still
    phrase one that way). *)
Ltac discharge cases :=
  intros;
  cases;
  finish_goal.

Section WithP.

Variable p : Protocol.

Notation State := (st p).
Notation Event := (ev p).

Notation runp := (run (init p) (next p)).
Notation runf := (run_from (next p)).
Notation acceptsp := (accepts (init p) (next p) (is_error p)).
Notation genp := (gen (prod p) (start p)).

Lemma run_from_app : forall tr1 tr2 s,
    runf s (tr1 ++ tr2) = runf (runf s tr1) tr2.
Proof.
  induction tr1 as [| e tr1 IH]; intros tr2 s; simpl; [ reflexivity | ].
  apply IH.
Qed.

(** * ============================================================
    Direction 1: generated traces do not fault.

    [fix] rather than [induction]: after an [induction] on the
    derivation the sub-derivation of the head nonterminal has been
    replaced by its induction hypothesis, and [Reach] needs exactly
    that sub-derivation to place the continuation's state. *)
Lemma soundness : forall alpha tr, derives (prod p) alpha tr ->
    forall s, ok (fault p) (next p) (inv p) (prod p) s alpha ->
    runf s tr <> fault p.
Proof.
  fix soundness 3.
  intros alpha tr H.
  destruct H as [ | e alpha' tr' Hder
                | A beta tr1 tr2 alpha' Hp Hder1 Hder2 ];
    intros s Hok.
  - simpl in *. exact Hok.
  - simpl in *. destruct Hok as [Hs Hok'].
    exact (soundness alpha' tr' Hder (next p s e) Hok').
  - rewrite run_from_app. destruct Hok as [Hinv Hok'].
    pose proof (prod_ok p A beta s Hp Hinv) as Hokb.
    assert (Hne1 : runf s tr1 <> fault p)
      by exact (soundness beta tr1 Hder1 s Hokb).
    assert (Hs1 : Reach (fault p) (next p) (prod p) s A (runf s tr1)).
    { exists tr1. split.
      - exact (derives_sn (prod p) A beta tr1 Hp Hder1).
      - split; [ reflexivity | exact Hne1 ]. }
    exact (soundness alpha' tr2 Hder2 (runf s tr1) (Hok' _ Hs1)).
Qed.

Lemma accepts_iff : forall tr, acceptsp tr = true <-> runp tr <> fault p.
Proof.
  intros tr. unfold acceptsp, accepts.
  destruct (is_error p (runp tr)) eqn: He; simpl.
  - split; [ discriminate | intro H; exfalso; apply H;
      exact (proj1 (is_error_ok p (runp tr)) He) ].
  - split; [ intro H; intro Hf; rewrite Hf in He;
      pose proof (proj2 (is_error_ok p (fault p)) eq_refl) as Hc;
      rewrite Hc in He; discriminate He
    | intros _; reflexivity ].
Qed.

Lemma gen_run : forall tr, genp tr -> runp tr <> fault p.
Proof.
  intros tr Hg. unfold gen, run in *.
  apply (soundness (Sn (start p) :: nil) tr Hg (init p)).
  split; [ exact (inv_start p) | ].
  intros s' [tr' [Hd [Hr Hne]]]. exact Hne.
Qed.

Lemma gen_accepts : forall tr, genp tr -> acceptsp tr = true.
Proof.
  intros tr Hg. apply accepts_iff. apply gen_run. exact Hg.
Qed.

(** * ============================================================
    Direction 2: every word the model calls safe is generated.

    Stated over [word_ok] because there is no generic route -- see the
    header for why that is a property of the problem, not of the
    library. *)
Lemma accepts_gen : forall tr, acceptsp tr = true -> genp tr.
Proof.
  intros tr H. apply accepts_iff in H.
  apply word_ok_gen. apply word_ok_run. exact H.
Qed.

(** * The headline theorem.  Free for every model. *)
Theorem gen_iff_accepts : forall tr, genp tr <-> acceptsp tr = true.
Proof.
  intros tr. split.
  - apply gen_accepts.
  - apply accepts_gen.
Qed.

(** * ============================================================
    Example enumeration.

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
  filter acceptsp (traces_upto alphabet n).

(** Whatever comes back really is accepted -- what a developer sees when
    the generator is asked for examples. *)
Lemma examples_upto_sound : forall l tr,
    In tr (filter acceptsp l) -> acceptsp tr = true.
Proof.
  intros l tr H. rewrite filter_In in H. destruct H as [_ H]. exact H.
Qed.

End WithP.
