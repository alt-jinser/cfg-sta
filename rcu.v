(* rcu.v -- RCU read-side critical section discipline.

   Provenance: ostd/src/sync/rcu.  `Rcu::read()` takes a token from a
   pool shared by the cell, and the read guard's `drop` returns it
   (rcu/mod.rs, `load_read_token` / `RcuReadGuardInner::drop`).  The
   pool is declared `RCU_READER_SLOTS = 1 << 60`, and its comment says
   the final proof should replace that bounded approximation with an
   *unbounded* ghost registry -- which is exactly the idealization this
   model makes: the outstanding-reader count is a `nat`.

   What can go wrong (the safety property modelled here):

       a read guard is dropped that no read is outstanding for.

   As in mutex.v this is API-level misuse, not a type-reachable state.
   Grace-period / reclamation behaviour is deliberately OUT of scope:
   it is a liveness property, in the same bucket as starvation freedom,
   and is deferred along with it.

   Alphabet (abstract, no thread ids -- the same choice mutex.v makes):

       Create   -- the cell comes into existence
       Read     -- enter a read-side critical section (take a token)
       Drop     -- leave it (return a token)
       Update   -- the writer publishes a new pointer; does not block
                  and does not touch the reader count

   Language: `Create` followed by any word in which `Drop` never
   underflows the reader count, with `Update` anywhere.  Intersected
   with the regular set `Create Read* Drop*` this contains

       { Create Read^n Drop^m | m <= n }

   which is not regular -- so no finite-state recognizer can have this
   language, and the grammar below (two nonterminals, one of the
   productions non-right-linear) is genuinely context-free rather than
   a right-linear presentation of an automaton.

   Grammar:

       Program -> epsilon | Create Body
       Body    -> epsilon | Update Body
                       | Read Body
                       | Read Body Drop Body

   What is proved here (the spike: one file, no library):

       gen_iff_accepts : forall tr, gen tr <-> accepts tr = true

   ...and the architecture it forced, which is what the reusable
   contract will have to carry:

     * Soundness (->) runs through [ok s alpha], whose nonterminal
       clause checks its tail at EVERY state the nonterminal can
       reach.  Checking the tail only at [s] would be wrong -- the
       nonterminal consumes input first -- and tying that clause to
       the derivation is why [Reach] is defined over [derives].  Its
       obligations are [prod_ok] (one per production; five of the six
       cases are [reflexivity], [PB_cs] needs the net measure) and
       [ok_init].  [soundness] is stated with [fix] rather than
       [induction]: an [induction] replaces the head nonterminal's
       sub-derivation by an induction hypothesis, and [Reach] needs
       that derivation.

     * Completeness (<-) is routed through the word-level predicate
       [good], never through a state-indexed induction: from a count
       above zero the machine accepts an extra [Drop] that no
       production can derive ([safe 1 [Drop]] holds, [derives] does
       not), so "same state, same conclusion" is simply false.  Both
       sides are therefore characterized against [safe 0] after the
       opening [Create], and the only real work is [body_complete] --
       Dyck-prefix completeness, whose [Read] case needs the first
       position where the count bottoms out ([dip_split]).

   Compiles with Rocq 9.1.1:  rocq compile rcu.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Open Scope bool_scope.

(** * STA side *)

Inductive State : Type :=
| Uninit
| Reading (readers : nat)
| Error.

Inductive Event : Type :=
| Create
| Read
| Drop
| Update.

Definition is_live (s : State) : bool :=
  match s with Reading _ => true | _ => false end.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** The transition matrix.  [Error] is a sink; everything outside the
    three live clauses is API misuse. *)
Definition step (s : State) (e : Event) : State :=
  match s, e with
  | Uninit, Create   => Reading 0
  | Reading n, Read  => Reading (S n)
  | Reading n, Drop  => if Nat.eqb n 0 then Error else Reading (Nat.pred n)
  | Reading n, Update => Reading n
  | Error, _         => Error
  | _, _             => Error
  end.

Lemma step_error_sink : forall e, step Error e = Error.
Proof. intros e; reflexivity. Qed.

(** * Recognizer *)

Fixpoint run_from (s : State) (tr : list Event) : State :=
  match tr with
  | nil => s
  | e :: es => run_from (step s e) es
  end.

Definition run (tr : list Event) : State := run_from Uninit tr.

Definition accepts (tr : list Event) : bool := negb (is_err (run tr)).

Lemma run_from_app : forall tr1 tr2 s,
    run_from s (tr1 ++ tr2) = run_from (run_from s tr1) tr2.
Proof.
  induction tr1 as [| e tr1 IH]; intros tr2 s; simpl; [ reflexivity | ].
  apply IH.
Qed.

Lemma run_from_err : forall tr, run_from Error tr = Error.
Proof.
  induction tr as [| e tr IH]; [ reflexivity | ].
  (* [simpl] has already folded [step Error e] to [Error]. *)
  simpl. exact IH.
Qed.

(** * CFG side *)

Inductive Nt : Type :=
| Program
| Body.

Inductive sym : Type :=
| Sn (n : Nt)
| Se (e : Event).

(** Productions.  Defined as a relation, not a table: the RHS is a
    symbol list, and the proof obligations below are discharged by
    constructor inversion rather than by boolean case analysis. *)
Inductive prod : Nt -> list sym -> Prop :=
| PR_nil  : prod Program nil
| PR_body : prod Program (Se Create :: Sn Body :: nil)
| PB_nil  : prod Body nil
| PB_upd  : prod Body (Se Update :: Sn Body :: nil)
| PB_read : prod Body (Se Read :: Sn Body :: nil)
| PB_cs   : prod Body (Se Read :: Sn Body :: Se Drop :: Sn Body :: nil).

(** Derivability, in YIELD form: a derivation records how the word
    splits between a nonterminal and its continuation.

    This is not cosmetic.  With a rewriting-style relation ("expand the
    leftmost nonterminal, then another, ...") the split of the word
    between a production and the rest of the form is never recorded, so
    every proof needs a separate decomposition lemma to recover it --
    and the state at which the continuation is run is exactly that
    missing piece of information.  Recording the split in the rule
    makes the state threading of the soundness proof direct.

    (The rewriting view, if anyone wants it, is equivalent: leftmost
    expansion can always be scheduled to match a yield derivation.) *)
Inductive derives : list sym -> list Event -> Prop :=
| D_base : derives nil nil
| D_se   : forall e alpha tr,
    derives alpha tr -> derives (Se e :: alpha) (e :: tr)
| D_sn   : forall A beta tr1 tr2 alpha,
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

Definition gen (tr : list Event) : Prop := derives (Sn Program :: nil) tr.

(** * The grammar really is unbounded-state.

    Machine-checked witness for the non-regularity argument in the
    header: every `Reading n` is reachable, so no finite automaton can
    recognize this language (its Myhill-Nerode classes are unbounded). *)
(** * ============================================================
    The F1 contract, discovered here in miniature.

    A context-free grammar knows nothing about states, yet its
    soundness proof has to know that a terminal is safe where it sits.
    The judgment below carries both -- and its middle clause is the
    whole point of this file. *)

(** Where a nonterminal may be expanded. *)
Definition inv (A : Nt) (s : State) : bool :=
  match A, s with
  | Program, Uninit  => true
  | Body,   Reading _ => true
  | _,      _        => false
  end.

(** States reachable by running some word derived from [A], WITHOUT
    faulting on the way.

    Restricting to non-faulting endpoints is deliberate, not a way of
    hiding the conclusion: the soundness proof only ever applies this
    clause after it has separately established that the endpoint does
    not fault (from the obligation on the production), so nothing is
    assumed that is not also proved -- while the top-level instance
    stays trivially dischargeable instead of demanding a word-level
    soundness lemma before the proof can even start. *)
Definition Reach (s : State) (A : Nt) (s' : State) : Prop :=
  exists tr, derives (Sn A :: nil) tr /\ run_from s tr = s' /\ s' <> Error.

(** [ok s alpha]: [alpha] is safe to expand and run from [s].

    The clause for a nonterminal checks its TAIL at every state the
    nonterminal can reach, not at [s].  Checking the tail only at [s]
    would be wrong: expanding a nonterminal makes it consume input
    first, so the tail is really run from a later state -- and whether
    it is still safe there is exactly what has to be guaranteed. *)
Fixpoint ok (s : State) (alpha : list sym) {struct alpha} : Prop :=
  match alpha with
  | nil           => s <> Error
  | Se e :: rest  => step s e <> Error /\ ok (step s e) rest
  | Sn A :: rest  => inv A s = true /\ (forall s', Reach s A s' -> ok s' rest)
  end.

(** * Net reader change.

    The [Drop] sitting after the inner [Body] in [PB_cs] is safe only
    because words the grammar derives never decrease the count.  That
    is not visible from the shape of a form alone -- a form's
    nonterminals contribute whatever their words contribute -- so it is
    measured with a signed net and bounded relative to the form.

    This is the obligation that a boolean/`nat`-only encoding cannot
    express: the bound has to carry a debt ([Se Drop] contributes -1),
    so [Z] is what makes it provable.

    The recursion is written with the recursive call as the FIRST
    argument of [Z.add]/[Z.sub].  With the usual [1 + net tr'] form,
    [simpl] fires the first match of [Z.add] (its left argument is the
    literal 1) and reduces the term to a raw match over [Pos], which
    [lia] cannot see through -- measured, not guessed. *)
Fixpoint net (tr : list Event) : Z :=
  match tr with
  | nil           => 0%Z
  | Read :: tr'   => Z.add (net tr') 1%Z
  | Drop :: tr'   => Z.sub (net tr') 1%Z
  | Update :: tr' => net tr'
  | Create :: tr' => net tr'
  end.

Lemma net_app : forall tr1 tr2, net (tr1 ++ tr2) = (net tr1 + net tr2)%Z.
Proof.
  induction tr1 as [| e tr1 IH]; intros tr2; simpl; [ reflexivity | ].
  destruct e; cbn [net]; rewrite IH; lia.
Qed.

(** Net contributed by a form: terminals count directly, nonterminals
    by the bound [nt_net] of their own words. *)
Definition nt_net (A : Nt) : Z := 0%Z.

Fixpoint form_net (alpha : list sym) : Z :=
  match alpha with
  | nil             => 0%Z
  | Se Create :: t  => form_net t
  | Se Read :: t    => Z.add (form_net t) 1%Z
  | Se Drop :: t    => Z.sub (form_net t) 1%Z
  | Se Update :: t  => form_net t
  | Sn A :: t       => Z.add (nt_net A) (form_net t)
  end.

(** The per-production half of the bound -- dischargeable mechanically,
    one case per production constructor. *)
Lemma prod_net : forall A beta, prod A beta -> (nt_net A <= form_net beta)%Z.
Proof.
  (* [simpl] will not unfold [nt_net]: its body ignores the argument,
     so nothing is "reduced away" by its heuristic. *)
  intros A beta H; destruct H; unfold nt_net; simpl; lia.
Qed.

Lemma derives_net : forall alpha tr, derives alpha tr ->
    (net tr >= form_net alpha)%Z.
Proof.
  intros alpha tr H;
    induction H as [ | e tr IH | A beta tr1 tr2 alpha Hp IH1 IH2 ].
  - cbn [net form_net]. lia.
  - destruct e; cbn [net form_net]; lia.
  - rewrite net_app. cbn [form_net]. pose proof (prod_net A beta Hp). lia.
Qed.

(** Running a safe word from [Reading k] lands at exactly [k + net]. *)
Lemma run_reading_net : forall tr k m,
    run_from (Reading k) tr = Reading m ->
    (Z.of_nat m = Z.of_nat k + net tr)%Z.
Proof.
  induction tr as [| e tr IH]; intros k m H.
  - simpl in *. inversion H. lia.
  - destruct e; simpl in *.
    + pose proof (run_from_err tr). congruence.
    + pose proof (IH (S k) m H). lia.
    + destruct k; simpl in H.
      * pose proof (run_from_err tr). congruence.
      * pose proof (IH k m H). lia.
    + pose proof (IH k m H). lia.
Qed.

Lemma run_reading_shape : forall tr k,
    run_from (Reading k) tr <> Error ->
    exists m, run_from (Reading k) tr = Reading m.
Proof.
  induction tr as [| e tr IH]; intros k H.
  - exists k. reflexivity.
  - destruct e; simpl in *.
    + pose proof (run_from_err tr). congruence.
    + exact (IH (S k) H).
    + destruct k; simpl in *.
      * exfalso. pose proof (run_from_err tr). congruence.
      * exact (IH k H).
    + exact (IH k H).
Qed.

(** [Reach] from a strictly positive count never lands at [Reading 0].
    This is what makes the [Drop] of the [PB_cs] production safe inside
    the per-production obligation below. *)
Lemma reach_positive : forall n s',
    Reach (Reading (S n)) Body s' -> exists k, s' = Reading (S k).
Proof.
  intros n s' [tr [Hd [Hr Hne]]].
  assert (Hsafe : run_from (Reading (S n)) tr <> Error)
    by (rewrite Hr; exact Hne).
  destruct (run_reading_shape tr (S n) Hsafe) as [m Hm].
  pose proof (run_reading_net tr (S n) m Hm) as Hz.
  pose proof (derives_net (Sn Body :: nil) tr Hd) as Hn.
  unfold nt_net in Hn. simpl in Hn.
  assert (Hge : (1 <= Z.of_nat m)%Z) by lia.
  destruct m as [| m']; [ lia | ].
  (* [subst s'] is wrong here: [Hr] also mentions [s'], and [subst]
     would rewrite the goal through it instead of through [Hms]. *)
  assert (Hms : s' = Reading (S m')) by (rewrite <- Hr; exact Hm).
  rewrite Hms. exists m'. reflexivity.
Qed.

(** * Word-level characterization of the safety property.

    The recognizer is safe from [n] readers exactly when the word never
    underflows and never mentions [Create].  Both directions of the
    final equivalence are routed through this: the STA side proves it
    directly, the CFG side proves it against the same predicate. *)
Fixpoint safe (n : nat) (tr : list Event) : bool :=
  match tr with
  | nil          => true
  | Read :: tr'  => safe (S n) tr'
  | Drop :: tr'  => match n with 0 => false | S k => safe k tr' end
  | Update :: tr' => safe n tr'
  | Create :: tr' => false
  end.

Lemma is_err_eq : forall s, is_err s = true <-> s = Error.
Proof.
  intros s; destruct s; simpl; split; intros H;
    try reflexivity; try discriminate.
Qed.

Lemma accepts_iff : forall tr, accepts tr = true <-> run tr <> Error.
Proof.
  intros tr. unfold accepts.
  destruct (is_err (run tr)) eqn: He; simpl.
  - split; [ discriminate | intro H; exfalso; apply H;
      exact (proj1 (is_err_eq (run tr)) He) ].
  - split; [ intro H; intro Hf; rewrite Hf in He; simpl in He;
      discriminate | intros _; reflexivity ].
Qed.

Lemma run_reading_safe : forall tr n,
    run_from (Reading n) tr <> Error <-> safe n tr = true.
Proof.
  induction tr as [| e tr IH]; intros n; simpl.
  - split; intros H; [ reflexivity | discriminate ].
  - destruct e.
    + split; intro H;
        [ exfalso; apply H; apply run_from_err | discriminate ].
    + exact (IH (S n)).
    + destruct n.
      * split; intro H;
          [ exfalso; apply H; apply run_from_err | discriminate ].
      * simpl. exact (IH n).
    + exact (IH n).
Qed.

Lemma reading_unbounded : forall n, exists tr, run tr = Reading n.
Proof.
  induction n as [| n IH].
  - exists (Create :: nil). reflexivity.
  - destruct IH as [tr Htr].
    exists (tr ++ (Read :: nil)).
    unfold run in *.
    rewrite run_from_app.
    rewrite Htr. simpl. reflexivity.
Qed.

(** * ============================================================
    Direction 1: generated traces do not fault. *)

(** The per-production obligation, in the shape the contract will
    generalize: an available nonterminal's production is safe where it
    sits.

    The two [epsilon] productions discharge themselves along the way --
    [try discriminate] head-reduces [ok s nil] to [s <> Error].  What
    remains are the four productions that start with a terminal; four
    of their six sub-goals are [reflexivity], and [PB_cs] is the only
    one that needs [reach_positive]. *)
Lemma prod_ok : forall A beta s, prod A beta -> inv A s = true -> ok s beta.
Proof.
  intros A beta s Hp Hinv.
  destruct Hp; unfold inv in Hinv; destruct s; try discriminate;
    simpl in *; try discriminate.
  - split; [ intro H; discriminate | ].    (* PR_body, Uninit *)
    split; [ reflexivity | ].
    intros s' [tr [Hd [Hr Hne]]]. exact Hne.
  - split; [ intro H; discriminate | ].    (* PB_upd, Reading readers *)
    split; [ reflexivity | ].
    intros s' [tr [Hd [Hr Hne]]]. exact Hne.
  - split; [ intro H; discriminate | ].    (* PB_read, Reading readers *)
    split; [ reflexivity | ].
    intros s' [tr [Hd [Hr Hne]]]. exact Hne.
  - split; [ intro H; discriminate | ].    (* PB_cs, Reading readers *)
    split; [ reflexivity | ].
    intros s1 Hs1.
    destruct (reach_positive readers s1 Hs1) as [k Hk]. subst s1.
    split; [ simpl; intro H; discriminate | ].
    split; [ simpl; reflexivity | ].
    intros s2 [tr [Hd [Hr Hne]]]. exact Hne.
Qed.

Lemma ok_init : ok Uninit (Sn Program :: nil).
Proof.
  split; [ reflexivity | ].
  intros s' [tr [Hd [Hr Hne]]]. exact Hne.
Qed.

(** The soundness theorem, in the shape the contract will generalize.

    [fix] rather than [induction]: after an [induction] on the
    derivation the sub-derivation of the head nonterminal has been
    replaced by its induction hypothesis, and [Reach] needs exactly
    that sub-derivation to place the continuation's state. *)
Lemma soundness : forall alpha tr, derives alpha tr ->
    forall s, ok s alpha -> run_from s tr <> Error.
Proof.
  fix soundness 3.
  intros alpha tr H.
  destruct H as [ | e alpha' tr' Hder
                | A beta tr1 tr2 alpha' Hp Hder1 Hder2 ];
    intros s Hok.
  - simpl in *. exact Hok.
  - simpl in *. destruct Hok as [Hs Hok'].
    exact (soundness alpha' tr' Hder (step s e) Hok').
  - rewrite run_from_app. destruct Hok as [Hinv Hok'].
    pose proof (prod_ok A beta s Hp Hinv) as Hokb.
    assert (Hne1 : run_from s tr1 <> Error)
      by exact (soundness beta tr1 Hder1 s Hokb).
    assert (Hs1 : Reach s A (run_from s tr1)).
    { exists tr1. split.
      - exact (derives_sn A beta tr1 Hp Hder1).
      - split; [ reflexivity | exact Hne1 ]. }
    exact (soundness alpha' tr2 Hder2 (run_from s tr1) (Hok' _ Hs1)).
Qed.

Lemma gen_run : forall tr, gen tr -> run tr <> Error.
Proof.
  intros tr Hg. unfold run.
  exact (soundness (Sn Program :: nil) tr Hg Uninit ok_init).
Qed.

Lemma gen_accepts : forall tr, gen tr -> accepts tr = true.
Proof.
  intros tr Hg. apply accepts_iff. apply gen_run. exact Hg.
Qed.

(** * ============================================================
    Direction 2: every safe trace is generated. *)

(** Where the running count first reaches its floor.

    Generalized over the floor [n] because the recursive cases move it:
    a leading [Read] raises it by one before the cut is found.  The
    word gets shorter in every recursive call, so plain structural
    induction on the word suffices.

    The split is placed at the FIRST position where the count bottoms
    out, which is exactly what keeps the prefix [n]-safe; the suffix
    comes out [0]-safe because it starts one below the floor. *)
Lemma dip_split : forall tr n,
    safe (S n) tr = true -> safe n tr = false ->
    exists w1 w2, tr = w1 ++ Drop :: w2 /\
        safe n w1 = true /\ safe 0 w2 = true.
Proof.
  induction tr as [| e tr IH]; intros n H1 H0.
  - simpl in *. discriminate.
  - destruct e; simpl in *.
    + discriminate.
    + destruct (IH (S n) H1 H0) as [w1 [w2 [Heq [Hw1 Hw2]]]].
      subst tr. exists (Read :: w1), w2.
      split; [ reflexivity | split; [ simpl; exact Hw1 | exact Hw2 ] ].
    + destruct n.
      * exists nil, tr.
        split; [ reflexivity | split; [ reflexivity | exact H1 ] ].
      * destruct (IH n H1 H0) as [w1 [w2 [Heq [Hw1 Hw2]]]].
        subst tr. exists (Drop :: w1), w2.
        split; [ reflexivity | split; [ simpl; exact Hw1 | exact Hw2 ] ].
    + destruct (IH n H1 H0) as [w1 [w2 [Heq [Hw1 Hw2]]]].
      subst tr. exists (Update :: w1), w2.
      split; [ reflexivity | split; [ simpl; exact Hw1 | exact Hw2 ] ].
Qed.

(** Completeness, stated at PRODUCTION level rather than as
    [derives (Sn Body :: nil) tr].

    The recursive cases need the head production of the sub-word to
    feed [D_sn] directly: inverting [derives (Sn A :: alpha) w] would
    mean taking apart [w = tr1 ++ tr2], and unification cannot split a
    concatenation.  [derives_sn] turns the conclusion back into the
    usual form whenever it is wanted. *)
Lemma body_complete : forall len tr, length tr <= len ->
    safe 0 tr = true ->
    exists beta, prod Body beta /\ derives beta tr.
Proof.
  induction len as [| len IH]; intros tr Hlen Hsafe.
  - destruct tr as [| e tr]; [ exists nil; split; [ constructor | constructor ] | ].
    simpl in Hlen. lia.
  - destruct tr as [| e tr].
    + exists nil; split; [ constructor | constructor ].
    + simpl in Hlen. destruct e; simpl in Hsafe.
      * discriminate.                       (* Create *)
      * (* Read *)
        destruct (safe 0 tr) eqn: H0.
        -- (* prefix is itself balanced: Read + inner *)
           destruct (IH tr ltac:(lia) H0) as [beta0 [Hp0 Hd0]].
           exists (Se Read :: Sn Body :: nil). split; [ constructor | ].
           apply D_se. apply (derives_sn Body beta0 tr Hp0 Hd0).
        -- (* the count bottoms out inside [tr]: read-body-drop *)
           destruct (dip_split tr 0 Hsafe H0)
             as [w1 [w2 [Heq [Hw1 Hw2]]]].
           subst tr.
           rewrite length_app in Hlen. simpl in Hlen.
           destruct (IH w1 ltac:(lia) Hw1) as [beta1 [Hp1 Hd1]].
           destruct (IH w2 ltac:(lia) Hw2) as [beta2 [Hp2 Hd2]].
           exists (Se Read :: Sn Body :: Se Drop :: Sn Body :: nil).
           split; [ constructor | ].
           apply D_se.
           exact (D_sn Body beta1 w1 (Drop :: w2)
                    (Se Drop :: Sn Body :: nil) Hp1 Hd1
                    (D_se Drop (Sn Body :: nil) w2
                      (derives_sn Body beta2 w2 Hp2 Hd2))).
      * discriminate.                       (* Drop at 0 *)
      * (* Update *)
        destruct (IH tr ltac:(lia) Hsafe) as [beta0 [Hp0 Hd0]].
        exists (Se Update :: Sn Body :: nil). split; [ constructor | ].
        apply D_se. apply (derives_sn Body beta0 tr Hp0 Hd0).
Qed.

Lemma body_complete0 : forall tr, safe 0 tr = true ->
    exists beta, prod Body beta /\ derives beta tr.
Proof.
  intros tr H. apply (body_complete (length tr)); [ apply le_n | exact H ].
Qed.

(** The recognizer is safe exactly when the trace starts with [Create]
    and the rest never underflows. *)
Definition good (tr : list Event) : bool :=
  match tr with
  | nil           => true
  | Create :: tr' => safe 0 tr'
  | _ :: _        => false
  end.

Lemma run_good : forall tr, run tr <> Error <-> good tr = true.
Proof.
  induction tr as [| e tr IH]; simpl.
  - split; [ reflexivity | intro Hx; discriminate ].
  - destruct e; simpl in *.
    + exact (run_reading_safe tr 0).
    + split; [ intro H; exfalso; apply H; apply run_from_err
             | intro H; discriminate H ].
    + split; [ intro H; exfalso; apply H; apply run_from_err
             | intro H; discriminate H ].
    + split; [ intro H; exfalso; apply H; apply run_from_err
             | intro H; discriminate H ].
Qed.

Lemma accepts_good : forall tr, accepts tr = true <-> good tr = true.
Proof.
  intros tr. rewrite accepts_iff. exact (run_good tr).
Qed.

Lemma good_gen : forall tr, good tr = true -> gen tr.
Proof.
  induction tr as [| e tr IH]; simpl; intro H.
  - exact (derives_sn Program nil nil PR_nil D_base).
  - destruct e.
    + destruct (body_complete0 tr H) as [beta0 [Hp0 Hd0]].
      apply (derives_sn Program (Se Create :: Sn Body :: nil) (Create :: tr)
               PR_body).
      apply D_se. apply (derives_sn Body beta0 tr Hp0 Hd0).
    + discriminate.
    + discriminate.
    + discriminate.
Qed.

(** * The headline theorem, for this model. *)
Theorem gen_iff_accepts : forall tr, gen tr <-> accepts tr = true.
Proof.
  intros tr. split.
  - intro H. apply gen_accepts. exact H.
  - intro H. apply accepts_good in H. apply good_gen. exact H.
Qed.
