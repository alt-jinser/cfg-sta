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

   THIS FILE IS A MODEL OF protocol_lib, not a proof development of its
   own: derivability, [ok], soundness, and the headline theorem
   `gen_iff_accepts` all come from the library.  What it owes the
   contract is the transition matrix, the grammar side (nonterminals,
   productions, availability), and the 7 obligations -- of which five
   are one-liners here, [ob_prod_ok] needs the net measure, and
   [ob_word_ok_gen] is the real content:

   * [ob_word_ok_gen] is the <- direction, and it is model-specific by
     necessity, not by choice: a state-indexed statement of
     completeness is FALSE for this protocol ([safe 1 [Drop]] holds but
     no production derives [Drop]), so which production applies, and
     where its word ends, has to be decided from the word.  For this
     grammar that means Dyck-prefix completeness ([body_complete]),
     whose [Read] case needs the first position where the count bottoms
     out ([dip_split]) -- because [Body -> Read Body Drop Body] is not
     right-linear, and a right-linear grammar would not need it.

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile rcu.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.micromega.Lia.
Require Import protocol_lib.
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

(** * Recognizer: the library's, instantiated here.

    One definition is shared by the recognizer, the obligations and the
    theorem -- writing a second one here would be exactly the
    duplication the contract exists to prevent.  These notations bind
    the table and the initial state, so the rest of the file reads as
    if the recognizer were defined locally. *)
Notation run_from := (protocol_lib.run_from step).
Notation run := (protocol_lib.run Uninit step).
Notation accepts := (protocol_lib.accepts Uninit step is_err).

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

(** * CFG side: nonterminals and productions *)

Inductive Nt : Type :=
| Program
| Body.

(** Productions.  Defined as a relation, not a table: the RHS is a
    symbol list, and the obligation below is discharged by constructor
    inversion rather than by boolean case analysis.

    [PB_cs] is the non-right-linear one -- two nonterminals in its RHS,
    straddling a terminal.  That single production is why the
    completeness direction needs a word cut rather than a per-event
    induction. *)
Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nil  : productions Program nil
| PR_body : productions Program (Se Create :: Sn Body :: nil)
| PB_nil  : productions Body nil
| PB_upd  : productions Body (Se Update :: Sn Body :: nil)
| PB_read : productions Body (Se Read :: Sn Body :: nil)
| PB_cs   : productions Body (Se Read :: Sn Body :: Se Drop :: Sn Body :: nil).

(** Where a nonterminal may be expanded. *)
Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | Program, Uninit  => true
  | Body,   Reading _ => true
  | _,      _        => false
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

Fixpoint form_net (alpha : list (sym Nt Event)) : Z :=
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
Lemma prod_net : forall A beta, productions A beta -> (nt_net A <= form_net beta)%Z.
Proof.
  (* [simpl] will not unfold [nt_net]: its body ignores the argument,
     so nothing is "reduced away" by its heuristic. *)
  intros A beta H; destruct H; unfold nt_net; simpl; lia.
Qed.

Lemma derives_net : forall alpha tr, derives productions alpha tr ->
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
    Reach Error step productions (Reading (S n)) Body s' ->
    exists k, s' = Reading (S k).
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
    underflows and never mentions [Create].  Both obligations that talk
    about words are routed through this: the recognizer side proves the
    equivalence directly, the grammar side proves generation from the
    same predicate. *)
Fixpoint safe (n : nat) (tr : list Event) : bool :=
  match tr with
  | nil          => true
  | Read :: tr'  => safe (S n) tr'
  | Drop :: tr'  => match n with 0 => false | S k => safe k tr' end
  | Update :: tr' => safe n tr'
  | Create :: tr' => false
  end.

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
    (* [run] is the library's, applied: expose the recursion to rewrite. *)
    change (run_from Uninit (tr ++ (Read :: nil)) = Reading (S n)).
    rewrite run_from_app.
    assert (Htr' : run_from Uninit tr = Reading n) by exact Htr.
    rewrite Htr'. simpl. reflexivity.
Qed.

(** * ============================================================
    The 7 obligations *)

Lemma ob_is_error_ok : forall s, is_err s = true <-> s = Error.
Proof.
  intros s; destruct s; simpl; split; intros H;
    try reflexivity; try discriminate.
Qed.

Lemma ob_init_fault_free : Uninit <> Error.
Proof. discriminate. Qed.

Lemma ob_inv_start : available Program Uninit = true.
Proof. reflexivity. Qed.

(** The per-production obligation: an available nonterminal's
    production is safe where it sits.

    The two [epsilon] productions discharge themselves along the way --
    [try discriminate] head-reduces [ok s nil] to [s <> Error].  What
    remains are the four productions that start with a terminal; four
    of their six sub-goals are [reflexivity], and [PB_cs] is the only
    one that needs [reach_positive]. *)
Lemma ob_prod_ok : forall A beta s,
    productions A beta -> available A s = true ->
    ok Error step available productions s beta.
Proof.
  intros A beta s Hp Hinv.
  destruct Hp; unfold available in Hinv; destruct s; try discriminate;
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

(** The word-level predicate of obligation 5 is defined further down,
    with [good] -- see [wellformed] there. *)

(** * ============================================================
    Direction 2: every safe trace is generated.

    Where the running count first reaches its floor.

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
    exists beta, productions Body beta /\ derives productions beta tr.
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
           apply D_se.
           apply (derives_sn productions Body beta0 tr Hp0 Hd0).
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
                      (derives_sn productions Body beta2 w2 Hp2 Hd2))).
      * discriminate.                       (* Drop at 0 *)
      * (* Update *)
        destruct (IH tr ltac:(lia) Hsafe) as [beta0 [Hp0 Hd0]].
        exists (Se Update :: Sn Body :: nil). split; [ constructor | ].
        apply D_se.
        apply (derives_sn productions Body beta0 tr Hp0 Hd0).
Qed.

Lemma body_complete0 : forall tr, safe 0 tr = true ->
    exists beta, productions Body beta /\ derives productions beta tr.
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

(** The word-level predicate of obligation 5: a trace the recognizer
    accepts. *)
Definition wellformed (tr : list Event) : Prop := good tr = true.

Lemma ob_word_ok_run : forall tr, run tr <> Error <-> wellformed tr.
Proof. intros tr. unfold wellformed. apply run_good. Qed.

Lemma ob_word_ok_gen : forall tr, wellformed tr -> gen productions Program tr.
Proof.
  induction tr as [| e tr IH]; simpl; intro H.
  - exact (derives_sn productions Program nil nil PR_nil D_base).
  - destruct e.
    + destruct (body_complete0 tr H) as [beta0 [Hp0 Hd0]].
      apply (derives_sn productions Program (Se Create :: Sn Body :: nil)
               (Create :: tr) PR_body).
      apply D_se. apply (derives_sn productions Body beta0 tr Hp0 Hd0).
    + discriminate.
    + discriminate.
    + discriminate.
Qed.

(** * Assemble the model *)
Definition P : Protocol :=
  {| st := State; ev := Event; nt := Nt;
     init := Uninit; fault := Error; next := step;
     is_error := is_err;
     start := Program; prod := productions; inv := available;

     is_error_ok := ob_is_error_ok;
     init_fault_free := ob_init_fault_free;
     inv_start := ob_inv_start;
     prod_ok := ob_prod_ok;
     word_ok := wellformed;
     word_ok_run := ob_word_ok_run;
     word_ok_gen := ob_word_ok_gen;
  |}.

(** [run] and [accepts] above are notations bound to THIS model's
    table, so the library's own (parameterized) ones have to be named
    qualifiedly here. *)
Notation runp := (protocol_lib.run (init P) (next P)).
Notation acceptsp := (protocol_lib.accepts (init P) (next P) (is_error P)).
Notation genp := (gen (prod P) (start P)).

(** * Everything below is library-provided; these are just checks. *)

(* The recognition criterion is prefix-closed: a trace may end while a
   read is still outstanding.  The grammar accepts it too. *)
Example prefix_read : acceptsp (Create :: Read :: nil) = true.
Proof. reflexivity. Qed.

Example balanced_ok : acceptsp (Create :: Read :: Drop :: nil) = true.
Proof. reflexivity. Qed.

(* Dropping a token nobody took is exactly the misuse this models. *)
Example drop_without_read_bad : acceptsp (Create :: Drop :: nil) = false.
Proof. reflexivity. Qed.

Example read_drop_generated : genp (Create :: Read :: Drop :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example drop_without_read_not_generated : ~ genp (Create :: Drop :: nil).
Proof.
  intro H. apply (gen_iff_accepts P) in H. simpl in H. discriminate H.
Qed.

(** The grammar really is unbounded-state: every [Reading n] is
    reachable AND accepted, so no finite automaton can recognize this
    language (its Myhill-Nerode classes are unbounded). *)
Example reading_unbounded_accepting :
    forall n, exists tr, run tr = Reading n /\ good tr = true.
Proof.
  intro n. destruct (reading_unbounded n) as [tr Htr].
  exists tr. split; [ exact Htr | apply run_good; rewrite Htr;
                      discriminate ].
Qed.
