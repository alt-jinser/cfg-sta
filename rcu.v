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

   Compiles with Rocq 9.1.1:  rocq compile rcu.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
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

(** One leftmost expansion step.  Expanding a nonterminal consumes no
    input: the machine advances only when a [Se] is run. *)
Inductive expand : list sym -> list sym -> Prop :=
| Ex_hd : forall A beta gamma,
    prod A beta -> expand (Sn A :: gamma) (beta ++ gamma)
| Ex_tl : forall e alpha alpha',
    expand alpha alpha' -> expand (Se e :: alpha) (Se e :: alpha').

(** An all-terminal form and the word it spells out. *)
Inductive terminal : list sym -> list Event -> Prop :=
| T_nil  : terminal nil nil
| T_cons : forall e alpha w,
    terminal alpha w -> terminal (Se e :: alpha) (e :: w).

Inductive derives : list sym -> list Event -> Prop :=
| D_base : forall alpha w, terminal alpha w -> derives alpha w
| D_step : forall alpha alpha' w,
    expand alpha alpha' -> derives alpha' w -> derives alpha w.

Definition gen (tr : list Event) : Prop := derives (Sn Program :: nil) tr.

(** * The grammar really is unbounded-state.

    Machine-checked witness for the non-regularity argument in the
    header: every `Reading n` is reachable, so no finite automaton can
    recognize this language (its Myhill-Nerode classes are unbounded). *)
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
