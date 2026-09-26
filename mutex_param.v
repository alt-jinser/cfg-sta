(* Parameterized Mutex protocol, on top of protocol_lib.

   One addition over mutex_grammar.v:

   1. IDENTITY.  Events carry a thread id and `Held` carries its owner, so
      the state space {Uninitialized} + {Unlocked} + {Held t | t : nat} +
      {Error} is INFINITE.  It is no longer a finite automaton -- which
      is why the grammar needs a *parameterized nonterminal* H(o) and a
      regular language will not do.  The refinement is documented:
      `ostd/docs/sync-protocol/mutex-fsm.md` defines
      `guard_drop(m,t2,g), t2 != t` as `wrong_owner_unlock`, keeping
      ownership precisely because the guard is `!Send`.

       Program -> epsilon | Create U

       U    -> epsilon
             | LockCall(t) U | TryLockFail(t) U
             | TryLockCall(t) U
             | LockAcquire(t) H(t) | TryLockSuccess(t) H(t)

       H(o) -> epsilon
             | LockCall(t) H(o) | TryLockFail(t) H(o)
             | TryLockCall(t) H(o)
             | GuardDrop(o) U             <-- identity match

   This file owes protocol_lib only the transition matrix, the
   nonterminals/productions/invariant, and the 7 obligations.  The
   equivalence comes from the library.

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile mutex_param.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import protocol_lib.

Definition tid := nat.

Inductive State : Type :=
| Uninitialized
| Unlocked
| Held (owner : tid)
| Error.

Inductive Event : Type :=
| Create
| LockCall       (t : tid)
| LockAcquire    (t : tid)
| TryLockCall    (t : tid)
| TryLockSuccess (t : tid)
| TryLockFail    (t : tid)
| GuardDrop      (t : tid).


Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** The transition matrix: the STA side. *)
Definition step (s : State) (e : Event) : State :=
  match s, e with
  | Uninitialized, Create => Unlocked
  | Uninitialized, _ => Error
  | Unlocked, Create => Error
  | Unlocked, LockCall _ => Unlocked
  | Unlocked, TryLockFail _ => Unlocked
  | Unlocked, TryLockCall _ => Unlocked
  | Unlocked, LockAcquire t => Held t
  | Unlocked, TryLockSuccess t => Held t
  | Unlocked, GuardDrop _ => Error
  | Held o, Create => Error
  | Held o, LockCall _ => Held o
  | Held o, TryLockFail _ => Held o
  | Held o, TryLockCall _ => Held o
  | Held o, LockAcquire _ => Error
  | Held o, TryLockSuccess _ => Error
  | Held o, GuardDrop t => if Nat.eqb t o then Unlocked else Error
  | Error, _ => Error
  end.

(** * Grammar side *)

Inductive Nt := Program | U | H (owner : tid).

Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nil  : productions Program nil
| PR_body : productions Program (Se Create :: Sn U :: nil)
| PU_nil  : productions U nil
| PU_call : forall t, productions U (Se (LockCall t) :: Sn U :: nil)
| PU_tryf : forall t, productions U (Se (TryLockFail t) :: Sn U :: nil)
| PU_tryc : forall t, productions U (Se (TryLockCall t) :: Sn U :: nil)
| PU_acq  : forall t, productions U (Se (LockAcquire t) :: Sn (H t) :: nil)
| PU_succ : forall t, productions U (Se (TryLockSuccess t) :: Sn (H t) :: nil)
| PH_nil  : forall o, productions (H o) nil
| PH_call : forall o t, productions (H o) (Se (LockCall t) :: Sn (H o) :: nil)
| PH_tryf : forall o t, productions (H o) (Se (TryLockFail t) :: Sn (H o) :: nil)
| PH_tryc : forall o t, productions (H o) (Se (TryLockCall t) :: Sn (H o) :: nil)
| PH_drop : forall o, productions (H o) (Se (GuardDrop o) :: Sn U :: nil).

(** The invariant is PRECISE about the owner: [H o] is available in
    [Held o'] only when [o = o'], because the production [H(o) ->
    GuardDrop(o) U] would otherwise derive a release the machine
    rejects. *)
Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | Program, Uninitialized => true
  | U, Unlocked            => true
  | H o, Held o'           => Nat.eqb o o'
  | _, _                   => false
  end.

(** * The 7 obligations *)

Ltac case_types := case_of State; case_of Event.

Lemma ob_is_error_ok : forall s, is_err s = true <-> s = Error.
Proof. discharge case_types. Qed.

Lemma ob_init_fault_free : Uninitialized <> Error.
Proof. discharge case_types. Qed.

Lemma ob_inv_start : available Program Uninitialized = true.
Proof. reflexivity. Qed.

Lemma ob_prod_ok : forall A beta s,
    productions A beta -> available A s = true ->
    ok Error step available productions s beta.
Proof. discharge_prod productions case_types. Qed.

(** [Error] is a sink in this table; [run_from_sink] turns that into
    the recognizer-level fact the completeness proof argues from. *)
Lemma run_from_error : forall tr, run_from step Error tr = Error.
Proof. apply run_from_sink. intros e; reflexivity. Qed.

Definition wellformed (tr : list Event) : Prop :=
  run Uninitialized step tr <> Error.

Lemma ob_word_ok_run : forall tr,
    run Uninitialized step tr <> Error <-> wellformed tr.
Proof. intros tr. unfold wellformed. split; intro H; exact H. Qed.

(** Direction 2: a safe run from an available nonterminal is derivable
    from it.  Same shape as mutex_grammar's, plus one guard split (the
    owner match) which the chain peels off before the cases are read --
    ten cases survive, one per real transition. *)
(** The two witnesses [gen_of_run] asks for; the library owns the
    induction. *)
Lemma nil_prod : forall A, productions A nil.
Proof. intros A; destruct A; constructor. Qed.

Lemma step_prod : forall A s e,
    available A s = true -> step s e <> Error ->
    exists B, productions A (Se e :: Sn B :: nil) /\
              available B (step s e) = true.
Proof.
  intros A s e Hinv Hne.
  destruct A as [| | o]; case_types; simpl in *;
    try (rewrite Nat.eqb_eq in Hinv; subst);
    try discriminate Hinv;
    repeat match goal with
           | [ H : context[if ?b then _ else _] |- _ ] =>
               destruct b eqn:Hb; simpl in *
           | |- context[if ?b then _ else _] =>
               destruct b eqn:Hb; simpl in *
           end;
    try (exfalso; apply Hne; reflexivity).
  - (* Program / Uninitialized / Create *)
    exists U. split; [ exact PR_body | reflexivity ].
  - (* U / Unlocked / LockCall *)
    exists U. split; [ exact (PU_call t) | reflexivity ].
  - (* U / Unlocked / LockAcquire *)
    exists (H t). split;
      [ exact (PU_acq t) | simpl; apply Nat.eqb_refl ].
  - (* U / Unlocked / TryLockCall *)
    exists U. split; [ exact (PU_tryc t) | reflexivity ].
  - (* U / Unlocked / TryLockSuccess *)
    exists (H t). split;
      [ exact (PU_succ t) | simpl; apply Nat.eqb_refl ].
  - (* U / Unlocked / TryLockFail *)
    exists U. split; [ exact (PU_tryf t) | reflexivity ].
  - (* H owner / Held owner / LockCall *)
    exists (H owner). split;
      [ exact (PH_call owner t) | simpl; apply Nat.eqb_refl ].
  - (* H owner / Held owner / TryLockCall *)
    exists (H owner). split;
      [ exact (PH_tryc owner t) | simpl; apply Nat.eqb_refl ].
  - (* H owner / Held owner / TryLockFail *)
    exists (H owner). split;
      [ exact (PH_tryf owner t) | simpl; apply Nat.eqb_refl ].
  - (* H owner / Held owner / GuardDrop owner *)
    pose proof (proj1 (Nat.eqb_eq t owner) Hb) as Hte. rewrite Hte.
    exists U. split; [ exact (PH_drop owner) | reflexivity ].
Qed.

Lemma ob_word_ok_gen : forall tr, wellformed tr -> gen productions Program tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run run_from_error nil_prod step_prod Program Uninitialized); [ reflexivity | exact H ].
Qed.

(** * Assemble the model. *)
Definition P : Protocol :=
  {| st := State; ev := Event; nt := Nt;
     init := Uninitialized; fault := Error; next := step;
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

Notation runp := (run (init P) (next P)).
Notation acceptsp := (accepts (init P) (next P) (is_error P)).
Notation genp := (gen (prod P) (start P)).

(** * ============================================================
    What the parameter actually buys you
    ============================================================ *)

(* --- the identity guard: releasing someone else's lock is an error --- *)
Example drop_by_other_rejected :
  acceptsp (Create :: LockAcquire 0 :: GuardDrop 1 :: nil) = false.
Proof. reflexivity. Qed.

Example drop_by_owner_accepted :
  acceptsp (Create :: LockAcquire 0 :: GuardDrop 0 :: nil) = true.
Proof. reflexivity. Qed.

(* --- and the grammar agrees in both directions --- *)
Example gen_drop_by_owner : genp (Create :: LockAcquire 0 :: GuardDrop 0 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

Example gen_try_call : genp (Create :: TryLockCall 7 :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

(** The identity constraint cannot be expressed over a finite alphabet:
    the recognizer has infinitely many states [Held t].  Two traces that
    differ only in the owner are accepted or rejected differently, and no
    finite automaton over {create, lock, unlock, ...} can tell them apart. *)
Example owners_are_distinguished :
    acceptsp (Create :: LockAcquire 0 :: GuardDrop 0 :: nil) = true
 /\ acceptsp (Create :: LockAcquire 0 :: GuardDrop 1 :: nil) = false.
Proof. split; reflexivity. Qed.
