(* Buffer protocol, on top of protocol_lib.

   The non-lock test of the contract: nothing here is a mutex, and the
   grammar still lines up with the recognizer.

   The nonterminal carries the COUNT.  That is not decoration: a
   production `Buf(n) -> Get ...` is state-independent, so if the
   nonterminal were count-free the grammar would derive `Get` from an
   empty buffer, which the machine rejects -- and [prod_ok] would fail
   at exactly that cell.  State:

       Program -> epsilon | Setup Buf(0)

       Buf(0)   -> epsilon | Put(x) Buf(1) | Peek Buf(0)
                         | Flush Buf(0) | Close Closed
       Buf(S k) -> epsilon | Put(x) Buf(S (S k)) | Get Buf(k)
                         | Peek Buf(S k) | Flush Buf(0) | Close Closed

       Closed   -> epsilon | Peek Closed

   (spelled with the guard `1 <= n` on the [Get] production, so one
   production covers every positive count).

   This file owes protocol_lib the transition matrix, the
   nonterminals/productions/invariant, and the 7 obligations.

   Compiles with Rocq 9.1.1:
     rocq compile protocol_lib.v && rocq compile buffer.v
*)

Require Import Corelib.Init.Nat.
Require Import Corelib.Lists.ListDef.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import protocol_lib.

Inductive State : Type :=
| Uninitialized
| Buffered (items : list nat)
| Closed
| Error.

Inductive Event : Type :=
| Setup
| Put    (x : nat)
| Get
| Peek
| Flush
| Close.

Definition Trace := list Event.

Definition is_err (s : State) : bool :=
  match s with Error => true | _ => false end.

(** Removing the head; only ever called under the `1 <= length` guard. *)
Definition pop (items : list nat) : list nat :=
  match items with nil => nil | _ :: rest => rest end.

(** * The transition matrix *)
Definition step (s : State) (e : Event) : State :=
  match s, e with
  (* initialization *)
  | Uninitialized, Setup => Buffered nil
  | Uninitialized, _     => Error
  | Error, _             => Error
  | _, Setup             => Error

  (* the buffer *)
  | Buffered items, Put x  => Buffered (items ++ (x :: nil))
  | Buffered items, Get    =>
      if Nat.leb 1 (length items) then Buffered (pop items) else Error
  | Buffered items, Peek   => Buffered items
  | Buffered items, Flush  => Buffered nil
  | Buffered items, Close  => Closed

  (* terminal state: only a peek is harmless *)
  | Closed, Peek  => Closed
  | Closed, _     => Error
  end.

(** * Grammar side *)

Inductive Nt := Program | Buf (n : nat) | Cl.

Inductive productions : Nt -> list (sym Nt Event) -> Prop :=
| PR_nil   : productions Program nil
| PR_setup : productions Program (Se Setup :: Sn (Buf 0) :: nil)
| PB_nil   : forall n, productions (Buf n) nil
| PB_put   : forall n x,
    productions (Buf n) (Se (Put x) :: Sn (Buf (S n)) :: nil)
| PB_get   : forall n, Nat.leb 1 n = true ->
    productions (Buf n) (Se Get :: Sn (Buf (Nat.pred n)) :: nil)
| PB_peek  : forall n,
    productions (Buf n) (Se Peek :: Sn (Buf n) :: nil)
| PB_flush : forall n,
    productions (Buf n) (Se Flush :: Sn (Buf 0) :: nil)
| PB_close : forall n,
    productions (Buf n) (Se Close :: Sn Cl :: nil)
| PC_nil   : productions Cl nil
| PC_peek  : productions Cl (Se Peek :: Sn Cl :: nil).

Definition available (A : Nt) (s : State) : bool :=
  match A, s with
  | Program, Uninitialized => true
  | Buf n, Buffered items  => Nat.eqb n (length items)
  | Cl, Closed             => true
  | _, _                   => false
  end.

(** Two length facts the invariant needs when it is re-established
    after a step. *)
Lemma length_put : forall (items : list nat) (x : nat),
    length (items ++ (x :: nil)) = S (length items).
Proof. intros. rewrite length_app. simpl. lia. Qed.

Lemma pop_length : forall (items : list nat),
    length (pop items) = Nat.pred (length items).
Proof. intros items; destruct items; simpl; reflexivity. Qed.

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
Proof.
  discharge_prod productions case_types.
  (* The two cells whose [available] needs a length fact: [simpl] folds
     [Nat.eqb (S n) (length (items ++ x))] into a raw match, and the
     [Get] cell has [Nat.pred] on the left. *)
  all: try (rewrite length_put; simpl; apply Nat.eqb_refl).
  all: try (rewrite pop_length; simpl; apply Nat.eqb_refl).
Qed.

Lemma step_error_sink : forall e, step Error e = Error.
Proof. intros e; reflexivity. Qed.

Lemma run_from_error : forall tr, run_from step Error tr = Error.
Proof.
  induction tr as [| e tr IH]; [ reflexivity | ].
  change (run_from step (step Error e) tr = Error).
  rewrite step_error_sink. exact IH.
Qed.

Definition wellformed (tr : list Event) : Prop :=
  run Uninitialized step tr <> Error.

Lemma ob_word_ok_run : forall tr,
    run Uninitialized step tr <> Error <-> wellformed tr.
Proof. intros tr. unfold wellformed. split; intro H; exact H. Qed.

(** Direction 2.  NOTE the normalisation: [cbn [run_from step available]]
    rather than [simpl].  [simpl] folds [Nat.leb 1 (length items)] into a
    raw match on [length items], and then the [Get] production's guard
    could not be reconstructed -- [cbn] with an explicit delta list
    leaves [Nat.leb] alone, so the guard survives as written. *)
Lemma gen_of_run : forall A s tr,
    available A s = true -> run_from step s tr <> Error ->
    derives productions (Sn A :: nil) tr.
Proof.
  intros A s tr. revert A s.
  induction tr as [| e tr IH]; intros A s Hinv Hrun.
  - destruct A as [| n | ].
    + exact (derives_sn productions Program nil nil PR_nil
               (derives_nil productions)).
    + exact (derives_sn productions (Buf n) nil nil (PB_nil n)
               (derives_nil productions)).
    + exact (derives_sn productions Cl nil nil PC_nil
               (derives_nil productions)).
  - cbn [run_from step] in Hrun.
    assert (Hne : step s e <> Error).
    { intro Hf. rewrite Hf in Hrun. rewrite run_from_error in Hrun.
      exact (Hrun eq_refl). }
    destruct A as [| n | ]; case_types; cbn [run_from step available] in *;
      try (rewrite Nat.eqb_eq in Hinv; subst);
      try discriminate Hinv;
      repeat match goal with
             | [ H : context[if ?b then _ else _] |- _ ] =>
                 destruct b eqn:Hb; cbn [run_from step] in *
             | |- context[if ?b then _ else _] =>
                 destruct b eqn:Hb; cbn [run_from step] in *
             end;
      try (exfalso; apply Hrun; apply run_from_error).
    + (* Program / Uninitialized / Setup *)
      refine (derives_sn productions Program
                (Se Setup :: Sn (Buf 0) :: nil)
                (Setup :: tr) PR_setup _).
      apply derives_se.
      apply (IH (Buf 0) (Buffered nil));
        [ cbn [available]; apply Nat.eqb_refl | exact Hrun ].
    + (* Buf (length items) / Buffered items / Put x *)
      refine (derives_sn productions (Buf (length items))
                (Se (Put x) :: Sn (Buf (S (length items))) :: nil)
                (Put x :: tr) (PB_put (length items) x) _).
      apply derives_se.
      apply (IH (Buf (S (length items))) (Buffered (items ++ (x :: nil))));
        [ cbn [available]; rewrite length_put; apply Nat.eqb_refl
        | exact Hrun ].
    + (* Buf (length items) / Buffered items / Get, non-empty *)
      refine (derives_sn productions (Buf (length items))
                (Se Get :: Sn (Buf (Nat.pred (length items))) :: nil)
                (Get :: tr) (PB_get (length items) Hb) _).
      apply derives_se.
      apply (IH (Buf (Nat.pred (length items))) (Buffered (pop items)));
        [ cbn [available]; rewrite pop_length; apply Nat.eqb_refl
        | exact Hrun ].
    + (* Buf (length items) / Buffered items / Peek *)
      refine (derives_sn productions (Buf (length items))
                (Se Peek :: Sn (Buf (length items)) :: nil)
                (Peek :: tr) (PB_peek (length items)) _).
      apply derives_se.
      apply (IH (Buf (length items)) (Buffered items));
        [ cbn [available]; apply Nat.eqb_refl | exact Hrun ].
    + (* Buf (length items) / Buffered items / Flush *)
      refine (derives_sn productions (Buf (length items))
                (Se Flush :: Sn (Buf 0) :: nil)
                (Flush :: tr) (PB_flush (length items)) _).
      apply derives_se.
      apply (IH (Buf 0) (Buffered nil));
        [ cbn [available]; apply Nat.eqb_refl | exact Hrun ].
    + (* Buf (length items) / Buffered items / Close *)
      refine (derives_sn productions (Buf (length items))
                (Se Close :: Sn Cl :: nil)
                (Close :: tr) (PB_close (length items)) _).
      apply derives_se.
      apply (IH Cl Closed); [ reflexivity | exact Hrun ].
    + (* Cl / Closed / Peek *)
      refine (derives_sn productions Cl
                (Se Peek :: Sn Cl :: nil)
                (Peek :: tr) PC_peek _).
      apply derives_se.
      apply (IH Cl Closed); [ reflexivity | exact Hrun ].
Qed.

Lemma ob_word_ok_gen : forall tr, wellformed tr -> gen productions Program tr.
Proof.
  intros tr H. unfold wellformed in H.
  apply (gen_of_run Program Uninitialized); [ reflexivity | exact H ].
Qed.

(** * Assemble the model *)
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

(** * What a developer would ask for *)
Example producer_consumer_roundtrip : acceptsp
  (Setup :: Put 1 :: Put 2 :: Peek :: Get :: Flush :: Close :: nil) = true.
Proof. reflexivity. Qed.

Example producer_consumer_generated : genp
  (Setup :: Put 1 :: Put 2 :: Peek :: Get :: Flush :: Close :: nil).
Proof. apply (gen_iff_accepts P). reflexivity. Qed.

(* Taking from an empty buffer is an error. *)
Example get_from_empty : acceptsp (Setup :: Get :: nil) = false.
Proof. reflexivity. Qed.

(* Everything after Close is an error. *)
Example put_after_close : acceptsp (Setup :: Close :: Put 1 :: nil) = false.
Proof. reflexivity. Qed.

(* Peeking a closed buffer is a no-op, not an error. *)
Example peek_after_close : acceptsp (Setup :: Close :: Peek :: nil) = true.
Proof. reflexivity. Qed.

(* Examples handed to a developer really are accepted. *)
Definition alphabet : list Event :=
  Setup :: Put 0 :: Get :: Peek :: Flush :: Close :: nil.

Example examples_upto_1 :
  examples_upto P alphabet 1 = nil :: (Setup :: nil) :: nil.
Proof. reflexivity. Qed.

Example enumerated_examples_are_accepted :
  forall tr, In tr (examples_upto P alphabet 2) -> acceptsp tr = true.
Proof.
  intros tr H. unfold examples_upto in H.
  exact (examples_upto_sound P (traces_upto P alphabet 2) tr H).
Qed.
