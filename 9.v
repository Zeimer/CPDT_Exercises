From mathcomp Require Import ssreflect.

(* Ex. 1 *)
Ltac deSome :=
match goal with
    | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst; deSome
    | _ => reflexivity
end.

Theorem test : forall a b c d e f g : nat,
  Some a = Some b ->
  Some b = Some c ->
  Some e = Some c ->
  Some f = Some g ->
  c = a.
Proof.
  intros; deSome.
Abort.

Theorem test2 : forall a x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : nat,
  Some x1 = Some y1 ->
  Some x2 = Some y2 ->
  Some x3 = Some y3 ->
  Some x4 = Some y4 ->
  Some x5 = Some y5 ->
  Some x6 = Some y6 ->
  Some a = Some a ->
  x1 = x2.
Proof.
  intros. Time try deSome.
Abort.

(* Answer: This is because if the tactic is going to fail, then
   because of its recurrence structure it tries to solve the goal
   by trying hypotheses in any order, which amount to n! calls. *)

Ltac deSome' := intros; repeat
match goal with
    | H : Some _ = Some _ |- _ => inversion H; subst; clear H
    | _ => reflexivity
end.

Theorem test : forall a b c d e f g : nat,
  Some a = Some b ->
  Some b = Some c ->
  Some e = Some c ->
  Some f = Some g ->
  c = a.
Proof.
  deSome'.
Qed.

Theorem test2 : forall a x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : nat,
  Some x1 = Some y1 ->
  Some x2 = Some y2 ->
  Some x3 = Some y3 ->
  Some x4 = Some y4 ->
  Some x5 = Some y5 ->
  Some x6 = Some y6 ->
  Some a = Some a ->
  x1 = x2.
Proof.
  deSome'.
Abort.

Require Import List.
Import ListNotations.

Fixpoint all_lists (n : nat) : list (list bool) :=
match n with
    | 0 => [[]]
    | S n' =>
        let l := all_lists n' in
        map (cons false) l ++ map (cons true) l
end.

Compute all_lists 5.

Definition all_pairs (n : nat) : list (list bool * list bool) :=
  list_prod (all_lists n) (all_lists n).

Ltac disprove' H l :=
match l with
    | [] => idtac
    | (?h1, ?h2) :: ?t =>
        try (specialize (H h1 h2); cbn in H; discriminate; fail);
        disprove' H t
end.

Ltac disprove n :=
lazymatch goal with
    | |- ?G : forall (A : Type) (l : list A), _ =>
        assert (~ G);
        [ let H := fresh "H" in intro H; specialize (H bool);
          let l := constr:(all_pairs n) in
          let l' := eval cbn in l in disprove' constr:(H) l'
        | idtac ]
end.


Theorem test1 :
  forall A (ls1 ls2 : list A), ls1 ++ ls2 = ls2 ++ ls1.
Proof.
  disprove 1.
Abort.

Theorem test2 :
  forall A (ls1 ls2 : list A), length (ls1 ++ ls2 ) = length ls1 - length ls2.
Proof.
  disprove 1.
Abort.

Theorem test3 :
  forall A (ls : list A), length (rev ls) - 3 = 0.
Proof.
  disprove 5. (* IMPROVE: make it works for any number of quantifiers,
  not just 2. *)
Abort.

