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

(* Disprove the hypothesis [H] whose type is expected to be of the form
   [forall _ : list bool, _] by instantiating it with litsts from the
   list [l2] and trying to discriminate.

   [l1] is an accumulator — each time a recursive call is made, [l1] is
   set to be [l2], so that each recursive call can draw from [l2] all
   the lists and not only the ones remaining after previous calls. *)
Ltac disprove' H l1 l2 :=
match type of H with
  | forall _ : list bool, _ =>
    match l1 with
        | [] => fail
        | ?h :: ?t => try (specialize (H h); disprove' H l2 l2; fail);
            disprove' H t l2
    end
  | _ => try discriminate
end.

(* If the goal is a quantified statement about lists, try to disprove
   it in the context by asserting its negation and calling [disprove']
   on it with all lists of bools of length ≤ n. *)
Ltac disprove n :=
match goal with
    | |- ?G : forall (A : Type) (l : list A), _ =>
        assert (~ G);
        [ let H := fresh "H" in intro H; specialize (H bool);
          let l := constr:(all_lists n) in
          let l' := eval cbn in l in disprove' constr:(H) l' l'
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
  disprove 4.
Abort.

(* Ex. 3 *)

Theorem test1 : exists x, x = 0.
Proof. eauto. Qed.

Theorem test2 : exists x : unit, 0 = 0.
Proof.
  eauto. eexists.
Abort.

Hint Constructors unit.

Theorem test2 : exists x : unit, 0 = 0.
Proof.
  eauto.
Qed.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T );
  let y := eval unfold x in x in clear x; k y.

Theorem test3 : exists x : nat * nat, fst x = 7 /\ snd x = 2 + fst x.
Proof.
  evar (x1 : nat). evar (x2 : nat). exists (x1, x2); unfold x1, x2.
  cbn. eauto.
Restart.
  makeEvar nat ltac:(fun x =>
    makeEvar nat ltac:(fun y => exists (x, y))). cbn. eauto.
Qed.

Lemma exists_prod :
  forall (A B : Type) (P : A * B -> Prop),
    (exists (a : A) (b : B), P (a, b)) -> exists x : A * B, P x.
Proof.
  destruct 1 as [a [b H]]. exists (a, b). assumption.
Qed.

Lemma exists_unit :
  forall P : Prop, P -> exists _ : unit, P.
Proof.
  intros. exists tt. assumption.
Qed.

Ltac preproc := repeat
match goal with
    | |- exists x : unit, _ => exists tt
    | |- exists x : _ * _, _ => apply exists_prod
    | |- exists _, _ => eexists
end; cbn.

Theorem test4 : exists x : (unit * nat) * (nat * bool),
  snd (fst x) = 7 /\ fst (snd x) = 2 + snd (fst x) /\ snd (snd x) = true.
Proof.
  preproc. eauto.
Qed.

Ltac pre T k :=
match T with
    | (?X * ?Y)%type =>
        pre X ltac:(fun x =>
          pre Y ltac:(fun y => k (x, y)))
    | unit => k tt
    | ?T' => makeEvar T' k
end; cbn.

Ltac ex :=
match goal with
    | |- exists x : ?T, _ => pre T ltac:(fun x => exists x); eauto
end.

Goal exists _ : unit, 3 = 3.
Proof.
  ex.
Qed.

Goal exists x : nat, 3 = 3.
Proof.
  ex. Unshelve. exact 0.
Abort.

Goal exists x : nat * nat, 3 = 3.
Proof.
  ex.
Abort.

Theorem test4' : exists x : (unit * nat) * (nat * bool),
  snd (fst x) = 7 /\ fst (snd x) = 2 + snd (fst x) /\ snd (snd x) = true.
Proof.
  ex.
Qed.