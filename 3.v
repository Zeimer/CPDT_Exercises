From mathcomp Require Import ssreflect.

(* Ex. 1 *)
CoInductive tree (A : Type) : Type :=
    | node : A -> tree A -> tree A -> tree A.

Arguments node [A] _ _ _.

CoFixpoint everywhere {A : Type} (x : A) : tree A :=
  node x (everywhere x) (everywhere x).

CoFixpoint map {A B : Type} (f : A -> B) (t : tree A) : tree B :=
match t with
    | node v l r => node (f v) (map f l) (map f r)
end.

CoFixpoint zip {A B C : Type} (f : A -> B -> C) (ta : tree A) (tb : tree B)
  : tree C :=
match ta, tb with
    | node a la ra, node b lb rb => node (f a b) (zip f la lb) (zip f ra rb)
end.

CoFixpoint falses : tree bool := node false falses falses.
CoFixpoint true_false : tree bool :=
  node true
    (node false true_false true_false)
    (node false true_false true_false).

Require Import Bool.

CoInductive tree_eq {A : Type} : tree A -> tree A -> Prop :=
    | node_eq : forall (l l' r r' : tree A) (v : A),
        tree_eq l l' -> tree_eq r r' -> tree_eq (node v l r) (node v l' r').

Definition wut {A : Type} (t : tree A) : tree A :=
match t with
    | node v l r => node v l r
end.

Lemma wut_eq :
  forall (A : Type) (t : tree A), t = wut t.
Proof.
  destruct t; reflexivity.
Qed.

Goal tree_eq (zip orb true_false falses) true_false.
Proof.
  cofix.
  rewrite (wut_eq _ (zip _ _ _)) (wut_eq _ true_false). cbn.
  constructor.
    rewrite (wut_eq _ (zip _ _ _)). cbn. constructor; auto.
    rewrite (wut_eq _ (zip _ _ _)). cbn. constructor; auto.
Qed.



