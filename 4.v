From mathcomp Require Import ssreflect.

(* Ex. 1 *)
Goal forall n m : nat, {n <= m} + {n > m}.
Proof.
  elim => [| n' IH] [| m'] //.
    by left.
    by left; apply le_0_n.
    right. unfold gt, lt. by apply le_n_S, le_0_n.
    by case: (IH m') => H; [left | right]; unfold gt, lt in *;
    apply le_n_S.
Qed.

(* Ex. 2 *)
Require Import Bool.

Definition var : Set := nat.

Inductive prop : Set :=
    | pvar : var -> prop
    | pnot : prop -> prop
    | pand : prop -> prop -> prop
    | por : prop -> prop -> prop.

Fixpoint propDenote (val : var -> bool) (p : prop) : Prop :=
match p with
    | pvar v => val v = true
    | pnot p' => ~ propDenote val p'
    | pand p1 p2 => propDenote val p1 /\ propDenote val p2
    | por p1 p2 => propDenote val p1 \/ propDenote val p2
end.

Definition bool_true_dec (b : bool) : {b = true} + {~ b = true}.
Proof.
  by case: b; [left | right].
Defined.

Definition decide (val : var -> bool) (p : prop)
  : {propDenote val p} + {~ propDenote val p}.
Proof.
  elim: p => [v | p' IH | p1 IH1 p2 IH2 | p1 IH1 p2 IH2] /=.
    case: (val v). all: firstorder.
Defined.

Definition negate (p : prop) : {p' : prop |
  forall val : var -> bool, propDenote val p <-> ~ propDenote val p'}.
Proof.
  exists (pnot p). intro.
  induction p; cbn.
    destruct (val v). firstorder.
    firstorder.
    firstorder.
    firstorder.
    destruct (decide val p1), (decide val p2); firstorder.
Defined.

Require Import Setoid.

Fixpoint negate' (p : prop) : prop :=
match p with
    | pvar v => pnot (pvar v)
    | pnot p' => p'
    | pand p1 p2 => por (negate' p1) (negate' p2)
    | por p1 p2 => pand (negate' p1) (negate' p2)
end.

Theorem negate'_spec :
  forall (p : prop) (val : var -> bool),
    propDenote val (negate' p) <-> ~ propDenote val p.
Proof.
  induction p; cbn; intro.
    destruct (val v); firstorder.
    destruct (decide val p); firstorder.
    destruct (decide val p1), (decide val p2); firstorder.
    destruct (decide val p1), (decide val p2); firstorder.
Qed.

Definition negate'' (p : prop) : {p' : prop |
  forall val : var -> bool, propDenote val p <-> ~ propDenote val p'}.
Proof.
  exists (negate' p). intro. rewrite negate'_spec.
  destruct (decide val p); firstorder.
Defined.

(* Ex. 3 *)
Module DPLL.

Require Import Bool.

Definition var : Set := nat.

Inductive formula : Set :=
    | f_var : var -> formula
    | f_not : formula -> formula
    | f_and : formula -> formula -> formula
    | f_or : formula -> formula -> formula
    | f_imp : formula -> formula -> formula
    | f_iff : formula -> formula -> formula.

Fixpoint denote (truth : var -> bool) (f : formula) : bool :=
match f with
    | f_var v => truth v
    | f_not f' => negb (denote truth f')
    | f_and f1 f2 => andb (denote truth f1) (denote truth f2)
    | f_or f1 f2 => orb (denote truth f1) (denote truth f2)
    | f_imp f1 f2 => implb (denote truth f1) (denote truth f2)
    | f_iff f1 f2 => eqb (denote truth f1) (denote truth f2)
end.

Fixpoint unarrow (f : formula) : formula :=
match f with
    | f_var v => f_var v
    | f_not f' => f_not (unarrow f')
    | f_and f1 f2 => f_and (unarrow f1) (unarrow f2)
    | f_or f1 f2 => f_or (unarrow f1) (unarrow f2)
    | f_imp f1 f2 => f_or (f_not (unarrow f1)) (unarrow f2)
    | f_iff f1 f2 =>
        let f1' := unarrow f1 in
        let f2' := unarrow f2 in
          f_and (f_or f1' (f_not f2')) (f_or (f_not f1') f2')
end.

Lemma unarrow_correct :
  forall (truth : var -> bool) (f : formula),
    denote truth (unarrow f) = denote truth f.
Proof.
  induction f; cbn; intros; repeat
  match goal with
      | H : _ = _ |- _ => rewrite H
  end; auto; repeat
  match goal with
      | |- context [negb ?b] => destruct b; cbn
      | |- context [?b1 || ?b2] => destruct b1, b2
  end; auto.
Qed.

Function push_not (f : formula) : formula :=
match f with
    | f_var v => f_var v
    | f_not f' =>
        match push_not f' with
            | f_not f'' => f''
            | f_and f1 f2 => f_or (f_not f1) (f_not f2)
            | f_or f1 f2 => f_and (f_not f1) (f_not f2)
            | f'' => f_not f''
        end
    | f_and f1 f2 => f_and (push_not f1) (push_not f2)
    | f_or f1 f2 => f_or (push_not f1) (push_not f2)
    | f_imp f1 f2 => f_imp (push_not f1) (push_not f2)
    | f_iff f1 f2 => f_iff (push_not f1) (push_not f2)
end.

Lemma push_not_correct :
  forall (truth : var -> bool) (f : formula),
    denote truth (push_not f) = denote truth f.
Proof.
  intros. functional induction push_not f; cbn; repeat
  match goal with
      | H : _ = _ |- _ => rewrite H
      | H : ?a = _, H' : denote _ ?a = _ |- _ => rewrite H in H'
  end; cbn in *; auto; repeat
  match goal with
      | H : context [negb ?b] |- _ => destruct b; cbn in H
      | |- context [negb ?b] => destruct b; cbn
      | |- context [?b1 || ?b2] => destruct b1, b2
  end; cbn in *; auto.
Qed.

Function distr_or (f : formula) : formula :=
match f with
    | f_var v => f_var v
    | f_not f' => f_not (distr_or f')
    | f_and f1 f2 => f_and (distr_or f1) (distr_or f2)
    | f_or f1 f2 => let f1' := distr_or f1 in
        match distr_or f2 with
            | f_and f2_1 f2_2 => f_and (f_or f1' f2_1) (f_or f1' f2_2)
            | f2' => f_or f1' f2'
        end
    | f_imp f1 f2 => f_imp (distr_or f1) (distr_or f2)
    | f_iff f1 f2 => f_iff (distr_or f1) (distr_or f2)
end.

Lemma distr_or_correct :
  forall (truth : var -> bool) (f : formula),
    denote truth (distr_or f) = denote truth f.
Proof.
  intros. functional induction distr_or f; cbn; repeat
  match goal with
      | H : _ = _ |- _ => rewrite H
      | H : ?a = _, H' : denote _ ?a = _ |- _ => rewrite H in H'
  end; cbn in *; auto;
  match goal with
      | H : context [negb ?b] |- _ => destruct b; cbn in H
      | |- context [negb ?b] => destruct b; cbn
      | |- context [?b1 || ?b2] => destruct b1, b2
      | |- context [?b1 && ?b2] => destruct b1, b2
  end; cbn in *; auto.
Qed.

Definition cnf (f : formula) : formula :=
  distr_or (push_not (unarrow f)).

Lemma cnf_correct :
  forall (truth : var -> bool) (f : formula),
    denote truth (cnf f) = denote truth f.
Proof.
  intros. unfold cnf.
  by rewrite distr_or_correct push_not_correct unarrow_correct.
Qed.

