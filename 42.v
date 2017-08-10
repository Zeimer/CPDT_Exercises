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
Module Ex2.

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

End Ex2.

(* Ex. 3 *)
Module Ex3.

Require Import Bool.

Definition var : Set := nat.

Inductive formula : Set :=
    | f_var : var -> formula
    | f_not : formula -> formula
    | f_and : formula -> formula -> formula
    | f_or : formula -> formula -> formula
    | f_imp : formula -> formula -> formula
    | f_iff : formula -> formula -> formula.

Fixpoint fdenote (truth : var -> bool) (f : formula) : bool :=
match f with
    | f_var v => truth v
    | f_not f' => negb (fdenote truth f')
    | f_and f1 f2 => andb (fdenote truth f1) (fdenote truth f2)
    | f_or f1 f2 => orb (fdenote truth f1) (fdenote truth f2)
    | f_imp f1 f2 => implb (fdenote truth f1) (fdenote truth f2)
    | f_iff f1 f2 => eqb (fdenote truth f1) (fdenote truth f2)
end.

Inductive prop : Set :=
    | pvar : var -> prop
    | pnot : prop -> prop
    | pand : prop -> prop -> prop
    | por : prop -> prop -> prop.

Fixpoint pdenote (truth : var -> bool) (p : prop) : bool :=
match p with
    | pvar v => truth v
    | pnot f' => negb (pdenote truth f')
    | pand f1 f2 => andb (pdenote truth f1) (pdenote truth f2)
    | por f1 f2 => orb (pdenote truth f1) (pdenote truth f2)
end.

Fixpoint unarrow (f : formula) : prop :=
match f with
    | f_var v => pvar v
    | f_not f' => pnot (unarrow f')
    | f_and f1 f2 => pand (unarrow f1) (unarrow f2)
    | f_or f1 f2 => por (unarrow f1) (unarrow f2)
    | f_imp f1 f2 => por (pnot (unarrow f1)) (unarrow f2)
    | f_iff f1 f2 =>
        let f1' := unarrow f1 in
        let f2' := unarrow f2 in
          pand (por f1' (pnot f2')) (por (pnot f1') f2')
end.

Lemma unarrow_correct :
  forall (truth : var -> bool) (f : formula),
    pdenote truth (unarrow f) = fdenote truth f.
Proof.
  induction f; cbn; intros; repeat
  match goal with
      | H : _ = _ |- _ => rewrite H
  end; auto; repeat
  match goal with
      | |- context [negb ?b] => destruct b; cbn
      | |- context [?b1 || ?b2] => destruct b1, b2
  end; auto.
(*Restart.
  induction f; cbn; intros; auto.
    try f_equal; auto.
    try f_equal; auto.
    try f_equal; auto.*)
Qed.

Inductive nnf_prop : Set :=
    | nnf_var : var -> nnf_prop
    | nnf_not : var -> nnf_prop
    | nnf_and : nnf_prop -> nnf_prop -> nnf_prop
    | nnf_or : nnf_prop -> nnf_prop -> nnf_prop.

Fixpoint ndenote (truth : var -> bool) (p : nnf_prop) : bool :=
match p with
    | nnf_var v => truth v
    | nnf_not v => negb (truth v)
    | nnf_and p1 p2 => andb (ndenote truth p1) (ndenote truth p2)
    | nnf_or p1 p2 => orb (ndenote truth p1) (ndenote truth p2)
end.

Fixpoint nnf_negate (p : nnf_prop) : nnf_prop :=
match p with
    | nnf_var v => nnf_not v
    | nnf_not v => nnf_var v
    | nnf_and p1 p2 => nnf_or (nnf_negate p1) (nnf_negate p2)
    | nnf_or p1 p2 => nnf_and (nnf_negate p1) (nnf_negate p2)
end.

Lemma nnf_negate_correct :
  forall (p : nnf_prop) (truth : var -> bool),
    ndenote truth (nnf_negate p) = negb (ndenote truth p).
Proof.
  induction p; intro; cbn;
  by rewrite ?negb_involutive // IHp1 IHp2 ?negb_andb ?negb_orb.
Qed.

Function push_not (p : prop) : nnf_prop :=
match p with
    | pvar v => nnf_var v
    | pnot p' => nnf_negate (push_not p')
    | pand p1 p2 => nnf_and (push_not p1) (push_not p2)
    | por p1 p2 => nnf_or (push_not p1) (push_not p2)
end.

Lemma push_not_correct :
  forall (truth : var -> bool) (p : prop),
    ndenote truth (push_not p) = pdenote truth p.
Proof.
  intros. functional induction push_not p; cbn; auto;
  rewrite ?nnf_negate_correct; f_equal; auto.
Qed.

Inductive literal : Set :=
    | pos : var -> literal
    | neg : var -> literal.

Function distr_or (p : nnf_prop) : nnf_prop :=
match p with
    | nnf_var v => nnf_var v
    | nnf_not v => nnf_not v
    | nnf_and p1 p2 => nnf_and (distr_or p1) (distr_or p2)
    | nnf_or p1 p2 =>
        match distr_or p1, distr_or p2 with
            | nnf_and p1_1 p1_2, p2' =>
                nnf_and (nnf_or p1_1 p2') (nnf_or p1_2 p2')
            | p1', nnf_and p2_1 p2_2 =>
                nnf_and (nnf_or p1' p2_1) (nnf_or p1' p2_2)
            | p1', p2' => nnf_or p1' p2'
        end
end.

Lemma distr_or_correct :
  forall (truth : var -> bool) (p : nnf_prop),
    ndenote truth (distr_or p) = ndenote truth p.
Proof.
  intros. functional induction distr_or p; cbn;
  rewrite ?IHn ?IHn0; auto; repeat 
  match goal with
      | H : ?a = _, H' : ndenote _ ?a = _ |- _ => rewrite H in H'; cbn in H'
      | |- context [?b1 || ?b2] => destruct b1, b2; cbn in *
  end; auto.
Qed.

Function distr_and (p : nnf_prop) : nnf_prop :=
match p with
    | nnf_var v => nnf_var v
    | nnf_not v => nnf_not v
    | nnf_and p1 p2 =>
        match distr_and p1, distr_and p2 with
            | nnf_or p1_1 p1_2, p2' =>
                nnf_or (nnf_and p1_1 p2') (nnf_and p1_2 p2')
            | p1', nnf_or p2_1 p2_2 =>
                nnf_or (nnf_and p1' p2_1) (nnf_and p1' p2_2)
            | p1', p2' => nnf_and p1' p2'
        end
    | nnf_or p1 p2 => nnf_or (distr_and p1) (distr_and p2)
end.

Lemma distr_and_correct :
  forall (truth : var -> bool) (p : nnf_prop),
    ndenote truth (distr_and p) = ndenote truth p.
Proof.
  intros. functional induction distr_and p; cbn;
  rewrite ?IHn ?IHn0; auto; repeat 
  match goal with
      | H : ?a = _, H' : ndenote _ ?a = _ |- _ => rewrite H in H'; cbn in H'
      | |- context [?b1 && ?b2] => destruct b1, b2; cbn in *
  end; auto.
Qed.

(*Definition s := f_and (f_var 1) (f_var 2).*)

Definition cnf (f : formula) : nnf_prop :=
  distr_or (push_not (unarrow f)).

Lemma cnf_correct :
  forall (truth : var -> bool) (f : formula),
    ndenote truth (cnf f) = fdenote truth f.
Proof.
  intros. unfold cnf.
  by rewrite distr_or_correct push_not_correct unarrow_correct.
Qed.

Definition empty : var -> bool := fun _ => false.

Definition satisfiable (p : prop) : Prop :=
  exists truth : var -> bool, pdenote truth p = true.

Lemma satisfiable_pvar :
  forall (v : var) (truth : var -> bool),
    truth v = true -> satisfiable (pvar v).
Proof.
  red. eauto.
Qed.

Lemma satisfiable_pnot :
  forall p : prop, (forall truth : var -> bool, pdenote truth p = false) ->
    satisfiable (pnot p).
Proof.
  destruct p; red; cbn; intro; exists (fun _ => false); by rewrite ?H.
Qed.

(*Lemma satisfiable_pand :
  forall (p1 p2 : prop) (truth : var -> bool),
    satisfiable p1 -> satisfiable truth p2 -> satisfiable (pand p1 p2).
Proof.*)

Lemma safisfiable_por :
  forall p1 p2 : prop,
    satisfiable p1 \/ satisfiable p2 -> satisfiable (por p1 p2).
Proof.
  unfold satisfiable. intros. decompose [or ex] H;
  cbn; exists x.
    by rewrite H1.
    by rewrite orb_comm H1.
Qed.

Definition cnf_clause := list literal.
Definition dnf_clause := list literal.

Require Import List.
Import ListNotations.

Definition ldenote (truth : var -> bool) (l : literal) : bool :=
match l with
    | pos v => truth v
    | neg v => negb (truth v)
end.

Fixpoint ccdenote (truth : var -> bool) (cc : cnf_clause) : bool :=
match cc with
    | [] => false
    | h :: t => ldenote truth h || ccdenote truth t
end.

Lemma ccdenote_app :
  forall (truth : var -> bool) (c1 c2 : cnf_clause),
    ccdenote truth (c1 ++ c2) = ccdenote truth c1 || ccdenote truth c2.
Proof.
  induction c1; cbn; intro; by rewrite // IHc1 orb_assoc.
Qed.

Fixpoint dcdenote (truth : var -> bool) (cc : cnf_clause) : bool :=
match cc with
    | [] => false
    | h :: t => ldenote truth h && ccdenote truth t
end.

Definition cnf_prop : Set := list cnf_clause.
Definition dnf_prop : Set := list dnf_clause.

Fixpoint cdenote (truth : var -> bool) (p : cnf_prop) : bool :=
match p with
    | [] => true
    | h :: t => ccdenote truth h && cdenote truth t
end.

Lemma cdenote_app :
  forall (truth : var -> bool) (p1 p2 : cnf_prop),
    cdenote truth (p1 ++ p2) = cdenote truth p1 && cdenote truth p2.
Proof.
  induction p1; cbn; intro; by rewrite // IHp1 andb_assoc.
Qed.

Fixpoint ddenote (truth : var -> bool) (p : cnf_prop) : bool :=
match p with
    | [] => false
    | h :: t => dcdenote truth h || ddenote truth t
end.

Fixpoint toCNF (p : nnf_prop) : cnf_prop :=
match p with
    | nnf_var v => [[pos v]]
    | nnf_not v => [[neg v]]
    | nnf_and p1 p2 => toCNF p1 ++ toCNF p2
    | nnf_or p1 p2 => [concat (toCNF p1 ++ toCNF p2)]
end.

Lemma toCNF_correct :
  forall (truth : var -> bool) (p : nnf_prop),
    cdenote truth (toCNF p) = ndenote truth p.
Proof.
  induction p; cbn.
    by rewrite orb_false_r andb_true_r.
    by rewrite orb_false_r andb_true_r.
    by rewrite cdenote_app IHp1 IHp2.
    rewrite concat_app ccdenote_app.
Abort.

Goal forall (truth : var -> bool) (p : cnf_prop),
  cdenote truth p = ccdenote truth (concat p).
Proof.
  induction p; cbn.
Abort.

Function toCNF' (p : nnf_prop) : cnf_prop :=
match p with
    | nnf_var v => [[pos v]]
    | nnf_not v => [[neg v]]
    | nnf_and p1 p2 => toCNF' p1 ++ toCNF' p2
    | nnf_or p1 p2 =>
        match distr_or p1, distr_or p2 with
            | nnf_and p1_1 p1_2, p2' =>
                nnf_and (nnf_or p1_1 p2') (nnf_or p1_2 p2')
            | p1', nnf_and p2_1 p2_2 =>
                nnf_and (nnf_or p1' p2_1) (nnf_or p1' p2_2)
            | p1', p2' => nnf_or p1' p2'
        end
end.

Fixpoint toDNF (p : nnf_prop) : dnf_prop :=
match p with
    | nnf_var v => [[pos v]]
    | nnf_not v => [[neg v]]
    | nnf_and p1 p2 => [concat (toDNF p1 ++ toDNF p2)]
    | nnf_or p1 p2 => toDNF p1 ++ toDNF p2
end.

Definition dnf (f : formula) : nnf_prop :=
  distr_and (push_not (unarrow f)).


Definition s := f_and (f_or (f_var 1) (f_var 2)) (f_var 3).

Compute cnf s.
Compute dnf s.
Compute toCNF (cnf s).
Compute toDNF (dnf s).