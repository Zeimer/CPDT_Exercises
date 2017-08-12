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

Require Import List.
Import ListNotations.

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

(* Nonempty lists *)

Inductive nel (A : Type) : Type :=
    | singl : A -> nel A
    | ncons : A -> nel A -> nel A.

Arguments singl [A].
Arguments ncons [A] _ _.

Fixpoint nel_app {A : Type} (l1 l2 : nel A) : nel A :=
match l1 with
    | singl x => ncons x l2
    | ncons h t => ncons h (nel_app t l2)
end.

Notation "l1 +++ l2" := (nel_app l1 l2) (at level 40). 

Fixpoint nel_bind {A B : Type} (l : nel A) (f : A -> nel B)
  : nel B :=
match l with
    | singl x => f x
    | ncons h t => f h +++ nel_bind t f
end.

Definition nel_prod {A : Type} (l1 l2 : nel (nel A)) : nel (nel A) :=
  nel_bind l1 (fun x =>
    nel_bind l2 (fun y => singl (x +++ y))).

(* Literals *)
Inductive literal : Set :=
    | pos : var -> literal
    | neg : var -> literal.

Definition ldenote (truth : var -> bool) (l : literal) : bool :=
match l with
    | pos v => truth v
    | neg v => negb (truth v)
end.

Definition clause := nel literal.

(* CNF translation *)

Fixpoint ccdenote (truth : var -> bool) (cc : clause) : bool :=
match cc with
    | singl x => ldenote truth x
    | ncons h t => ldenote truth h || ccdenote truth t
end.

Lemma ccdenote_app :
  forall (truth : var -> bool) (c1 c2 : clause),
    ccdenote truth (c1 +++ c2) = ccdenote truth c1 || ccdenote truth c2.
Proof.
  induction c1; cbn; intro; by rewrite // IHc1 orb_assoc.
Qed.

Definition cnf_prop : Set := nel clause.

Fixpoint cdenote (truth : var -> bool) (p : cnf_prop) : bool :=
match p with
    | singl c => ccdenote truth c
    | ncons h t => ccdenote truth h && cdenote truth t
end.

Lemma cdenote_app :
  forall (truth : var -> bool) (p1 p2 : cnf_prop),
    cdenote truth (p1 +++ p2) = cdenote truth p1 && cdenote truth p2.
Proof.
  induction p1; cbn; intro; by rewrite // IHp1 andb_assoc.
Qed.

Lemma cdenote_bind_l :
  forall (p : cnf_prop) (truth : var -> bool) (c : clause),
    cdenote truth (nel_bind p (fun x : nel literal => singl (x +++ c))) =
    cdenote truth p || ccdenote truth c.
Proof.
  induction p; cbn; intros;
  by rewrite ccdenote_app // IHp -orb_andb_distrib_l.
Qed.

Lemma cdenote_bind_r :
  forall (p : cnf_prop) (truth : var -> bool) (c : clause),
    cdenote truth (nel_bind p (fun x : nel literal => singl (c +++ x))) =
    cdenote truth p || ccdenote truth c.
Proof.
  induction p; cbn; intros;
  by rewrite ccdenote_app orb_comm // IHp -orb_andb_distrib_l.
Qed.

Ltac solve_bool := repeat (rewrite -?orb_assoc -?andb_assoc;
match goal with
    | |- context [?b1 || ?b2] => destruct b1; cbn; rewrite ?orb_true_l
    | |- context [?b1 && ?b2] => destruct b1; cbn; rewrite ?andb_false_l
end; auto).

Lemma cdenote_nel_prod :
  forall (truth : var -> bool) (p1 p2 : cnf_prop),
    cdenote truth (nel_prod p1 p2) = cdenote truth p1 || cdenote truth p2.
Proof.
  induction p1; induction p2; cbn in *.
    by rewrite ccdenote_app.
    by rewrite ccdenote_app IHp2 -orb_andb_distrib_r.
    by rewrite ccdenote_app cdenote_bind_l -orb_andb_distrib_l.
    specialize (IHp1 (ncons a0 p2)). cbn in *.
      rewrite ccdenote_app cdenote_app cdenote_bind_r IHp1. solve_bool.
Qed.

Function distr_or (p : nnf_prop) : cnf_prop :=
match p with
    | nnf_var v => singl (singl (pos v))
    | nnf_not v => singl (singl (neg v))
    | nnf_and p1 p2 => distr_or p1 +++ distr_or p2
    | nnf_or p1 p2 => nel_prod (distr_or p1) (distr_or p2)
end.

Lemma distr_or_correct :
  forall (truth : var -> bool) (p : nnf_prop),
    cdenote truth (distr_or p) = ndenote truth p.
Proof.
  intros. induction p; cbn; trivial.
    by rewrite cdenote_app IHp1 IHp2.
    by rewrite cdenote_nel_prod IHp1 IHp2.
Qed.

Definition cnf (f : formula) : cnf_prop :=
  distr_or (push_not (unarrow f)).

Lemma cnf_correct :
  forall (truth : var -> bool) (f : formula),
    cdenote truth (cnf f) = fdenote truth f.
Proof.
  intros. unfold cnf.
  by rewrite distr_or_correct push_not_correct unarrow_correct.
Qed.

(* DNF translation *)

Definition dnf_prop : Set := nel clause.

Fixpoint dcdenote (truth : var -> bool) (dc : clause) : bool :=
match dc with
    | singl x => ldenote truth x
    | ncons h t => ldenote truth h && dcdenote truth t
end.

Lemma dcdenote_app :
  forall (truth : var -> bool) (c1 c2 : clause),
    dcdenote truth (c1 +++ c2) = dcdenote truth c1 && dcdenote truth c2.
Proof.
  induction c1; cbn; intro; by rewrite // IHc1 andb_assoc.
Qed.

Fixpoint ddenote (truth : var -> bool) (p : dnf_prop) : bool :=
match p with
    | singl c => dcdenote truth c
    | ncons h t => dcdenote truth h || ddenote truth t
end.

Lemma ddenote_app :
  forall (truth : var -> bool) (p1 p2 : cnf_prop),
    ddenote truth (p1 +++ p2) = ddenote truth p1 || ddenote truth p2.
Proof.
  induction p1; cbn; intro; by rewrite // IHp1 orb_assoc.
Qed.

Lemma ddenote_bind_l :
  forall (p : cnf_prop) (truth : var -> bool) (c : clause),
    ddenote truth (nel_bind p (fun x : nel literal => singl (x +++ c))) =
    ddenote truth p && dcdenote truth c.
Proof.
  induction p; cbn; intros;
  by rewrite dcdenote_app // IHp -andb_orb_distrib_l.
Qed.

Lemma ddenote_bind_r :
  forall (p : cnf_prop) (truth : var -> bool) (c : clause),
    ddenote truth (nel_bind p (fun x : nel literal => singl (c +++ x))) =
    ddenote truth p && dcdenote truth c.
Proof.
  induction p; cbn; intros;
  by rewrite dcdenote_app andb_comm // IHp -andb_orb_distrib_l.
Qed.

Ltac solve_bool' := repeat (rewrite -?orb_assoc -?andb_assoc;
match goal with
    | |- context [?b1 && ?b2] => destruct b1; cbn; rewrite ?andb_false_l
    | |- context [?b1 || ?b2] => destruct b1; cbn; rewrite ?orb_true_l
end; auto).

Lemma ddenote_nel_prod :
  forall (truth : var -> bool) (p1 p2 : cnf_prop),
    ddenote truth (nel_prod p1 p2) = ddenote truth p1 && ddenote truth p2.
Proof.
  induction p1; induction p2; cbn in *.
    by rewrite dcdenote_app.
    by rewrite dcdenote_app IHp2 -andb_orb_distrib_r.
    by rewrite dcdenote_app ddenote_bind_l -andb_orb_distrib_l.
    specialize (IHp1 (ncons a0 p2)). cbn in *.
      rewrite dcdenote_app ddenote_app ddenote_bind_r IHp1.
      rewrite ?orb_assoc. solve_bool'.
Qed.

Fixpoint distr_and (p : nnf_prop) : dnf_prop :=
match p with
    | nnf_var v => singl (singl (pos v))
    | nnf_not v => singl (singl (neg v))
    | nnf_or p1 p2 => distr_and p1 +++ distr_and p2
    | nnf_and p1 p2 => nel_prod (distr_and p1) (distr_and p2)
end.

Lemma distr_and_correct :
  forall (truth : var -> bool) (p : nnf_prop),
    ddenote truth (distr_and p) = ndenote truth p.
Proof.
  intros. induction p; cbn; trivial.
    by rewrite ddenote_nel_prod IHp1 IHp2.
    by rewrite ddenote_app IHp1 IHp2.
Qed.

Definition dnf (f : formula) : dnf_prop :=
  distr_and (push_not (unarrow f)).

Lemma dnf_correct :
  forall (truth : var -> bool) (f : formula),
    ddenote truth (dnf f) = fdenote truth f.
Proof.
  intros. unfold dnf.
  by rewrite distr_and_correct push_not_correct unarrow_correct.
Qed.

(* Tests *)

Definition s := f_and (f_or (f_var 1) (f_var 2)) (f_var 3).
Definition s' := f_or (f_and (f_var 1) (f_var 2)) (f_var 3).

Compute cnf s.
Compute cnf s'.
Compute dnf s.
Compute dnf s'.

Definition empty : var -> bool := fun _ => false.