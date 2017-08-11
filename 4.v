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

Inductive literal : Set :=
    | pos : var -> literal
    | neg : var -> literal.

Definition ldenote (truth : var -> bool) (l : literal) : bool :=
match l with
    | pos v => truth v
    | neg v => negb (truth v)
end.

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

Fixpoint fmap {A B : Type} (f : A -> B) (l : nel A) : nel B :=
match l with
    | singl x => singl (f x)
    | ncons h t => ncons (f h) (fmap f t)
end.

Fixpoint join {A : Type} (l : nel (nel A)) : nel A :=
match l with
    | singl x => x
    | ncons h t => h +++ join t
end.

Definition clause := nel literal.

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

Fixpoint dcdenote (truth : var -> bool) (dc : clause) : bool :=
match dc with
    | singl x => ldenote truth x
    | ncons h t => ldenote truth h && ccdenote truth t
end.

Definition cnf_prop : Set := nel clause.
Definition dnf_prop : Set := nel clause.

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

Lemma cdenote_fmap_l :
  forall (truth : var -> bool) (c : clause) (p : cnf_prop),
    cdenote truth (fmap (fun l : nel literal => c +++ l) p) =
    ccdenote truth c || cdenote truth p.
Proof.
  induction p; cbn.
    by rewrite ccdenote_app.
    by rewrite ccdenote_app IHp -orb_andb_distrib_r.
Qed.

Lemma cdenote_fmap_r :
  forall (truth : var -> bool) (c : clause) (p : cnf_prop),
    cdenote truth (fmap (fun l : nel literal => l +++ c) p) =
    ccdenote truth c || cdenote truth p.
Proof.
  induction p; cbn.
    by rewrite ccdenote_app orb_comm.
    by rewrite ccdenote_app IHp orb_andb_distrib_r orb_comm.
Qed.

Fixpoint ddenote (truth : var -> bool) (p : dnf_prop) : bool :=
match p with
    | singl c => ccdenote truth c
    | ncons h t => ccdenote truth h || cdenote truth t
end.

Fixpoint nel_bind {A B : Type} (l : nel A) (f : A -> nel B)
  : nel B :=
match l with
    | singl x => f x
    | ncons h t => f h +++ nel_bind t f
end.

Definition nel_prod {A : Type} (l1 l2 : nel A) : nel (nel A) :=
  nel_bind l1 (fun x => nel_bind l2 (fun y => ncons (singl x) (singl (singl y)))).

Fixpoint distr_or (p : nnf_prop) : cnf_prop :=
match p with
    | nnf_var v => singl (singl (pos v))
    | nnf_not v => singl (singl (neg v))
    | nnf_and p1 p2 => distr_or p1 +++ distr_or p2
    | nnf_or p1 p2 =>
        match distr_or p1, distr_or p2 with
            | singl p1', _ => fmap (fun l => p1' +++ l) (distr_or p2)
            | _, singl p2' => fmap (fun l => l +++ p2') (distr_or p1)
            (*| singl p1', singl p2' => singl (p1' +++ p2')*)
            | p1', ncons _ _ =>
                join (fmap (fun c => ncons c p1') (distr_or p2))
                (*singl (join p1' +++ join (distr_or p2))*)
        end
end.

Ltac solve_bool := repeat (rewrite -?orb_assoc -?andb_assoc;
match goal with
    | |- context [?b1 || ?b2] => destruct b1; cbn; rewrite ?orb_true_l
    | |- context [?b1 && ?b2] => destruct b1; cbn; rewrite ?andb_false_l
end; auto).

Lemma cdenote_join_fmap :
  forall (truth : var -> bool) (p p' : cnf_prop),
    cdenote truth (join (fmap (fun c : clause => ncons c p) p')) =
    cdenote truth p && cdenote truth p'.
Proof.
  induction p; induction p'; cbn.
    by rewrite andb_comm.
    rewrite andb_comm IHp' //=. solve_bool.
    solve_bool.
    rewrite cdenote_app IHp' //=. solve_bool.
Qed.

Lemma distr_or_correct :
  forall (truth : var -> bool) (p : nnf_prop),
    cdenote truth (distr_or p) = ndenote truth p.
Proof.
  intros. induction p; cbn; trivial.
    by rewrite cdenote_app IHp1 IHp2.
    destruct (distr_or p1), (distr_or p2); cbn in *.
      by rewrite ccdenote_app IHp1 IHp2.
      by rewrite ccdenote_app cdenote_fmap_l -orb_andb_distrib_r IHp1 IHp2.
      by rewrite ccdenote_app cdenote_fmap_r orb_comm -orb_andb_distrib_r
        IHp1 IHp2 orb_comm.
      rewrite cdenote_app. rewrite andb_comm andb_assoc IHp1. 
Abort.

(*Function distr_or (p : nnf_prop) : cnf_prop :=
match p with
    | nnf_var v => singl (singl (pos v))
    | nnf_not v => singl (singl (neg v))
    | nnf_and p1 p2 => distr_or p1 +++ distr_or p2
    | nnf_or p1 p2 =>
        match distr_or p1, distr_or p2 with
            | singl p1', ncons _ _ => fmap (fun l => p1' +++ l) (distr_or p2)
            | ncons _ _, singl p2' => fmap (fun l => l +++ p2') (distr_or p1)
            | _, _ => distr_or p1 +++ distr_or p2
        end
end.
*)

Definition s := f_and (f_or (f_var 1) (f_var 2)) (f_var 3).
Definition s' := f_or (f_and (f_var 1) (f_var 2)) (f_var 3).

Definition cnf (f : formula) : cnf_prop :=
  distr_or (push_not (unarrow f)).

(*Definition dnf (f : formula) : nnf_prop :=
  distr_and (push_not (unarrow f)).
*)

Compute cnf s.
Compute cnf s'.
Compute dnf s.
Compute toDNF (dnf s).


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


Lemma cnf_correct :
  forall (truth : var -> bool) (f : formula),
    ndenote truth (cnf f) = fdenote truth f.
Proof.
  intros. unfold cnf.
  by rewrite distr_or_correct push_not_correct unarrow_correct.
Qed.

Definition empty : var -> bool := fun _ => false.

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
        match toCNF' p1, toCNF' p2 with
            | nnf_and p1_1 p1_2, p2' =>
                nnf_and (nnf_or p1_1 p2') (nnf_or p1_2 p2')
            | p1', nnf_and p2_1 p2_2 =>
                nnf_and (nnf_or p1' p2_1) (nnf_or p1' p2_2)
            | p1', p2' => concat (p1' ++ p2')
        end
end.

Fixpoint toDNF (p : nnf_prop) : dnf_prop :=
match p with
    | nnf_var v => [[pos v]]
    | nnf_not v => [[neg v]]
    | nnf_and p1 p2 => [concat (toDNF p1 ++ toDNF p2)]
    | nnf_or p1 p2 => toDNF p1 ++ toDNF p2
end.
