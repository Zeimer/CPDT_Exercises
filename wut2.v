Require Import List.
Import ListNotations.
Require Import QArith.

From Equations Require Import Equations.

Local Open Scope Q_scope.

Check 1 # 4.

Check 1 == 2 # 5.

Check -1 # 1.

Inductive Exp : Type :=
    | Var : nat -> Exp
    | Const : Q -> Exp
    | Add : Exp -> Exp -> Exp
(*    | Sub : Exp -> Exp -> Exp*)
    | Mul : Exp -> Exp -> Exp.
(*    | Div : Exp -> Exp -> Exp.*)

Definition Env : Type := list Q.

Equations lookup (n : nat) (l : Env) : option Q :=
lookup _ [] := None;
lookup 0 (q :: _) := Some q;
lookup (S n') (_ :: qs) := lookup n' qs.

Equations expDenote (e : Exp) (l : Env) : option Q :=
expDenote (Var n) l := lookup n l;
expDenote (Const q) l := Some q;
expDenote (Add e1 e2) l with (expDenote e1 l, expDenote e2 l) => {
  expDenote (Add e1 e2) l (Some q1, Some q2) := Some (q1 + q2);
  expDenote _ _ _ := None
};
expDenote (Mul e1 e2) l with (expDenote e1 l, expDenote e2 l) => {
  expDenote (Mul e1 e2) l (Some q1, Some q2) := Some (q1 * q2);
  expDenote _ _ _ := None
}.

Equations eqsDenote (eqs : list (Exp * Q)) (env : Env) : Prop :=
eqsDenote [] env := True;
eqsDenote ((e, q) :: eqs') env with (expDenote e env) => {
  eqsDenote ((e, q) :: eqs') env (Some q') := q' == q /\ eqsDenote eqs' env;
  eqsDenote _ _ _ := False
}.

Definition lhs := list Q.

(*
Definition lhsDenote (l : lhs) (env : Env) : Q := 0.
*)

Equations sum_lhs (l1 l2 : lhs) : lhs :=
sum_lhs [] _ := [];
sum_lhs _ [] := [];
sum_lhs (q1 :: l1') (q2 :: l2') := q1 + q2 :: sum_lhs l1' l2'.

Equations lhsDenote (l : lhs) (env : Env) : option Q :=
lhsDenote [] _ := Some 0;
lhsDenote (q :: qs) [] := None;
lhsDenote (q :: qs) (q' :: env') with (lhsDenote qs env') => {
  lhsDenote (q :: qs) (q' :: env') (Some q'') := Some (q * q' + q'');
  lhsDenote _ _ _ := None
}.

Definition linearize (k : Q) (e : Exp) : option lhs := None.

(*
Definition linearizeEqs
  (eqs : list (Exp * Q)) : option (lhs * Q) := None.
*)

Equations linearizeEqs (eqs : list (Exp * Q)) : option (lhs * Q) :=
linearizeEqs [] := None;
linearizeEqs ((e, q) :: eqs') with (linearize 1 e, linearizeEqs eqs') => {
  linearizeEqs ((e, q):: eqs') (Some l1, Some (l2, q')) :=
    Some (sum_lhs l1 l2, q + q');
  linearizeEqs _ _ := None
}.

Lemma linearize_spec :
  forall (k : Q) (e : Exp) (l : lhs) (env : Env),
    linearize k e = Some l ->
      lhsDenote l env = expDenote (Mul (Const k) e) env.
Abort.

Lemma linearizeEqs_spec :
  forall (eqs : list (Exp * Q)) (l : lhs) (q : Q) (env : Env),
    linearizeEqs eqs = Some (l, q) ->
      eqsDenote eqs env <-> lhsDenote l env = Some q.
Abort.































































