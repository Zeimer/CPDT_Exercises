From mathcomp Require Import ssreflect.

(* Ex. 1 *)

Theorem ex_1_1 : (True \/ False) /\ (False \/ True).
Proof.
  by split; [left | right].
Qed.

Theorem ex_1_2 : forall P : Prop, P -> ~ ~ P.
Proof.
  unfold not; intros. by apply H0.
Qed.

Theorem ex_1_3 :
  forall P Q R : Prop, P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intros. by decompose [and or] H; [left | right].
Qed.

(* Ex. 2 *)

Theorem ex_2 :
  forall (T : Set) (x : T) (P : T -> Prop) (Q : T -> T -> Prop) (f : T -> T),
    P x -> (forall x : T, P x -> exists y : T, Q x y) ->
    (forall x y : T, Q x y -> Q y (f y)) ->
      exists z : T, Q z (f z).
Proof.
  intros. destruct (H0 _ H). specialize (H1 _ _ H2).
  exists x0. assumption.
Qed.

(* Ex. 3 *)
Require Import Omega.

Inductive sot : nat -> Prop :=
    | C6 : forall n : nat, sot (6 * n)
    | C10 : forall n : nat, sot (10 * n).

Goal ~ sot 13.
Proof.
  inversion 1; omega.
Qed.

Goal forall n : nat, sot n -> forall k : nat, n <> S (2 * k).
Proof.
  induction 1; intro; omega.
Qed.

(* Ex. 4 *)
Definition var : Set := nat.

Inductive exp : Set :=
    | econst : nat -> exp
    | eadd : exp -> exp -> exp
    | epair : exp -> exp -> exp
    | efst : exp -> exp
    | esnd : exp -> exp
    | evar : var -> exp.

Inductive cmd : Set:=
    | cexp : exp -> cmd
    | asgn : var -> exp -> cmd -> cmd.

Inductive val : exp -> Prop :=
    | vconst : forall n : nat, val (econst n)
    | vpair : forall e1 e2 : exp,
        val e1 -> val e2 -> val (epair e1 e2).

Definition context : Set := var -> nat.


 Define a big-step evaluation relation eval, capturing what it means for an ex-
pression to evaluate to a value under a particular variable assignment. “Big step”
means that the evaluation of every expression should be proved with a single in-
stance of the inductive predicate you will define. For instance, “1 + 1 evaluates
to 2 under assignment va” should be derivable for any assignment va.
(g) Define a big-step evaluation relation run, capturing what it means for a command
to run to a value under a particular variable assignment. The value of a command
is the result of evaluating its final expression.
(h) Define a type of variable typings, which are like variable assignments, but map
variables to types instead of values. You might use polymorphism to share some
code with your variable assignments.
(i) Define typing judgments for expressions, values, and commands. The expression
and command cases will be in terms of a typing assignment.
(j) Define a predicate varsType to express when a variable assignment and a variable
typing agree on the types of variables.
3
(k) Prove that any expression that has type t under variable typing vt evaluates under
variable assignment va to some value that also has type t in vt, as long as va and
vt agree.
(l) Prove that any command that has type t under variable typing vt evaluates under
variable assignment va to some value that also has type t in vt, as long as va and
vt agree.
A few hints that may be helpful:
(a) One easy way of defining variable assignments and typings is to define both as
instances of a polymorphic map type. The map type at parameter T can be
defined to be the type of arbitrary functions from variables to T. A helpful function
for implementing insertion into such a functional map is eq nat dec, which you
can make available with Require Import Arith.. eq nat dec has a dependent type
that tells you that it makes accurate decisions on whether two natural numbers
are equal, but you can use it as if it returned a boolean, e.g., if eq nat dec n m
then E1 else E2.
(b) If you follow the last hint, you may find yourself writing a proof that involves an
expression with eq nat dec that you would like to simplify. Running destruct
on the particular call to eq nat dec should do the trick. You can automate this
advice with a piece of Ltac:
match goal with
| [ context[eq nat dec ?X ?Y ] ] ⇒ destruct (eq nat dec X Y )
end
(c) You probably do not want to use an inductive definition for compatibility of
variable assignments and typings.
(d) The CpdtTactics module from this book contains a variant crush’ of crush. crush’
takes two arguments. The first argument is a list of lemmas and other functions
to be tried automatically in “forward reasoning” style, where we add new facts
without being sure yet that they link into a proof of the conclusion. The second
argument is a list of predicates on which inversion should be attempted auto-
matically. For instance, running crush’ (lemma1, lemma2 ) pred will search for
chances to apply lemma1 and lemma2 to hypotheses that are already available,
adding the new concluded fact if suitable hypotheses can be found. Inversion will
be attempted on any hypothesis using pred, but only those inversions that narrow
the field of possibilities to one possible rule will be kept. The format of the list
arguments to crush’ is that you can pass an empty list as tt, a singleton list as the
unadorned single element, and a multiple-element list as a tuple of the elements.
(e) If you want crush’ to apply polymorphic lemmas, you may have to do a little
extra work, if the type parameter is not a free variable of your proof context (so
that crush’ does not know to try it). For instance, if you define a polymorphic
map insert function assign of some type ∀ T : Set, ..., and you want particular
4
applications of assign added automatically with type parameter U, you would need
to include assign in the lemma list as assign U (if you have implicit arguments
off) or assign (T := U ) or @assign U (if you have implicit arguments on).
