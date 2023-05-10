Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

#[local]
Existing Instance BoolEq.pair_eqb_spec.

#[global, program]
Instance listInfinite : listInfiniteFunRec_gen XList.
Next Obligation.
(* TODO: we need to analyze all while/for cycles
   and find upper bound for number of iterations *)
exact (repeat PhantomPoint 0).
Defined.

Notation rec := LocalStateLRecord.

Definition computed : LocalStateLRecord := Eval vm_compute in default. 
#[global]
Instance def : XDefault LocalStateLRecord := {
  default := computed 
} . 

Definition VMStateDefault : VMStateLRecord  := Eval vm_compute in default.
Definition LedgerDefault : LedgerLRecord LocalStateLRecord  := Eval vm_compute in default. 

Elpi Accumulate rec_def lp:{{
  get_rec {{ rec }}.
  get_def {{ def }}.
}}.

(* *********************************************************************************************** *)

Lemma exec_if_lift: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  exec_state f (if b then x else y) = if b then exec_state f x else exec_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma exec_if_lift2: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  exec_state f (xBoolIfElse b x y) = if b then exec_state f x else exec_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma eval_if_lift: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  eval_state f (if b then x else y) = if b then eval_state f x else eval_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma eval_if_lift2: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  eval_state f (xBoolIfElse b x y) = if b then eval_state f x else eval_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma toValue_if_lift: forall X (b: bool) (x y: ControlResult X false), 
  toValue (if b then x else y) = if b then toValue x else toValue y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma toValue_if_lift2: forall X (b: bool) (x y: ControlResult X false), 
  toValue (xBoolIfElse b x y) = if b then toValue x else toValue y.
Proof.
  intros.
  destruct b; auto.
Qed.


Tactic Notation "lift_all" := (repeat  (rewrite exec_if_lift || rewrite exec_if_lift2 ||
             rewrite eval_if_lift || rewrite eval_if_lift2 ||
             rewrite toValue_if_lift || rewrite  toValue_if_lift2)).

Lemma buint2 : forall n (v1 v: XUBInteger n) (T11 T12: _ -> Type) T2 f w w1, 
    ((let 'Build_XUBInteger a as a'' := v
    return T11 a'' -> T2 in
    fun _: T11 a'' => (let 'Build_XUBInteger b as b'' := v1
    return T12 b''-> T2 in fun _ : T12 b'' => f b a) w) w1) = 
    f (uint2N v1) (uint2N v).
Proof.    
  intros.
  destruct v, v1. auto.
Qed.  

Lemma buint1 : forall n (v: XUBInteger n) (T11: _ -> Type) T2 f w, 
(let 'Build_XUBInteger a as a'' := v
return T11 a'' -> T2 in
fun _: T11 a'' => f a) w = 
f (uint2N v).
Proof.
intros.

destruct v. auto.
Qed.

Lemma buint0 : forall X n (v: XUBInteger n) (f : _ -> X), 
match v with 
 | Build_XUBInteger x => f x
 end = f (uint2N v) .
Proof.
intros.

destruct v. auto.
Qed.

Tactic Notation "buint_all" := (repeat  (rewrite buint2 || rewrite buint1 ||
             rewrite buint0)).
