Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

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

(* Definition msg_pubkey_right (rec: Type) (def: XDefault rec) := msg_pubkey.

Check  msg_sender.

Definition msg_sender_right (rec: Type) (def: XDefault rec) := msg_sender.
Check  msg_sender_right.


Definition msg_value_right (rec: Type) (def: XDefault rec) := msg_value.
Definition tvm_pubkey_right (rec: Type) (def: XDefault rec) := tvm_pubkey.
Definition _now_right (rec: Type) (def: XDefault rec) := \\ now \\.
 *)

Definition transferFrom_exec_sig (_from :  address)
                             (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) :
                             {t | t = exec_state (Uinterpreter (@transferFrom rec def _ _ _ _  _from _to _value)) l}.
  unfold transferFrom. unfold dynamicAssignL.  
  repeat auto_build_P listInfinite.
Defined.

Definition transferFrom_exec_let (_from :  address)
                             (_to :  address) 
                             (_value :  uint256) (l : LedgerLRecord rec) : LedgerLRecord rec.
  let_term_of_2 @transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
Defined.

(* Print constructor_exec_let. *)

Lemma exec_if_transit: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  exec_state f (if b then x else y) = if b then exec_state f x else exec_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma exec_if_transit2: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  exec_state f (xBoolIfElse b x y) = if b then exec_state f x else exec_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma eval_if_transit: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  eval_state f (if b then x else y) = if b then eval_state f x else eval_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma eval_if_transit2: forall X (b: bool) (f: LedgerT X) (x y: LedgerLRecord rec), 
  eval_state f (xBoolIfElse b x y) = if b then eval_state f x else eval_state f y.
Proof.
  intros.
  destruct b; auto.
Qed.

Definition transferFrom_exec (_from :  address)
                         (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : LedgerLRecord rec.
  flat_term_of_2 @transferFrom_exec_let (transferFrom_exec_let _from _to _value l).
Defined.

(* Print transferFrom_exec. *)

(* Definition transferFrom_exec2 (_from :  address)
                         (_to :  address) 
                         (_value :  uint256)  (l : LedgerLRecord rec) : LedgerLRecord rec.
remember (transferFrom_exec _from _to _value l).
unfold transferFrom_exec in Heql0.
(* symmetry in Heql0. *)
repeat rewrite exec_if_transit, exec_if_transit2 in Heql0.
match goal with 
| Heql0: l0 = ?l |- _ => exact l
end.
Defined. *)


(* Print transferFrom_exec2. *)



Definition transferFrom_prf (_from :  address)
                         (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  transferFrom_exec _from _to _value l = 
  exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l.
  proof_of_2 transferFrom_exec transferFrom_exec_sig (transferFrom_exec_sig _from _to _value l).
Defined.


(* Print transferFrom_exec. *)