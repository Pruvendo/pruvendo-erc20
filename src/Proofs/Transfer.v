Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

Require Import EvalExecs.Transfer.

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

(* Definition msg_pubkey_right (rec: Type) (def: XDefault rec) := msg_pubkey.

Check  msg_sender.

Definition msg_sender_right (rec: Type) (def: XDefault rec) := msg_sender.
Check  msg_sender_right.


Definition msg_value_right (rec: Type) (def: XDefault rec) := msg_value.
Definition tvm_pubkey_right (rec: Type) (def: XDefault rec) := tvm_pubkey.
Definition _now_right (rec: Type) (def: XDefault rec) := \\ now \\.
 *)

Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Lemma transfer_set_sender_balance: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let msg_sender_balance0 := (_balances (l.(Ledger_MainState))) [msg_sender] in
    msg_sender <> _to -> 
    (_balances (l'.(Ledger_MainState))) [msg_sender] = 
        if (xIntGeb msg_sender_balance0  _value : bool) then 
        xIntMinus msg_sender_balance0 _value
        else msg_sender_balance0.
Proof.        
    intros. subst l'.
    rewrite <- transfer_prf.
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    compute.    

    match goal with
    | |- context [@addAdjustListPair _ _ _ a ?v _] => remember v
    end.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.

    erewrite lookup_some_find.
    reflexivity.
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    auto.
    assumption.

Qed.

Lemma transfer_set_recepient_balance: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let msg_sender_balance0 := (_balances (l.(Ledger_MainState))) [msg_sender] in
    let recepient_balance0 := (_balances (l.(Ledger_MainState))) [_to] in
    _to <> msg_sender -> 
    (_balances (l'.(Ledger_MainState))) [_to] = 
        if (xIntGeb msg_sender_balance0  _value : bool) then 
        xIntPlus recepient_balance0 _value
        else recepient_balance0.
Proof.        
    intros. subst l'.
    rewrite <- transfer_prf.
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.

    compute.

    match goal with
    | |- context [@addAdjustListPair ?K ?V ?H a ?v ?m] => remember (@addAdjustListPair K V H a v m)
    end.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.

    erewrite lookup_some_find.
    reflexivity.    

    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    subst l3.

    remember (x10 [_to] ?).
    destruct y.

    - 
    erewrite lookup_some_find.
    reflexivity. 
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    erewrite lookup_some_find.
    setoid_rewrite <- Heqy.    
    reflexivity. 
    setoid_rewrite <- Heqy.
    reflexivity.
    assumption. 

    -
    rewrite lookup_none_find.
    rewrite lookup_none_find.
    reflexivity.
    setoid_rewrite Heqy. reflexivity.

    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    setoid_rewrite <- Heqy. reflexivity. 
    assumption.
Qed.