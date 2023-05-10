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

(* *********************************************************************************************** *)

Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Lemma transfer_set_recepient_balance0: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    (* let msg_sender_balance0 := (_balances (l.(Ledger_MainState))) [msg_sender] in *)
    let recepient_balance0 := (_balances (l.(Ledger_MainState))) [_to] in
    _to = msg_sender -> 
    (_balances (l'.(Ledger_MainState))) [_to] = recepient_balance0.        
Proof.        
    intros. subst l'.
    rewrite <- transfer_exec_prf.
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.

    compute.
    compute in msg_sender, recepient_balance0.

    assert (forall n (v1 v: XUBInteger n) (T11 T12: _ -> Type) T2 f w w1, 
    ((let 'Build_XUBInteger a as a'' := v
    return T11 a'' -> T2 in
    fun _: T11 a'' => (let 'Build_XUBInteger b as b'' := v1
    return T12 b''-> T2 in fun _ : T12 b'' => f b a) w) w1) = 
    f (uint2N v1) (uint2N v)) as HH.

    intros.

    destruct v, v1. auto.
    rewrite ?HH.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.

    subst msg_sender.
    rewrite <- H.
    rewrite <- H in Heqb.

    erewrite lookup_some_find.
    reflexivity.    
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    erewrite lookup_some_find.
    
    2: unshelve erewrite lookup_addAdjust.
    2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2: reflexivity. 

    match goal with 
    | |- context [@Common.hmapFindWithDefault ?B ?I ?L ?M ?P ?HM ?H0 ?H1 ?H4 ?H6 ?K ?V ?v ?k ?m ?H7] =>
        remember (@Common.hmapFindWithDefault B I L M P HM H0 H1 H4 H6 K V v k m H7)
    end.

    destruct _value, x16.
    simpl. simpl in Heqb.

    rewrite H0 in Heqb.
    symmetry in Heqb.    
    apply N.leb_le in Heqb.

    do 2 f_equal.
    lia.    
Qed.    

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


Lemma toValue_if_transit: forall X (b: bool) (x y: ControlResult X false), 
  toValue (if b then x else y) = if b then toValue x else toValue y.
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma toValue_if_transit2: forall X (b: bool) (x y: ControlResult X false), 
  toValue (xBoolIfElse b x y) = if b then toValue x else toValue y.
Proof.
  intros.
  destruct b; auto.
Qed.




Lemma transfer_success: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let r := eval_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let msg_sender_balance0 := (_balances (l.(Ledger_MainState))) [msg_sender] in
    r = if (xIntGeb msg_sender_balance0  _value : bool) then 
        ControlValue true true
        else ControlError ERROR_DEFAULT. 
Proof.

    intros. subst r.
    rewrite <- transfer_eval_prf.
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.

    Print transfer_eval.

    unfold transfer_eval.    
    repeat  (rewrite exec_if_transit || rewrite exec_if_transit2 ||
             rewrite eval_if_transit || rewrite eval_if_transit2 ||
             rewrite toValue_if_transit || rewrite  toValue_if_transit2).
        
    compute. 
    compute in msg_sender, msg_sender_balance0.

    assert (forall n (v1 v: XUBInteger n) (T11 T12: _ -> Type) T2 f w w1, 
    ((let 'Build_XUBInteger a as a'' := v
    return T11 a'' -> T2 in
    fun _: T11 a'' => (let 'Build_XUBInteger b as b'' := v1
    return T12 b''-> T2 in fun _ : T12 b'' => f b a) w) w1) = 
    f (uint2N v1) (uint2N v)) as HH.

    intros.

    destruct v, v1. auto.
    rewrite ?HH.

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.  

    case_eq b; intros; auto.
Qed.


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
    
    compute in msg_sender_balance0, msg_sender.
    compute. 
 
    assert (forall n (v1 v: XUBInteger n) (T11 T12: _ -> Type) T2 f w w1, 
    ((let 'Build_XUBInteger a as a'' := v
    return T11 a'' -> T2 in
    fun _: T11 a'' => (let 'Build_XUBInteger b as b'' := v1
    return T12 b''-> T2 in fun _ : T12 b'' => f b a) w) w1) = 
    f (uint2N v1) (uint2N v)).

    intros.

    destruct v, v1. auto.
    rewrite ?H0.

    
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