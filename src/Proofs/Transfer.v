Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

Require Import Common.
Require Import EvalExecs.Transfer.


Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Definition transfer_exec_computed: forall
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), {t: LedgerLRecord rec | t = transfer_exec _to _value {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (transfer_exec _to _value {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transfer_exec in Heql0.
    lift_all in Heql0.    
    compute in Heql0.
    buint_all in Heql0.
    symmetry in Heql0.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.

Definition transfer_computed_prf  (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  proj1_sig (transfer_exec_computed _to _value l) = 
  exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) {$$ l with Ledger_LocalState := default $$}.
Proof. 
  rewrite <- transfer_exec_prf.
  destruct ((transfer_exec_computed _to _value l)).
  auto.
Defined.


Lemma transfer_set_recepient_balance0: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let recepient_balance0 := (_balances (l.(Ledger_MainState))) [_to] in
    _to = msg_sender -> 
    (_balances (l'.(Ledger_MainState))) [_to] = recepient_balance0.        
Proof.        
    intros. subst l'. subst l0.   

    rewrite <- transfer_computed_prf.

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transfer_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.

    match goal with 
    | |- _ = ?rhs => let RHS := fresh "rhs" in
                       let H := fresh "Heqrhs" in   
                       remember rhs as RHS eqn: H;
                       compute in H;
                       buint_all in H;
                       subst RHS
    end.
    
    compute in msg_sender, recepient_balance0.

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
    intros. subst l'. subst l0.   

    rewrite <- transfer_computed_prf.

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transfer_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.

    match goal with 
    | |- _ = ?rhs => let RHS := fresh "rhs" in
                       let H := fresh "Heqrhs" in   
                       remember rhs as RHS eqn: H;
                       compute in H;
                       buint_all in H;
                       subst RHS
    end.


    compute in msg_sender_balance0, msg_sender.
    
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
    intros. subst l'. subst l0.   

    rewrite <- transfer_computed_prf.

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transfer_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.

    match goal with 
    | |- _ = ?rhs => let RHS := fresh "rhs" in
                       let H := fresh "Heqrhs" in   
                       remember rhs as RHS eqn: H;
                       compute in H;
                       buint_all in H;
                       subst RHS
    end.
    
    compute in msg_sender_balance0, msg_sender, recepient_balance0.

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

    subst l2.

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

(* ********************************************************************************************* *)

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
    unfold transfer_eval.    
 
    lift_all.
    compute. 
    compute in msg_sender, msg_sender_balance0.

    buint_all.
    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.  

    case_eq b; intros; auto.
Qed.