Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

Require Import Common.
Require Import EvalExecs.TransferFrom.


Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb N.pow.


Lemma transferFrom_set_from_balance: forall
                            (_from :  address)
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let _from_balance0 := (_balances (l.(Ledger_MainState))) [_from] in
     let allowance := (_allowed(l.(Ledger_MainState)))[_from][msg_sender] in
    _from <> _to -> 
(*     (xIntGeb allowance  _value : bool) = true ->
 *)    (_balances (l'.(Ledger_MainState))) [_from] = 
        if ((xIntGeb _from_balance0  _value : bool)  && (xIntGeb allowance  _value : bool) ) then 
                xIntMinus _from_balance0 _value
        else _from_balance0.
Proof.        
    intros. subst l'.
    rewrite <- transferFrom_prf.

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transferFrom_exec.    
    lift_all.

    compute.
    compute in _from_balance0, allowance0, msg_sender.  

  buint_all.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    

    case_eq b; intros; auto.


    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.

    case_eq b0; intros.

    -    
    erewrite lookup_some_find.
    reflexivity.
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    remember (x10 [_from] ?).
    destruct y.
    + erewrite lookup_some_find.
    reflexivity. 
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    erewrite lookup_some_find.
    setoid_rewrite <- Heqy.    
    reflexivity. 
    setoid_rewrite <- Heqy.
    reflexivity.
    assumption. 

    + rewrite lookup_none_find.
    * rewrite lookup_none_find.
      reflexivity.
      setoid_rewrite Heqy. 
      reflexivity.

    * unshelve erewrite lookup_addAdjust_another.
      refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
      setoid_rewrite <- Heqy. reflexivity. 
      assumption.

    -  erewrite lookup_some_find.
    reflexivity.
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    remember (x10 [_from] ?).
    destruct y.
    + erewrite lookup_some_find.
    reflexivity. 
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    erewrite lookup_some_find.
    setoid_rewrite <- Heqy.    
    reflexivity. 
    setoid_rewrite <- Heqy.
    reflexivity.
    assumption. 

    + rewrite lookup_none_find.
    * rewrite lookup_none_find.
      reflexivity.
      setoid_rewrite Heqy. 
      reflexivity.

    * unshelve erewrite lookup_addAdjust_another.
      refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
      setoid_rewrite <- Heqy. reflexivity. 
      assumption.
Qed.


Lemma transferFrom_set_to_balance: forall
                            (_from :  address)
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let _from_balance0 := (_balances (l.(Ledger_MainState))) [_from] in
    let _to_balance0 := (_balances (l.(Ledger_MainState))) [_to] in
    let allowance := (_allowed(l.(Ledger_MainState)))[_from][msg_sender] in
    _to <> _from -> 
    (_balances (l'.(Ledger_MainState))) [_to] = 
        if ((xIntGeb _from_balance0  _value : bool)  && (xIntGeb allowance  _value : bool) ) then 
                xIntPlus _to_balance0 _value
        else _to_balance0.
Proof.        
    intros. subst l'.
    rewrite <- transferFrom_prf.

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transferFrom_exec.    

    lift_all.
    compute.
    compute in _from_balance0, _to_balance0, allowance0, msg_sender.  

    buint_all.
    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    

    case_eq b; intros; auto.


    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.

    case_eq b0; intros.

    -          
    erewrite lookup_some_find.
    reflexivity.
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    auto.
    assumption.

    -

    erewrite lookup_some_find.
    reflexivity.
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    auto.
    assumption.
Qed.


Lemma transferFrom_set_allowed: forall
                            (_from :  address)
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let _from_balance0 := (_balances (l.(Ledger_MainState))) [_from] in    
    let allowed0 := (_allowed(l.(Ledger_MainState)))[_from][msg_sender] in  
    let MAX_UINT256 := toValue (eval_state (sRReader (MAX_UINT256_right rec def)) l0) in
      (_allowed (l'.(Ledger_MainState))) [_from][msg_sender] = 
        if ((xIntGeb _from_balance0  _value : bool)  && (xIntGeb allowed0  _value : bool) ) then 
                if (xIntGtb MAX_UINT256 allowed0: bool) then xIntMinus allowed0 _value else allowed0
        else allowed0.
Proof.        
    intros. subst l'.
    rewrite <- transferFrom_prf.

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transferFrom_exec.    
(*     repeat rewrite exec_if_transit, exec_if_transit2.
 *)
    lift_all.
    compute.
    compute in _from_balance0, allowed0, msg_sender.  


  buint_all.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    

    case_eq b; intros; auto.

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.

    case_eq b0; intros; auto.

    erewrite lookup_some_find with (k:=_from).
    2: unshelve erewrite lookup_addAdjust.
    2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2: reflexivity.

    erewrite lookup_some_find with (k:=a).
    reflexivity.

    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    reflexivity.
Qed.
