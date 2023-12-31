Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.
Require Import Common.

Require Import EIP20.
Import EIP20.

Require Import EvalExecs.Constructor.

Opaque Common.hmapFindWithDefault
       CommonInstances.addAdjustListPair
       N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Tactic Notation "constructor_start"  constr(l) constr(l0) constr(l')  :=
    (subst l'; subst l0; destruct_ledger l;  
     rewrite constructor_exec_computed;
     unfold constructor_ls_payload_exec_computed;
     simpl uncurry;
     unfold Datatypes.id;
     unfold constructor_ls_payload_exec_computed_curried;
    (* simpl proj1_sig; *)
     unfold LedgerLGetField;
     unfold ContractLGetField;
     simpl fold_apply;
     unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3;
     unfold LedgerFields_rect;
     unfold ContractFields_rect).

Tactic Notation "compute_rhs" := 
(match goal with 
    | |- _ = ?rhs =>    let RHS := fresh "rhs" in
                        let H := fresh "Heqrhs" in   
                        remember rhs as RHS eqn: H;
                        compute in H;
                        buint_all in H;
                        subst RHS
    end).


Lemma constructor_msg_sender_unchanged: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),                          
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    VMState_ι_msg_sender (l'.(Ledger_VMState)) = msg_sender.
Proof.
    intros. constructor_start l l0 l'.
    auto.
Qed.


Lemma constructor_set__initialAmount: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
                           (*  (vmstate: VMStateLRecord),  *)
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in                               
    _totalSupply (l'.(Ledger_MainState)) = _initialAmount.
Proof.
    intros. constructor_start l l0 l'.
    auto.
Qed.

Lemma constructor_set__tokenName: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    _name (l'.(Ledger_MainState)) = _tokenName.
Proof.
    intros. constructor_start l l0 l'.
    auto.
Qed.

Lemma constructor_set__decimalUnits: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    _decimals (l'.(Ledger_MainState)) = _decimalUnits.
Proof.
    intros. constructor_start l l0 l'.
    auto.
Qed.

Lemma constructor_set__tokenSymbol: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    _symbol (l'.(Ledger_MainState)) = _tokenSymbol.
Proof.
    intros. constructor_start l l0 l'.
    auto.
Qed.


Lemma constructor_set_sender_balance: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),                            
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    (_balances (l'.(Ledger_MainState))) [msg_sender] = _initialAmount.
Proof.
    intros. constructor_start l l0 l'.   

    rewrite lookup_some_find with (v:=_initialAmount).
    reflexivity.
    
    unshelve eapply lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
Qed.


Lemma constructor_not_sender_balance: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (a: address)
                            (l: LedgerLRecord rec),                            
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let a_balance0 := (_balances (l.(Ledger_MainState))) [a] in
    a <> msg_sender ->
    (_balances (l'.(Ledger_MainState))) [a] = a_balance0.
Proof.
    intros. constructor_start l l0 l'.    

    compute_rhs.
    compute in a_balance0, msg_sender. 

    remember (s [a] ?).
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
    tauto. 

    + rewrite lookup_none_find.
    * rewrite lookup_none_find.
      reflexivity.
      setoid_rewrite Heqy. 
      reflexivity.

    * unshelve erewrite lookup_addAdjust_another.
      refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
      setoid_rewrite <- Heqy. reflexivity. 
      tauto.
Qed.


Lemma constructor_allowed_unchanged: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let allowed0 := _allowed (l.(Ledger_MainState)) in
     _allowed (l'.(Ledger_MainState)) = allowed0.
Proof.
    intros. constructor_start l l0 l'.
    auto.
Qed.

Lemma constructor_balances: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let balances0 := _balances (l.(Ledger_MainState)) in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in    
    (* keysDistinct balances0 -> *)
     _balances (l'.(Ledger_MainState)) = balances0 [msg_sender] ← _initialAmount.
Proof.
    intros. constructor_start l l0 l'.        
    
    compute in balances0, msg_sender.
    auto. 
Qed.

Lemma constructor_balances_keysDistinct: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let balances0 := _balances (l.(Ledger_MainState)) in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances := _balances (l'.(Ledger_MainState)) in
    keysDistinct balances0 -> 
    keysDistinct balances.
Proof.    
    intros.
    subst balances.
    subst l'. subst l0.    
    rewrite constructor_balances.
    apply insert_kd.
    assumption.
Qed.


Lemma constructor_balances_sum: forall (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec),
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let balances0 := _balances (l.(Ledger_MainState)) in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances := _balances (l'.(Ledger_MainState)) in
    keysDistinct balances0 ->
     hmapBSum balances = 
        xIntMinus (xIntPlus _initialAmount (hmapBSum balances0)) (balances0 [msg_sender]).
Proof.
    intros.
    subst balances.
    subst l'. subst l0.
    unfold hmapBSum.
    rewrite constructor_balances.
    (* rewrite hmapSumAdjust. *)
    (* rewrite hmapSumEqual with (m2:=mapBN2N(balances0[msg_sender] ← _initialAmount)). *)
    rewrite mapBN2N_addAdjust.
    rewrite hmapSumAdjust.
    rewrite mapBN2N_hmapLookup.
    subst balances0.
    remember (hmapSum (mapBN2N (_balances (Ledger_MainState l)))).
    setoid_rewrite <- Heqn.
    subst msg_sender.
    remember ((_balances (Ledger_MainState l)) [VMState_ι_msg_sender (Ledger_VMState l)]).
    setoid_rewrite <- Heqx.
    destruct _initialAmount, x; simpl. auto.
    
    refine pair_xbool_equable.    
    refine BoolEq.pair_eqb_spec.

    apply mapBN2N_keysDistinct. assumption.
    refine pair_xbool_equable.    
    refine BoolEq.pair_eqb_spec.

    assumption. 
Qed.
