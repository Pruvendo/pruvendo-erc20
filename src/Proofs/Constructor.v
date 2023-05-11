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

Definition constructor_exec_computed: forall
                             (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string)
                            (l: LedgerLRecord rec), {t: LedgerLRecord rec | t = constructor_exec _initialAmount _tokenName _decimalUnits _tokenSymbol {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (constructor_exec _initialAmount _tokenName _decimalUnits _tokenSymbol {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec in Heql0.
    lift_all in Heql0.    
    compute in Heql0.
    buint_all in Heql0.
    symmetry in Heql0.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.

Definition constructor_computed_prf  (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string) (l : LedgerLRecord rec) :
  proj1_sig (constructor_exec_computed _initialAmount _tokenName _decimalUnits _tokenSymbol l) = 
  exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) 
  {$$ l with Ledger_LocalState := default $$}.
Proof. 
  rewrite <- constructor_prf.
  destruct ((constructor_exec_computed _initialAmount _tokenName _decimalUnits _tokenSymbol l)).
  auto.
Defined.


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
    intros. subst l'. subst l0.
    rewrite <- constructor_computed_prf.
    
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.
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
    intros. subst l'. subst l0.
    rewrite <- constructor_computed_prf.
    
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.
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
    intros. subst l'. subst l0.
    rewrite <- constructor_computed_prf.
    
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.
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
    intros. subst l'. subst l0.
    rewrite <- constructor_computed_prf.
    
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.
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
    intros. subst l'. subst l0.
    rewrite <- constructor_computed_prf.
    
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.
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
    intros. subst l'. subst l0.
    rewrite <- constructor_computed_prf.
    
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec_computed.
    simpl proj1_sig.
    unfold LedgerLGetField.
    unfold ContractLGetField.
    simpl fold_apply.
    unfold ClassGeneratorsCommon.CountableMoreAll_obligation_3.
    unfold LedgerFields_rect.
    unfold ContractFields_rect.

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
    intros. subst l'. subst l0.
    rewrite <- constructor_computed_prf.
    
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold constructor_exec_computed.
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

    compute in a_balance0, msg_sender. 

    remember (x10 [a] ?).
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