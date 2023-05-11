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

Definition transferFrom_exec_computed: forall
                            (_from :  address)
                            (_to :  address)
                            (_value : uint256)
                            (l: LedgerLRecord rec), {t: LedgerLRecord rec | t = transferFrom_exec _from _to _value {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (transferFrom_exec _from _to _value {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold transferFrom_exec in Heql0.
    lift_all in Heql0.    
    compute in Heql0.
    buint_all in Heql0.
    symmetry in Heql0.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.

Definition transferFrom_computed_prf (_from :  address)
                         (_to :  address) 
                         (_value :  uint256) (l : LedgerLRecord rec) :
  proj1_sig (transferFrom_exec_computed _from _to _value l) = 
  exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) {$$ l with Ledger_LocalState := default $$}.
Proof. 
  rewrite <- transferFrom_prf.
  destruct ((transferFrom_exec_computed _from _to _value l)).
  auto.
Defined.

Tactic Notation "transferFrom_start"  constr(l) constr(l0) constr(l')  :=
    (subst l'; subst l0;
     rewrite <- transferFrom_computed_prf;
    
    destruct l as [c p]; destruct p as [c0 p];
    destruct p as [m p]; destruct p as [m0 p];
    destruct p as [v p]; destruct p as [l l0];

    destruct v as [v0 p]; destruct p as [v1 p]; 
    destruct p as [v2 p]; destruct p as [v3 p]; 
    destruct p as [v4 p]; destruct p as [v5 p]; 
    destruct p as [v6 p]; destruct p as [v7 p]; 
    destruct p as [v8 p]; destruct p as [v9 p]; 
    destruct p as [v10 p]; destruct p as [v11 p]; 
    destruct p as [v12 p]; destruct p as [v13 p]; 
    destruct p as [v14 p]; destruct p as [v15 v16]; 
    
    destruct c as [s0 p]; destruct p as [s1 p];
    destruct p as [s2 p]; destruct p as [s3 p];
    destruct p as [s4 s5];  

    unfold transferFrom_exec_computed;
    simpl proj1_sig;
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
    (_balances (l'.(Ledger_MainState))) [_from] = 
        if ((xIntGeb _from_balance0  _value : bool)  && (xIntGeb allowance  _value : bool) ) then 
                xIntMinus _from_balance0 _value
        else _from_balance0.
Proof. 
    intros. transferFrom_start l l0 l'.    
    compute_rhs.   

    compute in _from_balance0, msg_sender.  

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

    remember (s0 [_from] ?).
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

    remember (s0 [_from] ?).
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
    intros. transferFrom_start l l0 l'.    
    compute_rhs.
    compute in _from_balance0, _to_balance0, allowance0, msg_sender.  

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
    intros. transferFrom_start l l0 l'.    
    compute_rhs.
    compute in _from_balance0, allowed0, msg_sender.  

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

    erewrite lookup_some_find with (k:=v4).
    reflexivity.

    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    reflexivity.
Qed.


Lemma transferFrom_msg_sender_unchanged: forall (_from :  address) (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender0 := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    VMState_ι_msg_sender (l'.(Ledger_VMState)) = msg_sender0.
Proof.        
    intros. transferFrom_start l l0 l'.
    compute_rhs.    
    compute in msg_sender0.

    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b; auto
    end.
Qed.


Lemma transferFrom_allowed_others_unchanged: forall (_from :  address) (_to :  address) 
                            (_value : uint256)
                            (x y: address)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let allowed0 := _allowed (l.(Ledger_MainState)) in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    ((x <> _from) \/ (y <> msg_sender)) ->
    (_allowed (l'.(Ledger_MainState)))[x][y] = allowed0[x][y].
Proof.        
    intros. transferFrom_start l l0 l'.
    compute_rhs.    
    compute in allowed0, msg_sender.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    

    case_eq b; intros; auto.

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.

    case_eq b0; intros; auto.

    destruct H.
    -

    symmetry.
  
    match goal with 
    | |- context [@Common.hmapFindWithDefault ?B ?I ?L ?M ?P ?HM ?H0 ?H1 ?H4 ?H6 ?K ?V ?v x ?m ?H7] =>
        remember m [x]?
    end.

    destruct y0.
    symmetry.
    +     
    erewrite lookup_some_find with (k:=x).
    2: unshelve erewrite lookup_addAdjust_another.
    2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2: setoid_rewrite <- Heqy0.
    2: reflexivity.
    2: assumption.
    erewrite lookup_some_find with (k:=x).
    2: setoid_rewrite <- Heqy0.
    2: reflexivity.
    reflexivity.
    + 
    erewrite lookup_none_find with (k:=x).
    2: auto.
    erewrite lookup_none_find with (k:=x).
    reflexivity.
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    auto.
    assumption.
    -
    symmetry.
  
    match goal with 
    | |- context [@Common.hmapFindWithDefault ?B ?I ?L ?M ?P ?HM ?H0 ?H1 ?H4 ?H6 ?K ?V ?v x ?m ?H7] =>
        remember m [x]?
    end.

    destruct y0.
    symmetry.
    +
    assert (x = _from \/ x <> _from) by repeat decide equality.
    destruct H2.
    *
    erewrite lookup_some_find with (k:=x).
    all: cycle 1.        
    rewrite H2. unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    reflexivity.
    
    symmetry.
    match goal with 
    | |- context [@Common.hmapFindWithDefault ?B ?I ?L ?M ?P ?HM ?H0 ?H1 ?H4 ?H6 ?K ?V ?v y ?m ?H7] =>
        remember m [y]?
    end.
    destruct y0.

    ** erewrite lookup_some_find with (k:=y).
       2: setoid_rewrite <- Heqy1.
       2: reflexivity.
       erewrite lookup_some_find with (k:=y).
       reflexivity.
       unshelve erewrite lookup_addAdjust_another.
       refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
       auto.
       assumption.
    ** erewrite lookup_none_find with (k:=y).
       2: auto.
       erewrite lookup_none_find with (k:=y).
       auto.
       unshelve erewrite lookup_addAdjust_another.
       refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
       auto.
       assumption.
    * erewrite lookup_some_find with (k:=x).
      all: cycle 1.        
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    setoid_rewrite <- Heqy0.
    reflexivity.
    assumption.
    erewrite lookup_some_find with (k:=x).
    reflexivity. auto.
    +  symmetry. 
    assert (x = _from \/ x <> _from) by repeat decide equality.
    destruct H2.
    * rewrite H2.
    erewrite lookup_some_find with (k:=_from).
    all: cycle 1.
    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    reflexivity.
    symmetry.
    match goal with 
    | |- context [@Common.hmapFindWithDefault ?B ?I ?L ?M ?P ?HM ?H0 ?H1 ?H4 ?H6 ?K ?V ?v y ?m ?H7] =>
        remember m [y]?
    end.
    symmetry.
    destruct y0.
    **
    erewrite lookup_some_find with (k:=y).
    all: cycle 1.
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    setoid_rewrite <- Heqy1.
    reflexivity.
    tauto.
    erewrite lookup_some_find with (k:=y).
    reflexivity.
    auto.
    **
     erewrite lookup_none_find with (k:=y).
     erewrite lookup_none_find with (k:=y).
     auto.
     auto.
     unshelve erewrite lookup_addAdjust_another.
     refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
     auto.
     assumption.
   *  erewrite lookup_none_find with (k:=x).
      erewrite lookup_none_find with (k:=x).
      auto.
      auto.
      unshelve erewrite lookup_addAdjust_another.
      refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
      auto.
      assumption.
Qed. 