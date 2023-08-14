Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.
Require Import UMLang.ExecGenerator.

Require Import EIP20.
Require Import Common.
Import EIP20.

Require Import EvalExecs.TransferFrom.

Opaque Common.hmapFindWithDefault
       CommonInstances.addAdjustListPair
       N.add N.sub N.leb N.ltb N.eqb Z.eqb N.pow.

Tactic Notation "transferFrom_start"  constr(l) constr(l0) constr(l')  :=
    (subst l'; subst l0; destruct_ledger l;  
     rewrite transferFrom_exec_computed;
     unfold transferFrom_ls_payload_exec_computed;
     simpl uncurry;
     unfold Datatypes.id;
     unfold transferFrom_ls_payload_exec_computed_curried;
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
    intros. 
    transferFrom_start l l0 l'.

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

    remember (s [_from] ?).
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

    remember (s [_from] ?).
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

    erewrite lookup_some_find with (k:=v5).
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

Lemma transferFrom_others_balances: forall (_from :  address) (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in
    let allowed0 := (_allowed (l.(Ledger_MainState))) in
    _from <> _to  -> 
    _balances (l'.(Ledger_MainState)) = 
    if ((xIntGeb balances0 [_from]  _value : bool) && 
        (xIntGeb allowed0 [_from] [msg_sender] _value : bool) ) then 
        (balances0 [_to] ← (xIntPlus (balances0 [_to]) _value)) 
          [_from] ← (xIntMinus (balances0 [_from]) _value) else balances0.
Proof. 
    intros. transferFrom_start l l0 l'.
    compute_rhs.    
    compute in balances0, allowed0, msg_sender.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.    
    
    destruct b0.
    - remember (s[_from]?).
      destruct y.
      + erewrite lookup_some_find.
        2: erewrite lookup_addAdjust_another; auto.
        2: setoid_rewrite <- Heqy.
        2: reflexivity.
        erewrite lookup_some_find with (k:=_from).
        2: setoid_rewrite <- Heqy.
        2: reflexivity.
        auto.
      + erewrite lookup_none_find with (k:=_from).
        2: erewrite lookup_addAdjust_another; auto.
        erewrite lookup_none_find with (k:=_from).
        auto. auto.
    - remember (s[_from]?).
      destruct y.
      + erewrite lookup_some_find.
        2: erewrite lookup_addAdjust_another; auto.
        2: setoid_rewrite <- Heqy.
        2: reflexivity.
        erewrite lookup_some_find with (k:=_from).
        2: setoid_rewrite <- Heqy.
        2: reflexivity.
        auto.
      + erewrite lookup_none_find with (k:=_from).
        2: erewrite lookup_addAdjust_another; auto.
        erewrite lookup_none_find with (k:=_from).
        auto. auto.   
    Unshelve.
    all: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).     
Qed.


Lemma transferFrom_from_member_balances: forall (_from :  address) (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in     
    _from = _to -> 
    keysDistinct balances0 ->
    hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) _from balances0  = true ->
    _balances (l'.(Ledger_MainState)) = balances0.
Proof.
    intros. transferFrom_start l l0 l'.
    compute_rhs.    
    compute in balances0, msg_sender.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.    
    
    rewrite H.
    destruct b0.

    - remember (s[_to]?).
      destruct y.
      + erewrite lookup_some_find.
        2: erewrite lookup_addAdjust; auto.        
        erewrite lookup_some_find with (k:=_to).
        2: setoid_rewrite <- Heqy.
        2: reflexivity.
        erewrite insert_insert.
        unfold xHMapInsert. simpl.
        match goal with
        | |- context [@addAdjustListPair _ _ _ ?a ?v _] => remember v
        end.
        enough (x0 = x).
        destruct s.
        erewrite member_addAdjust; auto.
        rewrite H3. auto.
        subst x0.
        destruct x, _value. simpl.
        f_equal. lia.
      + subst _from.
        apply member_true_lookup in H1.
        destruct H1.
        setoid_rewrite H in Heqy.
        discriminate.
    - remember (s[_to]?).
      destruct y.
      + erewrite lookup_some_find.
        2: erewrite lookup_addAdjust; auto.        
        erewrite lookup_some_find with (k:=_to).
        2: setoid_rewrite <- Heqy.
        2: reflexivity.
        erewrite insert_insert.
        unfold xHMapInsert. simpl.
        match goal with
        | |- context [@addAdjustListPair _ _ _ ?a ?v _] => remember v
        end.
        enough (x0 = x).
        destruct s.
        erewrite member_addAdjust; auto.
        rewrite H3. auto.
        subst x0.
        destruct x, _value. simpl.
        f_equal. lia.
      + subst _from.
        apply member_true_lookup in H1.
        destruct H1.
        setoid_rewrite H in Heqy.
        discriminate.
    Unshelve.
    all: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
Qed.    


Lemma transferFrom_from_not_member_balances: forall (_from :  address) (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in    
    let allowed0 := (_allowed (l.(Ledger_MainState))) in 
    _from = _to -> 
    keysDistinct balances0 ->
    hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) _from balances0  = false ->
    _balances (l'.(Ledger_MainState)) =
    if ((xIntGeb balances0 [_from]  _value : bool) && 
        (xIntGeb allowed0 [_from] [msg_sender] _value : bool) ) then 
         balances0 [_from] ← default
    else balances0.
Proof.
    intros. transferFrom_start l l0 l'.
    compute_rhs.    
    compute in balances0, msg_sender, allowed0.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.
    subst msg_sender.
    subst _from.

    apply member_false_lookup in H1.    

    match goal with
    | |- context [if ?b then _ else _] => remember b
    end.    
    
    destruct b0.
    -
    erewrite lookup_some_find with (k:=_to).
    erewrite lookup_none_find with (k:=_to).    
    3: erewrite lookup_none_find with (k:=_to).    
    3: unshelve erewrite lookup_addAdjust.    
    3: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2, 3, 4: auto.
    enough (_value = default).
    subst _value.
    simpl.
    erewrite insert_insert.        
    simpl.
    match goal with
    | |- context [@addAdjustListPair _ _ _ ?a ?v _] => remember v
    end.
    enough (x = default).
    rewrite H. auto.
    subst x.
    simpl default.
    f_equal.
    remember ((uint2N _value <=?
          uint2N (Common.hmapFindWithDefault (Build_XUBInteger 0) _to s))%N).
    setoid_rewrite <- Heqb1 in Heqb.
    destruct b0.
    + erewrite lookup_none_find with (k:=_to) in Heqb1.
      destruct _value.
      simpl in Heqb1 |- *.
      symmetry in Heqb1.
      apply N.leb_le in Heqb1.
      unfold N.zero.
      f_equal. lia.
      auto.
    + congruence.
    -    
    erewrite lookup_some_find with (k:=_to).
    erewrite lookup_none_find with (k:=_to).    
    3: erewrite lookup_none_find with (k:=_to).    
    3: unshelve erewrite lookup_addAdjust.    
    3: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2, 3, 4: auto.
    enough (_value = default).
    subst _value.
    simpl.
    erewrite insert_insert.        
    simpl.
    match goal with
    | |- context [@addAdjustListPair _ _ _ ?a ?v _] => remember v
    end.
    enough (x = default).
    rewrite H. auto.
    subst x.
    simpl default.
    f_equal.
    remember ((uint2N _value <=?
          uint2N (Common.hmapFindWithDefault (Build_XUBInteger 0) _to s))%N).
    setoid_rewrite <- Heqb1 in Heqb.
    destruct b0.
    + erewrite lookup_none_find with (k:=_to) in Heqb1.
      destruct _value.
      simpl in Heqb1 |- *.
      symmetry in Heqb1.
      apply N.leb_le in Heqb1.
      unfold N.zero.
      f_equal. lia.
      auto.
    + congruence.
  Unshelve.
  all: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
Qed.  

Lemma transferFrom_balances_keysDistinct: forall (_from :  address) (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in
    let balances := (_balances (l'.(Ledger_MainState))) in 
    let allowed0 := (_allowed (l.(Ledger_MainState))) in     
    keysDistinct balances0 ->  keysDistinct balances.
Proof.
    intros.
    remember ((xIntGeb balances0 [_from]  _value : bool) && 
              (xIntGeb allowed0 [_from] [msg_sender] _value : bool) ) as b1.
    remember (eqb _from _to) as b2.
    remember (hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) _from balances0) as b3.
    subst balances. subst l'. subst l0. subst balances0. subst allowed0. subst msg_sender.
    destruct b1, b2, b3. 
    -   rewrite transferFrom_from_member_balances; auto.  
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transferFrom_from_not_member_balances; auto.
        setoid_rewrite <- Heqb1.
        apply insert_kd. assumption.
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transferFrom_others_balances; auto.
        rewrite <- Heqb1.
        repeat apply insert_kd. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
    -   rewrite transferFrom_others_balances; auto.
        rewrite <- Heqb1.
        repeat apply insert_kd. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
    -   rewrite transferFrom_from_member_balances; auto.
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transferFrom_from_not_member_balances; auto.
        rewrite <- Heqb1. assumption.
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transferFrom_others_balances; auto.
        rewrite <- Heqb1. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
    -   rewrite transferFrom_others_balances; auto.
        rewrite <- Heqb1. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
Qed.

Lemma transferFrom_balances_sum: forall (_from :  address) (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ _from _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in
    let balances := (_balances (l'.(Ledger_MainState))) in
    let allowed0 := (_allowed (l.(Ledger_MainState))) in  
    keysDistinct balances0 ->    
    hmapBSum balances = hmapBSum balances0.
Proof.
    intros.
    remember ((xIntGeb balances0 [_from]  _value : bool) && 
              (xIntGeb allowed0 [_from] [msg_sender] _value : bool) ) as b1.
    remember (eqb _from _to) as b2.
    remember (hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) _from balances0) as b3.
    subst balances. subst l'. subst l0. subst balances0. subst allowed0. subst msg_sender.
    destruct b1, b2, b3.   
    - (* 1/8 *) rewrite transferFrom_from_member_balances; auto.
      apply BoolEq.eqb_spec_intro. auto.
    - (* 2/8 *) rewrite transferFrom_from_not_member_balances; auto.
      setoid_rewrite <- Heqb1.
      unfold hmapBSum.
      rewrite mapBN2N_addAdjust.
      rewrite hmapSumAdjust.
      rewrite lookup_none_find.
      simpl. f_equal. unfold N.zero. lia. 
      symmetry in Heqb3.
      apply member_false_lookup in Heqb3. 
      rewrite mapBN2N_hmapLookup2.
      setoid_rewrite Heqb3. auto.
      1,4: refine pair_xbool_equable.    
      1,3: refine BoolEq.pair_eqb_spec.
      2: assumption.
      apply mapBN2N_keysDistinct. assumption.
      apply BoolEq.eqb_spec_intro.
      auto.
    - (* 3/8 *) rewrite transferFrom_others_balances; auto.
       rewrite <- Heqb1.
       unfold hmapBSum.
       repeat rewrite mapBN2N_addAdjust.
       repeat rewrite hmapSumAdjust.
       remember (hmapSum (mapBN2N (_balances (Ledger_MainState l)))).
       (* setoid_rewrite <- Heqn. *)
       remember ((mapBN2N (_balances (Ledger_MainState l))) [_to]?).
       destruct y.
       + erewrite 2lookup_some_find with (k:=_to).
         2: setoid_rewrite <- Heqy.
         2: reflexivity.                  
         rewrite mapBN2N_hmapLookup2 in Heqy.
         all: cycle 3.
         enough ((_balances (Ledger_MainState l)) [_to] ? = Some (Build_XUBInteger n0)).
         setoid_rewrite H0. reflexivity.
         rewrite mapBN2N_hmapLookup2 in Heqy.
         remember ((_balances (Ledger_MainState l)) [_to] ?).
         setoid_rewrite <- Heqy0 in Heqy.         
         destruct y. simpl in Heqy. inversion Heqy.
         destruct x.  auto. inversion Heqy.
         all: cycle 2.
         symmetry in Heqb3.
         apply member_true_lookup in Heqb3.
         destruct Heqb3.
         erewrite lookup_some_find with (k:=_from).
         2: setoid_rewrite H0.
         2: reflexivity.         
         erewrite lookup_some_find with (k:=_from).
         2: erewrite lookup_addAdjust_another.
         2: rewrite mapBN2N_hmapLookup2.
         2: setoid_rewrite H0.
         2: reflexivity.
         destruct x, _value.
         simpl. 
         f_equal.
         enough(n1 >= n2). lia.
         symmetry in Heqb1.
         apply andb_prop in Heqb1. inversion Heqb1.
         eapply lookup_some_find in H0.
         erewrite H0 in H1. simpl in H1.
         apply N.leb_le in H1.
         lia.
         1,4,6: refine pair_xbool_equable.    
         1,3,4: refine BoolEq.pair_eqb_spec.
         unfold not; intros. apply BoolEq.eqb_spec_intro in H1.
         rewrite H1 in Heqb2. discriminate.
      + erewrite 2lookup_none_find with (k:=_to); auto.
        2: rewrite mapBN2N_hmapLookup2 in Heqy.
        2: remember ((_balances (Ledger_MainState l)) [_to] ?).
        2: setoid_rewrite <- Heqy0. 
        2: setoid_rewrite <- Heqy0 in Heqy.
        2: destruct y; auto.
        2: discriminate.           
        rewrite mapBN2N_hmapLookup2 in Heqy.
        remember ((_balances (Ledger_MainState l)) [_to] ?).
        setoid_rewrite <- Heqy0 in Heqy.
        destruct y. discriminate.
        remember ((_balances (Ledger_MainState l)) [_from]?).
        destruct y.
          *
          erewrite 2lookup_some_find with (k:=_from).      
          3: setoid_rewrite <- Heqy1.
          3: reflexivity.
          2: erewrite lookup_addAdjust_another.
          2: rewrite mapBN2N_hmapLookup2.
          2: setoid_rewrite <- Heqy1.
          2: reflexivity.
          destruct x, _value. simpl. unfold N.zero.
          f_equal. enough (n0 >= n1). lia.
          symmetry in Heqb1.
          apply andb_prop in Heqb1. inversion Heqb1.
          erewrite lookup_some_find in H0.
          2: setoid_rewrite <- Heqy1.
          2: reflexivity.
          simpl in H0.        
          apply N.leb_le in H0.
          lia.
          refine pair_xbool_equable.
          refine BoolEq.pair_eqb_spec.
          unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
          rewrite H0 in Heqb2. discriminate.
          * symmetry in Heqb3.
            apply member_true_lookup in Heqb3.
            destruct Heqb3.
            setoid_rewrite H0 in Heqy1. 
            discriminate.
          * refine pair_xbool_equable.
          * refine BoolEq.pair_eqb_spec.
          * refine pair_xbool_equable.
          * refine BoolEq.pair_eqb_spec.
      + apply mapBN2N_keysDistinct. assumption.
      + apply insert_kd. apply mapBN2N_keysDistinct. assumption.
      + refine pair_xbool_equable.
      + refine BoolEq.pair_eqb_spec.
      + assumption.
      + refine pair_xbool_equable.
      + refine BoolEq.pair_eqb_spec.
      + apply insert_kd.  assumption.
      + unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
    - (* 4/8 *) rewrite transferFrom_others_balances; auto.
       rewrite <- Heqb1.
       unfold hmapBSum.
       repeat rewrite mapBN2N_addAdjust.
       repeat rewrite hmapSumAdjust.
       remember (hmapSum (mapBN2N (_balances (Ledger_MainState l)))).
       (* setoid_rewrite <- Heqn. *)
       remember ((mapBN2N (_balances (Ledger_MainState l))) [_to]?).
       destruct y.
       + erewrite 2lookup_some_find with (k:=_to).
         2: setoid_rewrite <- Heqy.
         2: reflexivity.                  
         rewrite mapBN2N_hmapLookup2 in Heqy.
         all: cycle 3.
         enough ((_balances (Ledger_MainState l)) [_to] ? = Some (Build_XUBInteger n0)).
         setoid_rewrite H0. reflexivity.
         rewrite mapBN2N_hmapLookup2 in Heqy.
         remember ((_balances (Ledger_MainState l)) [_to] ?).
         setoid_rewrite <- Heqy0 in Heqy.         
         destruct y. simpl in Heqy. inversion Heqy.
         destruct x.  auto. inversion Heqy.
         all: cycle 2.
         symmetry in Heqb3.
         apply member_false_lookup in Heqb3.         
         erewrite lookup_none_find with (k:=_from).
         2: setoid_rewrite Heqb3.
         2: reflexivity.         
         erewrite lookup_none_find with (k:=_from).
         2: erewrite lookup_addAdjust_another.
         2: rewrite mapBN2N_hmapLookup2.
         2: setoid_rewrite Heqb3.
         2: reflexivity.
         destruct  _value.
         simpl. 
         f_equal. unfold N.zero.
         enough (n1 = 0). rewrite H0. lia.
         symmetry in Heqb1.
         apply andb_prop in Heqb1. inversion Heqb1.
         erewrite lookup_none_find in H0. simpl in H0.         
         apply N.leb_le in H0. unfold N.zero in H0.
         lia. auto.
         1,4,6: refine pair_xbool_equable.    
         1,3,4: refine BoolEq.pair_eqb_spec.
         unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
         rewrite H0 in Heqb2. discriminate.
      + erewrite 2lookup_none_find with (k:=_to); auto.
        2: rewrite mapBN2N_hmapLookup2 in Heqy.
        2: remember ((_balances (Ledger_MainState l)) [_to] ?).
        2: setoid_rewrite <- Heqy0. 
        2: setoid_rewrite <- Heqy0 in Heqy.
        2: destruct y; auto.
        2: discriminate.           
        rewrite mapBN2N_hmapLookup2 in Heqy.
        remember ((_balances (Ledger_MainState l)) [_to] ?).
        setoid_rewrite <- Heqy0 in Heqy.
        destruct y. discriminate.
        remember ((_balances (Ledger_MainState l)) [_from]?).
        destruct y.
        * symmetry in Heqb3.
          rewrite member_false_lookup in Heqb3.
          setoid_rewrite Heqb3 in Heqy1.
          discriminate.
        * erewrite 2lookup_none_find with (k:=_from).
        3: setoid_rewrite <- Heqy1.
        3: reflexivity.
        2: erewrite lookup_addAdjust_another.
        2: rewrite mapBN2N_hmapLookup2.
        2: setoid_rewrite <- Heqy1.
        2: reflexivity.
        enough (_value = default). rewrite H0.
        simpl. unfold N.zero.
        f_equal. lia.         
        symmetry in Heqb1.
        apply andb_prop in Heqb1. inversion Heqb1.
        erewrite lookup_none_find in H0.
        destruct _value.
        simpl in H0. unfold N.zero in H0.
        apply N.leb_le in H0. simpl default.
        f_equal. unfold N.zero. lia.
        auto.
        refine pair_xbool_equable.
        refine BoolEq.pair_eqb_spec.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
        * refine pair_xbool_equable.
        * refine BoolEq.pair_eqb_spec.
        * refine pair_xbool_equable.
        * refine BoolEq.pair_eqb_spec.
        + apply mapBN2N_keysDistinct. assumption.
        + apply insert_kd. apply mapBN2N_keysDistinct. assumption.
        + refine pair_xbool_equable.
        + refine BoolEq.pair_eqb_spec.
        + assumption.
        + refine pair_xbool_equable.
        + refine BoolEq.pair_eqb_spec.
        + apply insert_kd.  assumption.
        + unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.    
      - (* 5/8 *) rewrite transferFrom_from_member_balances; auto.
        apply BoolEq.eqb_spec_intro. auto.
      - (* 6/8 *) rewrite transferFrom_from_not_member_balances; auto.
        rewrite <- Heqb1. auto.
        apply BoolEq.eqb_spec_intro. auto.
      - (* 7/8 *) rewrite transferFrom_others_balances; auto.
        rewrite <- Heqb1. auto.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
      - (* 8/8 *) rewrite transferFrom_others_balances; auto.
        rewrite <- Heqb1. auto.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
Qed.   