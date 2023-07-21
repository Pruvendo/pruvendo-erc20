Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.
Require Import Common.

Require Import EIP20.
Import EIP20.

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

Tactic Notation "transfer_start"  constr(l) constr(l0) constr(l')  :=
    (subst l'; subst l0;
     rewrite <- transfer_computed_prf;
    
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
    destruct p as [v14 p]; destruct p as [v15 p]; 
    destruct p as [v16 v17];
    
    destruct c as [s0 p]; destruct p as [s1 p];
    destruct p as [s2 p]; destruct p as [s3 p];
    destruct p as [s4 s5];  

    unfold transfer_exec_computed;
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
    intros. transfer_start l l0 l'.
    
    compute_rhs.
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

    destruct _value, x.
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
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in msg_sender_balance0, msg_sender.
    
    match goal with
    | |- context [@addAdjustListPair _ _ _ v5 ?v _] => remember v
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
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in msg_sender_balance0, msg_sender, recepient_balance0.

    match goal with
    | |- context [@addAdjustListPair ?K ?V ?H v5 ?v ?m] => remember (@addAdjustListPair K V H v5 v m)
    end.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.

    erewrite lookup_some_find.
    reflexivity.    

    unshelve erewrite lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    subst l1.

    remember (s0 [_to] ?).
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


Lemma transfer_others_balance_unchanged: forall (_to :  address) 
                            (_value : uint256)
                            (smbd : address)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let smbd_balance0 := (_balances (l.(Ledger_MainState))) [smbd] in

    smbd <> msg_sender ->
    smbd <> _to ->  
    (_balances (l'.(Ledger_MainState))) [smbd] = smbd_balance0.
Proof.        
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in smbd_balance0, msg_sender.

(*     match goal with
    | |- context [@addAdjustListPair ?K ?V ?H v4 ?v ?m] => remember (@addAdjustListPair K V H v4 v m)
    end. *)

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.    

    remember (s0 [smbd] ?).
    destruct y.

    - 
    erewrite lookup_some_find.
    reflexivity. 
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    erewrite lookup_some_find.    
    setoid_rewrite <- Heqy.    
    reflexivity. 
    setoid_rewrite <- Heqy.
    reflexivity.
    assumption. assumption. 

    -
    rewrite lookup_none_find.
    rewrite lookup_none_find.
    reflexivity.
    setoid_rewrite Heqy. reflexivity.

    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    unshelve erewrite lookup_addAdjust_another.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    setoid_rewrite <- Heqy. reflexivity. 
    assumption.
    assumption.
Qed.

Lemma transfer_msg_sender_unchanged: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender0 := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    VMState_ι_msg_sender (l'.(Ledger_VMState)) = msg_sender0.
Proof.        
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in msg_sender0.

    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b; auto
    end.
Qed.


Lemma transfer_others_balances: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in
    _to <> msg_sender -> 
    _balances (l'.(Ledger_MainState)) = 
    if (xIntGeb (balances0 [msg_sender])  _value : bool) then 
        (balances0 [msg_sender] ← (xIntMinus (balances0 [msg_sender]) _value)) [_to] ← 
            (xIntPlus (balances0 [_to]) _value) else balances0.
Proof. 
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in balances0, msg_sender.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.
    remember (eqb _to v5).
    destruct y.
    - symmetry in Heqy. 
      rewrite BoolEq.eqb_spec_intro in Heqy.
      subst msg_sender. contradiction.
    - 

    remember (s0 [_to] ?).
    destruct y.

    +

    erewrite 2lookup_some_find with (k:=_to).
    3: unshelve erewrite lookup_addAdjust_another.    
    3: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2, 3: setoid_rewrite <- Heqy0.
    2, 3: reflexivity.
    2: assumption.
    auto.

    +
    erewrite 2lookup_none_find with (k:=_to).
    3: unshelve erewrite lookup_addAdjust_another.    
    3: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2, 3: auto.
    2: assumption.
    auto.
Qed.    

Lemma transfer_msg_sender_member_balances: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in     
    _to = msg_sender -> 
    keysDistinct balances0 ->
    hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) msg_sender balances0  = true ->
    _balances (l'.(Ledger_MainState)) = balances0.
Proof.
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in balances0, msg_sender.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.
    subst msg_sender.
    subst v5.

    apply member_true_lookup in H1.
    destruct H1.    

    erewrite 2lookup_some_find with (k:=_to).
    3: erewrite lookup_some_find with (k:=_to).    
    3: unshelve erewrite lookup_addAdjust.    
    3: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    3: reflexivity.        
    2,3: setoid_rewrite H.    
    2,3: reflexivity.

    erewrite insert_insert.
    unfold xHMapInsert. simpl.
    match goal with
    | |- context [@addAdjustListPair _ _ _ ?a ?v _] => remember v
    end.
    enough (x0 = x).
    destruct s0.
    erewrite member_addAdjust; auto.
    rewrite H1. auto.
    subst x0.
    destruct x, _value. simpl.
    f_equal.
    erewrite lookup_some_find with (k:=_to) in Heqb.
    2: setoid_rewrite H.
    2: reflexivity.
    simpl in Heqb.
    rewrite H2 in Heqb.
    symmetry in Heqb.
    apply N.leb_le in Heqb.
    lia.
    Unshelve.
    all: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
Qed.    

Lemma transfer_msg_sender_not_member_balances: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in     
    _to = msg_sender -> 
    keysDistinct balances0 ->
    hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) msg_sender balances0  = false ->
    _balances (l'.(Ledger_MainState)) =
    if (xIntGeb (balances0 [msg_sender])  _value : bool) then 
         balances0 [msg_sender] ← default
    else balances0.
Proof.
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in balances0, msg_sender.

    match goal with
    | |- context [if ?b then false else true] => remember b
    end.    
    
    case_eq b; intros; auto.
    subst msg_sender.
    subst v5.

    apply member_false_lookup in H1.    

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


    simpl in Heqb.
    rewrite H2 in Heqb.
    symmetry in Heqb.
    apply N.leb_le in Heqb.
    destruct _value.
    simpl default.
    f_equal.
    erewrite lookup_none_find with (k:=_to) in Heqb.
    simpl in Heqb.    
    (* compute in Heqb. *)
    vm_compute.
    lia.
    subst balances0.
    auto.
    Unshelve.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
Qed.

Lemma transfer_balances_keysDistinct: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in
    let balances := (_balances (l'.(Ledger_MainState))) in     
    keysDistinct balances0 ->  keysDistinct balances.
Proof.
    intros.
    remember (xIntGeb (balances0 [msg_sender])  _value : bool) as b1.
    remember (eqb _to msg_sender) as b2.
    remember (hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) msg_sender balances0) as b3.
    subst balances. subst l'. subst l0. subst balances0. subst msg_sender.
    destruct b1, b2, b3. 
    -   rewrite transfer_msg_sender_member_balances; auto.  
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transfer_msg_sender_not_member_balances; auto.
        setoid_rewrite <- Heqb1.
        apply insert_kd. assumption.
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transfer_others_balances; auto.
        rewrite <- Heqb1.
        repeat apply insert_kd. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
    -   rewrite transfer_others_balances; auto.
        rewrite <- Heqb1.
        repeat apply insert_kd. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
    -   rewrite transfer_msg_sender_member_balances; auto.
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transfer_msg_sender_not_member_balances; auto.
        rewrite <- Heqb1. assumption.
        apply BoolEq.eqb_spec_intro. auto.
    -   rewrite transfer_others_balances; auto.
        rewrite <- Heqb1. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
    -   rewrite transfer_others_balances; auto.
        rewrite <- Heqb1. assumption.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
Qed.





Lemma transfer_balances_sum: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let balances0 := (_balances (l.(Ledger_MainState))) in
    let balances := (_balances (l'.(Ledger_MainState))) in     
    keysDistinct balances0 ->    
    hmapBSum balances = hmapBSum balances0.
Proof.
    intros.
    remember (xIntGeb (balances0 [msg_sender])  _value : bool) as b1.
    remember (eqb _to msg_sender) as b2.
    remember (hmapIsMember (H7 := @pair_xbool_equable bool _ Z _ uint256 _  ) msg_sender balances0) as b3.
    subst balances. subst l'. subst l0. subst balances0. subst msg_sender.
    destruct b1, b2, b3.
    - (* 1/8 *) rewrite transfer_msg_sender_member_balances; auto.
      apply BoolEq.eqb_spec_intro. auto.
    - (* 2/8 *) rewrite transfer_msg_sender_not_member_balances; auto.
      setoid_rewrite <- Heqb1.
      unfold hmapBSum.
      rewrite mapBN2N_addAdjust.
      rewrite hmapSumAdjust.
      rewrite lookup_none_find.
      simpl. f_equal. unfold N.zero. remember (hmapSum (mapBN2N (_balances (Ledger_MainState l)))).
      setoid_rewrite <- Heqn. lia.
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
    - (* 3/8 *) rewrite transfer_others_balances; auto.
       rewrite <- Heqb1.
       unfold hmapBSum.
       repeat rewrite mapBN2N_addAdjust.
       repeat rewrite hmapSumAdjust.
       remember (hmapSum (mapBN2N (_balances (Ledger_MainState l)))).
       setoid_rewrite <- Heqn.
       remember ((mapBN2N (_balances (Ledger_MainState l))) [_to]?).
       destruct y.
       + erewrite 2lookup_some_find with (k:=_to).
         2: erewrite lookup_addAdjust_another.
         3: unfold not.
         3: intros.         
         3: apply BoolEq.eqb_spec_intro in H0.
         3: rewrite H0 in Heqb2.
         3: discriminate.
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

         rewrite mapBN2N_hmapLookup.   
         remember ((_balances (Ledger_MainState l))
         [VMState_ι_msg_sender (Ledger_VMState l)]).
         setoid_rewrite <- Heqx.
         destruct x, _value.
         simpl. 
         f_equal.
         enough(n1 >= n2).
         enough(n >= n1). lia.
         2: symmetry in Heqb1.
         2: apply N.leb_le in Heqb1.
         2: lia. 
         subst n. 
         enough (n1 = ((mapBN2N (_balances (Ledger_MainState l))) [VMState_ι_msg_sender (Ledger_VMState l)])).
         subst n1.
         apply hmapSumGE.
         rewrite mapBN2N_hmapLookup.
         setoid_rewrite <- Heqx.
         auto.
         1,3,5,7: refine pair_xbool_equable.    
         1,2,3,4: refine BoolEq.pair_eqb_spec.
         +
         erewrite 2lookup_none_find with (k:=_to).
         2: erewrite lookup_addAdjust_another.
         3: unfold not.
         3: intros.         
         3: apply BoolEq.eqb_spec_intro in H0.
         3: rewrite H0 in Heqb2.
         3: discriminate.
         2: setoid_rewrite <- Heqy.
         2: reflexivity.
         rewrite mapBN2N_hmapLookup.   
         remember ((_balances (Ledger_MainState l))
         [VMState_ι_msg_sender (Ledger_VMState l)]).
         setoid_rewrite <- Heqx.
         destruct x, _value.
         simpl. 
         f_equal.
         unfold N.zero.
         enough(n0 >= n1).
         enough(n >= n0). lia.
         2: symmetry in Heqb1.
         2: apply N.leb_le in Heqb1.
         2: lia. 
         subst n. 
         enough (n0 = ((mapBN2N (_balances (Ledger_MainState l))) [VMState_ι_msg_sender (Ledger_VMState l)])).
         subst n0.
         apply hmapSumGE.
         rewrite mapBN2N_hmapLookup.
         setoid_rewrite <- Heqx.
         auto.
         1,3: refine pair_xbool_equable.    
         1,2: refine BoolEq.pair_eqb_spec.
         rewrite mapBN2N_hmapLookup2 in Heqy.
         remember ((_balances (Ledger_MainState l)) [_to] ?).         
         setoid_rewrite <- Heqy0.
         destruct y.
         setoid_rewrite <- Heqy0 in Heqy.
         inversion Heqy.
         auto.
         refine pair_xbool_equable.
         refine BoolEq.pair_eqb_spec.
         + apply mapBN2N_keysDistinct. assumption.
         + apply insert_kd. apply mapBN2N_keysDistinct. assumption.
         + refine pair_xbool_equable.
         + refine BoolEq.pair_eqb_spec.
         + assumption.
         + refine pair_xbool_equable.
         + refine BoolEq.pair_eqb_spec.
         + apply insert_kd. assumption.
         + unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
           rewrite H0 in Heqb2. discriminate.
    - (* 4/8 *) rewrite transfer_others_balances; auto.
       rewrite <- Heqb1.
       unfold hmapBSum.
       repeat rewrite mapBN2N_addAdjust.
       repeat rewrite hmapSumAdjust.
       remember (hmapSum (mapBN2N (_balances (Ledger_MainState l)))).
       setoid_rewrite <- Heqn.
       remember ((mapBN2N (_balances (Ledger_MainState l))) [_to]?).
       destruct y.
       + erewrite 2lookup_some_find with (k:=_to).
         2: erewrite lookup_addAdjust_another.
         3: unfold not.
         3: intros.         
         3: apply BoolEq.eqb_spec_intro in H0.
         3: rewrite H0 in Heqb2.
         3: discriminate.
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

         rewrite mapBN2N_hmapLookup.   
         remember ((_balances (Ledger_MainState l))
         [VMState_ι_msg_sender (Ledger_VMState l)]).
         setoid_rewrite <- Heqx.
         destruct x, _value.
         simpl. 
         f_equal.
         enough(n1 >= n2).
         enough(n >= n1). lia.
         2: symmetry in Heqb1.
         2: apply N.leb_le in Heqb1.
         2: lia. 
         subst n. 
         enough (n1 = ((mapBN2N (_balances (Ledger_MainState l))) [VMState_ι_msg_sender (Ledger_VMState l)])).
         subst n1.
         apply hmapSumGE.
         rewrite mapBN2N_hmapLookup.
         setoid_rewrite <- Heqx.
         auto.
         1,3,5,7: refine pair_xbool_equable.    
         1,2,3,4: refine BoolEq.pair_eqb_spec.
         +
         erewrite 2lookup_none_find with (k:=_to).
         2: erewrite lookup_addAdjust_another.
         3: unfold not.
         3: intros.         
         3: apply BoolEq.eqb_spec_intro in H0.
         3: rewrite H0 in Heqb2.
         3: discriminate.
         2: setoid_rewrite <- Heqy.
         2: reflexivity.      

         rewrite mapBN2N_hmapLookup.   
         remember ((_balances (Ledger_MainState l))
         [VMState_ι_msg_sender (Ledger_VMState l)]).
         setoid_rewrite <- Heqx.
         destruct x, _value.
         simpl. 
         f_equal.
         unfold N.zero.
         enough(n0 >= n1).
         enough(n >= n0). lia.
         2: symmetry in Heqb1.
         2: apply N.leb_le in Heqb1.
         2: lia. 
         subst n. 
         enough (n0 = ((mapBN2N (_balances (Ledger_MainState l))) [VMState_ι_msg_sender (Ledger_VMState l)])).
         subst n0.
         apply hmapSumGE.
         rewrite mapBN2N_hmapLookup.
         setoid_rewrite <- Heqx.
         auto.
         1,3: refine pair_xbool_equable.    
         1,2: refine BoolEq.pair_eqb_spec.
         rewrite mapBN2N_hmapLookup2 in Heqy.
         remember ((_balances (Ledger_MainState l)) [_to] ?).         
         setoid_rewrite <- Heqy0.
         destruct y.
         setoid_rewrite <- Heqy0 in Heqy.
         inversion Heqy.
         auto.
         refine pair_xbool_equable.
         refine BoolEq.pair_eqb_spec.
         + apply mapBN2N_keysDistinct. assumption.
         + apply insert_kd. apply mapBN2N_keysDistinct. assumption.
         + refine pair_xbool_equable.
         + refine BoolEq.pair_eqb_spec.
         + assumption.
         + refine pair_xbool_equable.
         + refine BoolEq.pair_eqb_spec.
         + apply insert_kd. assumption.
         + unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
           rewrite H0 in Heqb2. discriminate.  
      - (* 5/8 *) rewrite transfer_msg_sender_member_balances; auto.
        apply BoolEq.eqb_spec_intro. auto.
      - (* 6/8 *) rewrite transfer_msg_sender_not_member_balances; auto.
        rewrite <- Heqb1. auto.
        apply BoolEq.eqb_spec_intro. auto.
      - (* 7/8 *) rewrite transfer_others_balances; auto.
        rewrite <- Heqb1. auto.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
      - (* 8/8 *) rewrite transfer_others_balances; auto.
        rewrite <- Heqb1. auto.
        unfold not; intros. apply BoolEq.eqb_spec_intro in H0.
        rewrite H0 in Heqb2. discriminate.
Qed.        
          

Lemma transfer_allowed_unchanged: forall (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec), 
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l0 in
    let allowed0 := _allowed (l.(Ledger_MainState)) in
    _allowed (l'.(Ledger_MainState)) = allowed0.
Proof.        
    intros. transfer_start l l0 l'.
    compute_rhs.    
    compute in allowed0.

    repeat match goal with
    | |- context [if ?b then _ else _] => destruct b; auto
    end.
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