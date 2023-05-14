Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.
Require Import Common.

Require Import EIP20.
Import EIP20.

Require Import EvalExecs.Approve.

Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.

Definition approve_exec_computed: forall
                            (_spender :  address) (_value :  uint256)
                            (l: LedgerLRecord rec), 
                            {t: LedgerLRecord rec | t = approve_exec _spender _value {$$ l with Ledger_LocalState := default $$}}.
Proof.        
    intros. 
    remember (approve_exec _spender _value {$$ l with Ledger_LocalState := default $$}).

    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  

    unfold approve_exec in Heql0.
    lift_all in Heql0.    
    compute in Heql0.
    buint_all in Heql0.
    symmetry in Heql0.
    
    match goal with
    | Heql0: ?l = l0 |- _ => exact (@exist _ _ l Heql0)
    end.
Defined.

Definition approve_computed_prf  (_spender :  address) (_value :  uint256) (l : LedgerLRecord rec) :
  proj1_sig (approve_exec_computed _spender _value l) = 
  exec_state (Uinterpreter (@approve rec def _ _ _ _spender _value)) 
  {$$ l with Ledger_LocalState := default $$}.
Proof. 
  rewrite <- approve_prf.
  destruct ((approve_exec_computed _spender _value l)).
  auto.
Defined.

Tactic Notation "approve_start"  constr(l) constr(l0) constr(l')  :=
    (subst l'; subst l0;
     rewrite <- approve_computed_prf;
    
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

    unfold approve_exec_computed;
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




Lemma approve_msg_sender_unchanged: forall (_spender :  address) (_value :  uint256)
                            (l: LedgerLRecord rec),                          
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@approve rec def _ _ _ _spender _value)) l0 in
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    VMState_ι_msg_sender (l'.(Ledger_VMState)) = msg_sender.
Proof.
    intros. approve_start l l0 l'.
    auto.
Qed.

Lemma approve_balance_unchanged: forall (_spender :  address) (_value :  uint256)
                            (l: LedgerLRecord rec),                          
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@approve rec def _ _ _ _spender _value)) l0 in
    let balances0 := _balances (l.(Ledger_MainState)) in
    _balances (l'.(Ledger_MainState)) = balances0.
Proof.
    intros. approve_start l l0 l'.
    auto.
Qed.

Lemma approve_set_allowed: forall (_spender :  address) (_value :  uint256)
                            (l: LedgerLRecord rec),                            
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@approve rec def _ _ _ _spender _value)) l0 in   
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in 
    (_allowed (l'.(Ledger_MainState))) [msg_sender] [_spender] = _value.
Proof.
    intros. approve_start l l0 l'.   
    compute in msg_sender.
    subst msg_sender.

    
    erewrite lookup_some_find with (k:=v4).
    all: cycle 1.
    unshelve eapply lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).

    erewrite lookup_some_find with (k:=_spender).
    reflexivity.
    unshelve eapply lookup_addAdjust.
    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
Qed.

Lemma approve_allowed_other_unchanged: forall (_spender :  address) (_value :  uint256) (x y: address)
                            (l: LedgerLRecord rec),                            
    let l0 := {$$ l with Ledger_LocalState := default $$} in
    let l' := exec_state (Uinterpreter (@approve rec def _ _ _ _spender _value)) l0 in   
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    let allowed0 := _allowed (l.(Ledger_MainState)) in
    ((x <> msg_sender) \/ (y <> _spender)) ->
    (_allowed (l'.(Ledger_MainState)))[x][y] = allowed0[x][y].
Proof.
    intros. approve_start l l0 l'.   
    compute_rhs.
    compute in msg_sender, allowed0.
    subst msg_sender.    

    destruct H.
    - remember s1 [x]?.
      destruct y0.
    + erewrite lookup_some_find with (k:=x).
    2: unshelve erewrite lookup_addAdjust_another.
    2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2: setoid_rewrite <- Heqy0.
    2: reflexivity.
    2: assumption.
    erewrite lookup_some_find with (k:=x).
    2: setoid_rewrite <- Heqy0.
    2: reflexivity.
    reflexivity.
    + erewrite lookup_none_find with (k:=x).
    2: unshelve erewrite lookup_addAdjust_another.
    2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
    2: auto.
    2: assumption.
    erewrite lookup_none_find with (k:=x).
    auto. auto.
    - remember s1 [x]?.
      destruct y0.
      + assert (x = v4 \/ x <> v4) by repeat decide equality.
        destruct H0.
        * subst x.   
            erewrite lookup_some_find with (k:=v4).
            2: unshelve erewrite lookup_addAdjust.
            2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
            2: reflexivity.        
            **  erewrite lookup_some_find with (k:=v4).
                2: setoid_rewrite <- Heqy0.
                2: reflexivity.
                remember x0[y]?.
                destruct y0.
                *** erewrite lookup_some_find with (k:=y).
                    2: unshelve erewrite lookup_addAdjust_another.
                    2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
                    2: setoid_rewrite <- Heqy1.
                    2: reflexivity.
                    2: assumption.
                    erewrite lookup_some_find with (k:=y).
                    reflexivity.
                    auto.
                *** erewrite lookup_none_find with (k:=y).
                    erewrite lookup_none_find with (k:=y).
                    auto.
                    auto.
                    unshelve erewrite lookup_addAdjust_another.
                    refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
                    auto.
                    assumption.
        * erewrite lookup_some_find with (k:=x).
            2:  unshelve erewrite lookup_addAdjust_another.
            2:  refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
            2:  setoid_rewrite <- Heqy0.
            2:  reflexivity.
            2:  assumption.
            erewrite lookup_some_find with (k:=x).
            2: setoid_rewrite <- Heqy0.
            2: reflexivity.
            auto.
      + assert (x = v4 \/ x <> v4) by repeat decide equality.
        destruct H0.
        * subst x.
          erewrite lookup_some_find with (k:=v4).
          2: unshelve erewrite lookup_addAdjust.
          2: refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
          2: reflexivity.
          erewrite lookup_none_find with (k:=v4).
          2: auto.
          erewrite ?lookup_none_find with (k:=y).
          auto.
          auto.
          unshelve erewrite lookup_addAdjust_another.
          refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
          auto.
          assumption.
        * erewrite lookup_none_find with (k:=x).
          erewrite lookup_none_find with (k:=x).
          auto.
          auto.
          unshelve erewrite lookup_addAdjust_another.
          refine (BoolEq.pair_eqb_spec (X:=Z) (Y:=XUBInteger 256)).
          auto.
          assumption.
Qed.