Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

Require Import EvalExecs.TransferFrom.

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
        N.add N.sub N.leb N.ltb N.eqb Z.eqb N.pow.

Axiom EqSome: forall (a b: XUBInteger 256),
a = b -> Some a = Some b.


Lemma if_transit: forall X Y (b: bool) (f: X -> Y) x y, 
  f (if b then x else y) = if b then f x else f y.
Proof.
  intros.
  destruct b; auto.
Qed.

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
    repeat rewrite exec_if_transit, exec_if_transit2.

    (*repeat rewrite if_transit. *)


    compute.
    compute in _from_balance0, allowance0, msg_sender.  

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
(*     (xIntGeb allowance  _value : bool) = true ->
 *)    (_balances (l'.(Ledger_MainState))) [_to] = 
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
    repeat rewrite exec_if_transit, exec_if_transit2.

    (*repeat rewrite if_transit. *)


    compute.
    compute in _from_balance0, _to_balance0, allowance0, msg_sender.  

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

Check toValue (eval_state (sRReader (MAX_UINT256_right rec def)) _).

Print intFunRec_gen.


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
    repeat rewrite exec_if_transit, exec_if_transit2.

    compute.
    compute in _from_balance0, allowed0, msg_sender.  

    assert (forall n (v1 v: XUBInteger n) (T11 T12: _ -> Type) T2 f w w1, 
    ((let 'Build_XUBInteger a as a'' := v
    return T11 a'' -> T2 in
    fun _: T11 a'' => (let 'Build_XUBInteger b as b'' := v1
    return T12 b''-> T2 in fun _ : T12 b'' => f b a) w) w1) = 
    f (uint2N v1) (uint2N v)).

    intros.

    destruct v, v1. auto.
    rewrite ?H.


    assert (forall n (v: XUBInteger n) (T11: _ -> Type) T2 f w, 
    (let 'Build_XUBInteger a as a'' := v
    return T11 a'' -> T2 in
    fun _: T11 a'' => f a) w = 
    f (uint2N v)).

    intros.

    destruct v. auto.
    rewrite ?H0.


    assert (forall X n (v: XUBInteger n) (f : _ -> X), 
     match v with 
      | Build_XUBInteger x => f x
      end = f (uint2N v) ).

    intros.

    destruct v. auto.
    rewrite ?H1.

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
