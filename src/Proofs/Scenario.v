Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import FinProof.Lib.HMapList.

Require Import UMLang.ExecGenerator.

Require Import EIP20.
Import EIP20.

Require Import Common.
Require Import Proofs.Constructor.
Require Import Proofs.Transfer.
Require Import Proofs.TransferFrom.
Require Import Proofs.Approve.


Opaque Common.hmapFindWithDefault
        CommonInstances.addAdjustListPair
        N.add N.sub N.leb N.ltb N.eqb Z.eqb.




(* mint to some address
    1. create token
    2. mint (transfer) _value to _to*)
Lemma MintToSomeAddress_set_recepient_balance: forall 
                            (_initialAmount :  uint256) 
                            (_tokenName :  string) 
                            (_decimalUnits :  uint8) 
                            (_tokenSymbol :  string) 

                            (_to :  address) 
                            (_value : uint256)
                            (l: LedgerLRecord rec)
                            (l0: LedgerLRecord rec)
                            (l1: LedgerLRecord rec)
                            (l2: LedgerLRecord rec), 
(*     let l0 := {$$ default with Ledger_VMState := vmstate $$} in
    let l1 := exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 in
    let l2 := exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l1 in
 *) l = default ->
 l0 = {$$ l with Ledger_LocalState := default $$} ->
    l1 = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 ->
    let l1' := {$$ l1 with Ledger_LocalState := default $$} in
    l2 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ _to _value)) l1' ->
    let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
    (xIntGeb _initialAmount  _value = true) ->
    _to <> msg_sender ->
    (_balances (l2.(Ledger_MainState))) [_to] = _value.
Proof.
    intros.
    subst l2.
    subst l1'.
    rewrite transfer_set_recepient_balance.
    match goal with
    | |- context [if ?b then _ else _] => assert (b = true)
    end.
    rewrite <- H3.
     assert (VMState_ι_msg_sender (Ledger_VMState l1) = msg_sender).
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged. auto.
    rewrite H2.
     subst l1.
    subst l0.
    subst msg_sender.
    rewrite constructor_set_sender_balance. auto.
    rewrite H2.
    subst l1.
    subst l0.
    rewrite constructor_not_sender_balance.

    all: cycle 1.
    auto.
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged. auto.
    subst l.

    compute; buint_all; auto.
    erewrite lookup_none_find.
    all: cycle 1. 
    compute; buint_all; auto.
    destruct _value.
    simpl.
    f_equal.
Qed.


Lemma ChangeVM_balanceINV: forall    (vmstate: VMStateLRecord) (l: LedgerLRecord rec),
let l' := {$$ l with Ledger_VMState := vmstate $$} in
(_balances (l'.(Ledger_MainState))) = (_balances (l.(Ledger_MainState))).
Proof.
    intros.
    subst l'.
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  
    compute; auto.
Qed.

Lemma ChangeVM_allowedINV: forall    (vmstate: VMStateLRecord) (l: LedgerLRecord rec),
let l' := {$$ l with Ledger_VMState := vmstate $$} in
(_allowed (l'.(Ledger_MainState))) = (_allowed (l.(Ledger_MainState))).
Proof.
    intros.
    subst l'.
    destruct l. repeat destruct p.   
    destruct v. repeat destruct p.
    destruct c. repeat destruct p.  
    compute; auto.
Qed.

Ltac nbool2relG:=
repeat match goal with
| |- N.leb _ _ = true => apply N.leb_le
| |- N.leb _ _ = false  => apply N.leb_gt

| |- N.ltb _ _ = true => apply N.ltb_lt
| |- N.ltb _ _ = false => apply N.ltb_ge
| _ => idtac
end.
Ltac nbool2relH:=
repeat match goal with
| H: N.leb _ _ = true  |- _ => apply N.leb_le in H
| H: N.leb _ _ = false |- _ => apply N.leb_gt in H

| H: N.ltb _ _ = true  |- _ => apply N.ltb_lt in H
| H: N.ltb _ _ = false |- _ => apply N.ltb_ge in H
| _ => idtac
end.


Lemma AGebBGebC: forall (a b c : uint256),
xIntGeb a b = true ->
xIntGeb b c = true ->
xIntGeb a c = true.
Proof.
    intros.
    destruct a, b, c.
    simpl in *.
    nbool2relH.
    nbool2relG.
    lia.
Qed.
(* transfer to third address
    1. create token
    2. mint (transfer) _value1 to address1
    2'. change sender (change VMState)
    3. transfer _value2 to address2*)
Lemma TransferToThirdAddress_set_recepient_balance: forall 
    (_initialAmount :  uint256) 
    (_tokenName :  string) 
    (_decimalUnits :  uint8) 
    (_tokenSymbol :  string) 

    (address1 :  address) 
    (address2 :  address) 
    (value1 : uint256)
    (value2 : uint256)
    (vmstate1: VMStateLRecord)
    (l: LedgerLRecord rec)
    (l0: LedgerLRecord rec)
    (l1: LedgerLRecord rec)
    (l2: LedgerLRecord rec) 
    (l3: LedgerLRecord rec), 
    l = default ->
    l0 = {$$ l with Ledger_LocalState := default $$} ->
    l1 = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 ->
let l1' := {$$ l1 with Ledger_LocalState := default $$} in
    l2 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ address1 value1)) l1' ->
let l2' := {$$ l2 with Ledger_VMState := vmstate1 $$} in
let l2'' := {$$ l2' with Ledger_LocalState := default $$} in
    l3 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ address2 value2)) l2'' ->
let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
let msg_sender1 := VMState_ι_msg_sender (l2'.(Ledger_VMState)) in
(xIntGeb _initialAmount  value1 = true) ->
(xIntGeb value1  value2 = true) ->
(* address1 <> msg_sender ->
 *)address2 <> msg_sender ->
address1 <> address2 ->
address1 = msg_sender1 ->
(_balances (l3.(Ledger_MainState))) [address2] = value2.
Proof.
    intros.
    subst l3.
    subst l2''.
    subst l2'.
    subst l2.
    subst l1'.
    subst l1.
    subst l0.
    subst l.
    rewrite transfer_set_recepient_balance.
    -
    remember ((eqb address1 msg_sender): bool) as msg_sender_inv.
    destruct msg_sender_inv.
    +
match goal with
| |- context [xIntGeb ?b _ ] => assert (b = _initialAmount)
end.
*
subst msg_sender1.
rewrite <- H8.
rewrite ChangeVM_balanceINV.
assert (address1 = msg_sender).
apply BoolEq.eqb_spec_intro. auto.

rewrite transfer_set_recepient_balance0.
rewrite H.
subst msg_sender.
rewrite constructor_set_sender_balance. auto.
rewrite constructor_msg_sender_unchanged. auto.
*
rewrite H.
match goal with
| |- context [if ?b   then _ else _ ] => assert (b = true)
end.
eapply AGebBGebC; eassumption.
rewrite H0.
rewrite ChangeVM_balanceINV.
rewrite transfer_others_balance_unchanged; auto.
rewrite constructor_not_sender_balance; auto.
destruct value2.
vm_compute; auto.
+
match goal with
| |- context [xIntGeb ?b _ ] => assert (b = value1)
end.
*
subst msg_sender1.
rewrite <- H8.
rewrite ChangeVM_balanceINV.
setoid_rewrite MintToSomeAddress_set_recepient_balance; auto.
subst msg_sender. 
rewrite <- BoolEq.boolEqNot. auto.
*
rewrite H. rewrite H5.
rewrite ChangeVM_balanceINV.
rewrite transfer_others_balance_unchanged; auto.
rewrite constructor_not_sender_balance; auto.
destruct value2.   
vm_compute; auto.
-
subst msg_sender.
subst msg_sender1.
rewrite <- H8.
auto.

Qed.

(* transfer to third address
    1. create token
    2. mint (transfer) _value1 to address1
    2'. change sender (change VMState)
    3. Set allowance (approve) by address1 to address2 (value2)
    3'. change sender (change VMState)
    4. transfer _value3 from address1 to address3 by address2*)
Lemma TransferFromToThirdAddress_set_recepient_balance: forall 
    (_initialAmount :  uint256) 
    (_tokenName :  string) 
    (_decimalUnits :  uint8) 
    (_tokenSymbol :  string) 

    (address1 :  address) 
    (address2 :  address) 
    (address3 :  address) 
    (value1 : uint256)
    (value2 : uint256)
    (value3 : uint256)
    (vmstate1: VMStateLRecord) 
    (vmstate2: VMStateLRecord)
    (l: LedgerLRecord rec)
    (l0: LedgerLRecord rec)
    (l1: LedgerLRecord rec)
    (l2: LedgerLRecord rec) 
    (l3: LedgerLRecord rec) 
    (l4: LedgerLRecord rec), 

    l = default ->
    l0 = {$$ l with Ledger_LocalState := default $$} ->
    l1 = exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l0 ->
let l1' := {$$ l1 with Ledger_LocalState := default $$} in
    l2 = exec_state (Uinterpreter (@transfer rec def _ _ _ _ address1 value1)) l1' ->
let l2' := {$$ l2 with Ledger_VMState := vmstate1 $$} in
let l2'' := {$$ l2' with Ledger_LocalState := default $$} in
    l3 = exec_state (Uinterpreter (@approve rec def _ _ _  address2 value2)) l2'' ->
let l3' := {$$ l3 with Ledger_VMState := vmstate2 $$} in
let l3'' := {$$ l3' with Ledger_LocalState := default $$} in
    l4 = exec_state (Uinterpreter (@transferFrom rec def _ _ _ _ address1 address3 value3)) l3'' ->
let msg_sender := VMState_ι_msg_sender (l.(Ledger_VMState)) in
let msg_sender1 := VMState_ι_msg_sender (l2'.(Ledger_VMState)) in
let msg_sender2 := VMState_ι_msg_sender (l3'.(Ledger_VMState)) in
(xIntGeb _initialAmount  value1 = true) ->
(xIntGeb value1  value3 = true) ->
(xIntGeb value2  value3 = true) ->
address3 <> msg_sender ->
address3 <> address1 ->
address1 = msg_sender1 ->
address2 = msg_sender2 ->
(_balances (l4.(Ledger_MainState))) [address3] = value3.
Proof.
    intros.
    subst l4.
    subst l3''.
    rewrite transferFrom_set_to_balance; [ |auto ].
    match goal with
        | |- context [if ?b   then _ else _ ] => enough (b = true)
    end.
    -
    rewrite H4.
    subst l3'.
    rewrite ChangeVM_balanceINV.
    subst l3.
    subst l2''.
    rewrite approve_balance_unchanged.
    subst l2'.
    rewrite ChangeVM_balanceINV.
    subst l2.
    subst l1'.
    rewrite transfer_others_balance_unchanged; [ | |auto].
    +
    subst l1.
    subst l0.
    rewrite constructor_not_sender_balance; [ | auto].
    subst l.
    destruct value3.
    auto.
    +
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged.
    auto.
    -
    apply andb_true_intro.
    split.
    +
    subst l3'.
    rewrite ChangeVM_balanceINV.
    subst l3.
    subst l2''.
    rewrite approve_balance_unchanged.
    subst l2'.
    rewrite ChangeVM_balanceINV.
    subst l2.
    subst l1'.
    remember ((eqb address1 msg_sender): bool) as msg_sender_inv.
    destruct msg_sender_inv.
    *
    rewrite transfer_set_recepient_balance0.
    **
    subst l1.
    subst l0.
    symmetry in Heqmsg_sender_inv.
    rewrite  BoolEq.eqb_spec_intro in Heqmsg_sender_inv.
    rewrite Heqmsg_sender_inv.
    subst msg_sender.
    rewrite constructor_set_sender_balance.
    eapply AGebBGebC; eassumption.
    **
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged.
    symmetry in Heqmsg_sender_inv.
    rewrite  BoolEq.eqb_spec_intro in Heqmsg_sender_inv.
    rewrite Heqmsg_sender_inv.
    subst msg_sender.
    auto.
    *
    rewrite transfer_set_recepient_balance.
    **
    match goal with
        | |- context [if ?b   then _ else _ ] => enough (b = true)
    end.
    rewrite H2.
    ***
    subst l1.
    subst l0.
    rewrite constructor_not_sender_balance.
    ****
    subst l.
    rewrite <- H6.
    destruct value3, value1.
    auto.
    ****
    symmetry in Heqmsg_sender_inv.
    rewrite   BoolEq.boolEqNot  in Heqmsg_sender_inv.
    subst msg_sender.
    auto.
    ***
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged.
    rewrite constructor_set_sender_balance.
    auto.
    **
    symmetry in Heqmsg_sender_inv.
    rewrite   BoolEq.boolEqNot  in Heqmsg_sender_inv.
    subst l1.
    subst l0.
    rewrite constructor_msg_sender_unchanged.
    auto.
    +
    subst msg_sender2.
    rewrite <- H11.
    subst l3'.
    rewrite ChangeVM_allowedINV.
    subst l3.
    subst l2''.
    rewrite H10.
    subst msg_sender1.
    rewrite approve_set_allowed.
    auto.
Qed.

