(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/trees*)

Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UrsusContractCreator.UrsusFieldUtils.
Interfaces.
SetUrsusOptions.
MakeInterface Class EIP20Interface :=
{ 
    balanceOf : ( address) -> ( UExpression ((uint256)) false);
    transfer : ( address) -> ( uint256) -> ( UExpression ((bool)) true);
    transferFrom : ( address) -> ( address) -> ( uint256) -> ( UExpression ((bool)) true);
    approve : ( address) -> ( uint256) -> ( UExpression ((bool)) false);
    allowance : ( address) -> ( address) -> ( UExpression ((uint256)) false)
    (*;Transfer : ((* indexed *) address) -> ( (* indexed *) address) -> ( uint256) -> ( UExpression PhantomType false );*)
    (*Approval : ((* indexed *) address) -> ( (* indexed *) address) -> ( uint256) -> ( UExpression PhantomType false )*)
}.
EndInterfaces.