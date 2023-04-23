(*/Users/petrlarockin/Downloads/TON/solidity-coq-translator/trees*)

Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.

Require Import UrsusContractCreator.UrsusFieldUtils.
Interfaces.
SetUrsusOptions.
MakeInterface Class IERC20 :=
{ 
    totalSupply : ( UExpression (PhantomType) false);
    balanceOf : ( address) -> ( UExpression (( address)) false);
    transfer : ( address) -> ( uint256) -> ( UExpression (( address) ** ( uint256)) false);
    allowance : ( address) -> ( address) -> ( UExpression (( address) ** ( address)) false);
    approve : ( address) -> ( uint256) -> ( UExpression (( address) ** ( uint256)) false);
    transferFrom : ( address) -> ( address) -> ( uint256) -> ( UExpression (( address) ** ( address) ** ( uint256)) false);
    Transfer : ( (* indexed *)address) -> ( (* indexed *)address) -> ( uint256) -> ( UExpression (( (* indexed *)address) ** ( (* indexed *)address) ** ( uint256)) false );
    Approval : ( (* indexed *)address) -> ( (* indexed *)address) -> ( uint256) -> ( UExpression (( (* indexed *)address) ** ( (* indexed *)address) ** ( uint256)) false )
}.
EndInterfaces.