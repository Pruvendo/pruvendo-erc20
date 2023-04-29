Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.


Interfaces.
SetUrsusOptions.

MakeInterface Class EIP20Interface :=
{     
    transfer     :  address -> uint256 -> UExpression bool true;
    transferFrom : address -> address -> uint256 -> UExpression bool true;
    approve      : address -> uint256 -> UExpression bool false;

    (* getters *)
    balanceOf    :  address -> UExpression uint256 false;
    allowance    : address -> address -> UExpression uint256 false    
}.

EndInterfaces.