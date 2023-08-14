Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UMLang.ExecGenerator.

Require Import EIP20.
Require Import Common.
Require Import UrsusProofs.
Import EIP20.


Lemma constructor_ls_template_exec_correct: forall (_initialAmount :  uint256) 
                                                   (_tokenName :  string) 
                                                   (_decimalUnits :  uint8) 
                                                   (_tokenSymbol :  string)
                                                   (l : LedgerLRecord rec),
      exec_state (Uinterpreter (@constructor rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l = 
      exec_state (Uinterpreter (@constructor_ls_template rec def _ _ _ _initialAmount _tokenName _decimalUnits _tokenSymbol)) l.
Proof.
  intros.
  unfold constructor.
  unfold constructor_ls_template.
  auto.
Qed.