Require Import Coqlib Maps Errors Globalenvs AST.
Require Import Values Memory Globalenvs Events Smallstep Blockset InjRels Footprint.

Require Import val_casted CUAST GMemory FMemory InteractionSemantics
        Blockset LDSim SeqCorrect.
Require Import Lia.

Require Import SpecLang SpecLangSim.

Local Open Scope error_monad_scope.

Definition id_trans_speclang: @seq_comp speclang speclang :=
  fun cu => assertion (nodup_gd_ident (cu_defs cu));
           assertion (nodup_ef (cu_defs cu));
           OK cu.

Theorem id_trans_correct: seq_correct id_trans_speclang.
Proof.
  unfold seq_correct.
  unfold id_trans_speclang.
  intros. monadInv H. 
  split; auto. 
  apply speclangsim.
Qed.