#!/bin/sh
coqwc \
concurrency/comp_correct/cfrontend/cshmgen_proof.v \
concurrency/comp_correct/cfrontend/cminorgen_proof.v \
concurrency/comp_correct/backend/selection_proof.v \
concurrency/comp_correct/backend/rtlgen_proof.v \
concurrency/comp_correct/backend/tailcall_proof.v \
concurrency/comp_correct/backend/renumber_proof.v \
concurrency/comp_correct/backend/alloc_proof.v \
concurrency/comp_correct/backend/tunneling_proof.v \
concurrency/comp_correct/backend/linearize_proof.v \
concurrency/comp_correct/backend/cleanuplabels_proof.v \
concurrency/comp_correct/backend/stacking_proof.v \
concurrency/comp_correct/backend/asmgen_proof.v