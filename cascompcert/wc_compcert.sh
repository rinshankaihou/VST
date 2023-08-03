#!/bin/sh
coqwc \
cfrontend/Cshmgenproof.v \
cfrontend/Cminorgenproof.v \
backend/Selectionproof.v \
backend/RTLgenproof.v \
backend/Tailcallproof.v \
backend/Renumberproof.v \
backend/Allocproof.v \
backend/Tunnelingproof.v \
backend/Linearizeproof.v \
backend/CleanupLabelsproof.v \
backend/Stackingproof.v \
x86/Asmgenproof.v