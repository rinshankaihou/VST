# make file modified to include concurrency extensions.

#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU General Public License as published by  #
#  the Free Software Foundation, either version 2 of the License, or  #
#  (at your option) any later version.  This file is also distributed #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

include Makefile.config

COQCOPTS+=-w -notation-overridden,-redundant-canonical-projection

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif
CONCUR_DIRS  = \
  concurrency concurrency/framework concurrency/framework/NPDefs concurrency/framework/NPDefs/DRFLemmas\
  concurrency/framework/GlobUSim concurrency/framework/GlobDSim \
  concurrency/framework/Compositionality concurrency/comp_correct/cfrontend \
  concurrency/common concurrency/comp_correct concurrency/comp_correct/phases \
  concurrency/comp_correct/localize \
  concurrency/comp_correct/backend \
  concurrency/comp_correct/x86 \
  concurrency/x86TSO concurrency/x86TSO/lock_proof \

DIRS=lib common $(ARCHDIRS) backend cfrontend driver debug\
  flocq/Core flocq/Prop flocq/Calc flocq/Appli exportclight \
  cparser cparser/validator $(CONCUR_DIRS)


RECDIRS=lib common $(ARCHDIRS) backend cfrontend driver flocq exportclight cparser \
  concurrency 

COQINCLUDES=$(foreach d, $(RECDIRS), -R $(d) compcert.$(d))

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Concurrency-Part

CCOMMON =\
  Memperm.v Blockset.v GMemory.v Footprint.v InteractionSemantics.v         \
  Injections.v MemClosures.v GAST.v LDSimDefs.v GlobDefs.v ETrace.v         \
  GlobSemantics.v DRF.v ReachClose.v SeqCorrect.v LDSim.v ListDom.v\
  FMemPerm.v FMemory.v FMemOpFP.v FMemtype.v MemAux.v GlobSemantics_Lemmas.v FMemLemmas.v

CCOMP =\
  val_casted.v FCop.v FMemAux.v Cop_fp.v CminorLang.v CminorWD.v AsmLang.v AsmWD.v AsmDET.v \
  MemClosures_local.v LDSimDefs_local.v LDSim_local.v MemInterpolant.v Localize.v  ValRels.v \
  IS_local.v MemOpFP.v ValFP.v Cop_fp_local.v DetLemma.v VundefInj.v FiniteMaps.v\
  ClightLang.v\
  CminorLocalize.v AsmLocalize.v LDSim_local_transitive.v\
  AsmIDTransCorrect.v CompCorrect.v \
  LangProps.v DisableDebug.v InjRels.v renumber.v renumber_proof.v\
  Cminor_op_footprint.v Op_fp.v infp.v \
  CUAST.v \
  helpers.v Cminor_local.v selectop_proof.v splitlong_proof.v selectlong_proof.v selectdiv_proof.v \
  selection.v selection_proof.v\
  CminorSel_local.v rtlgen.v rtlgen_proof.v \
  RTL_local.v RTLtyping_local.v \
  tailcall.v tailcall_proof.v \
  allocation.v alloc_proof.v \
  LTL_local.v  tunneling.v tunneling_proof.v linearize.v linearize_proof.v \
  cleanuplabels.v cleanuplabels_proof.v \
  Linear_local.v Lineartyping_local.v loadframe.v \
  cleanuplabels.v \
  Mach_local.v stacking.v stacking_proof.v \
  ASM_local.v asmgen.v asmgen_proof0.v asmgen_proof1.v  asmgen_proof.v \
  Clight.v ClightLang.v ClightWD.v Clight_local.v cshmgen.v cshmgen_proof.v cminorgen.v cminorgen_proof.v  Csharpminor_local.v \
  ClightLocalize.v 

CFRAME =\
  NPSemantics.v NPDet.v NPDRF.v NPEquiv.v GSimDefs.v GlobUSim.v SimDRF.v\
  USimDRF.v GDefLemmas.v TypedSemantics.v FPLemmas.v RefineEquiv.v SmileReorder.v ConflictReorder.v PRaceLemmas.v DRFLemmas.v\
  GlobUSimRefine.v GlobDSim.v GlobSim.v Flipping.v SimEtr.v\
  AuxLDSim.v Invs.v Compositionality.v Soundness.v \
  AuxLDSim.v Init.v

TSOREF =\
  SpecLang.v SpecLangIDtrans.v SpecLangWDDET.v \
  TSOMem.v AsmTSO.v TSOGlobSem.v TSOGlobUSim.v TSOAuxDefs.v\
  RGRels.v LockSim.v ClientSim.v AsmClientSim.v ObjectSim.v TSOMemLemmas.v TSOStepAuxLemmas.v SpecLangSim.v \
  code.v InvRG.v LibTactics.v AuxTacLemmas.v MemLemmas.v ObjRGIProp.v LockAcqProof.v LockRelProof.v ObjLemmas.v LockProof.v \
  SCSemLemmas.v TSOSemLemmas.v \
  TSOCompInvs.v TSOCompositionality.v \
  FinalTheoremExt.v

CONCUR =$(CCOMMON) $(CCOMP) $(CFRAME) $(TSOREF) FinalTheorem.v Languages.v FinalTheoremExt.v 
# Flocq

WORKINGON = $(CONCUR) 

FLOCQ=\
  Fcore_Raux.v Fcore_Zaux.v Fcore_defs.v Fcore_digits.v                     \
  Fcore_float_prop.v Fcore_FIX.v Fcore_FLT.v Fcore_FLX.v                    \
  Fcore_FTZ.v Fcore_generic_fmt.v Fcore_rnd.v Fcore_rnd_ne.v                \
  Fcore_ulp.v Fcore.v                                                       \
  Fcalc_bracket.v Fcalc_digits.v Fcalc_div.v Fcalc_ops.v                    \
  Fcalc_round.v Fcalc_sqrt.v                                                \
  Fprop_div_sqrt_error.v Fprop_mult_error.v Fprop_plus_error.v              \
  Fprop_relative.v Fprop_Sterbenz.v                                         \
  Fappli_rnd_odd.v Fappli_double_round.v Fappli_IEEE.v Fappli_IEEE_bits.v

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Archi.v Fappli_IEEE_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v 				\
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v BoolEqual.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Unityping.v \
  Separation.v

# Back-end modules (in backend/, $(ARCH)/)

BACKEND=\
  Cminor.v Op.v CminorSel.v \
  SelectOp.v SelectDiv.v SplitLong.v SelectLong.v Selection.v \
  SelectOpproof.v SelectDivproof.v SplitLongproof.v \
  SelectLongproof.v Selectionproof.v \
  Registers.v RTL.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v \
  Tailcall.v Tailcallproof.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  Renumber.v Renumberproof.v \
  RTLtyping.v \
  Kildall.v Liveness.v \
  ValueDomain.v ValueAOp.v ValueAnalysis.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CSEdomain.v CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  NeedDomain.v NeedOp.v Deadcode.v Deadcodeproof.v \
  Unusedglob.v Unusedglobproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v LTL.v \
  Allocation.v Allocproof.v \
  Tunneling.v Tunnelingproof.v \
  Linear.v Lineartyping.v \
  Linearize.v Linearizeproof.v \
  CleanupLabels.v CleanupLabelsproof.v \
  Debugvar.v Debugvarproof.v \
  Mach.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v Asmgenproof.v

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v ClightBigstep.v SimplLocals.v SimplLocalsproof.v \
  Cshmgen.v Cshmgenproof.v \
  Csharpminor.v Cminorgen.v Cminorgenproof.v

# LR(1) parser validator

PARSERVALIDATOR=Alphabet.v Interpreter_complete.v Interpreter.v \
  Validator_complete.v Automaton.v Interpreter_correct.v Main.v \
  Validator_safe.v Grammar.v Interpreter_safe.v Tuples.v

# Parser

PARSER=Cabs.v Parser.v

# Putting everything together (in driver/)

DRIVER=Compopts.v Compiler.v Complements.v

# All source files

FILES=$(VLIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(PARSERVALIDATOR) $(PARSER) $(WORKINGON) \
  $(CCOMMON) $(CFRAME) $(CCOMP) $(TSOREF)
  
# Generated source files

GENERATED=\
  $(ARCH)/ConstpropOp.v $(ARCH)/SelectOp.v $(ARCH)/SelectLong.v \
  backend/SelectDiv.v backend/SplitLong.v \
  cparser/Parser.v
default:
	@test -f .depend || $(MAKE) depend
	$(MAKE) concur
work : $(WORKINGON:.v=.vo)
concur : $(CONCUR:.v=.vo)

clean_concur:
	rm -f $(patsubst %, %/*.vo, $(CONCUR_DIRS))
	rm -f $(patsubst %, %/.*.aux, $(CONCUR_DIRS))
all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CLIGHTGEN),true)
	$(MAKE) clightgen
endif


proof:	$(FILES:.v=.vo)

# Turn off some warnings for compiling Flocq
flocq/%.vo: COQCOPTS+=-w -deprecated-implicit-arguments

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

ccomp: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp
ccomp.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp.byte

clightgen: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen
clightgen.byte: .depend.extr compcert.ini exportclight/Clightdefs.vo driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr clightgen.byte

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof extraction runtime FORCE

documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -w +a-29 -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex -q doc/coq2html.mll

tools/ndfun: tools/ndfun.ml
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml
tools/modorder: tools/modorder.ml
	ocamlopt -o tools/modorder str.cmxa tools/modorder.ml

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod -w $*.v

compcert.ini: Makefile.config
	(echo "stdlib_path=$(LIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
         echo "struct_passing_style=$(STRUCT_PASSING)"; \
         echo "struct_return_style=$(STRUCT_RETURN)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > compcert.ini

driver/Version.ml: VERSION
	cat VERSION \
	| sed -e 's|\(.*\)=\(.*\)|let \1 = \"\2\"|g' \
	>driver/Version.ml

cparser/Parser.v: cparser/Parser.vy
	$(MENHIR) --coq cparser/Parser.vy

depend: $(GENERATED) depend1

depend1: $(FILES) exportclight/Clightdefs.v
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

install:
	install -d $(BINDIR)
	install -m 0755 ./ccomp $(BINDIR)
	install -d $(SHAREDIR)
	install -m 0644 ./compcert.ini $(SHAREDIR)
	install -d $(MANDIR)/man1
	install -m 0644 ./doc/ccomp.1 $(MANDIR)/man1
	$(MAKE) -C runtime install
ifeq ($(CLIGHTGEN),true)
	install -m 0755 ./clightgen $(BINDIR)
endif

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f doc/coq2html.ml doc/coq2html doc/*.cm? doc/*.o
	rm -f driver/Version.ml
	rm -f compcert.ini
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

# Problems with coqchk (coq 8.5pl1):
# Integers.Int.Z_mod_modulus_range takes forever to check
# compcert.lib.Floats.Float.of_longu_from_words takes forever to check
# compcert.backend.SelectDivproof.divs_mul_shift_2 takes forever to check

check-proof: $(FILES)
	$(COQCHK) -admit Integers -admit Floats -admit SelectDivproof 

print-includes:
	@echo $(COQINCLUDES)

-include .depend

FORCE:
