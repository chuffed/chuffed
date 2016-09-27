MZN2FZN = mzn2fzn -G ../../../../../lazy-clause/flatzinc/mznlib
MZNBENCHDIR = ~/g12/g12/zinc/benchmarks/minizinc

STILL_LIFE = 7x7 8x8 9x9
STILL_LIFE_FZN = $(STILL_LIFE:%=still_life/%.fzn)

NONOGRAM = #non_awful_1 non_awful_2 non_awful_3 non_awful_4 non_awful_5 non_med_1 non_med_2 non_med_3 non_med_4
NONOGRAM_FZN = $(NONOGRAM:%=nonogram/%.fzn)

RECTPACKING = rpp19_false rpp20_true rpp21_false rpp22_true rpp24_false rpp26_true rpp30_false
RECTPACKING_FZN = $(RECTPACKING:%=rectangle-packing/data_square/%.fzn)

GOLFERS = golfers_5_3_6 golfers_5_5_6 golfers_6_6_3
GOLFERS_FZN = $(GOLFERS:%=golfers/%.fzn)

PENTOMINOES = 01 02 03 04 05 06 07
PENTOMINOES_FZN = $(PENTOMINOES:%=pentominoes/%.fzn)

RADIATION = 01 02 03 04 05 06 07 08 09
RADIATION_FZN = $(RADIATION:%=radiation/%.fzn)

RCPSP = 00 01 02 03 04 05 06 07 08 09
RCPSP_FZN = $(RCPSP:%=rcpsp/%.fzn)

SHORTPATH = 00 01 02 03 04 05 06 07 08 09
SHORTPATH_FZN = $(SHORTPATH:%=shortest_path/%.fzn)

TEMPLATEDES = catfood_3
TEMPLATEDES_FZN = $(TEMPLATEDES:%=template_design/%.fzn)

SLOWCONVERGE = 0500 0600 0700 0800 0900
SLOWCONVERGE_FZN = $(SLOWCONVERGE:%=slow_convergence/%.fzn)

CURRICULUM = curriculum_8 curriculum_10 curriculum_12
CURRICULUM_FZN = $(CURRICULUM:%=curriculum/%.fzn)

QCP = qcp-25-264-0_ext qcp-25-264-1_ext qcp-25-264-2_ext qcp-25-264-3_ext qcp-25-264-4_ext qcp-25-264-5_ext qcp-25-264-6_ext qcp-25-264-7_ext qcp-25-264-8_ext qcp-25-264-9_ext qcp-25-264-10_ext qcp-25-264-11_ext qcp-25-264-12_ext qcp-25-264-13_ext qcp-25-264-14_ext
QCP_FZN = $(QCP:%=QCP/%.fzn)

BLACKHOLE = 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19
BLACKHOLE_FZN = $(BLACKHOLE:%=black-hole/%.fzn)

FILLOMINO = 01 07 08 11 12 13 14 15 16 17 18 19 20 21 22
FILLOMINO_FZN = $(FILLOMINO:%=fillomino/%.fzn)

P1F = 2 3 4 5 6 7 8 9 10 11 12
P1F_FZN = $(P1F:%=p1f/%.fzn)

ROSTER = chicroster_dataset_1 chicroster_dataset_2 chicroster_dataset_3 chicroster_dataset_4 chicroster_dataset_5 chicroster_dataset_6 chicroster_dataset_7 chicroster_dataset_8 chicroster_dataset_9 chicroster_dataset_10 chicroster_dataset_11 chicroster_dataset_12 chicroster_dataset_14 chicroster_dataset_17 chicroster_dataset_large_13 chicroster_dataset_large_15 chicroster_dataset_large_16 chicroster_dataset_large_18 chicroster_dataset_large_19
ROSTER_FZN = $(ROSTER:%=roster/%.fzn)

DEBRUIJN = 02_03 02_07 02_08 02_09 02_10 03_06 03_07 04_06
DEBRUIJN_FZN = $(DEBRUIJN:%=debruijn_binary/%.fzn)

TRUCKING = 01 02 03 04 05 06
TRUCKING_FZN = $(TRUCKING:%=trucking/%.fzn)

NMSEQ = 020 040 060 080 100 150 200
NMSEQ_FZN = $(NMSEQ:%=nmseq/%.fzn)

QUASIGROUP = 05 06 07 08 09
QUASIGROUP_FZN = $(QUASIGROUP:%=quasigroup7/%.fzn)

TALENT = film103 film105 film114 film116 film118 film119 MobStory
TALENT_FZN = $(TALENT:%=talent_scheduling/medium/%.fzn)

OPENSTACKS = gp50by50_1 problem_15_15_1 wbo_15_30_1 problem_20_20_1 problem_30_15_1 wbop_30_15_1
OPENSTACKS_FZN = $(OPENSTACKS:%=open_stacks/%.fzn)

NSP = 20 40 60 80 100
NSP_FZN = $(NSP:%=nsp/data/period_14/%.fzn) $(NSP:%=nsp/data/period_28/%.fzn)

ALL_FZN = $(STILL_LIFE_FZN) $(NONOGRAM_FZN) $(RECTPACKING_FZN) $(GOLFERS_FZN) \
	$(PENTOMINOES_FZN) $(RADIATION_FZN) $(RCPSP_FZN) $(SHORTPATH_FZN) \
	$(TEMPLATEDES_FZN) $(SLOWCONVERGE_FZN) $(CURRICULUM_FZN) $(QCP_FZN) \
	$(BLACKHOLE_FZN) $(FILLOMINO_FZN) $(P1F_FZN) $(ROSTER_FZN) $(DEBRUIJN_FZN) \
	$(TRUCKING_FZN) $(NMSEQ_FZN) $(QUASIGROUP_FZN) $(TALENT_FZN) $(OPENSTACKS_FZN) \
	$(NSP_FZN)


all : $(ALL_FZN)

$(STILL_LIFE_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/still_life/still_life.mzn
	$(MZN2FZN) -o $@ $^

$(NONOGRAM_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/nonogram/non.mzn
	$(MZN2FZN) -o $@ $^

$(RECTPACKING_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/rectangle-packing/rect_packing.mzn
	$(MZN2FZN) -o $@ $^

$(GOLFERS_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/golfers/golfers1.mzn
	$(MZN2FZN) -o $@ $^

$(PENTOMINOES_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/pentominoes/pentominoes-int.mzn
	$(MZN2FZN) -o $@ $^

$(RADIATION_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/radiation/radiation.mzn
	$(MZN2FZN) -o $@ $^

$(RCPSP_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/rcpsp/rcpsp.mzn
	$(MZN2FZN) -o $@ $^

$(SHORTPATH_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/shortest_path/shortest_path.mzn
	$(MZN2FZN) -o $@ $^

$(TEMPLATEDES_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/template_design/template_design.mzn
	$(MZN2FZN) -o $@ $^

$(SLOWCONVERGE_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/slow_convergence/slow_convergence.mzn
	$(MZN2FZN) -o $@ $^

$(CURRICULUM_FZN) : %.fzn : $(MZNBENCHDIR)/%.mzn
	$(MZN2FZN) -o $@ -I $(MZNBENCHDIR)/curriculum $^

$(QCP_FZN) : %.fzn : $(MZNBENCHDIR)/%.mzn
	$(MZN2FZN) -o $@ $^

$(BLACKHOLE_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/black-hole/black-hole.mzn
	$(MZN2FZN) -o $@ $^

$(FILLOMINO_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/fillomino/fillomino.mzn
	$(MZN2FZN) -o $@ $^

$(P1F_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/p1f/p1f.mzn
	$(MZN2FZN) -o $@ $^

$(ROSTER_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/roster/roster_model.mzn
	$(MZN2FZN) -o $@ $^

$(DEBRUIJN_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/debruijn_binary/debruijn_binary.mzn
	$(MZN2FZN) -o $@ $^

$(TRUCKING_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/trucking/trucking_no_colgen.mzn
	$(MZN2FZN) -o $@ $^

$(NMSEQ_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/nmseq/nmseq.mzn
	$(MZN2FZN) -o $@ $^

$(QUASIGROUP_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/quasigroup7/quasigroup7.mzn
	$(MZN2FZN) -o $@ $^

$(TALENT_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/talent_scheduling/talent_scheduling_alt.mzn
	$(MZN2FZN) -o $@ $^

$(OPENSTACKS_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/open_stacks/open_stacks_01.mzn
	$(MZN2FZN) -o $@ $^

$(NSP_FZN) : %.fzn : $(MZNBENCHDIR)/%.dzn $(MZNBENCHDIR)/nsp/nsp_1.mzn
	$(MZN2FZN) -o $@ -I $(MZNBENCHDIR)/nsp $^








clean :
	rm -rf $(ALL_FZN)







