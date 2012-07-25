
PROBAT ?= /home/tobias/projects/
PROBATOBJ = $(PROBAT)probat/*.d
jflags = -J.
commonobj = sat.d sattest.d testinstances.d
common = $(commonobj) $(PROBATOBJ)
main = main.d
testmain = testmain.d
DC ?= dmd
commonflags = -w -I$(PROBAT) $(jflags)

testfiles = sat.inst unsat.inst

$(testfiles):
	find  instances/unsat -maxdepth 2 -iname "*cnf" > unsat.inst
	find instances/sat -iname "*cnf" > sat.inst

dev: $(common) $(testmain) $(testfiles) 
	${DC} $(commonflags) -ofdev -debug -unittest -g  $(FLAGS) $(common) $(testmain)  

debug: $(common) $(testmain) $(testfiles)
	${DC} -ofdebug -release -g $(commonflags) $(FLAGS) $(common) $(testmain) 

release: $(common) $(main)
	${DC} $(commonflags) -ofsat -release -O -inline $(FLAGS) $(common) $(main) 
