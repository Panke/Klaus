
PROBAT = /home/tobias/projects/
PROBATOBJ = $(PROBAT)probat/*.d
jflags = -J.
commonobj = sat.d sattest.d testinstances.d
common = $(commonobj) $(PROBATOBJ)
main = main.d
testmain = testmain.d
DC = dmdgit
commonflags = -w -I$(PROBAT) $(jflags)

dev: $(common) $(testmain) 
	dmdgit  $(commonflags) -ofdev -debug -unittest -g  $(FLAGS) $(common) $(testmain)  

debug: $(common) $(testmain)
	dmdgit  -ofdebug -release -g $(commonflags) $(FLAGS) $(common) $(testmain) 

release: $(common) $(main)
	dmdgit $(commonflags) -ofsat -release -O -inline $(FLAGS) $(common) $(main) 
