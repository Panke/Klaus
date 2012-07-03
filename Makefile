sources = sat.d sattest.d lupe.d testutils.d
dev: $(sources) 
	dmdgit  -ofsat -debug -unittest -g $(FLAGS) sat.d sattest.d lupe.d testutils.d

debug: $(sources)
	dmdgit  -ofsat -release -g $(FLAGS) sat.d sattest.d lupe.d testutils.d
