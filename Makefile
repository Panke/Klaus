sources = sat.d sattest.d lupe.d testutils.d
dev: $(sources) 
	dmdgit $(FLAGS) -ofsat -debug -unittest -g sat.d sattest.d lupe.d testutils.d
