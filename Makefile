dev: sat.d sattest.d lupe.d testutils.d
	dmdgit -ofsat -debug -unittest -g sat.d sattest.d lupe.d testutils.d
