import probat.all;

import std.conv, std.file, std.string, std.array;

import sat;

bool verify(string dimacs, Value[] model)
{
    Solver solv = new Solver;
    solv.parse(dimacs);
    return solv.verify(model);
}

void create_tests_from_files(string filespec, string descprefix,
                             string tagprefix, bool satisfiable)
{
    string testfiles = filespec;
    foreach(size_t i, string line; testfiles.splitLines())
    {
        string dimacs = readText(line);
        string desc = descprefix ~ line;
        string tag = tagprefix ~ to!string(i);
        // need to build a closure cause of bug
        testCase(desc, ((string dimacs_) =>
        {
                Solver solv = new Solver;
                solv.parse(dimacs_);
                bool sat = solv.solve();
                assEq(sat, satisfiable);
                assert(!sat || verify(dimacs_, solv.model));
        })(dimacs), tag);
    }
}
// unsat instances
unittest
{
    string testfiles = import("unsat.inst");
    create_tests_from_files(testfiles, "satlib, unsat, ",
                            "UNSAT-", false);
}

// satisfiable instances
unittest
{
    string testfiles = import("sat.inst");
    create_tests_from_files(testfiles, "satlib, sat, ", "SAT-", true);
}