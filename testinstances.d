import probat.all;

import std.conv, std.file, std.string, std.array;

import sat;

unittest
{
    string testfiles = import("unsat.inst");
    foreach(size_t i, string line; testfiles.splitLines())
    {
        string dimacs = readText(line);
        string desc = "satlib, unsat, " ~ line;
        string tag = "SU-" ~ to!string(i);
        // need to build a closure cause of bug
        testCase(desc, ((string dimacs_) =>
        {
        	Solver solv = new Solver;
                solv.parse(dimacs_);
                assEq(solv.solve(), true);
        })(dimacs), tag);
    }

}
