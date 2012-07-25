import std.algorithm;
import std.stdio;
import std.file;

import sat;

void main(string[] args)
{
    foreach(file; args[1..$])
    {
        string dimacs = readText(file);
        Solver solv = new Solver();
        solv.parse(dimacs);
        bool res = solv.solve();
        if(res)
        {
                writeln("SAT");
                writeln(map!(a => a == 1 ? 1 : 0)(solv.model));
        }
        else
            writeln("UNSAT");
    }
}
