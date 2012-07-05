
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
		solv.solve();
	}
} 
