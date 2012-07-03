import std.stdio;

import probat.all;


void main(string[] argv)
{
	auto runner = new StandAloneTestRunner(argv);
	runner.run();
}
