module lupe;

import std.stdio;
import std.exception;
import std.algorithm;
import std.conv;
import std.variant;
import std.range;
import std.string;

enum TestEnum : long {A, B, C};


enum State { NotRun, Success, Failure };


class TestRunner
{
    struct Test
    {
        void delegate() dg;
        string desc;
        State state;

        this(void delegate() dg, string desc)
        {
            this.desc = desc;
            this.dg = dg;
            state = State.NotRun;
        }
    }

    static TestRunner self_;
    Test[] tests;

    private this() {};

    @property
    static TestRunner instance()
    {
        if(self_ is null)
        {
            self_ = new TestRunner();
            return self_;
        }
        return self_;
    }

    void register(Test tmp)
    {
        tests ~= tmp;
    }


    bool run()
    {
        auto count = tests.length;
        size_t failcount = 0;
        writefln("Running %s unit tests", count);
        writeln("--------------------------");
        foreach(ulong i; 0 .. tests.length)
        {
            try {
                writef("Running tests #%s: %s ... ", i, tests[i].desc);
                tests[i].dg();
                writeln("Success!");
                tests[i].state = State.Success;
            }
            catch(Throwable e) {

                auto app = appender!string();
                app.put("Failure! ");
                app.put("Reason:\n");
                app.put(e.msg);
                app.put(format("\tOn line %s in file %s", e.line, e.file));
                debug app.put(e.info.toString());
                writeln(app.data);
                tests[i].state = State.Failure;
                failcount ++;
            }
        }
        writeln("--------------------------");
        writefln("Ran %s tests. %s failed", tests.length, failcount);
        return failcount == 0;
    }

}

bool runner()
{
    import core.runtime;
    Runtime.moduleUnitTester = null;
    bool oldSuccess = runModuleUnitTests();
    bool newSuccess = TestRunner.instance.run();
    return oldSuccess && newSuccess;
}

void testCase(string name, void delegate() dg)
{
    TestRunner.Test tmp = TestRunner.Test(dg, name);
    TestRunner.instance.register(tmp);
}

void registerTestRunner()
{
    import core.runtime;
    Runtime.moduleUnitTester = &runner;
}


/* test helper */

void assertEqual(T, U)(auto ref T lhs, auto ref U rhs,
                       string file = __FILE__, size_t line = __LINE__)
{
    import core.exception;
    bool equal = lhs == rhs;
    if(!equal)
    {
        AssertError err = new AssertError(file, line);
        err.msg = "[" ~ to!string(lhs) ~ "] != [" ~ to!string(rhs) ~ "]";
        throw err;
    }
}
