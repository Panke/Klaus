module sat;

import std.conv;
import std.file;
import std.exception;
import std.stdio;
import std.algorithm;
import std.format;
import std.range;
import std.string;
import std.container;
import std.typetuple;
import std.typecons;
import std.c.stdlib;
import std.array;

import sattest;

struct Sign
{
    enum _Val : bool { Pos = true, Neg = false };

    static immutable Sign Pos = Sign(_Val.Pos);
    static immutable Sign Neg = Sign(_Val.Neg);

    bool sgn = Pos;
    alias sgn this;

    this(bool sign) { sgn = sign; }

    Sign opUnary(string op)() if(op == "~")
    {
        return Sign(!sgn);
    }
}

unittest
{
    Sign sign1 = true;
    Sign sign2 = false;
    Sign sign3 = sign1;
    assert(sign1 != sign2);
    assert(sign1 == sign3);
    assert(~sign1 == sign2);
    assert(~sign1 == ~sign3);
    assert(~sign1 == false);
}


// Variables are indexes into other datastructures
struct Var
{
    size_t idx;
    alias idx this;
}

size_t index(Literal lit) pure nothrow
out(result)
{
    assert((result - 2*lit.var) <= 1);
}
body
{
    return 2*lit.var + lit.sign;
}

// Literals store the index for the variable and the sign
struct Literal
{
    Var var;
    Sign sign;

    Literal opUnary(string op)() if(op == "~")
    {
        return Literal(var, ~sign);
    }

    string toString()
    {
        auto app = appender!string();
        formattedWrite(app, "L(%d, %s)", var, sign ? "t" : "f");
        return app.data;
    }
}

unittest
{
    Literal lit = { Var(0), Sign(false) };
    assert(~~lit == lit);
    assert(~lit == Literal(Var(0), Sign(true)));
    static assert(is(typeof(~lit) == Literal));
}


// a clause is basically a set of literals
struct Clause
{
    Literal[] literals;
//     alias literals this;
    string toString() { return to!string(literals); }
}

unittest
{
    Literal[] input = [ Literal(Var(0), Sign(true)),
                        Literal(Var(1), Sign(false)) ];
    Clause* clause = new Clause;
    clause.literals ~= input;

    assert(equal(clause.literals, input));
    assert(clause.literals is ((*clause).literals));
//     assert(equal(clause, input));
    assert(!(clause.literals is input));
}



// A variable can be true, false or unassigned
// Type for value of literal/variable under given
// assignment

/**
    ~False = True
    ~True = False
    ~Undef = Undef
*/
enum Value : byte { Undef = 0, False = -1, True = 1}

Value neg(Value op) pure nothrow
{
    return cast(Value)(op * -1);
}


unittest
{
    assert(neg(Value.Undef) == Value.Undef);
    assert(neg(Value.True) == Value.False);
    assert(neg(Value.False) == Value.True);
    assert(neg(Value.Undef) == Value.Undef);
}


class Solver
{
// TODO Report bug, that __returnLabel is
    // undefined if invariant is used

    @property curDeLevel() { return decisions.length; }


    /**
        add a variable to the solver.
    */
    Var addVariable()
    {
        // add new variable
        Var newOne = Var(varCount);
        varCount++;
        return newOne;
    }

    /**
        add a clause to the solver

        we don't support unit clauses
    */
    void addClause(Literal[] literals)
    in
    {
        assert(literals.length >= 0, "empty clause not allowed");
    }
    body
    {
        /* handle unit clauses differently */
        if(literals.length == 1)
            addAssumption(literals[0]);
        else
        {
            Clause* newClause = new Clause;
            newClause.literals ~= literals.dup;
            clauses ~= newClause;
        }
    }

    /**
        initialize datastructures, i.e.
            - assignments
            - variable queue
            - propagation queue
            - (...)
    */
    void initData()
    out
    {
        assert(checkWatchers());
        foreach(val;assigns) { assert(val == Value.Undef); }
        assert(assigns.length == varCount);
        assert(deLevels.length == varCount);
    }
    body
    {
        // datastructures which size is bounded by the number of variables
        // reserve space for there maximum size to avoid allocations
        assigns.length = varCount;
        reasons.length = varCount;
        deLevels.length = varCount;
        deLevels[] = -1;
        initWatchers();
    }

    bool checkWatchers()
    {
        int[Clause*] count;
        foreach(Clause*[] perLiteral; watchers._watchlist)
        {
            foreach(Clause* cl; perLiteral)
            {
                if( cl in count )
                    count[cl] += 1;
                else
                    count[cl] = 1;
            }
        }
        foreach(Clause* cl; clauses)
            if(count[cl] != 2)
                return false;

        return true;
    }

    void initWatchers()
    {
        watchers.expand(varCount * 2);
        // make the first two literals of every clause watched
        foreach(cl; clauses)
        {
            assert(cl.literals.length >= 2, "no unit clause");
            foreach(i; 0 .. 2)
            {
                Literal lit = cl.literals[i];
                watchers.watch(lit, cl);
            }
        }
    }


    /**
        returns true if a model for the clauses can be found,
        false otherwise
    */
    bool solve()
    {
        initData();
        foreach(ass; assumptions)
            assume(ass);
        return search();
    }

    bool search()
    body
    {
        // perform chronological backtracking with propagation
        // variables are picked in order (for now) and true is tried first
        while(true)
        {
            auto propResult = unitPropagation();
            if(propResult.conflict)
            {
                if(curDeLevel == 0)
                {
                    debug(search) writeln("not satable");
                    return false;
                }
                auto aconf = analyseConflict(propResult.conflictClause);
                debug(search) writefln("backtrack to %s", aconf.blevel);
                backtrack(aconf.blevel);
                Clause* cls = learn(aconf.learned);
                assume(aconf.asserting, cls);
            }
            else // no conflict
            {
                // all variables assigned AND no conflict ==> solution found
//                debug(search) writefln("trail:\n %s", trailToString());
                if(trail.length == varCount)
                    return true;

                // choose next variable to assign.
                // if the top element is assumend to be true, assume it should
                // be false
                Literal assumption = chooseLit();
                decide(assumption);
            }
        }
    }

    /*
     *do all desicions up to but not including toLevel
     */
    void backtrack(size_t toLevel)
    in
    {
        assert(toLevel >= 0);
    }
    body
    {

        decisions.length = toLevel;
        while(!trail.empty && trail.back.dlevel > toLevel)
        {
            Var v = trail.back.lit.var;
            assigns[v] = Value.Undef;
            reasons[v] = null;
            deLevels[v] = -1;
            trail.popBack();
        }
    }

    alias Tuple!(size_t, "blevel", Literal[], "learned", Literal, "asserting") AConf;
    AConf analyseConflict(Clause* clause)
    in
    {
        assert(clause !is null);
        assert(count!(a => deLevels[a.var] == curDeLevel)(clause.literals) > 0);
    }
    body
    {

        Literal[] lits = clause.literals.dup;
        debug(analyse) writefln("Conflicting Clause is %s", lits);

        // we can use the trail for breadth first search
        size_t idx = trail.length - 1;
        while(true)
        {
            // count number of literals from current d-level
            auto pred = (Literal a) => deLevels[a.var] == curDeLevel;
            auto numOfCurDeLevel = count!pred(lits);
            if(numOfCurDeLevel == 1)
            {
                debug(analyse) writeln("UIP");
                break;
            }

            auto curElem = trail[idx];
            idx--;
            if(!canFind(lits, curElem.lit) && !canFind(lits, ~curElem.lit))
                continue;
            assert(curElem.dlevel == curDeLevel);
            Clause* reason = reasons[curElem.lit.var];
            if(reason is null)
            {
                debug(analyse) writeln("reason null");
                break;
            }
            // decision variable reached. If this happend we should usually
            // have had a UIP already ?
            debug(analyse) writefln("resolving using %s", curElem.lit);
            lits = resolve(reason.literals, lits, curElem.lit);
        }

		debug(analyse) writefln("Learned Clause at dlevel %s is %s", curDeLevel, lits);
		debug(analyse) writeln(map!(a => deLevels[a.var])(lits).array());
		size_t blevel = 0;
		Literal asserting;
		foreach(lit; lits)
		{
			if(deLevels[lit.var] > blevel && deLevels[lit.var] != curDeLevel)
				blevel = deLevels[lit.var];
			if(deLevels[lit.var] == curDeLevel)
				asserting = lit;
		}
		return AConf(blevel, lits, asserting);
    }

    Literal[] resolve(Literal[] pos, Literal[] neg, Literal resolvent)
    {
        bool[] seen = new bool[varCount * 2];
        seen[] = false;

        Literal[] result;
        foreach(lit; pos)
        {
            if(lit != resolvent && !seen[lit.index])
            {
                seen[lit.index] = true;
                result ~= lit;
            }
        }
        foreach(lit; neg)
        {
            if(lit != ~resolvent && !seen[lit.index])
            {
                seen[lit.index] = true;
                result ~= lit;
            }
        }
        debug(resolve) writefln("resolve %s and\n%s to \n %s", pos, neg, result);
        return result;

    }

    Literal chooseLit()
    {
        for(int i = 0; i < varCount; ++i)
        {
            if(assigns[i] == Value.Undef)
                return Literal(Var(i), Sign(Sign.Pos));
        }
        throw new Exception("asking for unassigned var, but there is no");
    }

    bool decide(Literal lit)
    {
        decisions ~= lit;
        debug(decide) writefln("decide: %s at %s", lit, decisions.length);
        return assume(lit);
    }

    /**
        assume that a specific literal is true
    */
    bool assume(Literal lit, Clause* reason = null)
    {
        Value toSet = lit.sign == Sign.Pos ? Value.True: Value.False;
        debug(assume) writefln("assuming: %s = %s", lit.var, toSet);
        // check that the assumptions contradicts no previous knowledge
        if(assigns[lit.var] != Value.Undef)
        {
            if(assigns[lit.var] != toSet)
            {
                debug(assume) writeln("conflicting assignment");
                return false;
            }
            else
                return true;
        }

        // change assignment
        assigns[lit.var] = toSet;
        // enqueue for propagation
        propQ ~= lit;
        reasons[lit.var] = reason;
        // add to trail
        trail ~= (TrailElem(lit, curDeLevel));
        deLevels[lit.var] = curDeLevel;
        return true;
    }

    @property
    Value[] model()
    {
        return array(assigns);
    }

    /**
        propagate the last choosen variable
        and every new unit clause

        lit is the literal with it's correct sign, i.e. if we propagate
        the knowledge that x1 must be true under the current assignment, then
        lit is Literal(x1, Sign.Pos)

        return false if an conflict was found.
    */
    alias Tuple!(bool, "conflict", Clause*, "conflictClause") UProp;
    UProp unitPropagation()
    in
    {
        foreach(Clause* cl; clauses)
            assert(cl.literals.length >= 2);
    }
    out(result)
    {
        assert(!result.conflict || result.conflictClause !is null);
        assert(propQ.empty);
    }
    body
    {
        debug(uprop) writefln("starting unit-propagation,\n propQ is:\n%s", propQ);
        while(!propQ.empty)
        {
            Literal lit = ~(propQ.front);
            propQ.popFront();
            assert(value(lit) == Value.False);
            // iterate over all clauses, that watch lit
            Clause*[] watchingClauses = watchers[lit];
            debug(uprop) writefln("%s is watched by %s clauses:\n %s",
                                      lit,
                                      watchingClauses.length,
                                      map!"a.literals"(watchingClauses));
            foreach(Clause* cl; watchingClauses)
            {
                Literal[] lits = (*cl).literals;
                debug(uprop) writefln("prop %s to clause %s", lit, clauseString(lits));
                // swap lit into first place.
                if(lits[1] == lit)
                    swap(lits[0], lits[1]);

                size_t trueIdx = 0;
                size_t undefIdx = 0;
                // scan for true or undef literal from back
                foreach(size_t i, ref Literal curLit; lits)
                {
                    if(value(curLit) == Value.True)
                    {
                        trueIdx = i;
                        break;
                    }
                    if(value(curLit) == Value.Undef)
                    {
                        undefIdx = i;
                    }
                }

                // trueIdx > 0, clause is already fulfilled --> continue;
                if(trueIdx > 0)
                    continue;
                // if undefIdx == 1 -> no true and no other undef --> lits[1] can be assumed
                else if(undefIdx == 1)
                {
                    if(!assume(lits[1], cl))
                    {
                        propQ.length = 0;
                        return UProp(true, cl);
                    }
                }
                // some undef found (other than lits[1]), watch this literal
                else if(undefIdx > 1)
                {
                    watchers.release(lit, cl);
                    swap(lits[0], lits[undefIdx]);
                    watchers.watch(lits[0], cl);
                }
                // no undef, no true --> conflict
                else
                {
                    propQ.length = 0;
                    return UProp(true, cl);
                }
            }
        }
        return UProp(false, null);
    }

    Value value(Literal lit)
    in
    {
        assert(lit.var < assigns.length);
        assert(lit.var >= 0);
        assert([Sign.Pos, Sign.Neg].canFind(lit.sign));
    }
    out(result)
    {
        assert(result == Value.Undef || result == Value.True || result == Value.False);
    }
    body
    {
        Value varValue = assigns[lit.var];
        if(varValue == Value.Undef)
            return varValue;
        if(lit.sign == Sign.Pos)
            return varValue;
        else
            return neg(varValue);
    }


    void addAssumption(Literal lit)
    {
        enforce(lit.var < varCount, "undefined variable");
        if(assumptions.canFind(lit))
            return;
        assumptions ~= lit;
    }

    Clause* learn(Literal[] lits)
    in
    {
        assert(lits.length > 0);
    }
    body
    {
        if(lits.length == 1)
            return null; // todo

        debug(learn) write("learning ", lits, " ", clauses.length, "\n");
        Clause* cls = new Clause;
        cls.literals = lits;

        clauses ~= cls;
        watchers.watch(lits[0], cls);
        watchers.watch(lits[1], cls);
        return cls;
    }

    bool verify(Value[] solution)
    in
    {
        foreach(val; solution)
        {
            assert(val != Value.Undef);
        }
    }
    body
    {
        if(solution.length != varCount)
            throw new Exception("incompatible solution");

        assigns = solution;
        foreach(cl; clauses)
        {
            Literal[] lits = cl.literals;
            bool clauseSat = reduce!"a || b"(map!(a => (value(a) == Value.True))(lits));
            if(!clauseSat)
                return false;
        }
        return true;
    }

//private:
    size_t varCount;
    Value[] assigns;
    Clause*[] clauses;
    Literal[] decisions;
    Literal[] assumptions;

    Literal[] propQ;
    Clause*[] reasons;
    alias Tuple!(Literal, "lit", size_t, "dlevel") TrailElem;
    TrailElem[] trail;
    size_t[] deLevels;
    Watchers watchers;
//

    string trailToString()
    {
        auto app = appender!string();
        int curLvl = -1;
        foreach(elem; trail)
        {
            if(curLvl != elem.dlevel)
            {
                if(curLvl != -1) app.put("\n");
                curLvl = cast(int) elem.dlevel;
                formattedWrite(app, "%s: ", curLvl);
            }
            formattedWrite(app, "%s;  ", elem.lit);
        }
        app.put("\n");
        return app.data;
    }

    string clauseString(Literal[] lits)
    {
        auto app = appender!string();
        app.put("[");
        foreach(lit; lits)
        {
            Value val = value(lit);
            string rep;
            with(Value) final switch(val)
            {
                case Undef:
                    rep = "U";
                    break;
                case True:
                    rep = "T";
                    break;
                case False:
                    rep = "F";
                    break;
            }
            formattedWrite(app, "%s->%s; ", lit, rep);
        }
        app.put("]");
        return app.data;
    }
}

unittest
{
    Solver solver = new Solver;
    foreach(i; 0 .. 5)
        solver.addVariable();
    Literal[] clause = [{ Var(0), Sign(false) }, { Var(1), Sign(false) },
                        { Var(2), Sign(true) }];
    solver.addClause(clause);

    clause = [ Literal(Var(2), Sign(false)), Literal(Var(4), Sign(false)),
                        Literal(Var(5), Sign(true))];
    solver.addClause(clause);
    clause = [ Literal(Var(3), Sign(true)), Literal(Var(4), Sign(true))];
    solver.addClause(clause);
    solver.initData();
    assert(solver.checkWatchers());
}

unittest
{
    Solver solver = new Solver;
//    foreach(i; 0 .. 2)solver
}

struct Watchers
{
    Clause*[][] _watchlist;
    alias _watchlist this;

    ref Clause*[] opIndex(Literal lit)
    in
    {
        assert(index(lit) < _watchlist.length);
    }
    body
    {
        return _watchlist[index(lit)];
    }


    void watch(Literal lit, Clause* cls)
    in
    {
        assert(cls !is null);
        assert(index(lit) < _watchlist.length);
    }
    out
    {
        assert(this[lit].length > 0);
    }
    body
    {
        //this[lit] ~= cls; // workaround for bug #8292
        _watchlist[index(lit)] ~= cls;
    }

    void release(Literal lit, Clause* cls)
    in
    {
        assert(index(lit) < _watchlist.length);
        assert(cls !is null);
    }
    body
    {
        auto clauseList = this[lit];
        auto idx = countUntil(clauseList, cls);
        assert(idx < clauseList.length);
        this[lit] = clauseList[0 .. idx] ~ clauseList[idx+1 .. $];
    }

    void expand(size_t length)
    {
        if(_watchlist.length >= length)
            return;

        _watchlist.length = length;
    }
}

unittest
{
    Watchers watchers;
    watchers.length = 12;

    Literal lit = { Var(1), Sign(false) };
    Clause* cls = cast(Clause*) 144;
    watchers.watch(lit, cls);
    assert(watchers[lit].length >= 1);
    assert(watchers[lit][0] == cast(Clause*) 144);
    watchers._watchlist[index(lit)] = [ cast(Clause*) 32, cast(Clause*) 64, cast(Clause*) 128 ];
    assert(watchers[lit].length == 3);
    assert(watchers[lit][0] ==  cast(Clause*) 32);

    watchers.release(lit, cast(Clause*)64);
    assert(watchers[lit].length == 2);
    assert(watchers[lit][0] ==  cast(Clause*) 32);
    assert(watchers[lit][1] ==  cast(Clause*) 128);
}

/* given a value and a sign, is the result positive? */
bool isPositive(in Value val, in Sign sign) pure nothrow
{
    return (val == Value.True && sign == Sign.Pos) || (val == Value.False && sign == Sign.Neg);
}

unittest
{
    with(Value) with(Sign)
    {
        assert(isPositive(True, Sign(Pos)));
        assert(isPositive(False, Sign(Neg)));
        assert(!isPositive(False, Sign(Pos)));
        assert(!isPositive(Undef, Sign(Pos)));
    }
}

/**
    parse a DIMACS file that contains a CNF.
    stores found clauses in solver
*/
void parse(Solver solver, string desc)
in { assert(solver !is null); }
body
{
    enforce(solver.varCount == 0);

    auto lines = desc.splitLines();
    int numVar;
    Var[] vars;
    int numClause = -1;
    int clausesSeen;
    bool firstP = true;

    Literal[] curClause;

    foreach(string line; lines)
    {
        auto parts = line.split().map!strip();
        // discard comments
        if(parts[0] == "c")
            continue;

        // okay it's getting interesting
        if(parts[0] == "p")
        {
            enforce(parts[1].canFind("cnf"));
            enforce(firstP);
            firstP = false;
            numVar = to!int(parts[2]);
            numClause = to!int(parts[3]);

            foreach(i; 0 .. numVar)
            {
                vars ~= solver.addVariable();
            }
            continue;
        }

        foreach(lit; parts)
        {
            if(lit == "0")
            {
                if(curClause.length ==0)
                    goto done;
                solver.addClause(curClause);
                curClause = [];
                clausesSeen++;
                continue;
            }

            Sign sign = Sign.Pos;
            if(lit.startsWith("-"))
            {
                lit = lit[1 .. $];
                sign =  Sign.Neg;
            }

            int num = to!int(lit);
            enforce(num <= numVar, "variable number too high");
            enforce(num > 0, "variable number zero or below");
            Var var = vars[num-1];
            curClause ~= Literal(var, sign);
        }

    }
done:
    if(numClause != clausesSeen)
        throw new Exception("can't parse this shit (not enough clauses)");
}

unittest {

string  simple = q"EOF
c  simple_v3_c2.cnf
c
p cnf 3 2
1 -3 0
2 3 -1 0
EOF";

    Solver solv = new Solver();
    solv.parse(simple);
    solv.initData();
    assert(solv.clauses.length == 2);
    assert(solv.assigns.length == 3);
}

unittest
{
    string simple = q"EOF
p cnf 3 5
-1 -3 0
-2 -3 -1 0
-1 -2 0
-1 3 0
1 -3 0
EOF";
    Solver solv = new Solver();
    solv.parse(simple);
    solv.initData();
    writeln(solv.clauses.length);
    assert(solv.clauses.length == 5, "length not 5 ");
    assert(solv.assigns.length == 3);
}




