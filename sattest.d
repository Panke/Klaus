import std.stdio;
import std.algorithm;

import probat.all;

import sat;

Solver conf1()
{
        Solver solv = new Solver();
        foreach(i; 0 .. 3) solv.addVariable();

        Literal[] cl1 = [{Var(0), Sign.Neg}, {Var(1), Sign.Pos}];
        Literal[] cl2 = [{Var(1), Sign.Neg}, {Var(2), Sign.Pos}];
        Literal[] cl3 = [{Var(2), Sign.Neg}, {Var(0), Sign.Pos}];
        Literal[] cl4 = [{Var(0), Sign.Neg}, {Var(1), Sign.Neg}];
        foreach(cl; [cl1, cl2, cl3, cl4])
        {
            solv.addClause(cl);
        }
        solv.initData();
        return solv;
}

Solver conf2()
{
        Solver solv = new Solver();
        foreach(i; 0 .. 3) solv.addVariable();

        Literal[] cl1 = [{Var(0), Sign.Neg}, {Var(1), Sign.Pos}];
        Literal[] cl2 = [{Var(1), Sign.Pos}, {Var(1), Sign.Neg}, {Var(2), Sign.Pos}];
        foreach(cl; [cl1, cl2])
        {
            solv.addClause(cl);
        }
        solv.initData();
        return solv;
}

unittest
{
    testCase("solver internals",
    {
        Solver solv = conf1();
        assEq(solv.clauses.length, 4);


        assert(solv.checkWatchers());
    });

    testCase("unit propagation, conflict",
    {
        Solver solv = conf1();
        solv.decide(Literal(Var(0), Sign.Pos));
        assert(solv.unitPropagation().conflict);
    });

    testCase("unit propagation, no conflict & solution",
    {
        Solver solv = conf1();
        solv.decide(Literal(Var(1), Sign.Neg));
		assert(!solv.unitPropagation().conflict);
        auto model = solv.model;
        foreach(val; model)
            assEq(val, Value.False);

    });

    testCase("unit propagation, no conflict, no solution",
    {
        Solver solv = conf2();
        solv.decide(Literal(Var(0), Sign.Pos));
        assert(!solv.unitPropagation().conflict);
    });
}


unittest // parser
{
    testCase("parse correct dimacs file",
    {
        string simple = q"EOF
p cnf 3 5
-1 -3 0
-2 -3 -1 0
-1 -2 0
-1 3 0
1 -3 0
EOF";
        Solver solv = new Solver;
        solv.parse(simple);

        assEq(solv.clauses.length, 5);
        assEq(solv.varCount, 3);
    });

    testCase("parse dimacs file with less clauses",
    {
        string simple = q"EOF
p cnf 3 5
-2 -3 -1 0
-1 -2 0
-1 3 0
1 -3 0
EOF";
        Solver solv = new Solver;
        assertThrows!Exception(solv.parse(simple));
    });

    testCase("parse dimacs file with to many clauses",
    {
        string simple = q"EOF
p cnf 3 2
-2 -3 -1 0
-1 -2 0
-1 3 0
1 -3 0
EOF";
        Solver solv = new Solver;
        assertThrows!Exception(solv.parse(simple));
    });

    testCase("parse dimacs file with undef variable",
    {
        string simple = q"EOF
p cnf 3 2
-2 -3 -1 0
-1 -2 0
-1 5 0
1 -3 0
EOF";
        Solver solv = new Solver;
        assertThrows!Exception(solv.parse(simple));
    });
}

// full runs
bool verify(string dimacs, Value[] model)
{
    Solver solv = new Solver;
    solv.parse(dimacs);
    return solv.verify(model);
}
unittest
{
    testCase("full run, success, all false",
    {
        Solver solv = new Solver;
        string dimacs = q"EOF
            p cnf 3 4
            -1 2 0
            -2 3 0
            -3 1 0
            -1 -2 0
EOF";
        solv.parse(dimacs);
        assert(solv.solve());
        assEq(solv.model, [Value.False, Value.False, Value.False]);
        assert(verify(dimacs, solv.model));
    });

    testCase("full run, success, all true",
    {
        Solver solv = new Solver;
        string dimacs = q"EOF
            p cnf 3 4
            1 -2 0
            2 -3 0
            3 -1 0
            1 2 0
EOF";
        solv.parse(dimacs);
        assert(solv.solve());
        assEq(solv.model, [Value.True, Value.True, Value.True]);
        assert(verify(dimacs, solv.model));
    });

    testCase("full run, unsat",
    {
        Solver solv = new Solver;
        string dimacs = q"EOF
            p cnf 4 8
            1 2 0
            -1 -2 0
            -1 2 0
            1 -2 0
            3 4 0
            -3 -4 0
            -3 4 0
            3 -4 0
EOF";
        solv.parse(dimacs);
        assert(!solv.solve());
    });


    testCase("full run, unsat",
    {
        Solver solv = new Solver;
        string dimacs = q"EOF
        p cnf 4 6
        1 2 0
        1 -2 0
        3 4 0
        -3 -4 0
        -3 4 0
        3 -4 0
EOF";
        solv.parse(dimacs);
        assert(!solv.solve());
    });

    testCase("full run, sat",
    {
        Solver solv = new Solver;
        string sat = q"EOF
        p cnf 3 4
        1  2 3 0
        -1 -2 -3  0
        -1 2 3 0
        -1 2 -3 0
EOF";
        solv.parse(sat);
        assert(solv.solve());
        assert(verify(sat, solv.model));
    });


    testCase("full run, zebra",
    {
        Solver solv = new Solver;
        solv.parse(zebra);
        assert(solv.solve());
        assert(verify(zebra, solv.model));
    });


    testCase("not sat example",
    {
        Solver solv = new Solver;
        solv.parse(notSat);
        assert(!solv.solve());
    });

    testCase("full run, example from handbook of satisfiability (1)",
    {
        string dimacs = q"EOF
        p cnf 6 7
        1 2 0
        2 3 0
        -1 -4 5 0
        -1 4 6 0
        -1 -5 6 0
        -1 4 -6 0
        -1 -5 -6 0
EOF";
        Solver solv = new Solver;
        solv.parse(dimacs);
        assert(solv.solve());
        assert(verify(dimacs, solv.model));
    });


}
string zebra = q"EOF
c The zebra problem.
c
c  Reference:
c
c    Rina Dechter,
c    Enhancement Schemes for Constraint Processing:
c    Backjumping, Learning, and Cutset Decomposition",
c    Artificial Intelligence,
c    Volume 41, pages 273-312.
c
c  Encoded in CNF by Jon Freeman, November 1994.
c  I have found three solutions; there may be more.
c
p cnf 155 1135
1 2 3
4 5 0
-1 -2 0
-1 -3 0
-1 -4 0
-1 -5 0
-2 -3 0
-2 -4 0
-2 -5 0
-3 -4 0
-3 -5 0
-4 -5 0
6 7 8
9 10 0
-6 -7 0
-6 -8 0
-6 -9 0
-6 -10 0
-7 -8 0
-7 -9 0
-7 -10 0
-8 -9 0
-8 -10 0
-9 -10 0
11 12 13
14 15 0
-11 -12 0
-11 -13 0
-11 -14 0
-11 -15 0
-12 -13 0
-12 -14 0
-12 -15 0
-13 -14 0
-13 -15 0
-14 -15 0
16 17 18
19 20 0
-16 -17 0
-16 -18 0
-16 -19 0
-16 -20 0
-17 -18 0
-17 -19 0
-17 -20 0
-18 -19 0
-18 -20 0
-19 -20 0
21 22 23
24 25 0
-21 -22 0
-21 -23 0
-21 -24 0
-21 -25 0
-22 -23 0
-22 -24 0
-22 -25 0
-23 -24 0
-23 -25 0
-24 -25 0
51 52 53
54 55 0
-51 -52 0
-51 -53 0
-51 -54 0
-51 -55 0
-52 -53 0
-52 -54 0
-52 -55 0
-53 -54 0
-53 -55 0
-54 -55 0
56 57 58
59 60 0
-56 -57 0
-56 -58 0
-56 -59 0
-56 -60 0
-57 -58 0
-57 -59 0
-57 -60 0
-58 -59 0
-58 -60 0
-59 -60 0
61 62 63
64 65 0
-61 -62 0
-61 -63 0
-61 -64 0
-61 -65 0
-62 -63 0
-62 -64 0
-62 -65 0
-63 -64 0
-63 -65 0
-64 -65 0
66 67 68
69 70 0
-66 -67 0
-66 -68 0
-66 -69 0
-66 -70 0
-67 -68 0
-67 -69 0
-67 -70 0
-68 -69 0
-68 -70 0
-69 -70 0
71 72 73
74 75 0
-71 -72 0
-71 -73 0
-71 -74 0
-71 -75 0
-72 -73 0
-72 -74 0
-72 -75 0
-73 -74 0
-73 -75 0
-74 -75 0
26 27 28
29 30 0
-26 -27 0
-26 -28 0
-26 -29 0
-26 -30 0
-27 -28 0
-27 -29 0
-27 -30 0
-28 -29 0
-28 -30 0
-29 -30 0
31 32 33
34 35 0
-31 -32 0
-31 -33 0
-31 -34 0
-31 -35 0
-32 -33 0
-32 -34 0
-32 -35 0
-33 -34 0
-33 -35 0
-34 -35 0
36 37 38
39 40 0
-36 -37 0
-36 -38 0
-36 -39 0
-36 -40 0
-37 -38 0
-37 -39 0
-37 -40 0
-38 -39 0
-38 -40 0
-39 -40 0
41 42 43
44 45 0
-41 -42 0
-41 -43 0
-41 -44 0
-41 -45 0
-42 -43 0
-42 -44 0
-42 -45 0
-43 -44 0
-43 -45 0
-44 -45 0
46 47 48
49 50 0
-46 -47 0
-46 -48 0
-46 -49 0
-46 -50 0
-47 -48 0
-47 -49 0
-47 -50 0
-48 -49 0
-48 -50 0
-49 -50 0
101 102 103
104 105 0
-101 -102 0
-101 -103 0
-101 -104 0
-101 -105 0
-102 -103 0
-102 -104 0
-102 -105 0
-103 -104 0
-103 -105 0
-104 -105 0
106 107 108
109 110 0
-106 -107 0
-106 -108 0
-106 -109 0
-106 -110 0
-107 -108 0
-107 -109 0
-107 -110 0
-108 -109 0
-108 -110 0
-109 -110 0
111 112 113
114 115 0
-111 -112 0
-111 -113 0
-111 -114 0
-111 -115 0
-112 -113 0
-112 -114 0
-112 -115 0
-113 -114 0
-113 -115 0
-114 -115 0
116 117 118
119 120 0
-116 -117 0
-116 -118 0
-116 -119 0
-116 -120 0
-117 -118 0
-117 -119 0
-117 -120 0
-118 -119 0
-118 -120 0
-119 -120 0
121 122 123
124 125 0
-121 -122 0
-121 -123 0
-121 -124 0
-121 -125 0
-122 -123 0
-122 -124 0
-122 -125 0
-123 -124 0
-123 -125 0
-124 -125 0
76 77 78
79 80 0
-76 -77 0
-76 -78 0
-76 -79 0
-76 -80 0
-77 -78 0
-77 -79 0
-77 -80 0
-78 -79 0
-78 -80 0
-79 -80 0
81 82 83
84 85 0
-81 -82 0
-81 -83 0
-81 -84 0
-81 -85 0
-82 -83 0
-82 -84 0
-82 -85 0
-83 -84 0
-83 -85 0
-84 -85 0
86 87 88
89 90 0
-86 -87 0
-86 -88 0
-86 -89 0
-86 -90 0
-87 -88 0
-87 -89 0
-87 -90 0
-88 -89 0
-88 -90 0
-89 -90 0
91 92 93
94 95 0
-91 -92 0
-91 -93 0
-91 -94 0
-91 -95 0
-92 -93 0
-92 -94 0
-92 -95 0
-93 -94 0
-93 -95 0
-94 -95 0
96 97 98
99 100 0
-96 -97 0
-96 -98 0
-96 -99 0
-96 -100 0
-97 -98 0
-97 -99 0
-97 -100 0
-98 -99 0
-98 -100 0
-99 -100 0
-1 -7 126 0
-2 -8 126 0
-3 -9 126 0
-4 -10 126 0
-1 -12 127 0
-2 -13 127 0
-3 -14 127 0
-4 -15 127 0
-1 -17 128 0
-2 -18 128 0
-3 -19 128 0
-4 -20 128 0
-1 -22 129 0
-2 -23 129 0
-3 -24 129 0
-4 -25 129 0
-6 -2 130 0
-7 -3 130 0
-8 -4 130 0
-9 -5 130 0
-6 -12 131 0
-7 -13 131 0
-8 -14 131 0
-9 -15 131 0
-6 -17 132 0
-7 -18 132 0
-8 -19 132 0
-9 -20 132 0
-6 -22 133 0
-7 -23 133 0
-8 -24 133 0
-9 -25 133 0
-11 -2 134 0
-12 -3 134 0
-13 -4 134 0
-14 -5 134 0
-11 -7 135 0
-12 -8 135 0
-13 -9 135 0
-14 -10 135 0
-11 -17 136 0
-12 -18 136 0
-13 -19 136 0
-14 -20 136 0
-11 -22 137 0
-12 -23 137 0
-13 -24 137 0
-14 -25 137 0
-16 -2 138 0
-17 -3 138 0
-18 -4 138 0
-19 -5 138 0
-16 -7 139 0
-17 -8 139 0
-18 -9 139 0
-19 -10 139 0
-16 -12 140 0
-17 -13 140 0
-18 -14 140 0
-19 -15 140 0
-16 -22 141 0
-17 -23 141 0
-18 -24 141 0
-19 -25 141 0
-21 -2 142 0
-22 -3 142 0
-23 -4 142 0
-24 -5 142 0
-21 -7 143 0
-22 -8 143 0
-23 -9 143 0
-24 -10 143 0
-21 -12 144 0
-22 -13 144 0
-23 -14 144 0
-24 -15 144 0
-21 -17 145 0
-22 -18 145 0
-23 -19 145 0
-24 -20 145 0
-1 -8 -126 0
-1 -9 -126 0
-1 -10 -126 0
-2 -6 -126 0
-2 -9 -126 0
-2 -10 -126 0
-3 -6 -126 0
-3 -7 -126 0
-3 -10 -126 0
-4 -6 -126 0
-4 -7 -126 0
-4 -8 -126 0
-5 -6 -126 0
-5 -7 -126 0
-5 -8 -126 0
-5 -9 -126 0
-1 -13 -127 0
-1 -14 -127 0
-1 -15 -127 0
-2 -11 -127 0
-2 -14 -127 0
-2 -15 -127 0
-3 -11 -127 0
-3 -12 -127 0
-3 -15 -127 0
-4 -11 -127 0
-4 -12 -127 0
-4 -13 -127 0
-5 -11 -127 0
-5 -12 -127 0
-5 -13 -127 0
-5 -14 -127 0
-1 -18 -128 0
-1 -19 -128 0
-1 -20 -128 0
-2 -16 -128 0
-2 -19 -128 0
-2 -20 -128 0
-3 -16 -128 0
-3 -17 -128 0
-3 -20 -128 0
-4 -16 -128 0
-4 -17 -128 0
-4 -18 -128 0
-5 -16 -128 0
-5 -17 -128 0
-5 -18 -128 0
-5 -19 -128 0
-1 -23 -129 0
-1 -24 -129 0
-1 -25 -129 0
-2 -21 -129 0
-2 -24 -129 0
-2 -25 -129 0
-3 -21 -129 0
-3 -22 -129 0
-3 -25 -129 0
-4 -21 -129 0
-4 -22 -129 0
-4 -23 -129 0
-5 -21 -129 0
-5 -22 -129 0
-5 -23 -129 0
-5 -24 -129 0
-6 -3 -130 0
-6 -4 -130 0
-6 -5 -130 0
-7 -1 -130 0
-7 -4 -130 0
-7 -5 -130 0
-8 -1 -130 0
-8 -2 -130 0
-8 -5 -130 0
-9 -1 -130 0
-9 -2 -130 0
-9 -3 -130 0
-10 -1 -130 0
-10 -2 -130 0
-10 -3 -130 0
-10 -4 -130 0
-6 -13 -131 0
-6 -14 -131 0
-6 -15 -131 0
-7 -11 -131 0
-7 -14 -131 0
-7 -15 -131 0
-8 -11 -131 0
-8 -12 -131 0
-8 -15 -131 0
-9 -11 -131 0
-9 -12 -131 0
-9 -13 -131 0
-10 -11 -131 0
-10 -12 -131 0
-10 -13 -131 0
-10 -14 -131 0
-6 -18 -132 0
-6 -19 -132 0
-6 -20 -132 0
-7 -16 -132 0
-7 -19 -132 0
-7 -20 -132 0
-8 -16 -132 0
-8 -17 -132 0
-8 -20 -132 0
-9 -16 -132 0
-9 -17 -132 0
-9 -18 -132 0
-10 -16 -132 0
-10 -17 -132 0
-10 -18 -132 0
-10 -19 -132 0
-6 -23 -133 0
-6 -24 -133 0
-6 -25 -133 0
-7 -21 -133 0
-7 -24 -133 0
-7 -25 -133 0
-8 -21 -133 0
-8 -22 -133 0
-8 -25 -133 0
-9 -21 -133 0
-9 -22 -133 0
-9 -23 -133 0
-10 -21 -133 0
-10 -22 -133 0
-10 -23 -133 0
-10 -24 -133 0
-11 -3 -134 0
-11 -4 -134 0
-11 -5 -134 0
-12 -1 -134 0
-12 -4 -134 0
-12 -5 -134 0
-13 -1 -134 0
-13 -2 -134 0
-13 -5 -134 0
-14 -1 -134 0
-14 -2 -134 0
-14 -3 -134 0
-15 -1 -134 0
-15 -2 -134 0
-15 -3 -134 0
-15 -4 -134 0
-11 -8 -135 0
-11 -9 -135 0
-11 -10 -135 0
-12 -6 -135 0
-12 -9 -135 0
-12 -10 -135 0
-13 -6 -135 0
-13 -7 -135 0
-13 -10 -135 0
-14 -6 -135 0
-14 -7 -135 0
-14 -8 -135 0
-15 -6 -135 0
-15 -7 -135 0
-15 -8 -135 0
-15 -9 -135 0
-11 -18 -136 0
-11 -19 -136 0
-11 -20 -136 0
-12 -16 -136 0
-12 -19 -136 0
-12 -20 -136 0
-13 -16 -136 0
-13 -17 -136 0
-13 -20 -136 0
-14 -16 -136 0
-14 -17 -136 0
-14 -18 -136 0
-15 -16 -136 0
-15 -17 -136 0
-15 -18 -136 0
-15 -19 -136 0
-11 -23 -137 0
-11 -24 -137 0
-11 -25 -137 0
-12 -21 -137 0
-12 -24 -137 0
-12 -25 -137 0
-13 -21 -137 0
-13 -22 -137 0
-13 -25 -137 0
-14 -21 -137 0
-14 -22 -137 0
-14 -23 -137 0
-15 -21 -137 0
-15 -22 -137 0
-15 -23 -137 0
-15 -24 -137 0
-16 -3 -138 0
-16 -4 -138 0
-16 -5 -138 0
-17 -1 -138 0
-17 -4 -138 0
-17 -5 -138 0
-18 -1 -138 0
-18 -2 -138 0
-18 -5 -138 0
-19 -1 -138 0
-19 -2 -138 0
-19 -3 -138 0
-20 -1 -138 0
-20 -2 -138 0
-20 -3 -138 0
-20 -4 -138 0
-16 -8 -139 0
-16 -9 -139 0
-16 -10 -139 0
-17 -6 -139 0
-17 -9 -139 0
-17 -10 -139 0
-18 -6 -139 0
-18 -7 -139 0
-18 -10 -139 0
-19 -6 -139 0
-19 -7 -139 0
-19 -8 -139 0
-20 -6 -139 0
-20 -7 -139 0
-20 -8 -139 0
-20 -9 -139 0
-16 -13 -140 0
-16 -14 -140 0
-16 -15 -140 0
-17 -11 -140 0
-17 -14 -140 0
-17 -15 -140 0
-18 -11 -140 0
-18 -12 -140 0
-18 -15 -140 0
-19 -11 -140 0
-19 -12 -140 0
-19 -13 -140 0
-20 -11 -140 0
-20 -12 -140 0
-20 -13 -140 0
-20 -14 -140 0
-16 -23 -141 0
-16 -24 -141 0
-16 -25 -141 0
-17 -21 -141 0
-17 -24 -141 0
-17 -25 -141 0
-18 -21 -141 0
-18 -22 -141 0
-18 -25 -141 0
-19 -21 -141 0
-19 -22 -141 0
-19 -23 -141 0
-20 -21 -141 0
-20 -22 -141 0
-20 -23 -141 0
-20 -24 -141 0
-21 -3 -142 0
-21 -4 -142 0
-21 -5 -142 0
-22 -1 -142 0
-22 -4 -142 0
-22 -5 -142 0
-23 -1 -142 0
-23 -2 -142 0
-23 -5 -142 0
-24 -1 -142 0
-24 -2 -142 0
-24 -3 -142 0
-25 -1 -142 0
-25 -2 -142 0
-25 -3 -142 0
-25 -4 -142 0
-21 -8 -143 0
-21 -9 -143 0
-21 -10 -143 0
-22 -6 -143 0
-22 -9 -143 0
-22 -10 -143 0
-23 -6 -143 0
-23 -7 -143 0
-23 -10 -143 0
-24 -6 -143 0
-24 -7 -143 0
-24 -8 -143 0
-25 -6 -143 0
-25 -7 -143 0
-25 -8 -143 0
-25 -9 -143 0
-21 -13 -144 0
-21 -14 -144 0
-21 -15 -144 0
-22 -11 -144 0
-22 -14 -144 0
-22 -15 -144 0
-23 -11 -144 0
-23 -12 -144 0
-23 -15 -144 0
-24 -11 -144 0
-24 -12 -144 0
-24 -13 -144 0
-25 -11 -144 0
-25 -12 -144 0
-25 -13 -144 0
-25 -14 -144 0
-21 -18 -145 0
-21 -19 -145 0
-21 -20 -145 0
-22 -16 -145 0
-22 -19 -145 0
-22 -20 -145 0
-23 -16 -145 0
-23 -17 -145 0
-23 -20 -145 0
-24 -16 -145 0
-24 -17 -145 0
-24 -18 -145 0
-25 -16 -145 0
-25 -17 -145 0
-25 -18 -145 0
-25 -19 -145 0
-126 146 0
-127 147 0
-128 148 0
-129 149 0
-131 150 0
-132 151 0
-133 152 0
-136 153 0
-137 154 0
-141 155 0
-130 146 0
-134 147 0
-138 148 0
-142 149 0
-135 150 0
-139 151 0
-143 152 0
-140 153 0
-144 154 0
-145 155 0
126 130 -146 0
127 134 -147 0
128 138 -148 0
129 142 -149 0
131 135 -150 0
132 139 -151 0
133 143 -152 0
136 140 -153 0
137 144 -154 0
141 145 -155 0
-1 -6 0
-1 -11 0
-1 -16 0
-1 -21 0
-6 -11 0
-6 -16 0
-6 -21 0
-11 -16 0
-11 -21 0
-16 -21 0
-2 -7 0
-2 -12 0
-2 -17 0
-2 -22 0
-7 -12 0
-7 -17 0
-7 -22 0
-12 -17 0
-12 -22 0
-17 -22 0
-3 -8 0
-3 -13 0
-3 -18 0
-3 -23 0
-8 -13 0
-8 -18 0
-8 -23 0
-13 -18 0
-13 -23 0
-18 -23 0
-4 -9 0
-4 -14 0
-4 -19 0
-4 -24 0
-9 -14 0
-9 -19 0
-9 -24 0
-14 -19 0
-14 -24 0
-19 -24 0
-5 -10 0
-5 -15 0
-5 -20 0
-5 -25 0
-10 -15 0
-10 -20 0
-10 -25 0
-15 -20 0
-15 -25 0
-20 -25 0
-51 -56 0
-51 -61 0
-51 -66 0
-51 -71 0
-56 -61 0
-56 -66 0
-56 -71 0
-61 -66 0
-61 -71 0
-66 -71 0
-52 -57 0
-52 -62 0
-52 -67 0
-52 -72 0
-57 -62 0
-57 -67 0
-57 -72 0
-62 -67 0
-62 -72 0
-67 -72 0
-53 -58 0
-53 -63 0
-53 -68 0
-53 -73 0
-58 -63 0
-58 -68 0
-58 -73 0
-63 -68 0
-63 -73 0
-68 -73 0
-54 -59 0
-54 -64 0
-54 -69 0
-54 -74 0
-59 -64 0
-59 -69 0
-59 -74 0
-64 -69 0
-64 -74 0
-69 -74 0
-55 -60 0
-55 -65 0
-55 -70 0
-55 -75 0
-60 -65 0
-60 -70 0
-60 -75 0
-65 -70 0
-65 -75 0
-70 -75 0
-26 -31 0
-26 -36 0
-26 -41 0
-26 -46 0
-31 -36 0
-31 -41 0
-31 -46 0
-36 -41 0
-36 -46 0
-41 -46 0
-27 -32 0
-27 -37 0
-27 -42 0
-27 -47 0
-32 -37 0
-32 -42 0
-32 -47 0
-37 -42 0
-37 -47 0
-42 -47 0
-28 -33 0
-28 -38 0
-28 -43 0
-28 -48 0
-33 -38 0
-33 -43 0
-33 -48 0
-38 -43 0
-38 -48 0
-43 -48 0
-29 -34 0
-29 -39 0
-29 -44 0
-29 -49 0
-34 -39 0
-34 -44 0
-34 -49 0
-39 -44 0
-39 -49 0
-44 -49 0
-30 -35 0
-30 -40 0
-30 -45 0
-30 -50 0
-35 -40 0
-35 -45 0
-35 -50 0
-40 -45 0
-40 -50 0
-45 -50 0
-101 -106 0
-101 -111 0
-101 -116 0
-101 -121 0
-106 -111 0
-106 -116 0
-106 -121 0
-111 -116 0
-111 -121 0
-116 -121 0
-102 -107 0
-102 -112 0
-102 -117 0
-102 -122 0
-107 -112 0
-107 -117 0
-107 -122 0
-112 -117 0
-112 -122 0
-117 -122 0
-103 -108 0
-103 -113 0
-103 -118 0
-103 -123 0
-108 -113 0
-108 -118 0
-108 -123 0
-113 -118 0
-113 -123 0
-118 -123 0
-104 -109 0
-104 -114 0
-104 -119 0
-104 -124 0
-109 -114 0
-109 -119 0
-109 -124 0
-114 -119 0
-114 -124 0
-119 -124 0
-105 -110 0
-105 -115 0
-105 -120 0
-105 -125 0
-110 -115 0
-110 -120 0
-110 -125 0
-115 -120 0
-115 -125 0
-120 -125 0
-76 -81 0
-76 -86 0
-76 -91 0
-76 -96 0
-81 -86 0
-81 -91 0
-81 -96 0
-86 -91 0
-86 -96 0
-91 -96 0
-77 -82 0
-77 -87 0
-77 -92 0
-77 -97 0
-82 -87 0
-82 -92 0
-82 -97 0
-87 -92 0
-87 -97 0
-92 -97 0
-78 -83 0
-78 -88 0
-78 -93 0
-78 -98 0
-83 -88 0
-83 -93 0
-83 -98 0
-88 -93 0
-88 -98 0
-93 -98 0
-79 -84 0
-79 -89 0
-79 -94 0
-79 -99 0
-84 -89 0
-84 -94 0
-84 -99 0
-89 -94 0
-89 -99 0
-94 -99 0
-80 -85 0
-80 -90 0
-80 -95 0
-80 -100 0
-85 -90 0
-85 -95 0
-85 -100 0
-90 -95 0
-90 -100 0
-95 -100 0
51 0
42 0
122 0
11 0
82 0
-65             0
-55 147 0
-60   150 0
-70   153 0
-75   154 0
-101 -57  0
-101 -62 0
-101 -67  0
-101 -72  0
-106 -52 0
-106 -62  0
-106 -67   0
-106 -72   0
-111 -52 0
-111 -57   0
-111 -67   0
-111 -72   0
-116 -52 0
-116 -57   0
-116 -62  0
-116 -72   0
-121 -52 0
-121 -57   0
-121 -62  0
-121 -67   0
-30 -81  0
-30 -86 0
-30 -91  0
-30 -96  0
-35 -76 0
-35 -86  0
-35 -91   0
-35 -96   0
-40 -76 0
-40 -81   0
-40 -91   0
-40 -96   0
-45 -76 0
-45 -81   0
-45 -86  0
-45 -96   0
-50 -76 0
-50 -81   0
-50 -86  0
-50 -91   0
-54 -83  0
-54 -88 0
-54 -93  0
-54 -98  0
-59 -78 0
-59 -88  0
-59 -93   0
-59 -98   0
-64 -78 0
-64 -83   0
-64 -93   0
-64 -98   0
-69 -78 0
-69 -83   0
-69 -88  0
-69 -98   0
-74 -78 0
-74 -83   0
-74 -88  0
-74 -93   0
-79 -108  0
-79 -113 0
-79 -118  0
-79 -123  0
-84 -103 0
-84 -113  0
-84 -118   0
-84 -123   0
-89 -103 0
-89 -108   0
-89 -118   0
-89 -123   0
-94 -103 0
-94 -108   0
-94 -113  0
-94 -123   0
-99 -103 0
-99 -108   0
-99 -113  0
-99 -118   0
-105 -8  0
-105 -13 0
-105 -18  0
-105 -23  0
-110 -3 0
-110 -13  0
-110 -18   0
-110 -23   0
-115 -3 0
-115 -8   0
-115 -18   0
-115 -23   0
-120 -3 0
-120 -8   0
-120 -13  0
-120 -23   0
-125 -3 0
-125 -8   0
-125 -13  0
-125 -18   0
-53 -57  126 0
-53 -62 127 0
-53 -67  128 0
-53 -72  129 0
-58 -52 130 0
-58 -62  131 0
-58 -67   132 0
-58 -72   133 0
-63 -52 134 0
-63 -57   135 0
-63 -67   136 0
-63 -72   137 0
-68 -52 138 0
-68 -57   139 0
-68 -62  140 0
-68 -72   141 0
-73 -52 142 0
-73 -57   143 0
-73 -62  144 0
-73 -67   145 0
-80 -29 0
-85   -34   0
-90  -39  0
-95   -44   0
-100   -49   0
-80 -34  146 0
-80 -39 147 0
-80 -44  148 0
-80 -49  149 0
-85 -29 146 0
-85 -39  150 0
-85 -44   151 0
-85 -49   152 0
-90 -29 147 0
-90 -34   150 0
-90 -44   153 0
-90 -49   154 0
-95 -29 148 0
-95 -34   151 0
-95 -39  153 0
-95 -49   155 0
-100 -29 149 0
-100 -34   152 0
-100 -39  154 0
-100 -44   155 0
-78 -28 0
-83   -33   0
-88  -38  0
-93   -43   0
-98   -48   0
-78 -33  146 0
-78 -38 147 0
-78 -43  148 0
-78 -48  149 0
-83 -28 146 0
-83 -38  150 0
-83 -43   151 0
-83 -48   152 0
-88 -28 147 0
-88 -33   150 0
-88 -43   153 0
-88 -48   154 0
-93 -28 148 0
-93 -33   151 0
-93 -38  153 0
-93 -48   155 0
-98 -28 149 0
-98 -33   152 0
-98 -38  154 0
-98 -43   155 0
EOF";

string notSat = q"EOF
c FILE: aim-100-1_6-no-1.cnf
c
c SOURCE: Kazuo Iwama, Eiji Miyano (miyano@cscu.kyushu-u.ac.jp),
c          and Yuichi Asahiro
c
c DESCRIPTION: Artifical instances from generator by source.  Generators
c              and more information in sat/contributed/iwama.
c
c NOTE: Not Satisfiable
c
p cnf 100 160
16 30 95 0
-16 30 95 0
-30 35 78 0
-30 -78 85 0
-78 -85 95 0
8 55 100 0
8 55 -95 0
9 52 100 0
9 73 -100 0
-8 -9 52 0
38 66 83 0
-38 83 87 0
-52 83 -87 0
66 74 -83 0
-52 -66 89 0
-52 73 -89 0
-52 73 -74 0
-8 -73 -95 0
40 -55 90 0
-40 -55 90 0
25 35 82 0
-25 82 -90 0
-55 -82 -90 0
11 75 84 0
11 -75 96 0
23 -75 -96 0
-11 23 -35 0
-23 29 65 0
29 -35 -65 0
-23 -29 84 0
-35 54 70 0
-54 70 77 0
19 -77 -84 0
-19 -54 70 0
22 68 81 0
-22 48 81 0
-22 -48 93 0
3 -48 -93 0
7 18 -81 0
-7 56 -81 0
3 18 -56 0
-18 47 68 0
-18 -47 -81 0
-3 68 77 0
-3 -77 -84 0
19 -68 -70 0
-19 -68 74 0
-68 -70 -74 0
54 61 -62 0
50 53 -62 0
-50 61 -62 0
-27 56 93 0
4 14 76 0
4 -76 96 0
-4 14 80 0
-14 -68 80 0
-10 -39 -89 0
1 49 -81 0
1 26 -49 0
17 -26 -49 0
-1 17 -40 0
16 51 -89 0
-9 57 60 0
12 45 -51 0
2 12 69 0
2 -12 40 0
-12 -51 69 0
-33 60 -98 0
5 -32 -66 0
2 -47 -100 0
-42 64 83 0
20 -42 -64 0
20 -48 98 0
-20 50 98 0
-32 -50 98 0
-24 37 -73 0
-24 -37 -100 0
-57 71 81 0
-37 40 -91 0
31 42 81 0
-31 42 72 0
-31 42 -72 0
7 -19 25 0
-1 -25 -94 0
-15 -44 79 0
-6 31 46 0
-39 41 88 0
28 -39 43 0
28 -43 -88 0
-4 -28 -88 0
-30 -39 -41 0
-29 33 88 0
-16 21 94 0
-10 26 62 0
-11 -64 86 0
-6 -41 76 0
38 -46 93 0
26 -37 94 0
-26 53 -79 0
78 87 -94 0
65 76 -87 0
23 51 -62 0
-11 -36 57 0
41 59 -65 0
-56 72 -91 0
13 -20 -46 0
-13 15 79 0
-17 47 -60 0
-13 -44 99 0
-7 -38 67 0
37 -49 62 0
-14 -17 -79 0
-13 -15 -22 0
32 -33 -34 0
24 45 48 0
21 24 -48 0
-36 64 -85 0
10 -61 67 0
-5 44 59 0
-80 -85 -99 0
6 37 -97 0
-21 -34 64 0
-5 44 46 0
58 -76 97 0
-21 -36 75 0
-15 58 -59 0
-58 -76 -99 0
-2 15 33 0
-26 34 -57 0
-18 -82 -92 0
27 -80 -97 0
6 32 63 0
-34 -86 92 0
13 -61 97 0
-28 43 -98 0
5 39 -86 0
39 -45 92 0
27 -43 97 0
13 -58 -86 0
-28 -67 -93 0
-69 85 99 0
42 71 -72 0
10 -27 -63 0
-59 63 -83 0
36 86 -96 0
-2 36 75 0
-59 -71 89 0
36 -67 91 0
36 -60 63 0
-63 91 -93 0
25 87 92 0
-21 49 -71 0
-2 10 22 0
6 -18 41 0
6 71 -92 0
-53 -69 -71 0
-2 -53 -58 0
43 -45 -96 0
34 -45 -69 0
63 -86 -98 0
EOF";
