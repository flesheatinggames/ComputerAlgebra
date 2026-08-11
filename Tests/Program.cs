using ComputerAlgebra;
using ComputerAlgebra.LinqCompiler;
using System;
using System.Collections.Generic;
using System.Linq;

namespace Tests
{
    class Program
    {
        static void Test(Expression Expr, Expression Result)
        {
            Expression T = Binary.ApproxEqual(Expr, Result);
            Expression TE = T.Evaluate();

            bool passed = TE.IsTrue();
            if (!passed)
            {
                // Special case for NSolve since it does not produce exact results.
                Expression pattern = "NSolve[x, y]";
                MatchContext m = pattern.Matches(Expr);
                if (m != null)
                {
                    IEnumerable<Equal> f = Set.MembersOf(m["x"]).Cast<Equal>();
                    passed = f.All(i => Call.Abs(Binary.Subtract(i.Left, i.Right).Evaluate(Set.MembersOf(Result).Cast<Arrow>())) < 1e-3);
                }
            }
            if (!passed)
                throw new Exception(String.Format("Test failed: {0} -> {1}", T, TE));
        }

        /// <summary>
        /// Two expressions that should be worth the same, each evaluated on its own before they are
        /// compared.
        /// </summary>
        /// <remarks>
        /// Test above builds one ApproxEqual around both and evaluates that, which is right when the
        /// expected side is written out literally. It does not always reduce when both sides are
        /// calls that have to be evaluated to produce a set first, which is the shape every property
        /// below has: the same thing done in two orders.
        ///
        /// A set of solutions is compared solution by solution rather than as a whole, on the size
        /// of the difference. Two Reals of the same value but different internal form compare
        /// unequal while subtracting to exactly zero — 2/3 arrived at by two routes does it — and
        /// that is a wart in Real rather than anything these properties are about. A wrong
        /// elimination is wrong by a lot, not by a representation.
        /// </remarks>
        static void TestSame(Expression A, Expression B)
        {
            Expression a = A.Evaluate(), b = B.Evaluate();
            if (!Same(a, b))
                throw new Exception(String.Format("Test failed: {0} is {1}, and {2} is {3}", A, a, B, b));
        }

        private static bool Same(Expression A, Expression B)
        {
            if (A is Constant ca && B is Constant cb)
                return Real.Abs(ca.Value - cb.Value) <= (Real)1e-9 * Real.Max(1, Real.Abs(ca.Value));

            if (A is Set || B is Set)
            {
                List<Expression> x = Set.MembersOf(A).ToList(), y = Set.MembersOf(B).ToList();
                if (x.Count != y.Count)
                    return false;
                foreach (Expression i in x)
                {
                    // Solutions are matched by what they solve for, so an elimination that produces
                    // them in a different order is not reported as a different answer.
                    if (i is Arrow ai)
                    {
                        Arrow bi = y.OfType<Arrow>().SingleOrDefault(j => j.Left.Equals(ai.Left));
                        if (bi is null || !Same(ai.Right, bi.Right))
                            return false;
                    }
                    else if (!y.Any(j => Same(i, j)))
                    {
                        return false;
                    }
                }
                return true;
            }

            return Binary.ApproxEqual(A, B).Evaluate().IsTrue();
        }

        static void Test(Expression fx, Func<double, double> Result)
        {
            Variable vx = Variable.New("x");
            Func<double, double> compiled = ExprFunction.New(fx, vx).Compile<Func<double, double>>();

            int N = 1000;
            for (int i = 0; i < N; ++i)
            {
                double x = (((double)i / N) * 2 - 1) * Math.PI;

                if (Math.Abs((double)fx.Evaluate(vx, x) - Result(x)) > 1e-6)
                    throw new Exception(String.Format("{0} -> {1} != {2}", fx, fx.Evaluate(vx, x), Result(x)));

                if (Math.Abs(compiled(x) - Result(x)) > 1e-6)
                    throw new Exception(String.Format("Miscompile: {0} -> {1} != {2}", fx, compiled(x), Result(x)));
            }
        }

        /// <summary>
        /// Row reduce, back substitute and solve over a subset of the columns, once with a symbol
        /// among the coefficients and once with that symbol's value in its place, and check the two
        /// agree.
        /// </summary>
        /// <remarks>
        /// Solve[] always reduces over every unknown, so nothing in the expression language reaches
        /// this path. TransientSolution uses it for every circuit it solves: it reduces over the
        /// derivative columns alone and leaves the rest of the system standing. A live circuit
        /// parameter is a symbol among the coefficients while it does so.
        ///
        /// The symbolic leg is given PivotConditions, which is what TransientSolution passes and
        /// what lets the two legs choose the same pivots — without it a symbolic entry scores zero
        /// against a numeric one of any size, so a system with a symbol in it would be reduced in a
        /// different order and the comparison would be measuring that instead.
        /// </remarks>
        static void TestPartialSolve(string Name, Expression[] Equations, Expression[] Unknowns, Expression[] Columns, Arrow[] At)
        {
            // As many equations as columns, so that the columns are determined by the unknowns
            // outside them and nothing else. With more equations than columns the reduced columns
            // are over-determined: any subset of the equations gives a different expression for
            // them, all of which agree only where the leftover equations are satisfied, and two
            // reductions that eliminated in a different order would be reported as disagreeing when
            // they do not.
            if (Equations.Length != Columns.Length)
                throw new Exception(Name + ": this comparison needs one equation per column");

            List<Arrow> symbolic = PartialSolve(Equations, Unknowns, Columns, At);
            List<Arrow> baked = PartialSolve(
                Equations.Select(i => i.Substitute(At)).ToArray(), Unknowns, Columns, null);

            if (symbolic.Count != Columns.Length || baked.Count != Columns.Length)
                throw new Exception(String.Format(
                    "{0}: of {1} columns, solving with a symbol present solved {2} and solving with its value solved {3}",
                    Name, Columns.Length, symbolic.Count, baked.Count));

            // Whatever the two legs left unsolved stands in for itself, at values chosen only to be
            // distinct and away from zero, so the solutions are compared as functions rather than
            // as arrangements of terms.
            List<Arrow> point = Unknowns
                .Where(i => !symbolic.Any(j => j.Left.Equals(i)))
                .Select((i, n) => Arrow.New(i, (Expression)(Real)(1 + n * 0.37)))
                .ToList();

            foreach (Arrow i in symbolic)
            {
                Arrow j = baked.SingleOrDefault(k => k.Left.Equals(i.Left));
                if (j is null)
                    throw new Exception(String.Format("{0}: solving with a symbol present solved {1} and solving with its value did not", Name, i.Left));

                Expression a = i.Right.Substitute(At).Evaluate(point);
                Expression b = j.Right.Evaluate(point);
                if (!(a is Constant ca) || !(b is Constant cb) || Real.Abs(ca.Value - cb.Value) > 1e-9)
                    throw new Exception(String.Format(
                        "{0}: {1} is {2} when the symbol is eliminated and then substituted, and {3} when it is substituted and then eliminated",
                        Name, i.Left, a, b));
            }
        }

        private static List<Arrow> PartialSolve(Expression[] Equations, Expression[] Unknowns, Expression[] Columns, Arrow[] At)
        {
            SystemOfEquations S = new SystemOfEquations(Equations.Cast<Equal>(), Unknowns);
            List<Expression> columns = Columns.ToList();
            S.RowReduce(columns, At);
            S.BackSubstitute(columns);
            return S.Solve(columns);
        }

        static void Main(string[] args)
        {
            System.Diagnostics.Stopwatch timer = new System.Diagnostics.Stopwatch();
            timer.Start();

            // Function equality tests.
            Test("Abs[x]", Math.Abs);
            Test("Sign[x]", x => x > 0 ? 1 : (x < 0 ? -1 : 0));

            Test("Sin[x]", Math.Sin);
            Test("Cos[x]", Math.Cos);
            Test("Tan[x]", Math.Tan);
            Test("Sec[x]", x => 1 / Math.Cos(x));
            Test("Csc[x]", x => 1 / Math.Sin(x));
            Test("Cot[x]", x => 1 / Math.Tan(x));

            Test("ArcSin[x]", Math.Asin);
            Test("ArcCos[x]", Math.Acos);
            Test("ArcTan[x]", Math.Atan);
            Test("ArcSec[x]", x => Math.Acos(1 / x));
            Test("ArcCsc[x]", x => Math.Asin(1 / x));
            Test("ArcCot[x]", x => Math.Atan(1 / x));

            Test("Sinh[x]", Math.Sinh);
            Test("Cosh[x]", Math.Cosh);
            Test("Tanh[x]", Math.Tanh);
            Test("Sech[x]", x => 1 / Math.Cosh(x));
            Test("Csch[x]", x => 1 / Math.Sinh(x));
            Test("Coth[x]", x => 1 / Math.Tanh(x));

            Test("Sqrt[x]", Math.Sqrt);
            Test("Exp[x]", Math.Exp);
            Test("Ln[x]", Math.Log);
            Test("Log[x, 2]", x => Math.Log(x, 2));
            Test("Log[x, 6]", x => Math.Log(x, 6));

            Test("Floor[x]", Math.Floor);
            Test("Ceiling[x]", Math.Ceiling);
            Test("Round[x]", Math.Round);

            // Basic operations.
            Test("IsConstant[3]", "1");
            Test("IsConstant[x]", "IsConstant[x]");
            Test("IsInteger[2]", "1");
            Test("IsInteger[2.1]", "0");
            Test("IsInteger[x]", "IsInteger[x]");
            Test("-1.0", "-1");
            Test("-1.2e1", "-12");
            Test("Abs[e - 2.7183] < 0.01", "1");
            Test("Abs[Pi - 3.1416] < 0.01", "1");
            Test("1 > 0", "1");
            Test("0 > 1", "0");
            Test("1 >= 0", "1");
            Test("1 >= 1", "1");
            Test("1 >= 2", "0");
            Test("1 < 0", "0");
            Test("0 < 1", "1");
            Test("1 <= 0", "0");
            Test("1 <= 1", "1");
            Test("1 <= 2", "1");

            // Ordering and equality of negative rationals. Both of these were wrong until
            // Stompbench milestone A4, and both are reached by the elimination: it scores a pivot
            // by magnitude and it takes a reciprocal of every pivot it uses.
            //
            // Comparing two negatives that share a numerator took a shortcut that only holds above
            // zero, so -1/2 was reported as the larger.
            Test("-1/2 < -1/4", "1");
            Test("-1/4 > -1/2", "1");
            Test("-1/2 > -1/4", "0");
            Test("-1/3 < -1/4", "1");
            Test("1/2 > 1/4", "1");
            // A negative raised to an odd negative power put its sign in the denominator, which is
            // not the form the type's own equality, ordering and absolute value assume. The results
            // are equal, so nothing here is arithmetic that needs checking — the question is
            // whether a number is equal to and ordered against itself.
            Test("(-3/4)^-1 == -4/3", "1");
            Test("(-3/4)^-1 < -4/3", "0");
            Test("(-3/4)^-1 > -4/3", "0");
            Test("Abs[(-3/4)^-1] == 4/3", "1");
            Test("Abs[(-3/4)^-1] > 0", "1");
            Test("Sign[(-3/4)^-1]", "-1");
            Test("(-3/4)^-3 == -64/27", "1");
            Test("Abs[(-2/5)^-3] == 125/8", "1");
            Test("(-2)^-1 == -1/2", "1");
            //Test("f'[t]", "D[f[t], t]");

            Test("Sqrt[x] : x->4", "2");
            Test("D[x^2, x] : x->1", "2");
            Test("Sin[x] : x->t", "Sin[t]");
            Test("x + y : {x->1, y->2}", "3");
            Test("D[f[x], x] : x->0", "D[f[x], x] : x->0");
            Test("D[Cos[x], x] : x->0", "0");

            // Functional equivalents.
            Test("Ln[x]", "Log[x, e]");
            Test("Ln[x/2]", "Log[x/2, e]");
            Test("Sqrt[x]", "x^(1/2)");
            Test("Sqrt[x*A]", "(A*x)^(1/2)");
            Test("Exp[x]", "e^x");
            Test("Exp[2*x]", "e^(2*x)");

            // Basic arithmetic.
            Test("x + x", "2*x");
            Test("2*-x", "-2*x");
            Test("2*x + 3*x", "5*x");
            Test("2*x - 3*x", "-x");
            Test("-(2*x + 3*x)", "-5*x");
            Test("20*s - 20*s", "0");
            Test("x*x", "x^2");
            Test("x*x^2", "x^3");
            Test("x^3*x^2", "x^5");
            Test("x/x", "1");
            Test("x/-x", "-1");
            Test("x/x^2", "1/x");
            Test("x^3/x^2", "x");
            Test("x^-1 - 1/x", "0");
            Test("(x^2)^3", "x^6");
            Test("x/(y/z)", "(z*x)/y");
            Test("(x/y)/z", "x/(y*z)");
            Test("(x/y)/(z/w)", "(x*w)/(y*z)");
            Test("(x - y)/(y - x)", "-1");
            Test("(x - y)^3/(y - x)", "-(x - y)^2");
            Test("(x - y)^3/(y - x)^2", "(x - y)");
            Test("(x - y)/(y - x)^2", "1/(x - y)");
            Test("(x - y)/(y - x)^3", "-1/(x - y)^2");

            // Expand.
            // Some of these fail only because the order of the results is wrong.
            Test("Expand[2*(x + 2)]", "2*x + 4");
            //Test("Expand[x*(3*x + 2) + 4]", "3*x^2 + 2*x + 4");
            Test("Expand[(x + 1)*(x - 1)]", "x^2 - 1");
            //Test("Expand[(x + 1)^3]", "x^3 + 3*x^2 + 3*x + 1");
            //Test("Expand[(x + 1)^5]", "x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1");
            //Test("Expand[(x + 1)^7]", "x^7 + 7*x^6 + 21*x^5 + 35*x^4 + 35*x^3 + 21*x^2 + 7*x + 1");
            Test("Expand[a*(b + c)]", "a*b + a*c");
            Test("Expand[(a + b)*(c + d)]", "a*c + a*d + b*c + b*d");
            Test("Expand[(a + b)*(c + d)*(f + g)]", "a*c*f + a*d*f + b*c*f + b*d*f + a*c*g + a*d*g + b*c*g + b*d*g");
            Test("Expand[1/(s^3 + s), s]", "1/s - s/(s^2 + 1)");

            // Factor.
            //Test("Factor[A*x^2 + B*x + C]", "(x - ((-B + Sqrt[B^2 - 4*A*C])/(2*A)))*(x - ((-B - Sqrt[B^2 - 4*A*C])/(2*A)))");
            Test("Factor[x^2 - x, x]", "x*(x - 1)");
            Test("Factor[x^4 - x^2, x]", "x^2*(x^2 - 1)");
            Test("Factor[2*x^2 + 2*x*y, x]", "2*x*(x + y)");
            Test("Factor[A*Exp[x] + B*Exp[x] + C*Sin[x] + D*Sin[x]]", "(A + B)*Exp[x] + (C + D)*Sin[x]");
            Test("Factor[A*Exp[x] + B*Exp[x] + A*Sin[x] + B*Sin[x]]", "(A + B)*(Exp[x] + Sin[x])");

            // Factoring must not change what an expression is worth. Stated as a property rather
            // than as an expected form, because the point is the value and not the arrangement, and
            // because a hand-written expected form is a second thing that can be wrong.
            //
            // Every case below has a reciprocal in it. Until Stompbench milestone A4 they all gave
            // the wrong answer or did not terminate, because the common factor a sum was divided
            // through by could be the base of a power that was never a factor of the term on its
            // own: A/x + B/x came back as (A + B)*x/x, which is A + B. Nothing here had a
            // reciprocal in it before, and nothing that called Factor produced one either until a
            // circuit's coefficients stopped being numbers.
            TestSame("Factor[A*x^-1 + B*x^-1] : {A->2, B->3, x->5}", "A*x^-1 + B*x^-1 : {A->2, B->3, x->5}");
            TestSame("Factor[A/x + B/x] : {A->2, B->3, x->5}", "A/x + B/x : {A->2, B->3, x->5}");
            TestSame("Factor[A/x + B/x + C] : {A->2, B->3, C->7, x->5}", "A/x + B/x + C : {A->2, B->3, C->7, x->5}");
            TestSame("Factor[A/x + B/y] : {A->2, B->3, x->5, y->7}", "A/x + B/y : {A->2, B->3, x->5, y->7}");
            TestSame("Factor[A*y/x + B*z/x] : {A->2, B->3, x->5, y->7, z->11}", "A*y/x + B*z/x : {A->2, B->3, x->5, y->7, z->11}");
            TestSame("Factor[A/x + B/x^2] : {A->2, B->3, x->5}", "A/x + B/x^2 : {A->2, B->3, x->5}");
            TestSame("Factor[A/(G + 1) + B/(G + 1)] : {A->2, B->3, G->5}", "A/(G + 1) + B/(G + 1) : {A->2, B->3, G->5}");
            TestSame("Factor[x^2 + x^3] : x->5", "x^2 + x^3 : x->5");
            TestSame("Factor[A*x^2 + B*x^2] : {A->2, B->3, x->5}", "A*x^2 + B*x^2 : {A->2, B->3, x->5}");
            TestSame("Factor[(A + B)/x] : {A->2, B->3, x->5}", "(A + B)/x : {A->2, B->3, x->5}");
            TestSame("Factor[-A/x - B/x] : {A->2, B->3, x->5}", "-A/x - B/x : {A->2, B->3, x->5}");
            TestSame("Factor[2*A/x + 2*B/x] : {A->2, B->3, x->5}", "2*A/x + 2*B/x : {A->2, B->3, x->5}");
            TestSame("Factor[A*Sqrt[x] + B*Sqrt[x]] : {A->2, B->3, x->5}", "A*Sqrt[x] + B*Sqrt[x] : {A->2, B->3, x->5}");

            // The same property on the shape a circuit with a live parameter produces: a sum of
            // rational functions of a symbol that is a coefficient of an unknown rather than an
            // unknown itself.
            TestSame("Factor[y*G/(G + 1) + z*G/(G + 1)] : {y->2, z->3, G->0.5}", "y*G/(G + 1) + z*G/(G + 1) : {y->2, z->3, G->0.5}");
            TestSame("Factor[y/(G + 1) + z/(H + 1)] : {y->2, z->3, G->0.5, H->0.25}", "y/(G + 1) + z/(H + 1) : {y->2, z->3, G->0.5, H->0.25}");

            // Exponential functions.
            //Test("Ln[a^b]/b", "Ln[a]");
            //Test("Ln[Exp[x]]", "x");
            //Test("Log[b^x, b]", "x");
            //Test("Log[x, 3]", "Ln[x]/Ln[3]");
            //Test("Ln[x*y]", "Ln[x] + Ln[y]");
            //Test("Ln[x/y]", "Ln[x] - Ln[y]");
            //Test("Ln[x*y^2]", "Ln[x] + 2*Ln[y]");

            //// Hyperbolic functions.
            //Test("Exp[x] + Exp[-x]", "2*Cosh[x]");
            //Test("Exp[2*x] - Exp[-2*x]", "2*Sinh[2*x]");
            //Test("(Exp[x] - Exp[-x])/(Exp[x] + Exp[-x])", "Tanh[x]");
            //Test("(Exp[2*x] + Exp[-2*x])/(Exp[2*x] - Exp[-2*x])", "Coth[2*x]");
            //Test("2/(Exp[x] + Exp[-x])", "Sech[x]");
            //Test("3/(Exp[2*x] - Exp[-2*x])", "1.5*Csch[2*x]");

            //// Trig functions.
            //Test("Sin[x]/Cos[x]", "Tan[x]");
            //Test("Cos[x^2]/Sin[x^2]", "Cot[x^2]");
            //Test("Tan[x]*Cos[x]", "Sin[x]");
            //Test("Sin[x]^2 + Cos[x]^2", "1");
            //Test("y*Sin[x]^2 + y*Cos[x]^2", "y");

            // Derivatives.
            Test("D[Sin[x], x]", "Cos[x]");
            Test("D[Cos[x], x]", "-Sin[x]");
            Test("D[Tan[x], x]", "Sec[x]^2");
            Test("D[Sec[x], x]", "Sec[x]*Tan[x]");
            Test("D[Csc[x], x]", "-Csc[x]*Cot[x]");
            Test("D[Cot[x], x]", "-Csc[x]^2");

            Test("D[Sinh[A*x], x]", "A*Cosh[A*x]");
            Test("D[Cosh[A*x + B], x]", "A*Sinh[A*x + B]");
            Test("D[Tanh[A*x^2 + B*x + C], x]", "(2*A*x + B)*Sech[A*x^2 + B*x + C]^2");
            Test("D[Sech[x], x]", "-Sech[x]*Tanh[x]");
            Test("D[Csch[x], x]", "-Csch[x]*Coth[x]");
            Test("D[Coth[x], x]", "-Csch[x]^2");

            Test("D[A*x + B*x^2, x]", "A + 2*B*x");
            Test("D[(x^2 + 1)^5, x]", "5*(2*x)*(x^2 + 1)^4");
            Test("D[Ln[x], x]", "1/x");
            //Test("D[Ln[Abs[x]], x]", "Abs[x]/x^2");
            Test("D[(x + 1)^2, x]", "2*(x + 1)");
            Test("D[Exp[x^2], x]", "Exp[x^2]*2*x");
            Test("D[Exp[x^5], x]", "Exp[x^5]*5*x^4");
            //Test("D[Sqrt[2*x], x]", "1/Sqrt[2*x]");
            Test("D[Exp[u]:u->Sin[x], x]", "Exp[Sin[x]]*Cos[x]");
            Test("D[Pow[e^2, x^2], x]", "2*x*Pow[e^2, x^2]*Ln[e^2]");

            // Solve.
            Test("Solve[y == A*x + B, x]", "x -> (y - B)/A");
            Test("Solve[{2*x + 4*y == 8, x == 2*y + 3}, {x, y}]", "{x -> 7/2, y -> 1/4}");
            Test("Solve[{2*x + 4*y == A, x == 2*y + B}, {x, y}]", "{x->A/4 + B/2, y->A/8 - B/4}");

            // A symbol that is a coefficient of an unknown rather than a constant term. A and B
            // above sit in the constant column, which is the easy case: the elimination never
            // divides by them and never has to judge their size. A live circuit parameter is a
            // conductance, so it multiplies an unknown, and until Stompbench milestone A4 nothing
            // anywhere tested that.
            //
            // Stated as eliminating and then substituting against substituting and then
            // eliminating, because that is the property the solver has to have and it needs no
            // arithmetic worked out by hand to check.
            TestSame("Solve[{G*x + 4*y == 8, x == 2*y + 3}, {x, y}] : G->0.5",
                 "Solve[{0.5*x + 4*y == 8, x == 2*y + 3}, {x, y}]");
            TestSame("Solve[{2*x + G*y == 8, x == 2*y + 3}, {x, y}] : G->4",
                 "Solve[{2*x + 4*y == 8, x == 2*y + 3}, {x, y}]");
            TestSame("Solve[{G*x + 2*y + 3*z == 1, 4*x + 5*y + 6*z == 2, 7*x + 8*y + 10*z == 4}, {x, y, z}] : G->1",
                 "Solve[{x + 2*y + 3*z == 1, 4*x + 5*y + 6*z == 2, 7*x + 8*y + 10*z == 4}, {x, y, z}]");
            TestSame("Solve[{x + G*y + 3*z == 1, 4*x + 5*y + 6*z == 2, 7*x + 8*y + 10*z == 4}, {x, y, z}] : G->2",
                 "Solve[{x + 2*y + 3*z == 1, 4*x + 5*y + 6*z == 2, 7*x + 8*y + 10*z == 4}, {x, y, z}]");
            TestSame("Solve[{G*x + H*y == 8, x == 2*y + 3}, {x, y}] : {G->0.5, H->4}",
                 "Solve[{0.5*x + 4*y == 8, x == 2*y + 3}, {x, y}]");
            // A potentiometer's two halves: one symbol in two entries, constrained to sum to a
            // constant, which is the commonest way a knob reaches a system.
            TestSame("Solve[{G*x + (1 - G)*y == 8, x == 2*y + 3}, {x, y}] : G->0.25",
                 "Solve[{0.25*x + 0.75*y == 8, x == 2*y + 3}, {x, y}]");
            // The same symbol in more than one equation, which is what a shared node gives.
            TestSame("Solve[{G*x + 4*y == 8, G*x - 2*y == 3}, {x, y}] : G->0.5",
                 "Solve[{0.5*x + 4*y == 8, 0.5*x - 2*y == 3}, {x, y}]");

            // The same property on the column-subset path.
            TestPartialSolve("two of three columns, symbol on the diagonal",
                new Expression[] { "G*x + 4*y + 2*z == 8", "x - 2*y + z == 3" },
                new Expression[] { "x", "y", "z" },
                new Expression[] { "x", "y" },
                new Arrow[] { Arrow.New("G", 0.5) });
            TestPartialSolve("two of three columns, symbol off the diagonal",
                new Expression[] { "2*x + G*y + 2*z == 8", "x - 2*y + z == 3" },
                new Expression[] { "x", "y", "z" },
                new Expression[] { "x", "y" },
                new Arrow[] { Arrow.New("G", 4) });
            TestPartialSolve("two of three columns, symbol only outside them",
                new Expression[] { "2*x + 4*y + G*z == 8", "x - 2*y + z == 3" },
                new Expression[] { "x", "y", "z" },
                new Expression[] { "x", "y" },
                new Arrow[] { Arrow.New("G", 2) });
            TestPartialSolve("two of four columns, two independent symbols",
                new Expression[] { "G*x + 4*y + 2*z + w == 8", "x - H*y + z == 3" },
                new Expression[] { "x", "y", "z", "w" },
                new Expression[] { "x", "y" },
                new Arrow[] { Arrow.New("G", 0.5), Arrow.New("H", 2) });
            TestPartialSolve("a potentiometer's two halves across three of four columns",
                new Expression[] { "G*x + (1 - G)*y + 2*z + w == 8", "x - 2*y + z == 3", "x + y - z + 2*w == 1" },
                new Expression[] { "x", "y", "z", "w" },
                new Expression[] { "x", "y", "z" },
                new Arrow[] { Arrow.New("G", 0.25) });
            // Enough columns and enough symbols for the two-pass pivot rule to have a real choice
            // to make between a number and an expression of comparable size.
            TestPartialSolve("four of five columns, three symbols spread through them",
                new Expression[]
                {
                    "G*x + 4*y + 2*z + w + v == 8",
                    "x - H*y + z + 3*w == 3",
                    "2*x + y - z + 2*w - v == 1",
                    "x - y + K*z - w + 4*v == 2",
                },
                new Expression[] { "x", "y", "z", "w", "v" },
                new Expression[] { "x", "y", "z", "w" },
                new Arrow[] { Arrow.New("G", 0.5), Arrow.New("H", 2), Arrow.New("K", 1e-4) });

            // NSolve.
            Test("NSolve[x == Cos[x], x->0.5]", "x->0.739085");
            Test("NSolve[2 == Exp[x] - Exp[-x], x->0.5]", "x->0.881374");
            Test("NSolve[{y == x^2, x^2 + y^2 == 1}, {x->1, y->1}]", "{x->0.786, y->0.618}");
            Test("NSolve[{y == x^2, x^2 + y^2 == 1, z == x + y}, {x->1, y->1, z->1}]", "{x->0.786151, y->0.618034, z->1.40419}");
            Test("NSolve[{z == x^2, x^2 + y^2 == 1, z == y}, {x->1, y->1, z->1}]", "{x->0.786151, y->0.618034, z->0.618034}");
            Test("NSolve[{Exp[x + y] == 1, Exp[x - 2*y] == 2}, {x->0.5, y->0.5}]", "{x->0.231049, y->-0.231049}");
            Test("NSolve[(((0.01*Vo) + (-0.01*1) + (1E-12*Exp[(38.6847*Vo)]) + (-1E-12*Exp[(-38.6847*Vo)]))==0), Vo->0.57]", "Vo->0.573208");
            Test("NSolve[(((0.01*Vo) + (-0.01*1) + (1E-12*Exp[(38.6847*Vo)]) + (-1E-12*Exp[(-38.6847*Vo)]))==0), Vo->0]", "Vo->0.573208");
            Test("NSolve[(Ln[((0.01*Vo) + (1E-12*Exp[(38.6847*Vo)]) + (-1E-12*Exp[(-38.6847*Vo)]))]==Ln[0.01]), Vo->0.01]", "Vo->0.573208");

            // DSolve.
            Test("DSolve[D[y[t], t]==y[t], y[t], y[0]->1, t]", "y[t]->Exp[t]");
            Test("DSolve[D[y[t], t]==y[t], y[t], y[0]->C, t]", "y[t]->C*Exp[t]");
            Test("DSolve[D[y[t], t]==t, y[t], y[0]->0, t]", "y[t]->t^2/2");
            Test("DSolve[D[y[t], t]==1, y[t], y[0]->0, t]", "y[t]->t");
            Test("DSolve[D[D[y[t], t], t]==1, y[t], {y[0]->0, (D[y[t], t]:t->0)->0}, t]", "y[t]->t^2/2");
            Test("DSolve[D[y[t], t]==-y[t], y[t], y[0]->1, t]", "y[t]->Exp[-t]");
            Test("DSolve[D[y[t], t]==2*y[t], y[t], y[0]->1, t]", "y[t]->Exp[2*t]");
            Test("DSolve[D[y[t], t]==y[t]/3, y[t], y[0]->C, t]", "y[t]->C*Exp[t/3]");
            Test("DSolve[D[y[t], t] + y[t]==0, y[t], y[0]->1, t]", "y[t]->Exp[-t]");
            Test("DSolve[D[y[t], t]==Sin[t], y[t], y[0]->0, t]", "y[t]->1 - Cos[t]");

            //Test("DSolve[I[y[t], t]==y[t], y[t], y[0]->1, t]", "y[t]->Exp[t]");
            Test("DSolve[I[y[t], t]==t, y[t], y[0]->1, t]", "y[t]->1");
            Test("DSolve[I[y[t], t]==t^2/2, y[t], y[0]->1, t]", "y[t]->t");
            Test("DSolve[I[y[t], t]==Sin[t], y[t], y[0]->1, t]", "y[t]->Cos[t]");
            Test("DSolve[I[y[t], t]==Sin[t] + t, y[t], y[0]->1, t]", "y[t]->Cos[t] + 1");

            Console.WriteLine("{0} ms", timer.ElapsedMilliseconds);
            Console.WriteLine("TransformCalls: {0}", TransformSet.TransformCalls);
        }
    }
}
