using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace ComputerAlgebra
{
    /// <summary>
    /// List of equations and unknowns that supports row reduction and substitution of linear systems of equations. 
    /// </summary>
    public class SystemOfEquations : IEnumerable<LinearCombination>, IEnumerable
    {
        // What one entry of the system is worth as a pivot.
        //
        // Magnitude is the size of the entry, which for a coefficient that is not a number is the
        // size it has under the pivot conditions — the value the caller says the system will
        // actually be run at. Real.NegativeInfinity means the entry cannot be used at all.
        //
        // Size is how many atoms the entry's expression holds, and it is a cost rather than a
        // description. Eliminating with a pivot p divides every entry of every remaining row by p,
        // so the pivot's expression lands in the denominator of everything it touches and the next
        // step puts the next one inside that. A pivot that is a plain number costs nothing that
        // way — the entries stay the size they were — and a pivot that is already a large rational
        // function multiplies the size of every entry below it. Where two candidates are of
        // comparable magnitude the smaller one is worth choosing for that reason alone.
        private struct PivotCost
        {
            public readonly Real Magnitude;
            public readonly int Size;
            public PivotCost(Real Magnitude, int Size) { this.Magnitude = Magnitude; this.Size = Size; }
        }

        // Sizes are only ever compared, never reported, so counting stops once a candidate is
        // clearly worse than anything that could win. Without a stop the count is a full walk of an
        // expression that the growth this figure exists to control has already made enormous.
        private const int PivotSizeCap = 4096;

        // Single equation (linear combination of terms).
        private class Equation : DefaultDictionary<Expression, Expression>
        {
            private void AddTerm(IEnumerable<Expression> B, Expression t)
            {
                foreach (Expression b in B)
                {
                    if (Product.TermsOf(t).Count(i => i.Equals(b)) == 1)
                    {
                        this[b] += Product.New(Product.TermsOf(t).Except(b));
                        return;
                    }
                }
                this[1] += t;
            }

            public Equation(Equal Eq, IEnumerable<Expression> Terms)
                : base(0)
            {
                Terms = Terms.AsList();

                Expression f = Eq.Left - Eq.Right;
                foreach (Expression i in Sum.TermsOf(f.Expand()))
                    AddTerm(Terms, i);
            }

            public Equation(IEnumerable<KeyValuePair<Expression, Expression>> Terms)
                : base(0)
            {
                foreach (KeyValuePair<Expression, Expression> i in Terms)
                    this[i.Key] = i.Value;
            }

            public Expression Solve(Expression x)
            {
                return Unary.Negate(Sum.New(this.Where(i => !i.Key.Equals(x)).Select(i => Product.New(i.Key, i.Value)))) / this[x];
            }

            // What an entry is worth as a pivot, computed when it is first asked for and dropped
            // when Eliminate writes the entry.
            //
            // Keyed by the column rather than by its position, so that reordering the columns —
            // which full pivoting does on every step — invalidates nothing. Row swaps move whole
            // equations, and each equation carries its own costs, so those are safe too.
            private Dictionary<Expression, PivotCost> costs;

            public void InvalidateCost(Expression x) { costs?.Remove(x); }
            public void InvalidateCosts() { costs?.Clear(); }

            public PivotCost Cost(Expression x, IEnumerable<Arrow> PivotConditions)
            {
                if (costs == null)
                    costs = new Dictionary<Expression, PivotCost>();
                else if (costs.TryGetValue(x, out PivotCost cached))
                    return cached;

                PivotCost cost = ComputeCost(x, PivotConditions);
                costs[x] = cost;
                return cost;
            }

            private PivotCost ComputeCost(Expression x, IEnumerable<Arrow> PivotConditions)
            {
                Expression ij = this[x];
                if (ij.EqualsZero())
                    return new PivotCost(Real.NegativeInfinity, 0);

                bool numeric = ij is Constant;
                int size = numeric ? 1 : ij.Atoms.Take(PivotSizeCap).Count();

                // Select the larger pivot if this is a constant, using the PivotConditions.
                if (!numeric && PivotConditions != null)
                    ij = ij.Evaluate(PivotConditions);

                // An expression that is not zero but evaluates to zero is as unusable as one that
                // is, and refusing it here is the only place that can tell. Eliminating with it
                // divides by its reciprocal, so choosing it produces an infinity at the first
                // evaluation rather than a bad answer, and the test above cannot see it because the
                // expression is genuinely not the zero expression — it is a difference of two free
                // parameters that happen to be equal, which is what two identical potentiometers at
                // the same position give. Added by Stompbench milestone A4; before it nothing ever
                // supplied PivotConditions, so this case could not arise.
                if (ij is Constant Z && Z.Value.EqualsZero())
                    return new PivotCost(Real.NegativeInfinity, size);

                return new PivotCost((ij is Constant C) ? Real.Abs(C.Value) : 0, size);
            }

            public Expression Expression { get { return Sum.New(this.Select(i => Product.New(i.Key, i.Value))); } }

            public bool DependsOn(IEnumerable<Expression> x)
            {
                DependsOnVisitor v = new DependsOnVisitor(x);
                // It's faster to check the keys first.
                return
                    this.Any(i => v.Visit(i.Key)) ||
                    this.Any(i => v.Visit(i.Value));
            }
            public bool DependsOn(params Expression[] x) { return DependsOn(x.AsEnumerable()); }

            public IEnumerable<Expression> Unknowns { get { return this.Keys.Where(i => !(i is Constant)); } }

            public override string ToString()
            {
                return Expression.ToString() + " == 0";
            }
        }

        private List<Expression> unknowns;
        /// <summary>
        /// Enumerate the unknowns x in the system.
        /// </summary>
        public IEnumerable<Expression> Unknowns { get { return unknowns; } }

        private List<Equation> equations = new List<Equation>();
        /// <summary>
        /// Enumerate the equations in the system in the form F(x) == 0.
        /// </summary>
        public IEnumerable<LinearCombination> Equations { get { return equations.Select(i => LinearCombination.New(i)); } }

        private SystemOfEquations(List<Equation> Equations, List<Expression> Unknowns)
        {
            equations = Equations;
            unknowns = Unknowns;
        }

        /// <summary>
        /// Create a new system of equations with the given equations and unknowns.
        /// </summary>
        /// <param name="Equations"></param>
        /// <param name="Unknowns"></param>
        public SystemOfEquations(IEnumerable<Equal> Equations, IEnumerable<Expression> Unknowns)
        {
            unknowns = Unknowns.ToList();
            AddRange(Equations);
        }

        public SystemOfEquations(IEnumerable<IEnumerable<KeyValuePair<Expression, Expression>>> Equations, IEnumerable<Expression> Unknowns)
        {
            unknowns = Unknowns.ToList();
            AddRange(Equations);
        }

        /// <summary>
        /// Create an empty system of equations for the unknowns.
        /// </summary>
        /// <param name="Unknowns"></param>
        public SystemOfEquations(IEnumerable<Expression> Unknowns)
        {
            unknowns = Unknowns.ToList();
        }

        public void Add(Equal Eq) { equations.Add(new Equation(Eq, unknowns)); }
        public void Add(IEnumerable<KeyValuePair<Expression, Expression>> Eq) { equations.Add(new Equation(Eq)); }
        public void AddRange(IEnumerable<Equal> Eqs) { equations.AddRange(Eqs.Select(i => new Equation(i, unknowns))); }
        public void AddRange(IEnumerable<IEnumerable<KeyValuePair<Expression, Expression>>> Eqs) { equations.AddRange(Eqs.Select(i => new Equation(i))); }

        // The first pivot cost function is the magnitude of the pivot.
        private Real PivotScore(int i, int j, IList<Expression> Columns, IEnumerable<Arrow> PivotConditions)
        {
            return equations[i].Cost(Columns[j], PivotConditions).Magnitude;
        }

        // The second pivot cost function is the number of things already zero that don't need to be eliminated.
        private int PivotEliminationZeros(int row, int col, int pi, int pj, IList<Expression> Columns)
        {
            // A pivot is better if the row containing the pivot has more zeros.
            int zeros = Columns.Count - equations[pi].Count;

            // A pivot is better if the column containing the pivot has more zeros.
            for (int i = row + 1; i < equations.Count; ++i)
            {
                if (i == pi) continue;

                if (equations[i][Columns[pj]].EqualsZero())
                    zeros += 1;
            }

            return zeros;
        }

        // How far below the largest pivot available a candidate may be and still be considered on
        // its other merits. The single-pass rule below has always used a factor of eight; the
        // two-pass rule keeps the same figure so that the two differ in how they search and not in
        // what they are willing to accept.
        private const int PivotTolerance = 8;

        /// <summary>
        /// Find the best pivot when the caller has said what the system's free symbols are worth.
        /// </summary>
        /// <remarks>
        /// Two passes, because the choice has to be made against the best pivot in the whole
        /// submatrix rather than against the best one seen so far. The single-pass rule below takes
        /// any candidate that beats the running best outright, so a large pivot found early rules
        /// out everything that comes after it within the tolerance — which is harmless when the
        /// only thing being traded off is magnitude, and not harmless once a plain number is worth
        /// preferring over an expression of the same size.
        ///
        /// Preferring the smaller expression is what makes a live parameter affordable. Milestone A4's first
        /// attempt supplied pivot conditions and left this rule alone, and three of the fourteen
        /// circuits with a knob stopped solving inside three minutes: given a magnitude, a symbolic
        /// entry of any size can outrank a small one, and eliminating with it puts its expression into the
        /// denominator of every entry of every row below, and the next step puts the next one
        /// inside that. The growth is in the size of each entry rather than in how many there are —
        /// on the MXR Phase 90 the entry count barely moved over the last ten columns while the
        /// time for a column went from a tenth of a second to ninety.
        ///
        /// Reached only when PivotConditions are supplied, which is only when a circuit has a live
        /// parameter, so a circuit without one provably takes the path it took before.
        /// </remarks>
        private Tuple<int, int> PivotWithConditions(int row, int col, int maxj, IList<Expression> Columns, IEnumerable<Arrow> PivotConditions)
        {
            Real largest = Real.NegativeInfinity;
            for (int i = row; i < equations.Count; ++i)
                for (int j = col; j <= maxj; ++j)
                {
                    Real m = equations[i].Cost(Columns[j], PivotConditions).Magnitude;
                    if (m > largest)
                        largest = m;
                }

            // Nothing in this submatrix can be used as a pivot.
            if (largest.IsNaN() || largest < 0)
                return new Tuple<int, int>(-1, -1);

            Real floor = largest / PivotTolerance;

            int besti = -1;
            int bestj = -1;
            int bestSize = 0;
            // To avoid computing the number of zeros unnecessarily, -1 means uncomputed.
            int zeros = -1;

            for (int i = row; i < equations.Count; ++i)
            {
                for (int j = col; j <= maxj; ++j)
                {
                    PivotCost c = equations[i].Cost(Columns[j], PivotConditions);
                    // Excludes the unusable as well as the too-small: an unusable entry scores
                    // negative infinity and the floor is never below zero.
                    if (c.Magnitude < floor)
                        continue;

                    if (besti < 0)
                    {
                        besti = i; bestj = j; bestSize = c.Size; zeros = -1;
                        continue;
                    }

                    // A smaller expression beats a larger one of comparable magnitude, whichever
                    // order the two were found in.
                    if (c.Size != bestSize)
                    {
                        if (c.Size < bestSize)
                        {
                            besti = i; bestj = j; bestSize = c.Size; zeros = -1;
                        }
                        continue;
                    }

                    // Two of the same size, so fall back to the rule that has always applied:
                    // prefer the pivot that leaves fewer entries to eliminate.
                    if (zeros == -1)
                        zeros = PivotEliminationZeros(row, col, besti, bestj, Columns);
                    int e = PivotEliminationZeros(row, col, i, j, Columns);
                    if (e > zeros)
                    {
                        zeros = e;
                        besti = i;
                        bestj = j;
                    }
                }
            }
            return new Tuple<int, int>(besti, bestj);
        }

        // Find the best pivot using full or partial pivoting.
        private Tuple<int, int> Pivot(int row, int col, IList<Expression> Columns, bool FullPivoting, IEnumerable<Arrow> PivotConditions)
        {
            // If we are full pivoting, we can consider any column after j.
            int maxj = FullPivoting ? Columns.Count - 1 : col;

            if (PivotConditions != null)
                return PivotWithConditions(row, col, maxj, Columns, PivotConditions);

            int besti = -1;
            int bestj = -1;
            Real score = Real.NegativeInfinity;
            // To avoid computing the number of zeros unnecessarily, -1 means uncomputed.
            int zeros = -1;

            for (int i = row; i < equations.Count; ++i)
            {
                for (int j = col; j <= maxj; ++j)
                {
                    // Check if we found a bigger pivot first.
                    Real s = PivotScore(i, j, Columns, PivotConditions);
                    if (s > score)
                    {
                        score = s;
                        // We don't know the tie-breaker cost yet.
                        zeros = -1;
                        besti = i;
                        bestj = j;
                    } 
                    else if (s > score / 8 && besti >= 0)
                    {
                        // The pivots are close enough. If another pivot has fewer non-zero eliminations, we should use that instead.
                        if (zeros == -1)
                            zeros = PivotEliminationZeros(row, col, besti, bestj, Columns);
                        int e = PivotEliminationZeros(row, col, i, j, Columns);
                        if (e > zeros)
                        {
                            // Don't update the score, so we don't repeatedly decay the score.
                            zeros = e;
                            besti = i;
                            bestj = j;
                        }
                    }
                }
            }
            return new Tuple<int, int>(besti, bestj);
        }

        // Swap rows i1 and i2.
        private void Swap(int i1, int i2)
        {
            Equation t = equations[i1];
            equations[i1] = equations[i2];
            equations[i2] = t;
        }

        // Swap columns j1 and j2.
        private static void Swap(IList<Expression> x, int j1, int j2)
        {
            Expression t = x[j1];
            x[j1] = x[j2];
            x[j2] = t;
        }

        // Eliminate the pivot position from row t using row s.
        private void Eliminate(int s, int t, Expression p, IEnumerable<Expression> Columns)
        {
            Equation T = equations[t];
            if (T[p].EqualsZero())
                return;

            Equation S = equations[s];

            // This is a pretty hot path, so avoid unnecessary evaluations.
            Expression scale = Product.New(-1, T[p], Binary.Power(S[p], -1));
            foreach (Expression j in Columns)
                if (!S[j].EqualsZero())
                {
                    T[j] += Product.New(S[j], scale);
                    T.InvalidateCost(j);
                }
            T[p] = 0;
            T.InvalidateCost(p);
        }

        private void RowReduce(IList<Expression> Columns, bool FullPivoting, IEnumerable<Arrow> PivotConditions)
        {
            // A pivot cost is only meaningful under the conditions it was computed with, and the
            // same system can be reduced more than once under different ones, so nothing is carried
            // across a call. Within a call the conditions do not change.
            foreach (Equation i in equations)
                i.InvalidateCosts();

            int row = 0;
            List<Expression> elim = unknowns.Append(1).ToList();
            for (int _j = 0; _j < Columns.Count; ++_j)
            {
                // Find the best pivot to use.
                Tuple<int, int> pivot = Pivot(row, _j, Columns, FullPivoting, PivotConditions);
                if (pivot.Item1 != -1)
                {
                    // Found a pivot, swap the rows and eliminate the remaining rows.
                    if (pivot.Item1 != row)
                        Swap(pivot.Item1, row);
                    if (_j != pivot.Item2)
                        Swap(Columns, _j, pivot.Item2);

                    Expression j = Columns[_j];
                    elim = elim.Except(j).ToList();
                    for (int i = row + 1; i < equations.Count; ++i)
                        Eliminate(row, i, j, elim);

                    ++row;
                }
            }
            equations.RemoveAll(i => i.Empty());
        }

        /// <summary>
        /// Row reduce the system in terms of the given columns with partial pivoting.
        /// </summary>
        /// <param name="Columns">Columns to perform row reduction on.</param>
        /// <param name="PivotConditions">Substitutions to use when considering an element as a pivot.</param>
        public void RowReduce(IEnumerable<Expression> Columns, IEnumerable<Arrow> PivotConditions = null)
        {
            RowReduce(Columns.AsList(), false, PivotConditions);
        }

        /// <summary>
        /// Row reduce the system in terms of the given columns with full pivoting. The Columns will be reordered according to a full pivot solution.
        /// </summary>
        /// <param name="Columns">Columns to perform row reduction on.</param>
        /// <param name="PivotConditions">Substitutions to use when considering an element as a pivot.</param>
        public void RowReduce(IList<Expression> Columns, IEnumerable<Arrow> PivotConditions = null)
        {
            RowReduce(Columns, true, PivotConditions);
        }

        /// <summary>
        /// Row reduce the system. The unknowns will be reorderd to reflect the full pivot solution.
        /// </summary>
        /// <param name="PivotConditions">Substitutions to use when considering an element as a pivot.</param>
        public void RowReduce(IEnumerable<Arrow> PivotConditions = null) { RowReduce(unknowns, PivotConditions); }

        private void BackSubstitute(IList<Expression> x)
        {
            List<Expression> elim = unknowns.Append(1).ToList();
            for (int i = Math.Min(x.Count, equations.Count) - 1, _j = x.Count - 1; _j >= 0; --_j)
            {
                Expression j = x[_j];
                elim = elim.Except(j).ToList();

                // While we still haven't reached a pivot row...
                while (i >= 0 && x.Take(_j).All(j2 => equations[i][j2].EqualsZero()))
                {
                    if (!equations[i][j].EqualsZero())
                    {
                        for (int i2 = i - 1; i2 >= 0; --i2)
                            Eliminate(i, i2, j, elim);
                        break;
                    }

                    --i;
                }
            }
            equations.RemoveAll(i => i.Empty());
        }

        /// <summary>
        /// Back-substitute the solutions for the given columns.
        /// </summary>
        /// <param name="Columns"></param>
        public void BackSubstitute(IEnumerable<Expression> Columns) { BackSubstitute(Columns.AsList()); }
        /// <summary>
        /// Back-substitute the solutions for all of the columns in the system.
        /// </summary>
        public void BackSubstitute() { BackSubstitute(unknowns); }

        private bool Solve(Expression x_i, IList<Expression> x, List<Arrow> fwd, List<Arrow> back)
        {
            foreach (Equation eq in equations.Reverse<Equation>())
            {
                if (eq[x_i].EqualsZero()) continue;

                bool allowFwd = !equations.Except(eq).Any(i => i.DependsOn(x_i));

                Expression s = eq.Solve(x_i);
                allowFwd = allowFwd && !s.DependsOn(x_i);
                bool allowBack = back != null && !s.DependsOn(unknowns);

                if (allowFwd)
                    fwd.Add(Arrow.New(x_i, s));
                else if (allowBack)
                    back.Add(Arrow.New(x_i, s));
                else
                    continue;

                // Remove the equation and unknown.
                equations.Remove(eq);
                x.Remove(x_i);
                if (!ReferenceEquals(x, unknowns))
                    unknowns.Remove(x_i);
                return true;
            }
            return false;
        }

        private bool SolveOne(IList<Expression> x, List<Arrow> fwd, List<Arrow> back)
        {
            foreach (Expression x_i in x)
                if (Solve(x_i, x, fwd, back))
                    return true;
            return false;
        }

        /// <summary>
        /// Solve the system for the given variables. The system must already be in row-echelon form, optionally with back substitution.
        /// 
        /// This method removes the equations and unknowns from the system as they are solved.
        /// </summary>
        /// <param name="x"></param>
        /// <returns>The solutions for the unknowns that were successfully solved. If the system was not back substituted, solutions may
        /// depend on previous solutions in the list.</returns>
        public List<Arrow> Solve(IEnumerable<Expression> x) {
            List<Arrow> fwd = new List<Arrow>();
            PartialSolve(x.AsList(), fwd, null);
            return fwd;
        }
        public List<Arrow> Solve() { return Solve(unknowns); }

        /// <summary>
        /// Solve the system for the given variables. The system must already be in row-echelon form, optionally with back substitution.
        /// 
        /// This method removes the equations and unknowns from the system as they are solved.
        /// </summary>
        /// <param name="x"></param>
        /// <param name="fwd"></param>
        /// <param name="back"></param>
        public void PartialSolve(IList<Expression> x, List<Arrow> fwd, List<Arrow> back)
        {
            fwd.Reverse();
            while (!x.Empty())
            {
                if (!SolveOne(x, fwd, back)) break;
            }
            fwd.Reverse();
        }
        public void PartialSolve(List<Arrow> fwd, List<Arrow> back) { PartialSolve(unknowns, fwd, back); }

        /// <summary>
        /// Find independent systems of equations within this system.
        /// </summary>
        /// <returns></returns>
        public IEnumerable<SystemOfEquations> Partition()
        {
            List<Expression> x = new List<Expression>();
            List<Equation> eqs = new List<Equation>();
            while (unknowns.Any())
            {
                x.Add(unknowns.Last());
                unknowns.RemoveAt(unknowns.Count - 1);

                do
                {
                    eqs.AddRange(equations.Where(i => i.DependsOn(x)));
                    equations.RemoveAll(i => eqs.Contains(i));

                    x.AddRange(unknowns.Where(i => eqs.Any(j => j.DependsOn(i))));
                    unknowns.RemoveAll(i => x.Contains(i));
                } while (equations.Any(i => i.DependsOn(x)));

                yield return new SystemOfEquations(eqs, x);
                x.Clear();
                eqs.Clear();
            }
        }

        // IEnumerable<LinearCombination>
        public IEnumerator<LinearCombination> GetEnumerator() { return Equations.GetEnumerator(); }

        IEnumerator IEnumerable.GetEnumerator() { return this.GetEnumerator(); }
    }
}
