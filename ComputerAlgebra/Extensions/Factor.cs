using System;
using System.Collections.Generic;
using System.Linq;

namespace ComputerAlgebra
{
    public static class FactorExtension
    {
        // Enumerates x, splitting negative constants into a positive constant and -1.
        //
        // Everything yielded here is multiplied back together below — a term the chosen factor does
        // not divide is rebuilt with Product.New, and a term it does divide is rebuilt from what is
        // left after the factor is removed — so the product of what this yields has to be x itself.
        // Splitting -2 into -1 and 2 keeps that, and is what lets 2*A - 2*B factor out the 2.
        //
        // Yielding the base of a power alongside the power did not. It was there so that x^2 and
        // x^3 could be seen to share an x, but nothing divided the term by the factor it removed:
        // pulling x out of the list [x^2, x] left [x^2], which multiplied by x is x^3 and not x^2.
        // A/x + B/x came back as (A + B)*x/x, which is A + B, and A/x + B/x^2 did not terminate.
        // Nothing in this library produced a sum of reciprocals until Stompbench milestone A4 made
        // a circuit's coefficients symbolic, which is why it went unnoticed; a solved circuit whose
        // coefficients are all numbers has no power among its terms and never reached it. See
        // docs/stompbench-a4-result.md.
        private static IEnumerable<Expression> FactorsOf(Expression x)
        {
            foreach (Expression i in Product.TermsOf(x))
            {
                if (i is Constant && (Real)i < 0)
                {
                    yield return -1;
                    yield return Real.Abs((Real)i);
                }
                else
                {
                    yield return i;
                }
            }
        }

        /// <summary>
        /// Distribute products across sums.
        /// </summary>
        /// <param name="f"></param>
        /// <param name="x"></param>
        /// <returns></returns>
        public static Expression Factor(this Expression f, Expression x)
        {
            // If f is a product, just factor its terms.
            if (f is Product product)
                return Product.New(product.Terms.Select(i => i.Factor(x)));

            // If if is l^r, factor l and distribute r.
            if (f is Power power)
            {
                Expression l = power.Left.Factor(x);
                Expression r = power.Right;
                return Product.New(Product.TermsOf(l).Select(i => Power.New(i, r)));
            }

            // If f is a polynomial of x, use polynomial factoring methods.
            if (f is Polynomial p && (p.Variable.Equals(x) || (x is null)))
                return p.Factor();

            // Try interpreting f as a polynomial of x.
            if (!(x is null))
            {
                // If f is a polynomial of x, factor it.
                try
                {
                    return Polynomial.New(f, x).Factor();
                }
                catch (Exception) { }
            }

            // Just factor out common sub-expressions.
            if (f is Sum s)
            {
                // Make a list of each terms' products.
                List<List<Expression>> terms = s.Terms.Select(i => FactorsOf(i).ToList()).ToList();

                // All of the distinct factors.
                IEnumerable<Expression> factors = terms.SelectMany(i => i.Except(1, -1)).Distinct();
                // Choose the most common factor to factor.
                Expression factor = factors.ArgMax(i => terms.Count(j => j.Contains(i)));
                // Find the terms that contain the factor.
                List<List<Expression>> contains = terms.Where(i => i.Contains(factor)).ToList();
                // If more than one term contains the factor, pull it out and factor the resulting expressions (again).
                if (contains.Count() > 1)
                {
                    Expression factored = Sum.New(contains.Select(i => Product.New(i.Except(factor))));
                    Expression not_factored = Sum.New(terms.Except(contains).Select(i => Product.New(i)));
                    return Sum.New(Product.New(factor, factored), not_factored).Factor(null);
                }
            }
            return f;
        }

        public static Expression Factor(this Expression f) { return Factor(f, null); }
    }
}
