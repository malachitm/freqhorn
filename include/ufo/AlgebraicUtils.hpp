#ifndef ALGEBRAIC_UTILS__HPP_
#define ALGEBRAIC_UTILS__HPP_

/**
 * Utility functions for working with ALNUM (algebraic number) Expr nodes.
 *
 * An ALNUM expression wraps an AlgebraicNum value that stores:
 *   - An isolating rational interval  [lower, upper]
 *   - The integer polynomial whose root defines the number
 *   - The root index (which root of the polynomial)
 *
 * These helpers let downstream code query, compare, and convert algebraic
 * numbers without reaching into the Terminal<AlgebraicNum> internals.
 */

#include "ufo/Expr.hpp"

namespace ufo
{
    // ---------------------------------------------------------------
    //  Predicates
    // ---------------------------------------------------------------

    /// True iff \p e is an algebraic number (ALNUM terminal).
    inline bool isAlgebraicNum(Expr e) { return isOpX<ALNUM>(e); }

    // ---------------------------------------------------------------
    //  Accessors  (precondition: isAlgebraicNum(e))
    // ---------------------------------------------------------------

    /// Return the full AlgebraicNum value stored inside an ALNUM Expr.
    inline const AlgebraicNum &getAlgebraicNum(Expr e)
    {
        return getTerm<AlgebraicNum>(e);
    }

    /// Lower bound of the isolating interval (exact rational).
    inline mpq_class algebraicLower(Expr e)
    {
        return getAlgebraicNum(e).lower;
    }

    /// Upper bound of the isolating interval (exact rational).
    inline mpq_class algebraicUpper(Expr e)
    {
        return getAlgebraicNum(e).upper;
    }

    /// Rational midpoint of the isolating interval.
    inline mpq_class algebraicMidpoint(Expr e)
    {
        return getAlgebraicNum(e).midpoint();
    }

    /// Double approximation (midpoint).
    inline double algebraicToDouble(Expr e)
    {
        return getAlgebraicNum(e).to_double();
    }

    /// Integer-polynomial coefficients [c_0, c_1, …, c_n].
    inline const std::vector<mpz_class> &algebraicPoly(Expr e)
    {
        return getAlgebraicNum(e).poly;
    }

    /// Root index (0-based).
    inline unsigned algebraicRootIndex(Expr e)
    {
        return getAlgebraicNum(e).rootIdx;
    }

    /// Degree of the defining polynomial.
    inline unsigned algebraicDegree(Expr e)
    {
        return getAlgebraicNum(e).degree();
    }

    /// True if the algebraic number is actually rational (degree <= 1).
    inline bool algebraicIsRational(Expr e)
    {
        return getAlgebraicNum(e).isRational();
    }

    // ---------------------------------------------------------------
    //  Conversions
    // ---------------------------------------------------------------

    /// Convert an ALNUM to an MPQ using the rational midpoint.
    /// Useful when downstream code only understands rationals.
    inline Expr algebraicToMPQ(Expr e)
    {
        mpq_class mid = getAlgebraicNum(e).midpoint();
        return mkTerm(mid, e->efac());
    }

    /// Return a pair of MPQ expressions (lower, upper) for the
    /// isolating interval.
    inline std::pair<Expr, Expr> algebraicInterval(Expr e)
    {
        const AlgebraicNum &a = getAlgebraicNum(e);
        return {mkTerm(a.lower, e->efac()),
                mkTerm(a.upper, e->efac())};
    }

    // ---------------------------------------------------------------
    //  Symbolic constraint builders
    // ---------------------------------------------------------------

    /**
     * Build the defining-polynomial constraint for variable \p var:
     *
     *   c_0 + c_1*var + c_2*var^2 + … + c_n*var^n = 0
     *
     * combined with the isolating-interval bounds:
     *
     *   lower <= var  AND  var <= upper
     *
     * The conjunction of these constraints uniquely characterises the
     * algebraic number among the reals.
     */
    inline Expr algebraicDefiningConstraint(Expr var, Expr alnumExpr)
    {
        const AlgebraicNum &a = getAlgebraicNum(alnumExpr);
        ExprFactory &efac = var->efac();

        // --- polynomial = 0 ---
        // Build:  c_0 + c_1*var + c_2*var^2 + ... + c_n*var^n
        Expr polyExpr = mkTerm(mpq_class(a.poly[0]), efac); // c_0 as rational
        Expr varPow = var;                                  // var^1
        for (size_t k = 1; k < a.poly.size(); ++k)
        {
            Expr ck = mkTerm(mpq_class(a.poly[k]), efac);
            Expr term = mk<MULT>(ck, varPow);
            polyExpr = mk<PLUS>(polyExpr, term);
            if (k + 1 < a.poly.size())
                varPow = mk<MULT>(varPow, var);
        }
        Expr zero = mkTerm(mpq_class(0), efac);
        Expr polyEq = mk<EQ>(polyExpr, zero);

        // --- isolating interval ---
        Expr lo = mkTerm(a.lower, efac);
        Expr hi = mkTerm(a.upper, efac);
        Expr intvl = mk<AND>(mk<LEQ>(lo, var), mk<LEQ>(var, hi));

        return mk<AND>(polyEq, intvl);
    }

    /**
     * Convenience: if \p e is ALNUM, return its midpoint as MPQ;
     * if it is already MPQ or MPZ, return as-is.
     * Returns nullptr for anything else.
     */
    inline Expr numericApprox(Expr e)
    {
        if (isOpX<ALNUM>(e))
            return algebraicToMPQ(e);
        if (isOpX<MPQ>(e) || isOpX<MPZ>(e))
            return e;
        return nullptr;
    }

} // namespace ufo

#endif // ALGEBRAIC_UTILS__HPP_
