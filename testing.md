# Understanding RndLearnerV5

In order to understand where there may be redundant behaviors, or repeated tasks that could be handled by a helper function

I am going to start by listing member variables for this class, and then how these member variables are used inside the functions

```c++
    template <typename T>
    struct NumericPairAlias
    {
        // Check that T is a number (int, float, double, etc.)
        static_assert(std::is_arithmetic<T>::value, "Template type must be numeric");

        // Define the type
        using Type = std::pair<T, expr::Expr>;
    };

    // A helper alias to make usage cleaner: MyPair<int>
    template <typename T>
    using numExpr_t = typename NumericPairAlias<T>::Type;

    using ComplexExpr = typename std::pair<Expr, Expr>;

    struct
    {
        Expr realExpr;
        Expr imagExpr;
        Expr rootObject;
        bool principalSqrt;
    } algebraicExpr;
            Expr indexZero;
        Expr indexIncr;
        vector<HornRuleExt *> tr;
        vector<HornRuleExt *> fc;
        vector<HornRuleExt *> qr;
        map<int, ExprVector> invVars;
        map<int, ExprVector> invVarsPr;
        map<int, int> invVarsSz;
        map<int, ExprVector> auxVars;
        map<int, ExprVector> auxVarsPr;
        map<int, int> auxVarsSz;
        // vector<bool> hasNonlinearity; // helps determine which solver to use
        bool hasNonlinearity = false; // by default
        std::vector<std::vector<std::string>> polarVarNames;
        std::vector<std::vector<std::string>> initVarNames;
        map<int, std::vector<std::pair<std::string, std::string>>> pendingInitVarPairs;
        map<int, std::map<std::string, std::string>> initVarNameMap;
        map<int, ExprVector> initVars;
        /// Variables whose transition was an identity (v' = v) and has been
        /// rewritten to v' = v_init'.  For these, v = v_init is a global
        /// invariant property rather than a step-0-only property.
        map<int, std::set<std::string>> identityLinkedVarNames;
        map<int, Expr> indices;
        std::string probFilePath;

        Expr oneReal = mkTerm(mpq_class("1"), m_efac);
        Expr zeroReal = mkTerm(mpq_class("0"), m_efac);
        Expr expEpsilon = mkTerm(mpq_class("1/1000"), m_efac);
        std::vector<ExprSet> learnedExprs; // indexed by invNumber
        map<int, ExprVector> symbolicRoots;
        map<int, ExprVector> numericRoots;
        map<int, ExprVector> squareRoots;
        map<int, set<std::string>> squareRootExists;
        map<int, std::map<std::string, Expr>> rootMaps;
```

We know that, when we look at a transition system, we are thinking storing them as three formulae with a
set of variables for the destination variable, and the initial variables. We think of these three formulae
as "rules".
