#ifndef RNDLEARNERV5__HPP__
#define RNDLEARNERV5__HPP__

#include "RndLearnerV4.hpp"
#include "deep/Config.hpp"
#include <memory>
#include "deep/Horn.hpp"    // For CHCs, HornRuleExt
#include "ufo/Expr.hpp"     // For Expr, ExprVector, etc.
#include "ae/ExprSimpl.hpp" // For getConj, etc.
#include <fstream>
#include <sstream>
#include <vector>
#include <map>
#include <optional>
#include <algorithm> // For std::find
#include <boost/algorithm/string.hpp>
#include <nlohmann/json.hpp>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <iostream>
#include <string>
#include <utility>     // for std::pair
#include <type_traits> // for std::is_arithmetic_v
#include <sstream>     // Required for std::istringstream
#include <stdexcept>   // Required for exceptions
#include <iomanip>     // For output formatting
#include <cmath>       // For std::sqrt, std::abs
#include <chrono>      // For timing QF_NRA solver
#include <boost/range/combine.hpp>
#include <iostream>
#include <stdexcept>
#include <sys/wait.h>
#include <stdio.h>
#include <string>
using namespace std;
using namespace boost;

struct CommandResult
{
    std::string output;
    int exitCode;
    bool signaled;
    int signalNumber;
};

CommandResult exec(const char *cmd)
{
    char buffer[128];
    std::string wrappedCmd = std::string(cmd) + " 2>&1";
    std::string result = "";
    FILE *pipe = popen(wrappedCmd.c_str(), "r");
    if (!pipe)
        throw std::runtime_error("popen() failed!");
    int status = 0;
    try
    {
        while (fgets(buffer, sizeof buffer, pipe) != NULL)
        {
            result += buffer;
        }
    }
    catch (...)
    {
        pclose(pipe);
        throw;
    }
    status = pclose(pipe);

    CommandResult commandResult;
    commandResult.output = result;
    commandResult.exitCode = -1;
    commandResult.signaled = false;
    commandResult.signalNumber = 0;

    if (status != -1)
    {
        if (WIFEXITED(status))
        {
            commandResult.exitCode = WEXITSTATUS(status);
        }
        if (WIFSIGNALED(status))
        {
            commandResult.signaled = true;
            commandResult.signalNumber = WTERMSIG(status);
        }
    }

    return commandResult;
}

std::vector<std::string> getAllSqrtWords(const std::string &input)
{
    std::string modifiedString = input;
    std::vector<std::string> replacedWords;

    size_t pos = 0;

    while ((pos = modifiedString.find("sqrt", pos)) != std::string::npos)
    {
        // Confirm it's the start of a word
        if (pos == 0 || modifiedString[pos - 1] == ' ' || modifiedString[pos - 1] == '(')
        {
            // Find the end of the word — stop at any non-identifier character
            size_t endPos = pos + 4; // start after "sqrt"
            while (endPos < modifiedString.length() &&
                   modifiedString[endPos] != ' ' &&
                   modifiedString[endPos] != ')' &&
                   modifiedString[endPos] != '(' &&
                   modifiedString[endPos] != ',')
            {
                endPos++;
            }

            // Extract the suffix after "sqrt" (e.g., "36401")
            replacedWords.push_back(modifiedString.substr(pos + 4, endPos - (pos + 4)));

            // Replace the whole "sqrt<number>" token with "1.0"
            std::string replacement = "1.0";
            modifiedString.replace(pos, endPos - pos, replacement);

            pos += replacement.length();
        }
        else
        {
            pos += 4;
        }
    }

    return replacedWords;
}

struct phaseLemmas
{
    std::function<expr::Expr(expr::Expr)> min;
    std::function<expr::Expr(expr::Expr)> max;
};

namespace ufo
{
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

    class RndLearnerV5 : public RndLearnerV4
    {
    private:
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

        /// Persistent QF_NRA solver, lazily initialized on first use.
        /// Kept as std::optional because ZSolver has no default ctor.
        std::optional<ZSolver<EZ3>> nlsolver;

    public:
        RndLearnerV5(ExprFactory &_e, EZ3 &_z3, CHCs &_r, unsigned _to, int _debug) : RndLearnerV4(_e, _z3, _r, _to, false, false, 0, 0, false, 0, false, false,
                                                                                                   false, false, 0, 0, false, _debug) {}
        ~RndLearnerV5() {}
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

        Expr generateInitCond(int i)
        {
            Expr init = getInitBody(i);
            Expr conds = mk<AND>(mk<LEQ>(zeroReal, indices[i]), mk<LT>(indices[i], oneReal));
            return mk<IMPL>(conds, init);
        }

        /**
         *
         */
        // Numerically evaluate a base-value string that may contain sqrtN
        // variables.  Substitutes each sqrtN with std::sqrt(N) so that the
        // resulting string is purely numeric and can be parsed by
        // expr_to_double.
        double evaluateBaseString(const std::string &baseStr)
        {
            std::string s = baseStr;
            // Find all occurrences of "sqrtDDD..." and replace with numeric value
            std::string::size_type pos = 0;
            while ((pos = s.find("sqrt", pos)) != std::string::npos)
            {
                auto numStart = pos + 4; // position right after "sqrt"
                auto numEnd = numStart;
                while (numEnd < s.size() && std::isdigit(s[numEnd]))
                    ++numEnd;
                if (numEnd > numStart)
                {
                    std::string digits = s.substr(numStart, numEnd - numStart);
                    double sqrtVal = std::sqrt(std::stod(digits));
                    // Use enough precision so the approximation is accurate
                    std::ostringstream oss;
                    oss << std::setprecision(15) << sqrtVal;
                    s.replace(pos, numEnd - pos, oss.str());
                    pos += oss.str().size();
                }
                else
                {
                    pos += 4; // skip "sqrt" without digits
                }
            }
            // Now s is purely numeric — parse and evaluate
            return expr_to_double(s, m_z3);
        }

        std::optional<Expr> generateRootBounds(int i)
        {
            assert(i < invNumber);
            if (!rootMaps.count(i))
            {
                return {};
            }
            ExprSet bounds;
            for (auto &[numeric, symbolic] : rootMaps[i])
            {
                double temp = evaluateBaseString(numeric);
                if (temp < 0)
                {
                    if (printLog >= 3)
                    {
                        outs() << "negative roots are not supported\n";
                        outs() << "root: " << numeric << "\n";
                    }
                    outs() << "unknown\n";
                    exit(EXIT_FAILURE);
                }
                double absTemp = temp;

                if (printLog >= 3)
                {
                    outs() << "generateRootBounds: base=\"" << numeric
                           << "\" value=" << temp
                           << " |value|=" << absTemp << "\n";
                }

                if (absTemp > 0.0 && absTemp < 1.0)
                {
                    // |eigenvalue| in (0,1): root variable decays to 0
                    bounds.insert(mk<LEQ>(symbolic, oneReal));
                    bounds.insert(mk<GEQ>(symbolic, zeroReal));
                }
                else if (absTemp == 1.0)
                {
                    // Eigenvalue is exactly 1 (e.g., _r_0 * 1): root stays constant
                    bounds.insert(mk<EQ>(symbolic, oneReal));
                }
                else if (absTemp == 0.0)
                {
                    // Could not evaluate — skip rather than assert =1
                    if (printLog >= 2)
                    {
                        outs() << "Warning: could not evaluate base \""
                               << numeric << "\" for " << symbolic
                               << " — skipping bounds\n";
                    }
                }
                else
                {
                    // |eigenvalue| > 1: root grows — still valid but unbounded
                    // For now just skip; no useful bound to add
                    if (printLog >= 3)
                    {
                        outs() << "generateRootBounds: |eigenvalue| > 1 for "
                               << symbolic << ", no bound added\n";
                    }
                }
            }

            // Add sqrt variable defining constraints as top-level invariant
            // conjuncts.  These must NOT be guarded by any index condition
            // because the coefficients in the closed forms reference sqrtN
            // at every step, not just the initial one.
            if (squareRootExists.count(i))
            {
                for (const auto &sqrtSuffix : squareRootExists[i])
                {
                    std::string fullName = "sqrt" + sqrtSuffix;
                    Expr sqrtVar = bind::realConst(mkTerm<std::string>(fullName, m_efac));
                    Expr constraint = createRootConstraint(sqrtVar, sqrtSuffix);
                    bounds.insert(constraint);
                    if (printLog >= 3)
                        outs() << "generateRootBounds: added sqrt constraint for "
                               << fullName << ": " << constraint << "\n";
                }
            }

            if (bounds.empty())
                return mk<TRUE>(m_efac);
            return conjoin(bounds, m_efac);
        }

        Expr generateSymbolicClosedForms(int i, nlohmann::json closedformJson)
        {
            indices[i] = addIndex(i);
            Expr index = indices[i];
            std::map<std::string, Expr> rootMap = insertRoots(i, closedformJson, m_z3);
            ExprSet initialClauses;
            initialClauses.insert(mk<GEQ>(index, zeroReal));

            // each variable that has a closed form — use only the final
            // (general) piece, guarded by i >= 0 for the entire domain.
            for (auto &[name, v] : closedformJson.items())
            {
                //  get variable using the name of the variable stored in v
                auto is_equal = [&](Expr var)
                {
                    return boost::algorithm::to_lower_copy(getVarName(var)) == name;
                };
                auto itr = std::find_if(
                    invarVarsShort[i].begin(),
                    invarVarsShort[i].end(),
                    is_equal);
                if (itr == invarVarsShort[i].end())
                    continue; // Skip to the next variable if not found
                Expr var = *itr;

                // Use only the last (general) closed form piece
                size_t lastIdx = v.size() - 1;
                auto &lastPiece = v[lastIdx];
                Expr cond = mk<GEQ>(index, zeroReal);

                // Build the closed-form sum: sum_j ( coeff_j * base_j )
                size_t jdx = 0;
                Expr sum;
                for (auto base_itr = lastPiece["bases"].begin(), coeff_itr = lastPiece["coeffs"].begin();
                     base_itr != lastPiece["bases"].end() && coeff_itr != lastPiece["coeffs"].end();
                     ++base_itr, ++coeff_itr)
                {
                    std::string c_str = coeff_itr->is_number() ? std::to_string(coeff_itr->get<int>()) : coeff_itr->get<std::string>();
                    std::string b_str = base_itr->is_number() ? std::to_string(base_itr->get<int>()) : base_itr->get<std::string>();
                    if (printLog >= 5)
                    {
                        outs() << "c_str: " << c_str << "\n";
                        outs() << "b_str: " << b_str << "\n";
                    }
                    if ((c_str.find("n") != std::string::npos && b_str != "1.0") || c_str.find("sqrt") != std::string::npos || b_str.find("sqrt") != std::string::npos)
                    {
                        hasNonlinearity = true;
                    }

                    Expr t = str_to_expr(c_str);
                    if (printLog >= 5)
                        outs() << "new expression: " << t << "\n";
                    Expr c = replaceCoeffVariables(t, index, i);
                    Expr b = rootMap[b_str];
                    if (jdx == 0)
                        sum = mk<MULT>(c, b);
                    else
                        sum = mk<PLUS>(sum, mk<MULT>(c, b));
                    jdx++;
                }
                initialClauses.insert(mk<IMPL>(cond, mk<EQ>(var, sum)));
            }

            rootMaps[i] = rootMap;
            return conjoin(initialClauses, m_efac);
        }

        void resolveDependencies(
            std::map<expr::Expr, expr::Expr> &definitions,
            const expr::ExprVector &dstVars,
            const expr::ExprVector &srcVars)
        {
            // Iterate over the definitions and replace variables in the RHS with their definitions
            bool changedInPass = true;
            if (printLog > 3)
            {
                outs() << "Resolving dependencies for definitions:\n";
                for (const auto &def : definitions)
                {
                    outs() << *def.first << " = " << *def.second << "\n";
                }
            }
            while (changedInPass)
            {
                changedInPass = false;
                for (auto &def : definitions)
                {
                    expr::Expr currentRHS = def.second;
                    expr::ExprMap substitutions;

                    // Find all variables in the current RHS
                    expr::ExprSet varsInRHS;
                    filter(currentRHS, expr::op::bind::IsConst(), inserter(varsInRHS, varsInRHS.begin()));

                    for (const auto &var : varsInRHS)
                    {
                        // If a variable in the RHS is one of the destination variables...
                        auto it = definitions.find(var);
                        if (it != definitions.end())
                        {
                            if (printLog > 3)
                            {
                                outs() << "Substituting " << *var << " with " << *it->second << "\n";
                            }
                            // ...add its own definition to the substitution map for the current expression.
                            substitutions[it->first] = it->second;
                        }
                    }

                    if (!substitutions.empty())
                    {
                        expr::Expr newRHS = replaceAll(currentRHS, substitutions);
                        if (newRHS != currentRHS)
                        {
                            def.second = newRHS;
                            changedInPass = true;
                        }
                        if (printLog > 3)
                        {
                            outs() << "Updated definition: " << *def.first << " = " << *def.second << "\n";
                        }
                    }
                }
                // If a full pass makes no changes, we are done.
                if (!changedInPass)
                {
                    break;
                }
            }
            if (printLog > 3)
            {
                outs() << "Final dependencies for definitions:\n";
                for (const auto &def : definitions)
                {
                    outs() << *def.first << " = " << *def.second << "\n";
                }
            }
        }

        std::string getVarName(const expr::Expr &varExpr)
        {
            if (expr::op::bind::isFapp(varExpr) && expr::op::bind::isFdecl(varExpr->left()))
            {
                expr::Expr nameExpr = varExpr->left()->left(); // FDECL's name
                if (expr::isOpX<expr::op::STRING>(nameExpr))
                {
                    return expr::getTerm<std::string>(nameExpr);
                }
            }
            // Fallback or error
            return "unknown_var_" + std::to_string(varExpr->getId());
        }

        // Helper function to convert an Expr to its POLAR string representation
        std::string exprToPolarString(const Expr &e, const std::map<std::string, std::string> &varRenames = {})
        {
            if (printLog >= 3)
            {
                std::cout << "Converting expresion to POLAR string: " << *e << std::endl;
            }
            if (!e)
                return "null_expr";

            if (expr::isOpX<expr::op::MPZ>(e) || expr::isOpX<expr::op::MPQ>(e))
            {
                return boost::lexical_cast<std::string>(e);
            }
            if (expr::op::bind::isRealConst(e))
            { // Checks for FAPP(FDECL(...))
                std::string baseName = getVarName(e);
                auto it = varRenames.find(baseName);
                if (it != varRenames.end())
                {
                    return it->second;
                }
                return baseName;
            }
            if (expr::isOpX<expr::op::PLUS>(e))
            {
                if (e->arity() == 0)
                    return "0";
                std::string out = exprToPolarString(e->arg(0), varRenames);
                for (unsigned i = 1; i < e->arity(); ++i)
                {
                    out = "(" + out + " + " + exprToPolarString(e->arg(i), varRenames) + ")";
                }
                return out;
            }
            if (expr::isOpX<expr::op::MINUS>(e) && e->arity() == 2)
            {
                return "(" + exprToPolarString(e->left(), varRenames) + " - " + exprToPolarString(e->right(), varRenames) + ")";
            }
            if (expr::isOpX<expr::op::NEG>(e) && e->arity() == 1)
            {
                return "(-" + exprToPolarString(e->left(), varRenames) + ")";
            }
            if (expr::isOpX<expr::op::UN_MINUS>(e) && e->arity() == 1)
            {
                return "(-" + exprToPolarString(e->left(), varRenames) + ")";
            }
            if (expr::isOpX<expr::op::MULT>(e))
            {
                if (e->arity() == 0)
                    return "1";
                std::string out = exprToPolarString(e->arg(0), varRenames);
                for (unsigned i = 1; i < e->arity(); ++i)
                {
                    out = "(" + out + " * " + exprToPolarString(e->arg(i), varRenames) + ")";
                }
                return out;
            }
            if ((expr::isOpX<expr::op::DIV>(e) || expr::isOpX<expr::op::IDIV>(e)) && e->arity() == 2)
            {
                return "(" + exprToPolarString(e->left(), varRenames) + " / " + exprToPolarString(e->right(), varRenames) + ")";
            }
            // Add more operators as needed (e.g., MOD)
            std::cout << "Unsupported expression type: " << *e << std::endl;
            return "unsupported_expr(" + boost::lexical_cast<std::string>(e->op()) + ")";
        }

        void generatePolarFile(ufo::CHCs &ruleManager, const std::string &outputFilename)
        {
            ufo::HornRuleExt *factRule = nullptr;
            ufo::HornRuleExt *inductiveRule = nullptr;

            for (auto &rule : ruleManager.chcs)
            {
                if (rule.isFact)
                {
                    factRule = &rule;
                }
                if (rule.isInductive)
                {
                    inductiveRule = &rule;
                }
            }

            if (!factRule)
            {
                std::cerr << "Error: Fact CHC not found." << std::endl;
                return;
            }
            if (!inductiveRule)
            {
                std::cerr << "Error: Inductive CHC not found." << std::endl;
                return;
            }

            std::ostringstream polarProgram;
            std::vector<std::string> initLhsVars, initRhsVals;
            std::map<std::string, std::string> initialValueMap; // var_name -> value_string

            // 1. Process Fact CHC for initial values
            // Use canonical variable names from invVars for the relation
            expr::Expr factRelation = factRule->dstRelation; // This is the relation name (e.g., "inv")
            const expr::ExprVector &canonicalFactVars = ruleManager.invVars[factRelation];

            // Create a map from the Expr in dstVars of the fact to its canonical name string
            std::map<expr::Expr, std::string> factDstVarToName;
            for (size_t i = 0; i < factRule->dstVars.size() && i < canonicalFactVars.size(); ++i)
            {
                // It's safer to use the names from invVars[factRelation] if dstVars are just placeholders
                // or if their names in the rule aren't the canonical ones.
                // For simplicity, we'll assume dstVars in the rule match the canonical order/names
                // or that invVars gives the true names for the positions.
                factDstVarToName[factRule->dstVars[i]] = getVarName(canonicalFactVars[i]);
            }

            expr::ExprSet factConjuncts;
            ufo::getConj(factRule->body, factConjuncts);

            for (const auto &varExpr : canonicalFactVars)
            {
                std::string varName = getVarName(varExpr);
                initLhsVars.push_back(varName);
                bool foundAssignment = false;
                for (const auto &conj : factConjuncts)
                {
                    if (expr::isOpX<expr::op::EQ>(conj) && conj->arity() == 2)
                    {
                        // Check if conj->right() corresponds to varExpr
                        // This direct comparison might fail if they are different Expr objects
                        // even if they represent the "same" variable in different contexts.
                        // A more robust way is to compare names if dstVars in rule are named.
                        std::string conjVarName;
                        if (printLog > 3)
                        {
                            std::cout << "Processing EQ: " << *conj << " for variable: " << varName << std::endl;
                            std::cout << "Left side of EQ: " << *conj->left() << std::endl;
                            std::cout << "Right side of EQ: " << *conj->right() << std::endl;
                        }

                        if (factDstVarToName.count(conj->left()))
                        {
                            conjVarName = factDstVarToName[conj->left()];
                        }
                        else
                        {
                            // Fallback if conj->right() is not directly in dstVars (e.g. it's already a canonical var Expr)
                            conjVarName = getVarName(conj->left());
                        }

                        if (conjVarName == varName)
                        {
                            if (expr::isOpX<expr::op::MPZ>(conj->left()) || expr::isOpX<expr::op::MPQ>(conj->left()))
                            {
                                initialValueMap[varName] = exprToPolarString(conj->left());
                                foundAssignment = true;
                                break;
                            }
                        }
                    }
                }
                if (!foundAssignment)
                {
                    initialValueMap[varName] = varName + "_INIT";
                }
            }

            // Ensure order for LHS and RHS
            for (const auto &varName : initLhsVars)
            {
                initRhsVals.push_back(initialValueMap[varName]);
            }

            /**
             * TODO:
             * Make sure that making all of the variables lower case doesn't lead to name clashes
             * for CHCs where the only distinguishing factor is case.
             */
            if (!initLhsVars.empty())
            {
                for (size_t i = 0; i < initLhsVars.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << boost::algorithm::to_lower_copy(initLhsVars[i]);
                }
                polarProgram << " = ";
                for (size_t i = 0; i < initRhsVals.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << boost::algorithm::to_lower_copy(initRhsVals[i]);
                }
                polarProgram << "\n";
            }

            // 2. Process Transition CHC for loop updates
            polarProgram << "while true:\n";
            std::vector<std::string> loopLhsVars, loopRhsExprs;
            std::map<std::string, std::string> updateValueMap;

            // Use canonical variable names for the inductive relation
            expr::Expr indRelation = inductiveRule->srcRelation; // src and dst relation are the same
            const expr::ExprVector &canonicalIndVarsSrc = ruleManager.invVars[indRelation];
            const expr::ExprVector &canonicalIndVarsDst = ruleManager.invVarsPrime[indRelation]; // Or invVars if primes are not distinct

            // Map for renaming srcVars in the body to their base names for exprToPolarString
            std::map<std::string, std::string> srcVarRenames;
            for (size_t i = 0; i < inductiveRule->srcVars.size() && i < canonicalIndVarsSrc.size(); ++i)
            {
                // Get the base name from canonicalFactVars (assuming order correspondence)
                srcVarRenames[getVarName(inductiveRule->srcVars[i])] = getVarName(canonicalIndVarsSrc[i]);
            }

            expr::ExprSet inductiveConjuncts;
            ufo::getConj(inductiveRule->body, inductiveConjuncts);

            for (const auto &dstVarExprCanonical : canonicalIndVarsDst)
            {                                                          // Iterate using canonical dst var order
                std::string varName = getVarName(dstVarExprCanonical); // This is the name for LHS of POLAR
                loopLhsVars.push_back(varName);
                bool foundUpdate = false;
                for (const auto &conj : inductiveConjuncts)
                {
                    if (expr::isOpX<expr::op::EQ>(conj) && conj->arity() == 2)
                    {
                        // We need to match conj->left() (a dstVar from the rule)
                        // with dstVarExprCanonical (a canonical dstVar Expr)
                        std::string conjDstVarName = getVarName(conj->left());
                        std::cout << "Checking EQ: " << *conj << " for variable: " << varName << std::endl;
                        std::cout << "Conj left: " << *conj->left() << ", Conj right: " << *conj->right() << std::endl;
                        // A more direct mapping if dstVars in rule are consistently named:
                        // if (getVarName(conj->left()) == varName) { ... }
                        // This assumes that inductiveRule->dstVars items correspond positionally
                        // to canonicalIndVarsDst, and we can map by comparing their names.
                        // A robust way: find which inductiveRule->dstVars[j] corresponds to dstVarExprCanonical,
                        // then check if conj->left() IS inductiveRule->dstVars[j].
                        bool match = false;
                        for (const auto &ruleDstVar : inductiveRule->dstVars)
                        {
                            if (getVarName(ruleDstVar) == varName && ruleDstVar == conj->left())
                            {
                                match = true;
                                break;
                            }
                        }

                        if (match)
                        {
                            updateValueMap[varName] = exprToPolarString(conj->right(), srcVarRenames);
                            foundUpdate = true;
                            break;
                        }
                    }
                }
                if (!foundUpdate)
                {
                    updateValueMap[varName] = varName; // Default to "var = var" if no update found
                }
            }

            // Ensure order for LHS and RHS
            for (const auto &varName : loopLhsVars)
            {
                loopRhsExprs.push_back(updateValueMap[varName]);
            }

            if (!loopLhsVars.empty())
            {
                polarProgram << "    ";
                for (size_t i = 0; i < loopLhsVars.size(); ++i)
                {
                    std::string x = boost::algorithm::to_lower_copy(loopLhsVars[i].substr(0, loopLhsVars[i].size() - 1));
                    polarProgram << (i == 0 ? "" : ", ") << x;
                }
                polarProgram << " = ";
                for (size_t i = 0; i < loopRhsExprs.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << boost::algorithm::to_lower_copy(loopRhsExprs[i]);
                }
                polarProgram << "\n";
            }

            polarProgram << "end\n";

            // 3. Write to file
            std::ofstream outFile(outputFilename);
            if (outFile.is_open())
            {
                outFile << polarProgram.str();
                outFile.close();
                std::cout << "Successfully wrote POLAR program to " << outputFilename << std::endl;
            }
            else
            {
                std::cerr << "Error: Unable to open file " << outputFilename << " for writing." << std::endl;
            }
        }

        void generatePolarFile2(ufo::CHCs &ruleManager, const std::string &outputFilename, int myinv = 0)
        {
            ufo::HornRuleExt *factRule = nullptr;
            ufo::HornRuleExt *inductiveRule = nullptr;

            for (auto &rule : ruleManager.chcs)
            {
                if (rule.isFact)
                {
                    factRule = &rule;
                }
                if (rule.isInductive)
                {
                    inductiveRule = &rule;
                }
            }

            if (!factRule)
            {
                std::cerr << "Error: Fact CHC not found." << std::endl;
                return;
            }
            if (!inductiveRule)
            {
                std::cerr << "Error: Inductive CHC not found." << std::endl;
                return;
            }

            std::ostringstream polarProgram;
            std::vector<std::string> initLhsVars, initRhsVals;
            std::map<std::string, std::string> initialValueMap; // var_name -> value_string

            // 1. Process Fact CHC for initial values
            // Use canonical variable names from invVars for the relation
            expr::Expr factRelation = factRule->dstRelation; // This is the relation name (e.g., "inv")
            const expr::ExprVector &canonicalFactVars = ruleManager.invVars[factRelation];

            // Create a map from the Expr in dstVars of the fact to its canonical name string
            std::map<expr::Expr, std::string> factDstVarToName;
            for (size_t i = 0; i < factRule->dstVars.size() && i < canonicalFactVars.size(); ++i)
            {
                // It's safer to use the names from invVars[factRelation] if dstVars are just placeholders
                // or if their names in the rule aren't the canonical ones.
                // For simplicity, we'll assume dstVars in the rule match the canonical order/names
                // or that invVars gives the true names for the positions.
                factDstVarToName[factRule->dstVars[i]] = getVarName(canonicalFactVars[i]);
            }

            expr::ExprSet factConjuncts;
            ufo::getConj(factRule->body, factConjuncts);

            for (const auto &varExpr : canonicalFactVars)
            {
                std::string varName = getVarName(varExpr);
                initLhsVars.push_back(varName);
                bool foundAssignment = false;
                for (const auto &conj : factConjuncts)
                {
                    if (expr::isOpX<expr::op::EQ>(conj) && conj->arity() == 2)
                    {
                        // Check if conj->right() corresponds to varExpr
                        // This direct comparison might fail if they are different Expr objects
                        // even if they represent the "same" variable in different contexts.
                        // A more robust way is to compare names if dstVars in rule are named.
                        std::string conjVarName;
                        if (printLog > 3)
                        {
                            std::cout << "Processing EQ: " << *conj << " for variable: " << varName << std::endl;
                            std::cout << "Left side of EQ: " << *conj->left() << std::endl;
                            std::cout << "Right side of EQ: " << *conj->right() << std::endl;
                        }

                        if (factDstVarToName.count(conj->left()))
                        {
                            conjVarName = factDstVarToName[conj->left()];
                        }
                        else
                        {
                            // Fallback if conj->right() is not directly in dstVars (e.g. it's already a canonical var Expr)
                            conjVarName = getVarName(conj->left());
                        }

                        if (conjVarName == varName)
                        {
                            if (expr::isOpX<expr::op::MPZ>(conj->right()) || expr::isOpX<expr::op::MPQ>(conj->right()))
                            {
                                initialValueMap[varName] = exprToPolarString(conj->right());
                                foundAssignment = true;
                                break;
                            }
                        }
                    }
                }
                // If there isn't a default assignment for the variable,
                // we can assign a default value like "varName_INIT" to indicate initialization.

                // For what we are doing, if there isn't any "equality" found,
                // we'll use this default assignment, and then will give this varName_INIT
                // value a bounds inside of the invariant we create.
                if (!foundAssignment)
                {
                    initialValueMap[varName] = varName + "_INIT";
                }
            }

            // Ensure order for LHS and RHS
            for (const auto &varName : initLhsVars)
            {
                initRhsVals.push_back(initialValueMap[varName]);
            }

            /**
             * TODO:
             * Make sure that making all of the variables lower case doesn't lead to name clashes
             * for CHCs where the only distinguishing factor is case.
             */
            if (!initLhsVars.empty())
            {
                for (size_t i = 0; i < initLhsVars.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << boost::algorithm::to_lower_copy(initLhsVars[i]);
                }
                polarProgram << " = ";
                for (size_t i = 0; i < initRhsVals.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << boost::algorithm::to_lower_copy(initRhsVals[i]);
                }
                polarProgram << "\n";
            }
            polarProgram << "while true:\n";
            std::vector<std::string> loopLhsVars;
            std::vector<expr::Expr> loopFinalRhsExprs;

            expr::Expr indRelation = inductiveRule->srcRelation;
            const expr::ExprVector &canonicalLoopVars = ruleManager.invVars[indRelation];

            // Build the initial map of definitions from the CHC body
            std::map<expr::Expr, expr::Expr> dstVarDefinitions;
            expr::ExprSet inductiveConjuncts;
            ufo::getConj(inductiveRule->body, inductiveConjuncts);
            for (const auto &conj : inductiveConjuncts)
            {
                if (expr::isOpX<expr::op::EQ>(conj) && conj->arity() == 2)
                {
                    // Assuming conj->left() is a dstVar and conj->right() is its definition
                    if (printLog > 3)
                    {
                        std::cout << "Assuming conj->left() is a dstVar and conj->right() is its definition." << std::endl;
                        std::cout << "Processing EQ: " << *conj << std::endl;
                        std::cout << "Left side of EQ: " << *conj->left() << std::endl;
                        std::cout << "Right side of EQ: " << *conj->right() << std::endl;
                    }
                    dstVarDefinitions[conj->left()] = conj->right();
                }
            }

            // *** Inlining Step ***
            // This resolves dependencies like the following
            // x' = x + 1 /\ y' = x' + 1 into x' = x + 1 /\ y' = (x + 1) + 1
            resolveDependencies(dstVarDefinitions, inductiveRule->dstVars, inductiveRule->srcVars);

            if (printLog > 3)
            {
                std::cout << "Resolved definitions after inlining:" << std::endl;
                for (const auto &def : dstVarDefinitions)
                {
                    std::cout << getVarName(def.first) << " = " << exprToPolarString(def.second) << std::endl;
                }
            }
            // Prepare for final string conversion
            std::map<std::string, std::string> srcVarRenames;
            for (size_t i = 0; i < inductiveRule->srcVars.size() && i < canonicalLoopVars.size(); ++i)
            {
                srcVarRenames[getVarName(inductiveRule->srcVars[i])] = getVarName(canonicalLoopVars[i]);
            }

            // Generate the final LHS and RHS lists in a canonical order
            for (const auto &canonicalVar : canonicalLoopVars)
            {
                std::string varName = getVarName(canonicalVar);
                loopLhsVars.push_back(varName);
                if (printLog > 5)
                {
                    std::cout << "Canonical variable: " << varName << std::endl;
                }
                // Find the corresponding dstVar from the rule to look up its resolved definition
                expr::Expr correspondingDstVar;
                for (const auto &ruleDstVar : inductiveRule->dstVars)
                {
                    if (printLog > 5)
                    {
                        std::cout << "Checking ruleDstVar: " << getVarName(ruleDstVar) << std::endl;
                        std::cout << "Comparing with varName: " << (varName + "'") << std::endl;
                    }
                    if (getVarName(ruleDstVar) == (varName + "'"))
                    { // A simplified matching by name
                        correspondingDstVar = ruleDstVar;
                        break;
                    }
                }
                if (printLog >= 5)
                {
                    std::cout << "Corresponding dstVar: " << (correspondingDstVar ? getVarName(correspondingDstVar) : "not found") << std::endl;
                }

                if (dstVarDefinitions.count(correspondingDstVar))
                {
                    loopFinalRhsExprs.push_back(dstVarDefinitions.at(correspondingDstVar));
                }
                else
                {
                    // If no update rule is found, assume the variable remains unchanged
                    // Find the corresponding srcVar to represent the "old" value
                    if (printLog > 5)
                    {
                        std::cout << "No update rule found for " << varName << ", looking for srcVars." << std::endl;
                    }
                    for (const auto &ruleSrcVar : inductiveRule->srcVars)
                    {
                        if (getVarName(ruleSrcVar) == varName)
                        {
                            loopFinalRhsExprs.push_back(ruleSrcVar);
                            break;
                        }
                    }
                }
            }
            if (printLog > 3)
            {
                std::cout << "Final LHS variables: ";
                for (const auto &var : loopLhsVars)
                {
                    std::cout << var << " ";
                }
                std::cout << "\nFinal RHS expressions: ";
                for (const auto &expr : loopFinalRhsExprs)
                {
                    std::cout << *expr << " ";
                }
                std::cout << std::endl;
            }

            // Convert the final RHS expressions to strings
            std::vector<std::string> loopRhsStrings;
            for (const auto &rhsExpr : loopFinalRhsExprs)
            {
                loopRhsStrings.push_back(exprToPolarString(rhsExpr, srcVarRenames));
            }

            if (!loopLhsVars.empty())
            {
                polarProgram << "    ";
                // This program assumes that the polar variables for each invariant are generated in order
                assert(polarVarNames.size() < invNumber);
                assert(polarVarNames.size() == myinv);
                polarVarNames.push_back(std::vector<std::string>());
                for (size_t i = 0; i < loopLhsVars.size(); ++i)
                {
                    std::string s = boost::algorithm::to_lower_copy(loopLhsVars[i]);
                    polarProgram << (i == 0 ? "" : ", ") << s;
                    polarVarNames.back().push_back(s);
                }
                polarProgram << " = ";
                for (size_t i = 0; i < loopRhsStrings.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << boost::algorithm::to_lower_copy(loopRhsStrings[i]);
                }
                polarProgram << "\n";
            }

            polarProgram << "end\n";

            // 3. Write to file
            std::ofstream outFile(outputFilename);
            if (outFile.is_open())
            {
                outFile << polarProgram.str();
                outFile.close();
                if (printLog >= 5)
                {
                    std::cout << "Successfully wrote POLAR program to " << outputFilename << std::endl;
                }
            }
            else
            {
                std::cerr << "Error: Unable to open file " << outputFilename << " for writing." << std::endl;
                exit(EXIT_FAILURE);
            }
        }

        void reflipSimpleEqualities(void)
        {
            /**
             * Currently, when CHCs are taken in from the SMTLIB2 file, they will flip
             * simple equalities like x = y into y = x.
             * In order to help with translating CHCs into POLAR, we need to
             * reflip these equalities back to their original form.
             *
             * There are two ways to determine if this flip occured:
             * 1. If the right hand side is a variable and the left hand side is a constant,
             *   then the equality was flipped.
             * 2. If the both the left and right hand sides are a variable by themselves,
             *   then the equality was flipped.
             */

            for (auto &rule : ruleManager.chcs)
            {
                ExprSet newBody, oldBody;
                ufo::getConj(rule.body, oldBody);
                for (auto &conj : oldBody)
                {
                    if (expr::isOpX<expr::op::EQ>(conj) && conj->arity() == 2)
                    {
                        Expr left = conj->left();
                        Expr right = conj->right();
                        IsVar isVarCheck;
                        IsHardIntConst isHardIntConstCheck;
                        IsConst isConstCheck;
                        if (printLog >= 3)
                        {
                            outs() << "Reflipping equality: " << *conj << "\n";
                            outs() << "Left: " << *left << ", Right: " << *right << "\n";
                            if (isConstCheck(left) && isConstCheck(right))
                            {
                                outs() << "Both sides are variables, flipping back.\n";
                            }
                            else if (isOpX<MPQ>(left) || isIntConst(left) || isHardIntConstCheck(left))
                            {
                                outs() << "Left side is constant, flipping back.\n";
                            }
                            else
                            {
                                outs() << "Equality does not need flipping.\n";
                            }
                        }

                        // Check if the equality was flipped
                        if (isConstCheck(right) && isConstCheck(left) || isOpX<MPQ>(left) || isIntConst(left) || isHardIntConstCheck(left))
                        {
                            // Flip the equality back
                            newBody.insert(mk<EQ>(right, left));
                        }
                        else
                        {
                            newBody.insert(conj); // Keep the original equality
                        }
                    }
                    else
                    {
                        newBody.insert(conj); // Keep non-equality expressions as is
                    }
                }
                rule.body = conjoin(newBody, m_efac); // Update the body with flipped equalities
            }

            for (auto i = 0; i < invNumber; i++)
                updateCategorizationOfCHCs(i);
        }
        void replaceRule(HornRuleExt *hr, HornRuleExt *rule)
        {
            rule->srcRelation = hr->srcRelation;
            rule->srcVars = hr->srcVars;
            rule->dstRelation = hr->dstRelation;
            rule->dstVars = hr->dstVars;
            rule->isFact = hr->isFact;
            rule->isInductive = hr->isInductive;
            rule->isQuery = hr->isQuery;
            rule->body = hr->body;
        }

        void replaceRule(HornRuleExt *hr)
        {
            for (auto &rule : ruleManager.chcs)
            {
                if (!hr->isInductive && !hr->isQuery && !rule.isInductive && !rule.isQuery)
                {
                    replaceRule(hr, &rule);
                }
                else if (hr->isInductive && rule.isInductive)
                {
                    replaceRule(hr, &rule);
                }
                else if (hr->isQuery && rule.isQuery)
                {
                    replaceRule(hr, &rule);
                }
            }
        }
        Expr gatherLemmas(int invNum)
        {
            assert(invNum < learnedExprs.size());
            if (learnedExprs[invNum].empty())
                return mk<TRUE>(m_efac);
            if (printLog >= 3)
                outs() << "Gathering lemmas for invariant #" << invNum << ": " << decls[invNum] << "\n";
            return conjoin(learnedExprs[invNum], m_efac);
        }
        void initializeDecl2(Expr invDecl)
        {
            if (printLog)
                outs() << "\nINITIALIZE PREDICATE " << invDecl << "\n====================\n";
            //      assert (invDecl->arity() > 2);
            assert(decls.size() == invNumber);
            assert(curCandidates.size() == invNumber);

            decls.push_back(invDecl);
            invarVars.push_back(map<int, Expr>());
            invarVarsShort.push_back(ExprVector());

            curCandidates.push_back(NULL);

            sfs.push_back(vector<SamplFactory>());
            sfs.back().push_back(SamplFactory(m_efac, aggressivepruning));
            SamplFactory &sf = sfs.back().back(); // may be needless now?

            learnedExprs.push_back(ExprSet());

            for (int i = 0; i < ruleManager.invVars[invDecl].size(); i++)
            {
                Expr var = ruleManager.invVars[invDecl][i];
                invarVars[invNumber][i] = var;
                invarVarsShort[invNumber].push_back(var);
            }

            arrCands.push_back(ExprSet());
            arrAccessVars.push_back(ExprVector());
            arrIterRanges.push_back(ExprSet());

            invNumber++;
        }
        // filepath: [RndLearnerV5.hpp](http://_vscodecontentref_/50)
        // Add this helper inside RndLearnerV5, before checkCHC2

        // Returns the primed version of invarVarsShort[i] by looking up
        // ruleManager.invVarsPrime, in the same order as invarVarsShort[i].
        ExprVector getPrimedVars(int invIdx)
        {
            Expr rel = decls[invIdx];
            const ExprVector &unprimed = ruleManager.invVars[rel];
            const ExprVector &primed = ruleManager.invVarsPrime[rel];
            // Build a map: unprimed[j] -> primed[j]
            ExprMap up;
            for (size_t j = 0; j < std::min(unprimed.size(), primed.size()); ++j)
                up[unprimed[j]] = primed[j];

            ExprVector result;
            for (auto &v : invarVarsShort[invIdx])
            {
                auto it = up.find(v);
                result.push_back(it != up.end() ? it->second : v);
            }
            return result;
        }

        tribool checkCHC2(HornRuleExt &hr, map<int, ExprVector> &annotations,
                          bool checkAll = false)
        {
            int srcNum = getVarIndex(hr.srcRelation, decls);
            int dstNum = getVarIndex(hr.dstRelation, decls);
            if (!hr.isQuery) // shortcuts
            {
                if (dstNum < 0)
                {
                    if (printLog >= 3)
                        outs() << "      Trivially true since " << hr.dstRelation << " is not initialized\n";
                    return false;
                }
                if (checkAll && annotations[dstNum].empty())
                    return false;
            }
            ExprSet exprs = {hr.body};

            if (!hr.isFact)
            {
                const ExprVector &canonicalSrc = ruleManager.invVars[hr.srcRelation];
                if (printLog >= 5)
                {
                    outs() << "checkCHC2: srcVars size=" << hr.srcVars.size()
                           << " canonicalSrc size=" << canonicalSrc.size() << "\n";
                }
                // Only substitute if sizes agree
                if (canonicalSrc.size() == hr.srcVars.size())
                {
                    ExprSet lms = learnedExprs[srcNum];
                    for (auto &a : annotations[srcNum])
                        lms.insert(a);
                    for (auto a : lms)
                    {
                        a = replaceAll(a, invarVarsShort[srcNum], hr.srcVars);
                        exprs.insert(a);
                    }
                }
                else
                {
                    if (printLog >= 2)
                        outs() << "Warning: skipping src substitution due to size mismatch ("
                               << invarVarsShort[srcNum].size() << " vs " << hr.srcVars.size() << ")\n";
                }
            }
            if (!hr.isQuery)
            {
                const ExprVector &canonicalDst = ruleManager.invVars[hr.dstRelation];
                if (printLog >= 5)
                {
                    outs() << "checkCHC2: dstVars size=" << hr.dstVars.size()
                           << " canonicalDst size=" << canonicalDst.size() << "\n";
                }
                if (invarVarsShort[dstNum].size() == hr.dstVars.size())
                {
                    ExprSet lms = learnedExprs[dstNum];
                    ExprSet negged;
                    for (auto &a : annotations[dstNum])
                        lms.insert(a);
                    for (auto a : lms)
                    {
                        a = replaceAll(a, invarVarsShort[dstNum], hr.dstVars);
                        negged.insert(mkNeg(a));
                    }
                    exprs.insert(disjoin(negged, m_efac));
                }
            }

            // Dump the formula to a compliant SMT-LIB2 (v2.6) file for debugging.
            // Uses EZ3's built-in serializer (Z3_PRINT_SMTLIB2_COMPLIANT mode)
            // so that variable declarations carry their actual sorts and
            // all expressions are printed in proper S-expression form.
            if (printLog >= 5)
            {
                static int queryCount = 0;
                std::string filename = std::string(FREQHORN_SOURCE_DIR) + "/debug_queries/freqhorn_query_" + std::to_string(queryCount++) + ".smt2";
                std::ofstream smtFile(filename);
                if (smtFile.is_open())
                {
                    // Temporarily disable decimal printing so rationals
                    // appear as (/ p q) instead of truncated decimals.
                    Z3_global_param_set("pp.decimal", "false");

                    // smtFile << "(set-info :smt-lib-version 2.6)\n";
                    smtFile << "(set-logic QF_NRA)\n";

                    // Convert all MPZ (integer) leaves to MPQ (rational)
                    // so that Z3 marshals them with Real sort, avoiding
                    // (to_real N) coercions in the output.
                    ExprVector assertVec;
                    assertVec.reserve(exprs.size());
                    for (auto &e : exprs)
                        assertVec.push_back(mpzToMpq(e));

                    // Emit (declare-fun ...) for every uninterpreted constant
                    // appearing in the assertions, with correct sorts.
                    smtFile << m_z3.toSmtLibDecls(assertVec);

                    for (auto &e : assertVec)
                        smtFile << "(assert " << m_z3.toSmtLib(e) << ")\n";

                    smtFile << "(check-sat)\n";
                    smtFile << "(exit)\n";
                    smtFile.close();

                    // Restore decimal printing
                    Z3_global_param_set("pp.decimal", "true");

                    if (printLog >= 5)
                    {
                        outs() << "Dumped SMT-LIB2 query to " << filename << "\n";
                    }
                }
            }

            // Use QF_NRA (nlsat) solver directly for nonlinear real
            // arithmetic.  The default combined solver often returns UNKNOWN
            // on formulas involving products of variables (e.g. _r_N * sqrt).
            //
            // IMPORTANT: We use ZSolver's NoPush constructor so that Z3's
            // combined_solver stays in non-incremental (tactic) mode.
            // ZSolver's normal constructors call solver.push(), which
            // permanently switches combined_solver into incremental mode
            // (dispatching to the plain SMT kernel instead of the QF_NRA
            // tactic pipeline: simplify → propagate_values → qe_lite →
            // nlsat).  Even pop() cannot undo this — it also calls
            // switch_inc_mode().  With NoPush, the solver matches
            // standalone z3 behavior.
            boost::tribool sat;
            try
            {
                auto startTime = std::chrono::steady_clock::now();
                // Lazily construct the solver once; reset between calls
                // to clear assertions while staying in non-incremental
                // (tactic/nlsat) mode.
                if (!nlsolver.has_value())
                {
                    nlsolver.emplace(m_z3, "QF_NRA", 30000,
                                     ZSolver<EZ3>::NoPush{});
                }
                else
                {
                    nlsolver->resetNoPush();
                    ZParams<EZ3> p(m_z3);
                    p.set("timeout", 30000u);
                    nlsolver->set(p);
                }
                for (auto &e : exprs)
                    nlsolver->assertExpr(e);
                sat = nlsolver->solve();
                auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
                                   std::chrono::steady_clock::now() - startTime)
                                   .count();

                if (printLog >= 3)
                {
                    std::cout << "checkCHC2: QF_NRA solved in " << elapsed << "ms\n";
                }
                if (sat)
                {
                    auto model = nlsolver->getModel();
                    ExprVector eqs;
                    ExprSet allVars;
                    filter(conjoin(exprs, m_efac), bind::IsConst(), inserter(allVars, allVars.begin()));
                    for (auto &v : allVars)
                    {
                        Expr val = model.eval(v);
                        if (val != nullptr && val != v)
                            eqs.push_back(mk<EQ>(v, val));
                    }
                    Expr modelExpr = conjoin(eqs, m_efac);
                    if (printLog >= 5)
                    {
                        outs() << "Model: " << modelExpr << "\n";
                    }
                }
            }
            catch (const std::exception &e)
            {
                if (printLog >= 2)
                    std::cout << "checkCHC2: QF_NRA solver exception: " << e.what()
                              << ", falling back to default solver\n";
                sat = u.isSat(exprs);
                if (printLog >= 5)
                {
                    if (sat)
                        std::cout << "checkCHC2 result: SAT\n";
                    else if (!sat)
                        std::cout << "checkCHC2 result: UNSAT\n";
                    else
                        std::cout << "checkCHC2 result: UNKNOWN\n";
                }
                if (sat && printLog >= 5)
                {
                    outs() << "Expressions" << conjoin(exprs, m_efac) << "\n";
                    outs() << u.getModel() << "\n";
                }
            }
            return sat;
        }

        boost::tribool checkFact(int i, map<int, ExprVector> &annotations)
        {
            if (printLog >= 6)
            {
                outs() << "Checking fact...\n";
            }
            return !checkCHC2(*fc[i], annotations, true);
        }

        boost::tribool checkConsecution(int i, map<int, ExprVector> &annotations)
        {
            if (printLog >= 6)
            {
                outs() << "Checking consecution...\n";
            }
            return !checkCHC2(*tr[i], annotations, true);
        }

        boost::tribool checkQuery(int i, map<int, ExprVector> &annotations)
        {
            if (printLog >= 6)
            {
                outs() << "Checking query...\n";
            }
            return !checkCHC2(*qr[i], annotations, true);
        }

        bool checkAllCHCs(int i, Expr x)
        {
            assert(i < invNumber);
            map<int, ExprVector> annotations;
            annotations[i].push_back(x); // Initialize with the candidate invariant
            boost::tribool result = false;
            result = result || checkCHC2(*fc[i], annotations, true); // Check the fact rule
            if (result)
            {
                outs() << "Candidate invariant " << x << " failed to satisfy the fact rule for predicate " << decls[i] << "\n";
                return false; // If it fails the fact rule, we can stop here
            }
            result = result || checkCHC2(*tr[i], annotations, true); // Check the inductive rule
            if (result)
            {
                outs() << "Candidate invariant " << x << " failed to satisfy the inductive rule for predicate " << decls[i] << "\n";
                return false; // If it fails the inductive rule, we can stop here
            }
            result = result || checkCHC2(*qr[i], annotations, true); // Check the query rule
            if (result)
            {
                outs() << "Candidate invariant " << x << " failed to satisfy the query rule for predicate " << decls[i] << "\n";
                return false; // If it fails the query rule, we can stop here
            }
            return true;
        }

        void categorizeCHCs2()
        {
            for (HornRuleExt &hr : ruleManager.chcs)
            {
                if (hr.isFact)
                {
                    fc.push_back(&hr);
                }
                else if (hr.isQuery)
                {
                    qr.push_back(&hr);
                }
                else if (hr.isInductive)
                {
                    tr.push_back(&hr);
                }
            }
            // Ensure that the size of fc, tr, and qr matches invNumber
            assert(fc.size() == invNumber);
            assert(tr.size() == invNumber);
            assert(qr.size() == invNumber);
        }

        void updateCategorizationOfCHCs(int i)
        {
            assert(i < invNumber);
            // Update the categorization of CHCs for the i-th invariant
            for (auto &hr : ruleManager.chcs)
            {
                if (hr.isFact && hr.dstRelation == decls[i])
                {
                    fc[i] = &hr; // Update the fact rule for this invariant
                }
                else if (hr.isInductive && hr.srcRelation == decls[i])
                {
                    tr[i] = &hr; // Update the inductive rule for this invariant
                }
                else if (hr.isQuery && hr.srcRelation == decls[i])
                {
                    qr[i] = &hr; // Update the query rule for this invariant
                }
            }
        }

        void insertCounter(int inv)
        {
            if (printLog >= 3)
                outs() << "setUpCounters\n";
            assert(inv < invNumber);
            Expr new_name = mkTerm<string>("_i" + to_string(0), m_efac);
            Expr var = bind::realConst(new_name);
            auxVars[inv].push_back(var);
            new_name = mkTerm<string>("_i" + to_string(0) + "p", m_efac);
            var = bind::realConst(new_name);
            auxVarsPr[inv].push_back(var);
            Expr indexZero = mk<EQ>(auxVars[inv][0], mkTerm(mpq_class("0"), m_efac));
            Expr indexInc = mk<EQ>(auxVarsPr[inv][0], mk<PLUS>(auxVars[inv][0], mkTerm(mpq_class("1"), m_efac)));
        }

        Expr addRoot(int i, std::string rootVal, size_t rootCount, EZ3 &z3, std::vector<std::string> sqrts = std::vector<std::string>())
        {
            /* TODO:
                Support roots that are complex, this assumes all roots are real due
                to how it writes the update
            */
            // outs() << "Adding root " << rootVal << " to invariant #" << i << "\n";
            assert(i < invNumber);
            // --- Define the counter variable ---
            std::string rootBaseName = "_r_" + std::to_string(rootCount);
            Expr rootNameUnprimedExpr = mkTerm<string>(rootBaseName, m_efac);
            Expr rootNamePrimedExpr = mkTerm<string>(rootBaseName + "'", m_efac);
            Expr myRealRoot = bind::realConst(rootNameUnprimedExpr);
            Expr myRealRootPrime = bind::realConst(rootNamePrimedExpr);
            if (printLog >= 5)
            {
                outs() << "Created symbolic root variables: " << myRealRoot << ", " << myRealRootPrime << "\n";
            }

            Expr myRootUpdate = str_to_expr(rootVal, sqrts);

            if (isOpX<expr::op::DIV>(myRootUpdate))
            {
                Expr left = myRootUpdate->left();
                Expr right = myRootUpdate->right();
                if (printLog >= 5)
                {
                    outs() << "Root Type: " << typeid(myRootUpdate->op()).name() << "\n";
                    outs() << "Numerator Type: " << typeid(left->op()).name() << "\n";
                    outs() << "Denominator Type: " << typeid(right->op()).name() << "\n";
                }
            }
            if (printLog >= 3)
            {
                outs() << "Root update expression: " << myRootUpdate << "\n";
            }

            Expr updateConstraint = mk<EQ>(myRealRootPrime, mk<MULT>(myRealRoot, myRootUpdate));
            invarVarsShort[i].push_back(myRealRoot);
            symbolicRoots[i].push_back(myRealRoot);
            numericRoots[i].push_back(myRootUpdate);

            // outs() << "Added symbolic roots\n";
            // outs() << "Now adding to rules\n";
            for (auto &hr : ruleManager.chcs)
            {
                // --- Modify the Fact ---
                if (hr.isFact)
                { // Ensure it's actually a fact
                    // Add to destination variables
                    if (printLog >= 3)
                        outs() << "Adding " << myRealRoot << " to source variables of fact: " << hr.dstRelation << "\n";
                    hr.dstVars.push_back(myRealRootPrime);

                    if (printLog >= 3)
                        outs() << "Adding " << myRealRootPrime << " to destination variables of fact: " << hr.dstRelation << "\n";
                    // Add constraint to body: _my_real_counter_prime = 0.0
                    ExprSet bodyConjuncts;
                    getConj(hr.body, bodyConjuncts); // Get existing conjuncts

                    // Create 0 real literal
                    Expr oneReal = mkTerm(mpq_class("1"), m_efac);
                    Expr initConstraint = mk<EQ>(oneReal, myRealRootPrime);
                    bodyConjuncts.insert(initConstraint);

                    hr.body = conjoin(bodyConjuncts, m_efac); //

                    // Update ruleManager for the relation defined by this fact
                    Expr relationName = hr.dstRelation;
                    if (find(ruleManager.invVars[relationName].begin(),
                             ruleManager.invVars[relationName].end(),
                             myRealRoot) == ruleManager.invVars[relationName].end())
                    {
                        ExprVector updatedQueryDstUnprimedVars = ruleManager.invVars[relationName];
                        updatedQueryDstUnprimedVars.push_back(myRealRoot);
                        ruleManager.invVars[relationName].clear();
                        ruleManager.invVarsPrime[relationName].push_back(myRealRootPrime);
                        ruleManager.addDeclAndVars(relationName, updatedQueryDstUnprimedVars);
                    }
                    // outs() << "Updated ruleManager for relation: " << relationName << "\n";
                }

                // --- Modify the Transition Rule ---
                if (hr.isInductive || (!hr.isFact && !hr.isQuery))
                {
                    if (printLog >= 3)
                        outs() << "Adding " << myRealRoot << " to source variables of transition rule: " << hr.srcRelation << "\n";

                    hr.srcVars.push_back(myRealRoot);

                    if (printLog >= 3)
                        outs() << "Adding " << myRealRootPrime << " to destination variables of transition rule: " << hr.dstRelation << "\n";
                    hr.dstVars.push_back(myRealRootPrime);

                    // Add constraint to body: _my_real_root_prime = _my_real_root * rootUpdate
                    ExprSet bodyConjuncts;
                    getConj(hr.body, bodyConjuncts);
                    bodyConjuncts.insert(updateConstraint);
                    hr.body = conjoin(bodyConjuncts, m_efac);

                    // Update ruleManager for the source relation if it's not already updated
                    Expr srcRelationName = hr.srcRelation;
                    if (find(ruleManager.invVars[srcRelationName].begin(),
                             ruleManager.invVars[srcRelationName].end(),
                             myRealRoot) == ruleManager.invVars[srcRelationName].end())
                    {
                        ExprVector updatedQuerySrcUnprimedVars = ruleManager.invVars[srcRelationName];
                        updatedQuerySrcUnprimedVars.push_back(myRealRoot);
                        ruleManager.invVars[srcRelationName].clear();
                        ruleManager.invVarsPrime[srcRelationName].push_back(myRealRootPrime);
                        ruleManager.addDeclAndVars(srcRelationName, updatedQuerySrcUnprimedVars);
                    }

                    // Update ruleManager for the destination relation (if different from source and not already updated)
                    /*
                    Expr dstRelationName = hr.dstRelation;
                    if (srcRelationName != dstRelationName &&
                        find(ruleManager.invVars[dstRelationName].begin(),
                             ruleManager.invVars[dstRelationName].end(),
                             myRealCounter) == ruleManager.invVars[dstRelationName].end())
                    {
                        ruleManager.invVars[dstRelationName].push_back(myRealCounter);
                    }
                    */
                }

                // --- Modify the Query Rule ---
                if (hr.isQuery)
                {
                    if (printLog >= 3)
                        outs() << "Adding " << myRealRoot << " to source variables of query rule: " << hr.srcRelation << "\n";
                    // Add to source variables (inputs to the query condition)
                    hr.srcVars.push_back(myRealRoot);

                    ExprSet bodyConjuncts;
                    getConj(hr.body, bodyConjuncts);        // Get existing conjuncts
                    bodyConjuncts.insert(updateConstraint); // Add the increment constraint
                    hr.body = conjoin(bodyConjuncts, m_efac);

                    Expr srcRelationName = hr.srcRelation;
                    if (find(ruleManager.invVars[srcRelationName].begin(),
                             ruleManager.invVars[srcRelationName].end(),
                             myRealRoot) == ruleManager.invVars[srcRelationName].end())
                    {
                        ExprVector updatedQuerySrcUnprimedVars = ruleManager.invVars[srcRelationName];
                        updatedQuerySrcUnprimedVars.push_back(myRealRoot);
                        ruleManager.invVars[srcRelationName].clear();
                        ruleManager.invVarsPrime[srcRelationName].push_back(myRealRootPrime);
                        ruleManager.addDeclAndVars(srcRelationName, updatedQuerySrcUnprimedVars);
                    }
                }
            }

            updateCategorizationOfCHCs(i); // Update the categorization of CHCs for this invariant
            return myRealRoot;
        }

        std::optional<Expr> addConst(int i, std::string rootVal, size_t rootCount)
        {
            return std::nullopt;
        };

        std::optional<Expr> addVar(int i, std::string rootVal, size_t rootCount, EZ3 &z3, std::vector<std::string> sqrts = std::vector<std::string>())
        {
            return std::nullopt;
        };

        Expr addIndex(int i)
        {
            assert(i < invNumber);
            // --- Define the counter variable ---
            std::string counterBaseName = "_i_0";
            Expr counterNameUnprimedExpr = mkTerm<string>(counterBaseName, m_efac);
            Expr counterNamePrimedExpr = mkTerm<string>(counterBaseName + "'", m_efac);
            Expr myRealCounter = bind::realConst(counterNameUnprimedExpr);
            Expr myRealCounterPrime = bind::realConst(counterNamePrimedExpr);
            Expr oneReal = mkTerm(mpq_class("1"), m_efac);
            Expr incrementConstraint = mk<EQ>(myRealCounterPrime, mk<PLUS>(myRealCounter, oneReal));
            invarVarsShort[i].push_back(myRealCounter);

            for (auto &hr : ruleManager.chcs)
            {
                // --- Modify the Fact ---
                if (hr.isFact)
                { // Ensure it's actually a fact
                    // Add to destination variables
                    if (printLog >= 3)
                        outs() << "Adding " << myRealCounter << " to source variables of fact: " << hr.dstRelation << "\n";
                    hr.dstVars.push_back(myRealCounterPrime);

                    if (printLog >= 3)
                        outs() << "Adding " << myRealCounterPrime << " to destination variables of fact: " << hr.dstRelation << "\n";
                    // Add constraint to body: _my_real_counter_prime = 0.0
                    ExprSet bodyConjuncts;
                    getConj(hr.body, bodyConjuncts); // Get existing conjuncts

                    // Create 0 real literal
                    Expr zeroReal = mkTerm(mpq_class("0"), m_efac);
                    Expr initConstraint = mk<EQ>(zeroReal, myRealCounterPrime);
                    bodyConjuncts.insert(initConstraint);

                    hr.body = conjoin(bodyConjuncts, m_efac); //

                    // Update ruleManager for the relation defined by this fact
                    Expr relationName = hr.dstRelation;
                    if (find(ruleManager.invVars[relationName].begin(),
                             ruleManager.invVars[relationName].end(),
                             myRealCounter) == ruleManager.invVars[relationName].end())
                    {
                        ExprVector updatedQueryDstUnprimedVars = ruleManager.invVars[relationName];
                        updatedQueryDstUnprimedVars.push_back(myRealCounter);
                        ruleManager.invVars[relationName].clear();
                        ruleManager.invVarsPrime[relationName].push_back(myRealCounterPrime);
                        ruleManager.addDeclAndVars(relationName, updatedQueryDstUnprimedVars);
                    }
                }

                // --- Modify the Transition Rule ---
                if (hr.isInductive || (!hr.isFact && !hr.isQuery))
                {
                    if (printLog >= 3)
                        outs() << "Adding " << myRealCounter << " to source variables of transition rule: " << hr.srcRelation << "\n";

                    hr.srcVars.push_back(myRealCounter);

                    if (printLog >= 3)
                        outs() << "Adding " << myRealCounterPrime << " to destination variables of transition rule: " << hr.dstRelation << "\n";
                    hr.dstVars.push_back(myRealCounterPrime);

                    // Add constraint to body: _my_real_counter_prime = _my_real_counter + 1.0
                    ExprSet bodyConjuncts;
                    getConj(hr.body, bodyConjuncts);
                    bodyConjuncts.insert(incrementConstraint);
                    hr.body = conjoin(bodyConjuncts, m_efac);

                    // Update ruleManager for the source relation if it's not already updated
                    Expr srcRelationName = hr.srcRelation;
                    if (find(ruleManager.invVars[srcRelationName].begin(),
                             ruleManager.invVars[srcRelationName].end(),
                             myRealCounter) == ruleManager.invVars[srcRelationName].end())
                    {
                        ExprVector updatedQuerySrcUnprimedVars = ruleManager.invVars[srcRelationName];
                        updatedQuerySrcUnprimedVars.push_back(myRealCounter);
                        ruleManager.invVars[srcRelationName].clear();
                        ruleManager.invVarsPrime[srcRelationName].push_back(myRealCounterPrime);
                        ruleManager.addDeclAndVars(srcRelationName, updatedQuerySrcUnprimedVars);
                    }

                    // Update ruleManager for the destination relation (if different from source and not already updated)
                    /*
                    Expr dstRelationName = hr.dstRelation;
                    if (srcRelationName != dstRelationName &&
                        find(ruleManager.invVars[dstRelationName].begin(),
                             ruleManager.invVars[dstRelationName].end(),
                             myRealCounter) == ruleManager.invVars[dstRelationName].end())
                    {
                        ruleManager.invVars[dstRelationName].push_back(myRealCounter);
                    }
                    */
                }

                // --- Modify the Query Rule ---
                if (hr.isQuery)
                {
                    if (this->printLog >= 3)
                        outs() << "Adding " << myRealCounter << " to source variables of query rule: " << hr.srcRelation << "\n";
                    // Add to source variables (inputs to the query condition)
                    hr.srcVars.push_back(myRealCounter);

                    ExprSet bodyConjuncts;
                    getConj(hr.body, bodyConjuncts);           // Get existing conjuncts
                    bodyConjuncts.insert(incrementConstraint); // Add the increment constraint
                    hr.body = conjoin(bodyConjuncts, m_efac);

                    Expr srcRelationName = hr.srcRelation;
                    if (find(ruleManager.invVars[srcRelationName].begin(),
                             ruleManager.invVars[srcRelationName].end(),
                             myRealCounter) == ruleManager.invVars[srcRelationName].end())
                    {
                        ExprVector updatedQuerySrcUnprimedVars = ruleManager.invVars[srcRelationName];
                        updatedQuerySrcUnprimedVars.push_back(myRealCounter);
                        ruleManager.invVars[srcRelationName].clear();
                        ruleManager.invVarsPrime[srcRelationName].push_back(myRealCounterPrime);
                        ruleManager.addDeclAndVars(srcRelationName, updatedQuerySrcUnprimedVars);
                    }
                }
            }

            updateCategorizationOfCHCs(i); // Update the categorization of CHCs for this invariant
            return myRealCounter;
        }

        // For version 0.0, this only grabs variables that are inside of the body
        // of the body of query
        std::string getCallToPolar(int i)
        {
            assert(i < invNumber);
            ExprVector allVar = qr[i]->srcVars;
            ExprVector bodyVar;
            std::copy_if(allVar.begin(), allVar.end(), std::back_inserter(bodyVar),
                         [&](Expr e)
                         { return contains(qr[i]->body, e); });
            auto shellQuote = [](const std::string &path)
            {
                std::string quoted = "'";
                for (char ch : path)
                {
                    if (ch == '\'')
                    {
                        quoted += "'\\''";
                    }
                    else
                    {
                        quoted += ch;
                    }
                }
                quoted += "'";
                return quoted;
            };

            std::string polarBase = std::string(FREQHORN_SOURCE_DIR) + "/tools/polar";
            std::string venvPython = polarBase + "/.venv/bin/python3";
            std::string polarScript = polarBase + "/closedforms2.py";

            std::string pythonCmd;
            if (std::ifstream(venvPython).good())
            {
                pythonCmd = venvPython;
            }
            else if (!std::string(POLAR_PYTHON_EXECUTABLE).empty())
            {
                pythonCmd = std::string(POLAR_PYTHON_EXECUTABLE);
            }
            else
            {
                pythonCmd = "python3";
            }

            std::string call = shellQuote(pythonCmd) + " " + shellQuote(polarScript);
            call += " " + shellQuote(probFilePath);
            call += std::accumulate(bodyVar.begin(), bodyVar.end(), string(),
                                    [&](std::string &a, Expr b)
                                    { return a += " " + boost::algorithm::to_lower_copy(getVarName(b)); });
            // outs() << call << "\n";
            return call;
        }

        // Helper: Extract numeric value from special root variable names like "sqrt17"
        // Returns empty string if not a special root variable
        std::optional<std::string> extractRootValue2(const std::string &varName)
        {
            // Pattern: "sqrt<number>" -> extract <number>
            if (varName.substr(0, 4) == "sqrt" && varName.size() > 4)
            {
                std::string numStr = varName.substr(4); // extract after "sqrt"
                // Check if remaining characters are all digits
                if (std::all_of(numStr.begin(), numStr.end(), ::isdigit))
                {
                    return numStr;
                }
            }
            // Add more patterns as needed: "cbrt<number>", etc.
            return std::nullopt;
        }

        // Function to find all instances
        std::vector<std::string> extractRootValue(const std::string &input)
        {
            std::vector<std::string> results;
            std::string target = "sqrt";

            // Create iterators representing the range of the string we are currently searching
            auto searchStart = input.begin();
            auto searchEnd = input.end();

            while (true)
            {
                // 1. Find the next occurrence of "sqrt" within the current range
                // boost::make_iterator_range creates a temporary range object we can search
                auto rangeToSearch = boost::make_iterator_range(searchStart, searchEnd);
                auto foundRange = boost::algorithm::find_first(rangeToSearch, target);

                // If the range is empty, we didn't find "sqrt". Break the loop.
                if (foundRange.empty())
                {
                    break;
                }

                // 2. Identification: The value starts immediately after "sqrt"
                auto value_start = foundRange.end();
                auto value_end = value_start;

                // 3. Extraction: Move valueEnd forward until we hit a space, ')', or end of string
                while (value_end != searchEnd &&
                       !boost::algorithm::is_space()(*value_end) &&
                       *value_end != ')')
                {
                    value_end++;
                }

                // Only add if there is actual content (handles edge case like "sqrt " with nothing after)
                if (value_start != value_end)
                {
                    results.emplace_back(value_start, value_end);
                }

                // 4. Update the search start position to be after the current value
                // so we don't find the same "sqrt" again.
                searchStart = value_end;
            }

            return results;
        }

        // Helper: Create constraint assertion for special root variables
        // For "sqrt17": (assert (and (> sqrt17 0) (= 17 (* sqrt17 sqrt17))))
        Expr createRootConstraint(Expr rootVar, const std::string &rootValue)
        {
            try
            {
                int value = std::stoi(rootValue);
                // Create: (> rootVar 0)
                Expr positivityConstraint = mk<GT>(rootVar, zeroReal);

                // Create: (= value (* rootVar rootVar))
                Expr valueTerm = mkTerm(mpq_class(rootValue), m_efac);
                Expr productConstraint = mk<EQ>(valueTerm, mk<MULT>(rootVar, rootVar));

                // Combine: (and positivityConstraint productConstraint)
                return mk<AND>(positivityConstraint, productConstraint);
            }
            catch (const std::exception &e)
            {
                if (this->printLog >= 2)
                {
                    outs() << "Warning: Could not create root constraint for " << rootValue << "\n";
                }
                return mk<TRUE>(m_efac);
            }
        }

        std::map<std::string, Expr> insertRoots(int i, nlohmann::json &closedformJson, EZ3 &z3)
        {
            assert(i < invNumber);
            symbolicRoots[i] = ExprVector();
            numericRoots[i] = ExprVector();
            squareRootExists[i] = set<std::string>();
            std::map<std::string, Expr> rootMap;

            ExprSet rootConstraints; // Collect constraints for special roots
            size_t rootCount = 0;
            for (const auto &v : closedformJson)
            {
                if (!v.is_array())
                    continue;

                for (const auto &item : v)
                {
                    if (!item.contains("bases") || !item["bases"].is_array())
                        continue;

                    for (const auto &base : item["bases"])
                    {

                        std::string baseStr = base.get<std::string>();
                        if (!rootMap.count(baseStr))
                        {
                            // Check if this is a special root variable like "sqrt17"
                            std::vector<std::string> rootValueOpt;
                            rootValueOpt = extractRootValue(baseStr);

                            if (rootValueOpt.size() != 0)
                            {
                                if (this->printLog >= 3)
                                {
                                    outs() << "Adding constraint for special root: " << baseStr << "\n";
                                }

                                for (auto r : rootValueOpt)
                                {
                                    if (squareRootExists[i].count(r) == 0)
                                    {
                                        std::string name = "sqrt" + r;
                                        Expr var = mkTerm<string>(name, m_efac);
                                        Expr mySqrt = bind::realConst(var);
                                        // NOTE: Do NOT push to invarVarsShort here.
                                        // sqrt variables are registered in the post-loop block below,
                                        // which appends them to both invarVarsShort AND dstVars/srcVars
                                        // at the same position, avoiding ordering mismatches.

                                        Expr constraint = createRootConstraint(mySqrt, r);
                                        rootConstraints.insert(constraint);
                                        squareRootExists[i].insert(r);
                                    }
                                }

                                // Create and add constraint
                            }

                            Expr rootExpr = addRoot(i, baseStr, rootCount++, z3, rootValueOpt);
                            rootMap[baseStr] = rootExpr;
                        }
                        else if (this->printLog >= 3)
                        {
                            outs() << baseStr << " was already in the map\n";
                        }
                    }
                }
            }

            // Add all root constraints to initial conditions
            if (!rootConstraints.empty())
            {
                ExprSet bodyConjuncts;
                // Get any existing fact constraints
                for (auto &hr : ruleManager.chcs)
                {
                    if (hr.isFact)
                    {
                        getConj(hr.body, bodyConjuncts);
                        break; // Only need to check the fact rule
                    }
                }
                // Add all root constraints
                bodyConjuncts.insert(rootConstraints.begin(), rootConstraints.end());

                // Update fact rule body with root constraints
                for (auto &hr : ruleManager.chcs)
                {
                    if (hr.isFact)
                    {
                        hr.body = conjoin(bodyConjuncts, m_efac);
                        if (this->printLog >= 3)
                        {
                            outs() << "Updated fact rule body with root constraints\n";
                        }
                        break;
                    }
                }
            }

            // === Register sqrt variables in invarVarsShort AND CHC srcVars/dstVars ===
            // IMPORTANT: sqrt variables must be appended to invarVarsShort[i] HERE
            // (after all _r_N roots have been added), so their position matches
            // the position in dstVars/srcVars. Adding them earlier (before addRoot)
            // causes a positional mismatch that corrupts replaceAll substitution.
            for (const auto &sqrtSuffix : squareRootExists[i])
            {
                std::string fullName = "sqrt" + sqrtSuffix;
                std::string primedName = fullName + "'";

                Expr sqrtVar = bind::realConst(mkTerm<std::string>(fullName, m_efac));
                Expr sqrtVarPrime = bind::realConst(mkTerm<std::string>(primedName, m_efac));

                // Check if already registered in ruleManager to avoid duplicates
                Expr rel = decls[i];
                bool alreadyInRM = false;
                for (const auto &v : ruleManager.invVars[rel])
                {
                    if (v == sqrtVar)
                    {
                        alreadyInRM = true;
                        break;
                    }
                }
                if (alreadyInRM)
                    continue;

                if (printLog >= 3)
                    outs() << "Registering sqrt variable " << fullName
                           << " in CHC rules and ruleManager for invariant #" << i << "\n";

                // Add to invarVarsShort[i] — must happen HERE, after all _r_N roots,
                // so the position matches the dstVars/srcVars push below.
                invarVarsShort[i].push_back(sqrtVar);

                // Update ruleManager.invVars and invVarsPrime
                ExprVector updatedVars = ruleManager.invVars[rel];
                updatedVars.push_back(sqrtVar);
                ruleManager.invVars[rel].clear();
                ruleManager.invVarsPrime[rel].push_back(sqrtVarPrime);
                ruleManager.addDeclAndVars(rel, updatedVars);

                // Add to each CHC rule's srcVars/dstVars
                for (auto &hr : ruleManager.chcs)
                {
                    int srcNum = getVarIndex(hr.srcRelation, decls);
                    int dstNum = getVarIndex(hr.dstRelation, decls);

                    if (hr.isFact && dstNum == i)
                    {
                        hr.dstVars.push_back(sqrtVarPrime);

                        // Add sqrt' = sqrt to fact body so the value is constrained
                        ExprSet bodyConj;
                        getConj(hr.body, bodyConj);
                        bodyConj.insert(mk<EQ>(sqrtVarPrime, sqrtVar));
                        hr.body = conjoin(bodyConj, m_efac);

                        if (printLog >= 3)
                            outs() << "Adding " << primedName
                                   << " to dstVars of fact rule\n";
                    }

                    if (hr.isInductive || (!hr.isFact && !hr.isQuery))
                    {
                        hr.srcVars.push_back(sqrtVar);
                        hr.dstVars.push_back(sqrtVarPrime);

                        // sqrt is constant across iterations: sqrt' = sqrt
                        ExprSet bodyConj;
                        getConj(hr.body, bodyConj);
                        bodyConj.insert(mk<EQ>(sqrtVarPrime, sqrtVar));
                        hr.body = conjoin(bodyConj, m_efac);

                        if (printLog >= 3)
                            outs() << "Adding " << fullName << " / " << primedName
                                   << " to srcVars/dstVars of transition rule\n";
                    }

                    if (hr.isQuery && srcNum == i)
                    {
                        hr.srcVars.push_back(sqrtVar);

                        if (printLog >= 3)
                            outs() << "Adding " << fullName
                                   << " to srcVars of query rule\n";
                    }
                }
            }

            updateCategorizationOfCHCs(i);

            return rootMap;
        }

        void redefineDeclAndVars(Expr rel, ExprVector &args, int i)
        {
            ExprVector types;
            for (auto &var : args)
            {
                types.push_back(bind::typeOf(var));
            }
            types.push_back(mk<BOOL_TY>(m_efac));

            decls[i] = bind::fdecl(rel, types);

            for (auto &v : args)
            {
                ruleManager.invVars[rel].push_back(v);
            }
        }

        // Replace variables in a coefficient expression that was parsed from
        // POLAR output.  Only the index variable 'n' should become _i_0;
        // sqrtNNN variables should become their corresponding Expr constants.
        Expr replaceCoeffVariables(Expr expr, Expr indexVar, int invIdx)
        {
            ExprSet vars;
            filter(expr, bind::IsConst(), inserter(vars, vars.begin()));

            if (vars.empty())
                return expr;

            ExprMap replacements;
            for (const Expr &var : vars)
            {
                std::string vname = getVarName(var);
                if (vname == "n" || vname == "_x")
                {
                    replacements[var] = indexVar;
                }
                else if (vname.substr(0, 4) == "sqrt")
                {
                    // Look up the matching sqrt Expr in invarVarsShort
                    Expr sqrtExpr = bind::realConst(mkTerm<std::string>(vname, m_efac));
                    replacements[var] = sqrtExpr;
                }
                else
                {
                    // Unknown variable — replace with index as fallback
                    if (printLog >= 2)
                        outs() << "Warning: unknown variable '" << vname
                               << "' in coefficient, replacing with index\n";
                    replacements[var] = indexVar;
                }
            }

            return replaceAll(expr, replacements);
        }

        Expr replaceUniqueVariable(Expr expr, Expr newVar)
        {
            ExprSet vars;
            filter(expr, bind::IsConst(), inserter(vars, vars.begin()));

            if (vars.empty())
            {
                if (printLog >= 5)
                {
                    outs() << "Warning: No variables found in expression\n";
                }

                return expr;
            }

            if (vars.size() > 1)
            {
                if (printLog >= 5)
                {
                    outs() << "Warning: Expression has multiple variables, replacing all\n";
                }
            }

            ExprMap replacements;
            for (const Expr &var : vars)
            {
                replacements[var] = newVar;
            }

            return replaceAll(expr, replacements);
        }

        /// Recursively convert every MPZ (integer) leaf in \p e to an
        /// equivalent MPQ (rational) leaf.  This ensures that expressions
        /// round-tripped through Z3's parser are marshalled back to Z3
        /// with Real sort, avoiding the problem where bare integer
        /// literals like 9 get printed as "9" instead of "(/ 9 1)".
        Expr mpzToMpq(Expr e)
        {
            if (!e)
                return e;
            if (isOpX<MPZ>(e))
            {
                mpz_class z = getTerm<mpz_class>(e);
                return mkTerm(mpq_class(z), m_efac);
            }
            // Recurse into children
            bool changed = false;
            std::vector<Expr> kids(e->arity());
            for (unsigned i = 0; i < e->arity(); ++i)
            {
                kids[i] = mpzToMpq(e->arg(i));
                if (kids[i] != e->arg(i))
                    changed = true;
            }
            if (!changed)
                return e;
            if (kids.size() == 0)
                return e;
            if (kids.size() == 1)
                return e->getFactory().mkNary(e->op(), kids.begin(), kids.end());
            return e->getFactory().mkNary(e->op(), kids.begin(), kids.end());
        }

        // Only works for expressions that are either numeric
        // constants or include "_i_0"
        Expr str_to_expr(std::string exprString, std::vector<std::string> sqrts = std::vector<std::string>(), int i = 0)
        {

            if (sqrts.size() == 0)
            {
                auto sqrtNums = getAllSqrtWords(exprString);
                sqrts = sqrtNums;
            }

            std::string outfile;
            // outfile << "(set-logic QF_LIRA)\n";
            outfile += "(declare-const _x Real)\n";
            outfile += "(declare-const n Real)\n";
            for (auto s : sqrts)
            {
                outfile += "(declare-const sqrt" + s + " Real)\n";
            }
            outfile += "(assert (= _x " + exprString + "))\n";
            outfile += "(check-sat)\n";
            // outfile.close();

            // Parse the file
            Expr result = z3_from_smtlib(m_z3, outfile);

            // Extract just the expression from the equality
            // result should be: (and (= _x (/ 10 5)))
            // We want: (/ 10 5)

            // Convert MPZ leaves to MPQ so that all numeric
            // constants are Real-sorted when marshalled back to Z3.
            result = mpzToMpq(result);

            if (isOpX<EQ>(result))
            {
                // Single equality, return RHS (the actual expression)
                return result->right();
            }
            else if (isOpX<AND>(result))
            {
                // AND of equalities, get first conjunct
                Expr eq = result->left();
                if (isOpX<EQ>(eq))
                    return eq->right();
            }

            return result;
        }

        Expr double_to_expr(const double &x)
        {
            return mkTerm(mpq_class(x), m_efac);
        }

        double expr_to_double(Expr expr)
        {
            if (this->printLog >= 3)
            {
                outs() << "Simplified expression: " << *expr << "\n";
            }
            // Leaf: integer
            if (isOpX<MPZ>(expr))
            {
                mpz_class val = getTerm<mpz_class>(expr);
                return val.get_d();
            }
            // Leaf: rational
            else if (isOpX<MPQ>(expr))
            {
                mpq_class val = getTerm<mpq_class>(expr);
                return val.get_d();
            }
            // Leaf: algebraic (irrational) number — use midpoint approximation
            else if (isOpX<ALNUM>(expr))
            {
                const AlgebraicNum &a = getTerm<AlgebraicNum>(expr);
                return a.to_double();
            }
            // Division
            else if (isOpX<expr::op::DIV>(expr))
            {
                double num = expr_to_double(expr->left());
                double den = expr_to_double(expr->right());
                if (den == 0.0)
                    return 0.0;
                return num / den;
            }
            // Multiplication (binary or n-ary)
            else if (isOpX<MULT>(expr))
            {
                double result = 1.0;
                for (unsigned j = 0; j < expr->arity(); ++j)
                    result *= expr_to_double(expr->arg(j));
                return result;
            }
            // Addition (binary or n-ary)
            else if (isOpX<PLUS>(expr))
            {
                double result = 0.0;
                for (unsigned j = 0; j < expr->arity(); ++j)
                    result += expr_to_double(expr->arg(j));
                return result;
            }
            // Subtraction
            else if (isOpX<MINUS>(expr))
            {
                return expr_to_double(expr->left()) - expr_to_double(expr->right());
            }
            // Unary minus
            else if (isOpX<UN_MINUS>(expr))
            {
                return -expr_to_double(expr->arg(0));
            }
            else
            {
                if (this->printLog >= 3)
                {
                    outs() << "Warning: Expression is not a numeric constant\n";
                }
                return 0.0;
            }
        }

        template <typename Z>
        double expr_to_double(const std::string &exprString, Z &z3)
        {
            // Parse the string into an expression using the temp file method
            Expr expr = str_to_expr(exprString);

            if (!expr)
            {
                outs() << "Warning: Failed to parse expression string\n";
                return 0.0;
            }

            // Now extract the numeric value from the expression
            return expr_to_double(expr);
        }

        Expr getInitBody(int i)
        {
            assert(i < invNumber);
            Expr dstRelationName = fc[i]->dstRelation;
            ExprVector unprimed = ruleManager.invVars[dstRelationName];
            ExprVector primed = ruleManager.invVarsPrime[dstRelationName];
            ExprMap mappings;
            size_t amount = ruleManager.invVars[dstRelationName].size();
            for (size_t index = 0; index < amount; index++)
            {
                // outs() << "Primed: "*primed[index] << " Unprimed: " << *unprimed[index] << "\n";
                mappings[primed[index]] = unprimed[index];
            }

            Expr test = replaceAll(fc[i]->body, mappings);
            return test;
        }
    };

    void learnInvariants5(std::string smt, unsigned to, bool doElim, bool doArithm, bool getRoots, int debug)
    {
        ExprFactory m_efac;
        EZ3 z3(m_efac);
        SMTUtils u(m_efac);
        CHCs ruleManager(m_efac, z3, debug - 2);
        auto res = ruleManager.parse(smt, doElim, doArithm);
        RndLearnerV5 ds(m_efac, z3, ruleManager, to, debug);
        // ds.z3_testing();
        // return;

        for (int i = 0; i < ruleManager.cycles.size(); i++)
        {
            Expr dcl = ruleManager.chcs[ruleManager.cycles[i][0]].srcRelation;
            if (ds.initializedDecl(dcl))
                continue;
            ds.initializeDecl2(dcl);
        }
        ds.categorizeCHCs2();
        int i = 0; // invariant number we want to look at

        /**
         * TODO: There's actually a non-zero probability that I don't
         * need to add the update for the index of the safety, just
         * as a heads up.
         */

        ds.reflipSimpleEqualities(); // Reflip simple equalities in CHCs
        if (debug >= 3)
        {
            ruleManager.print(true);
        }

        ds.probFilePath = std::string(FREQHORN_SOURCE_DIR) + "/out.prob";
        ds.generatePolarFile2(ruleManager, ds.probFilePath);
        /**
         * TODO: Use boost algorithm instead of this home-written
         * function
         */
        std::string polarCommand = ds.getCallToPolar(i);
        CommandResult polarResult = exec(polarCommand.c_str());
        std::string output_test = polarResult.output;

        if (polarResult.signaled || polarResult.exitCode != 0)
        {
            errs() << "Error: POLAR subprocess failed.\n";
            errs() << "Command was: " << polarCommand << "\n";

            if (polarResult.signaled)
            {
                errs() << "POLAR terminated by signal " << polarResult.signalNumber << ".\n";
            }
            else
            {
                errs() << "POLAR exited with code " << polarResult.exitCode << ".\n";
            }

            if (!output_test.empty())
            {
                errs() << "POLAR output was:\n"
                       << output_test << "\n";
            }

            if (output_test.find("KeyboardInterrupt") != std::string::npos)
            {
                errs() << "Reason: POLAR was interrupted while solving the generated recurrence. This usually means the recurrence is too expensive for SymPy's root solver on this benchmark.\n";
            }
            else if (output_test.find("Traceback") != std::string::npos)
            {
                errs() << "Reason: POLAR raised a Python exception while analyzing the generated recurrence.\n";
            }

            outs() << "unknown\n";
            return;
        }

        if (output_test.empty())
        {
            errs() << "Error: POLAR subprocess returned no output.\n";
            errs() << "Command was: " << polarCommand << "\n";
            errs() << "POLAR exited successfully but did not emit JSON output.\n";
            outs() << "unknown\n";
            return;
        }
        nlohmann::json closedformJson;
        try
        {
            closedformJson = nlohmann::json::parse(output_test);
        }
        catch (const nlohmann::json::parse_error &e)
        {
            errs() << "Error: Failed to parse POLAR output as JSON.\n";
            errs() << "Command was: " << polarCommand << "\n";
            errs() << "POLAR output was:\n"
                   << output_test << "\n";
            errs() << "JSON error: " << e.what() << "\n";
            outs() << "unknown\n";
            return;
        }

        /**
         * Get the initial symbolic closed form as a conjunction
         */
        Expr symbolicClosedForms = ds.generateSymbolicClosedForms(i, closedformJson);

        if (getRoots)
        {
            for (const auto &[numericStr, symbolicExpr] : ds.rootMaps[i])
            {
                outs() << symbolicExpr << " (base: " << numericStr << ")\n";
            }
            return;
        }

        Expr index = ds.indices[i];
        Expr oneReal = mkTerm(mpq_class("1"), m_efac);
        Expr zeroReal = mkTerm(mpq_class("0"), m_efac);
        if (debug >= 5)
        {
            pprint(symbolicClosedForms);
        }

        /**
         * Get the root bounds as a conjunction
         */
        auto rootBoundsRes = ds.generateRootBounds(i);
        Expr rootBounds;
        if (!rootBoundsRes && debug >= 5)
        {
            outs() << "For some reason the program tried to generate root bounds for roots that don't exist\n";
            outs() << "The request was ignored...\n";
            rootBounds = mk<TRUE>(m_efac);
        }
        else
        {
            rootBounds = rootBoundsRes.value();
        }

        /**
         * Get the lemma (0<=i<1) -> Init(V)
         */
        Expr initialCondition = ds.generateInitCond(i);
        ExprSet lemmasSet;
        getConj(symbolicClosedForms, lemmasSet);
        getConj(rootBounds, lemmasSet);
        getConj(initialCondition, lemmasSet);
        Expr firstInv = conjoin(lemmasSet, m_efac);
        if (debug >= 3)
        {
            ruleManager.print(true);
            outs() << firstInv << "\n";
        }

        /**
         * Check first to see if it passes initiation and consecution.
         * - If so, check safety. And if that works, you're done.
         * - If not, exit out of confusion.
         */
        map<int, ExprVector> annotations;
        annotations[i].push_back(firstInv);
        // boost::tribool result = ds.checkFact(i, annotations);
        if (ds.checkFact(i, annotations) && ds.checkConsecution(i, annotations))
        {
            if (ds.checkQuery(i, annotations))
            {
                // you can reformat this later
                if (debug >= 2)
                {
                    outs() << "Success! Invariant found by n=0\n";
                    ds.learnedExprs[i].insert(firstInv);
                    pprint(conjoin(ds.learnedExprs[i], m_efac));
                }
                else
                {
                    outs() << "Success!\n";
                }

                exit(EXIT_SUCCESS);
            }
            ds.learnedExprs[i].insert(firstInv);
        }

        else
        {
            // This could be caused by Sqrt Approximation. Future work can be done to
            // fix this.

            if (debug >= 5)
            {
                outs() << "initial invariant did not pass initiation and consecution...\n";
            }
            outs() << "unknown\n";

            return;
        }

        /**
         * TODO: Here you should enter the algorithm for computing
         * the maximum N based on the closed forms. Use an optional type
         * in case there is no solution / the system cannot compute an N.
         */

        /**
         * TODO: This is where to place a call to a function that generates
         * a new thread to run the dReal reachability algorithm.
         * Make sure to not use the same Z3 context, you will have to make
         * it from scratch. You may be able to make a deep copy of things,
         * but make sure to double check.
         */

        /**
         * Main analysis loop:
         * 1) Go through list of roots and add a clause showing how the value has been
         * decreased with an increased index
         * 2) If it does not pass consecution, increment the estimation by an epsilon
         * 3) after this is done, see if it passes safety.
         */

        uint64_t max_iterations = 10000;
        ExprSet lemmas;
        ExprMap previousUpper; // maps variable to it's upper last iteration
        ExprMap previousLower; // maps variable to it's lower last iteration
        for (auto v : ds.symbolicRoots[i])
        {
            previousUpper[v] = oneReal;
            previousLower[v] = oneReal;
        }

        boost::container::flat_set<Expr> hasDeviated;
        std::unordered_map<Expr, phaseLemmas> phaseCond;
        ExprVector symbolsToKeep;
        ExprVector numeralsToKeep;
        Expr n, s;
        auto forward = [&](Expr curr) -> Expr
        {
            return mk<GEQ>(index, curr);
        };
        auto backward = [&](Expr curr) -> Expr
        {
            return mk<LEQ>(index, curr);
        };

        // filter out 1.0 roots and create
        // a dispatch table for the non-1 roots.
        for (const auto &tuple : boost::combine(ds.numericRoots[i], ds.symbolicRoots[i]))
        {
            boost::tie(n, s) = tuple;
            if (n == oneReal)
            {
                continue;
            }
            numeralsToKeep.push_back(n);
            symbolsToKeep.push_back(s);
            double val = ds.expr_to_double(n);
            if (val > 1.0) // uphill
            {
                phaseLemmas pl;
                pl.max = backward;
                pl.min = forward;
                phaseCond[s] = pl;
            }
            else if (val < 1.0 && val > 0.0) // downhill
            {
                phaseLemmas pl;
                pl.max = forward;
                pl.min = backward;
                phaseCond[s] = pl;
            }
            else
            {
                if (debug >= 3)
                {
                    outs() << "Unsupported root: " << n << "\n";
                }

                outs() << "unknown\n";
            }
        }

        ds.numericRoots[i] = numeralsToKeep;
        ds.symbolicRoots[i] = symbolsToKeep;
        Expr itr = zeroReal;
        map<int, ExprVector> verifiedLemmas;
        for (size_t j = 1; j < max_iterations; j++)
        {
            itr = ds.mpzToMpq(simplifyArithm(mk<PLUS>(itr, oneReal)));
            // Assumes we only have roots 0<r<1 and 1<r
            for (const auto &tuple : boost::combine(ds.numericRoots[i], ds.symbolicRoots[i]))
            {
                Expr n, s;
                boost::tie(n, s) = tuple;

                // --- Upper bound ---
                Expr upperBound = simplifyArithm(mk<MULT>(previousUpper[s], n));
                Expr cond = phaseCond[s].max(itr);
                Expr bnd = mk<LEQ>(s, upperBound);
                Expr newLemma = mk<IMPL>(cond, bnd);
                annotations[i][0] = newLemma;
                {
                    boost::tribool consResult = ds.checkConsecution(i, annotations);
                    if (!(consResult == true))
                    {
                        hasDeviated.insert(s);
                        do
                        {
                            upperBound = simplifyArithm(mk<PLUS>(upperBound, ds.expEpsilon));
                            bnd = mk<LEQ>(s, upperBound);
                            newLemma = mk<IMPL>(cond, bnd);
                            annotations[i][0] = newLemma;
                            consResult = ds.checkConsecution(i, annotations);
                        } while (!(consResult == true));
                    }
                }

                Expr upperLemma = newLemma;
                previousUpper[s] = upperBound;

                Expr lowerBound;
                if (hasDeviated.count(s) > 0)
                {
                    lowerBound = simplifyArithm(mk<MULT>(previousLower[s], n));
                }
                else
                {
                    lowerBound = upperBound;
                }

                cond = phaseCond[s].min(itr);
                bnd = mk<GEQ>(s, lowerBound);
                newLemma = mk<IMPL>(cond, bnd);
                annotations[i][0] = mk<AND>(upperLemma, newLemma);
                {
                    boost::tribool consResult = ds.checkConsecution(i, annotations);
                    if (!consResult == true)
                    {
                        hasDeviated.insert(s);
                        do
                        {
                            lowerBound = simplifyArithm(mk<MINUS>(lowerBound, ds.expEpsilon));
                            bnd = mk<GEQ>(s, lowerBound);
                            newLemma = mk<IMPL>(cond, bnd);
                            annotations[i][0] = mk<AND>(upperLemma, newLemma);
                            consResult = ds.checkConsecution(i, annotations);
                        } while (!(consResult == true));
                    }
                }

                // Check safety
                {
                    boost::tribool qResult = ds.checkQuery(i, annotations);
                    if (qResult == true)
                    {
                        if (ds.checkFact(i, annotations) == true)
                        {
                            if (debug >= 1)
                            {
                                outs() << "Invariant found by index " << j << "\n";
                                ds.learnedExprs[i].insert(newLemma);
                                outs() << conjoin(ds.learnedExprs[i], m_efac) << "\n";
                            }
                            else
                            {
                                outs() << "Success!\n";
                            }
                            exit(EXIT_SUCCESS);
                        }
                        else
                        {
                            if (debug >= 5)
                                outs() << "didn't pass initiation...\n";
                            outs() << "unknown\n";
                            exit(EXIT_FAILURE);
                        }
                    }
                    else if (boost::indeterminate(qResult))
                    {
                        if (debug >= 3)
                            outs() << "Warning: checkQuery returned UNKNOWN at index " << j << "\n";
                    }
                }

                // Use an interval condition instead of a point equality so
                // that non-integer values of _i_0 (e.g. 40.5) cannot slip
                // between the cracks and evade all learned lemmas.
                Expr nextItr = ds.mpzToMpq(simplifyArithm(mk<PLUS>(itr, oneReal)));
                Expr lemma = mk<AND>(mk<GEQ>(index, itr), mk<LT>(index, nextItr));
                Expr resultant;
                if (hasDeviated.count(s) == 0)
                {
                    resultant = mk<EQ>(s, upperBound);
                }
                else
                {
                    resultant = mk<AND>(mk<LEQ>(s, upperBound), mk<GEQ>(s, lowerBound));
                }
                ds.learnedExprs[i].insert(mk<IMPL>(lemma, resultant));
                previousLower[s] = lowerBound;
            }
        }

        outs() << "Analysis inconclusive after " << max_iterations << " iterations.\n";
        exit(EXIT_SUCCESS);
    }
}

#endif // RNDLEARNERV5__HPP__