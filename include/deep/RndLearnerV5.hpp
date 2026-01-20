#ifndef RNDLEARNERV5__HPP__
#define RNDLEARNERV5__HPP__

#include "RndLearnerV4.hpp"
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
#include <boost/range/combine.hpp>
#include <iostream>
#include <stdexcept>
#include <stdio.h>
#include <string>
using namespace std;
using namespace boost;

std::string exec(const char *cmd)
{
    char buffer[128];
    std::string result = "";
    FILE *pipe = popen(cmd, "r");
    if (!pipe)
        throw std::runtime_error("popen() failed!");
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
    pclose(pipe);
    return result;
}

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

        std::vector<std::vector<std::string>> polarVarNames;

    public:
        RndLearnerV5(ExprFactory &_e, EZ3 &_z3, CHCs &_r, unsigned _to, int _debug) : RndLearnerV4(_e, _z3, _r, _to, false, false, 0, 0, false, 0, false, false,
                                                                                                   false, false, 0, 0, false, _debug) {}
        ~RndLearnerV5() {}
        map<int, Expr> indices;

        Expr oneReal = mkTerm(mpq_class("1"), m_efac);
        Expr zeroReal = mkTerm(mpq_class("0"), m_efac);
        std::vector<ExprSet> learnedExprs; // indexed by invNumber
        map<int, ExprVector> symbolicRoots;
        map<int, ExprVector> numericRoots;
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
                double temp = expr_to_double(numeric, m_z3);
                if (0 < temp && temp < 1.0)
                {
                    bounds.insert(mk<LEQ>(symbolic, oneReal));
                    bounds.insert(mk<GT>(symbolic, zeroReal));
                }
                else
                {
                    bounds.insert(mk<EQ>(symbolic, oneReal));
                }
            }
            return conjoin(bounds, m_efac);
        }

        Expr generateSymbolicClosedForms(int i, nlohmann::json closedformJson)
        {
            indices[i] = addIndex(i);
            Expr index = indices[i];
            std::map<std::string, Expr> rootMap = insertRoots(i, closedformJson, m_z3);
            ExprSet initialClauses;
            initialClauses.insert(mk<GEQ>(index, zeroReal));
            // each variable that has a closed form
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
                Expr var;
                if (itr == invarVarsShort[i].end())
                {
                    continue; // Skip to the next variable if not found
                }
                else
                {
                    var = *itr;
                }
                size_t idx = 0;
                for (auto itr = v.begin(); itr != v.end(); ++itr)
                {
                    Expr cond;
                    Expr curr_idx = mkTerm(mpq_class(std::to_string(idx)), m_efac);
                    if (std::next(itr) == v.end())
                    {
                        cond = mk<GEQ>(index, curr_idx);
                    }
                    else
                    {
                        cond = mk<AND>(mk<GEQ>(index, curr_idx), mk<LT>(index, mk<PLUS>(curr_idx, oneReal)));
                    }

                    size_t jdx = 0;
                    Expr sum;
                    for (auto base_itr = v[idx]["bases"].begin(), coeff_itr = v[idx]["coeffs"].begin();
                         base_itr != v[idx]["bases"].end(), coeff_itr != v[idx]["coeffs"].end(); ++base_itr,
                              ++coeff_itr)
                    {
                        std::string c_str = coeff_itr->is_number() ? std::to_string(coeff_itr->get<int>()) : coeff_itr->get<std::string>();
                        std::string b_str = base_itr->is_number() ? std::to_string(base_itr->get<int>()) : base_itr->get<std::string>();
                        if (printLog >= 5)
                        {
                            outs() << "c_str: " << c_str << "\n";
                            outs() << "b_str: " << b_str << "\n";
                        }

                        Expr t = str_to_expr(c_str);
                        if (printLog >= 5)
                        {
                            outs() << "new expression: " << t << "\n";
                        }
                        Expr c = replaceUniqueVariable(t, index);
                        Expr b = rootMap[b_str];
                        if (jdx == 0)
                        {
                            sum = mk<MULT>(c, b);
                        }
                        else
                        {
                            sum = mk<PLUS>(sum, mk<MULT>(c, b));
                        }
                        jdx++;
                    }
                    Expr temp = mk<IMPL>(cond, mk<EQ>(var, sum));
                    initialClauses.insert(temp);
                    idx++;
                }
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
            if (expr::isOpX<expr::op::PLUS>(e) && e->arity() == 2)
            {
                return "(" + exprToPolarString(e->left(), varRenames) + " + " + exprToPolarString(e->right(), varRenames) + ")";
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
            if (expr::isOpX<expr::op::MULT>(e) && e->arity() == 2)
            {
                return "(" + exprToPolarString(e->left(), varRenames) + " * " + exprToPolarString(e->right(), varRenames) + ")";
            }
            if (expr::isOpX<expr::op::DIV>(e) || expr::isOpX<expr::op::IDIV>(e) && e->arity() == 2)
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
                        // Check if conj->left() corresponds to varExpr
                        // This direct comparison might fail if they are different Expr objects
                        // even if they represent the "same" variable in different contexts.
                        // A more robust way is to compare names if dstVars in rule are named.
                        std::string conjVarName;
                        std::cout << "Left side of EQ: " << *conj->left() << std::endl;
                        std::cout << "Right side of EQ: " << *conj->right() << std::endl;
                        if (factDstVarToName.count(conj->right()))
                        {
                            conjVarName = factDstVarToName[conj->right()];
                        }
                        else
                        {
                            // Fallback if conj->left() is not directly in dstVars (e.g. it's already a canonical var Expr)
                            conjVarName = getVarName(conj->right());
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

            if (!initLhsVars.empty())
            {
                for (size_t i = 0; i < initLhsVars.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << initLhsVars[i];
                }
                polarProgram << " = ";
                for (size_t i = 0; i < initRhsVals.size(); ++i)
                {
                    polarProgram << (i == 0 ? "" : ", ") << initRhsVals[i];
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
                ExprSet lms = learnedExprs[srcNum];
                for (auto &a : annotations[srcNum])
                    lms.insert(a);
                for (auto a : lms)
                {
                    a = replaceAll(a, invarVarsShort[srcNum], hr.srcVars);
                    exprs.insert(a);
                }
            }
            if (!hr.isQuery)
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

            if (u.isSat(exprs) && printLog >= 5)
            {
                std::cout << "Formula is SAT. Model: \n";

                // Retrieve model as an expression tree of equalities
                Expr modelExpr = u.getModel();

                // Print the model to stdout
                if (modelExpr)
                {
                    u.print(modelExpr, std::cout);
                    std::cout << std::endl;
                }

                outs() << "Expressions" << conjoin(exprs, m_efac) << "\n";
            }
            return u.isSat(exprs);
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

        Expr addRoot(int i, std::string rootVal, size_t rootCount, EZ3 &z3)
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
            // outs() << "Created symbolic root variables: " << myRealRoot << ", " << myRealRootPrime << "\n";
            Expr myRootUpdate = str_to_expr(rootVal);
            if (isOpX<expr::op::DIV>(myRootUpdate))
            {
                Expr left = myRootUpdate->left();
                Expr right = myRootUpdate->right();
                // outs() << "Root Type: " << typeid(myRootUpdate->op()).name() << "\n";
                // outs() << "Numerator Type: " << typeid(left->op()).name() << "\n";
                // outs() << "Denominator Type: " << typeid(right->op()).name() << "\n";
            }
            // outs() << "Root update expression: " << myRootUpdate << "\n";
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
            // Use absolute path instead of ~ to ensure proper expansion in popen/system
            const char *home = std::getenv("HOME");
            std::string call(home ? std::string(home) + "/tools/freqhorn/tools/polar/.venv/bin/python3 " : "");
            call += home ? std::string(home) + "/tools/freqhorn/tools/polar/closedforms2.py" : "~/tools/freqhorn/tools/polar/closedforms2.py";
            call += " ./out.prob";
            call += std::accumulate(bodyVar.begin(), bodyVar.end(), string(),
                                    [&](std::string &a, Expr b)
                                    { return a += " " + boost::algorithm::to_lower_copy(getVarName(b)); });
            // outs() << call << "\n";
            return call;
        }

        std::map<std::string, Expr> insertRoots(int i, nlohmann::json &closedformJson, EZ3 &z3)
        {
            assert(i < invNumber);
            symbolicRoots[i] = ExprVector();
            numericRoots[i] = ExprVector();
            std::map<std::string, Expr> rootMap;
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
                            rootMap[baseStr] = addRoot(i, baseStr, rootCount++, z3);
                        }
                        else if (this->printLog >= 3)
                        {
                            outs() << baseStr << " was already in the map\n";
                        }
                    }
                }
            }
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

        // Only works for expressions that are either numeric
        // constants or include "_i_0"
        Expr str_to_expr(std::string exprString)
        {
            const char *tmpfile = "/tmp/z3_expr_temp.smt2";

            std::ofstream outfile(tmpfile);
            if (!outfile.is_open())
            {
                errs() << "Failed to create temp file\n";
                return Expr();
            }

            outfile << "(set-logic QF_LIRA)\n";
            outfile << "(declare-const _x Real)\n";
            outfile << "(declare-const n Real)";
            outfile << "(assert (= _x " << exprString << "))\n";
            outfile << "(check-sat)\n";
            outfile.close();

            // Parse the file
            Expr result = z3_from_smtlib_file(m_z3, tmpfile);
            std::remove(tmpfile);

            // Extract just the expression from the equality
            // result should be: (and (= _x (/ 10 5)))
            // We want: (/ 10 5)

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
            // expr = simplifyArithm(expr, false, false);
            if (this->printLog >= 3)
            {
                outs() << "Simplified expression: " << *expr << "\n";
            }
            if (isOpX<MPZ>(expr))
            {
                mpz_class val = getTerm<mpz_class>(expr);
                return val.get_d();
            }
            else if (isOpX<MPQ>(expr))
            {
                mpq_class val = getTerm<mpq_class>(expr);
                return val.get_d();
            }

            else if (isOpX<expr::op::DIV>(expr))
            {
                Expr num = expr->left();
                Expr denom = expr->right();
                if (isOpX<MPQ>(num) && isOpX<MPQ>(denom))
                {
                    mpq_class x = getTerm<mpq_class>(num);
                    mpq_class y = getTerm<mpq_class>(denom);
                    return x.get_d() / y.get_d();
                }
                else
                {
                    return 0.0;
                }
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

        [[deprecated("This isn't used right now, you can ignore this")]]
        numExpr_t<double> getNumExpr(std::string s)
        {
            Expr temp = str_to_expr(s);
            if (!temp)
            {
                errs() << "Error: Failed to parse expression string: " << s << "\n";
                throw std::runtime_error("Failed to parse expression string");
            }
            return getNumExpr(temp);
        }
        [[deprecated("This isn't used right now, you can ignore this")]]
        numExpr_t<double> getNumExpr(Expr expr)
        {
            double d = expr_to_double(expr);
            numExpr_t<double> x = {d, expr};
            return x;
        }
        [[deprecated("This isn't used right now, you can ignore this")]]
        numExpr_t<double> getNumExpr(double n)
        {
            numExpr_t<double> x = {n, mkTerm(mpq_class(std::to_string(n)), m_efac)};
            return x;
        }

        /*
        Expr getBounds(EZ3 &z3, std::string numeric_root, Expr symbolic_root)
        {
            std::string test("(and (< 0.0");
            test += numeric_root;
            test += ") (< ";
            test += numeric_root;
            test += " 1.0))";

            const char *tmpfile = "/tmp/z3_expr_temp.smt2";

            std::ofstream outfile(tmpfile);
            if (!outfile.is_open())
            {
                errs() << "Failed to create temp file\n";
                return Expr();
            }

            outfile << "(set-logic QF_LIRA)\n";
            outfile << "(declare-const _x Bool)\n";
            outfile << "(assert (= _x " << numeric_root << "))\n";
            outfile << "(check-sat)\n";
            outfile.close();
            Expr result = z3_from_smtlib_file(m_z3, tmpfile);
            std::remove(tmpfile);

            ZSolver<EZ3> solver(m_z3);
            solver.assertExpr(result);
            boost::tribool result = solver.solve();
        }
        */
        void conversion_testing()
        {
            outs() << "Testing functions to see if data type conversion works properly\n";
            std::string s = "(/ 9.0 10.0)";
            outs() << s << "\n";
            Expr t = str_to_expr(s);
            outs() << t << "\n";
            double d = expr_to_double(t);
            outs() << std::to_string(d) << "\n";
            Expr t2 = double_to_expr(d);
            outs() << t2 << "\n";
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

    void learnInvariants5(std::string smt, unsigned to, bool doElim, bool doArithm, int debug)
    {
        ExprFactory m_efac;
        EZ3 z3(m_efac);
        SMTUtils u(m_efac);
        CHCs ruleManager(m_efac, z3, debug - 2);
        auto res = ruleManager.parse(smt, doElim, doArithm);
        RndLearnerV5 ds(m_efac, z3, ruleManager, to, debug);

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

        ds.generatePolarFile2(ruleManager, "out.prob");
        /**
         * TODO: Use boost algorithm instead of this home-written
         * function
         */
        std::string output_test = exec(ds.getCallToPolar(i).c_str());
        nlohmann::json closedformJson = nlohmann::json::parse(output_test);

        /**
         * Get the initial symbolic closed form as a conjunction
         */
        Expr symbolicClosedForms = ds.generateSymbolicClosedForms(i, closedformJson);
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
        boost::tribool result = ds.checkFact(i, annotations);
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
            // It is unclear why a system would not pass initiation
            // and consecution at this step, so exit if this happens.
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
        double epsilon = 1e-7;
        ExprSet lemmas;
        ExprMap previousUpper; // maps variable to it's upper last iteration
        ExprMap previousLower; // maps variable to it's lower last iteration
        for (auto v : ds.symbolicRoots[i])
        {
            previousUpper[v] = oneReal;
            previousLower[v] = zeroReal;
        }
        for (size_t j = 1; j < max_iterations; j++)
        {
            // Assumes we only have roots 0<r<1 and r=1
            for (const auto &tuple : boost::combine(ds.numericRoots[i], ds.symbolicRoots[i]))
            {
                Expr n, s;
                boost::tie(n, s) = tuple;
                // Case 1: r=1
                double val = ds.expr_to_double(n);
                if (val == ds.expr_to_double(oneReal))
                {
                    continue; // Note: maybe I can just do n == oneReal?
                }

                // Case 2: 0<r<1

                Expr newBound = simplifyArithm(mk<MULT>(previousUpper[s], n));
                if (debug >= 3)
                {
                    outs() << "New bound for " << s << ": " << newBound << "\n";
                }
                Expr cond = mk<GEQ>(index, ds.double_to_expr(j));
                Expr bnd = mk<LEQ>(s, newBound);
                Expr newLemma = mk<IMPL>(cond, bnd);
                annotations[i][0] = newLemma;
                while (!(ds.checkFact(i, annotations) && ds.checkConsecution(i, annotations)))
                {
                    double widenedBound = ds.expr_to_double(newBound) + epsilon;
                    newBound = ds.double_to_expr(widenedBound);
                    bnd = mk<LEQ>(s, newBound);
                    newLemma = mk<IMPL>(cond, bnd);
                    annotations[i][0] = newLemma;
                }

                // If safety is also met, there's nothing more to do!
                if (ds.checkQuery(i, annotations))
                {
                    if (debug >= 2)
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

                // Add lemma to the learned expressions
                ds.learnedExprs[i].insert(newLemma);
                previousUpper[s] = newBound;

                /*
                newBound = simplifyArithm(mk<MULT>(previousLower[s], n));
                cond = mk<LEQ>(index, ds.double_to_expr(j));
                bnd = mk<GEQ>(s, newBound);
                newLemma = mk<IMPL>(cond, bnd);
                annotations[i][0] = newLemma;

                while (!(ds.checkFact(i, annotations) && ds.checkConsecution(i, annotations)))
                {
                    double widenedBound = ds.expr_to_double(newBound) - epsilon;
                    newBound = ds.double_to_expr(widenedBound);
                    bnd = mk<GEQ>(s, newBound);
                    newLemma = mk<IMPL>(cond, bnd);
                    annotations[i][0] = newLemma;
                }

                // If safety is also met, there's nothing more to do!
                if (ds.checkQuery(i, annotations))
                {
                    outs() << "Invariant found by index " << j << "\n";
                    ds.learnedExprs[i].insert(newLemma);
                    outs() << conjoin(ds.learnedExprs[i], m_efac) << "\n";
                    exit(EXIT_SUCCESS);
                }

                // Add lemma to the learned expressions
                ds.learnedExprs[i].insert(newLemma);
                previousLower[s] = newBound;
                */
            }
        }

        outs() << "Analysis inconclusive after " << max_iterations << " iterations.\n";
        exit(EXIT_SUCCESS);
    }
}

#endif // RNDLEARNERV5__HPP__