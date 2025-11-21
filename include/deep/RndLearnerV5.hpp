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
#include <algorithm> // For std::find
#include <boost/algorithm/string.hpp>
#include <nlohmann/json.hpp>
using namespace std;
using namespace boost;

// --- Hypothetical C++ Code Snippet ---

// Helper function to get the string name of a variable from an Expr
// Assuming varExpr is an FAPP of an FDECL, and the FDECL's name is a STRING

// --- End of Hypothetical C++ Code Snippet ---

// Source - https://stackoverflow.com/a/478960
// Posted by waqas, modified by community. See post 'Timeline' for change history
// Retrieved 2025-11-19, License - CC BY-SA 4.0

#include <iostream>
#include <stdexcept>
#include <stdio.h>
#include <string>

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
        std::vector<ExprSet> learnedExprs; // indexed by invNumber

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
            std::cout << "Converting expresion to POLAR string: " << *e << std::endl;
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
                std::cout << "Corresponding dstVar: " << (correspondingDstVar ? getVarName(correspondingDstVar) : "not found") << std::endl;

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
                std::cout << "Successfully wrote POLAR program to " << outputFilename << std::endl;
            }
            else
            {
                std::cerr << "Error: Unable to open file " << outputFilename << " for writing." << std::endl;
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
            return u.isSat(exprs);
        }

        boost::tribool checkFact(int i, map<int, ExprVector> &annotations)
        {
            return checkCHC2(*fc[i], annotations, true);
        }

        boost::tribool checkConsecution(int i, map<int, ExprVector> &annotations)
        {
            return checkCHC2(*tr[i], annotations, true);
        }

        boost::tribool checkQuery(int i, map<int, ExprVector> &annotations)
        {
            return checkCHC2(*qr[i], annotations, true);
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

        Expr addRoot(int i, std::string rootVal, size_t rootCount)
        {
            /* TODO:
                Support roots that are complex, this assumes all roots are real due
                to how it writes the update
            */
            assert(i < invNumber);
            // --- Define the counter variable ---
            std::string rootBaseName = "_r_" + std::to_string(rootCount);
            Expr rootNameUnprimedExpr = mkTerm<string>(rootBaseName, m_efac);
            Expr rootNamePrimedExpr = mkTerm<string>(rootBaseName + "'", m_efac);
            Expr myRealRoot = bind::realConst(rootNameUnprimedExpr);
            Expr myRealRootPrime = bind::realConst(rootNamePrimedExpr);
            Expr myRootUpdate = z3_from_smtlib(m_z3, rootVal);
            Expr updateConstraint = mk<EQ>(myRealRootPrime, mk<MULT>(myRealRoot, myRootUpdate));
            invarVarsShort[i].push_back(myRealRoot);

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
                    Expr zeroReal = mkTerm(mpq_class("0"), m_efac);
                    Expr initConstraint = mk<EQ>(zeroReal, myRealRootPrime);
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
                    if (printLog >= 3)
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
            return myRealCounter
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

        ruleManager.print(true);
        int i = 0; // invariant number we want to look at
        // TODO:
        // There's actually a non-zero probability that I don't need to add the update
        // for the index inside of the query. Just as a heads up.
        Expr index = ds.addIndex(i);
        ds.reflipSimpleEqualities(); // Reflip simple equalities in CHCs
        ruleManager.print(true);
        ds.generatePolarFile2(ruleManager, "out.prob");
        /* TODO:
            Use boost algorithm instead of this home-written function
         */
        // std::system(ds.getCallToPolar(i).c_str());
        std::string output_test = exec(ds.getCallToPolar(i).c_str());
        // outs() << ds.getCallToPolar(i) << "\n";
        /*if (debug > 3)
        {
            outs() << "Results for \"python version\": " << output_test << "\n";
        }*/

        // std::vector<std::string> lines;
        // boost::algorithm::split(lines, output_test, is_cntrl());
        /* TODO:
            Implement dReal and have it be able to check whether the property holds.
            For the time being, create a built-in max for how many times this algorithm
            can iterate.
        */

        // Include new variables in the CHC systems using the information in lines.
        // tools that may be useful:
        //      regex_match
        nlohmann::json closedformJson = nlohmann::json::parse(output_test);
        if (debug >= 0)
        {
            outs() << "Here is the closed form data:" << "\n";
            outs() << closedformJson.dump(4) << "\n";
        }

        // insert all data into the CHC system and create the first part of the invariant
        // with the bounds

        ExprSet initialClauses;
        for (auto v : closedformJson)
        {
            for (size_t idx = 0; idx < v.size(); idx++)
                Expr cond;
            if (v[idx] + 1 == v.size())
            {
                cond = mkTerm<GEQ>()
            }
            // The closed form for this one
            if (v["coeff"].size() == 1 && v["bases"].size() == 0)
            {
                Expr cf = z3_from_smtlib(v["bases"][0].get<std::string>());
                initialClauses.insert(cf);
            }
            for (size_t idx = 0;)
        }

        exit(EXIT_SUCCESS);
        for (auto i : ds.invarVarsShort[i])
        {
            outs() << "Invar Vars Short: " << i << "\n";
        }
        // Inv = x=2i /\ y=i /\ (x,y,i)>=0
        Expr realZero = mkTerm(mpq_class("0"), m_efac);
        Expr realTwo = mkTerm(mpq_class("2"), m_efac);
        ExprSet clauses;
        Expr clause1 = mk<EQ>(ds.invarVarsShort[i][0], mk<MULT>(ds.invarVarsShort[i][2], realTwo));
        clauses.insert(clause1);
        Expr clause2 = mk<EQ>(ds.invarVarsShort[i][1], ds.invarVarsShort[i][2]);
        clauses.insert(clause2);
        Expr clause3 = mk<GEQ>(ds.invarVarsShort[i][0], realZero);
        clauses.insert(clause3);
        Expr clause4 = mk<GEQ>(ds.invarVarsShort[i][1], realZero);
        clauses.insert(clause4);
        Expr clause5 = mk<GEQ>(ds.invarVarsShort[i][2], realZero);
        clauses.insert(clause5);
        Expr inv = conjoin(clauses, m_efac);
        if (ds.checkAllCHCs(i, inv))
        {
            outs() << "Candidate invariant " << *inv << " satisfies all CHCs for predicate " << ds.decls[i] << "\n";
        }
        else
        {
            outs() << "Candidate invariant " << *inv << " does not satisfy all CHCs for predicate " << ds.decls[i] << "\n";
        }
        for (auto &hr : ds.ruleManager.invVars[ds.decls[i]])
        {
            outs() << "Var: " << hr << "\n";
        }

        exit(EXIT_SUCCESS);
    }
}

#endif // RNDLEARNERV5__HPP__