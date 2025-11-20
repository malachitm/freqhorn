START

How could I make this 1 SMT Query? Or if anything, a couple SMT Queries?
FUNCTION safetyPropertyCantHoldWithGivenClosedForm(Safety_Property, Roots, Closed_Forms):
    First, determine if any of the variables in the safety property must be bounded between
    a max and a min. If so, the roots associated with that variable, or the independent variable that
    determines the value of the variable in the safety property, should be between 0 and 1 always.
    If it isn't, we already know that the property won't hold forever. Unless the property specifies
    that it is only interested in determining if it is bounded for a small section of indices and not
    for all indices greater than some INDEX, end it here and return TRUE.

    IF the variable only has 1 bound:
        IF the bound is a maximum and the root(s) is(are) greater than 1 and the coefficient(s) is(are) positive
            RETURN True
        IF the bound is a minimum and the root(s) is(are) greater than 1 and the coefficient(s) is(are) negative
            RETURN True
    
    Note that the coefficient is question is the coefficients that are in front of all instances of
    the root in question, and the root(s) are the roots associated with the independent variable that
    determines the value in the safety property.

    ELSE
        RETURN False
END FUNCTION

FUNCTION addAuxilaryVariable(CHCs, Root)
    Create new_CHCs
    # _FH_RK models Root**i at a given index i
    new_CHCs.initiation = CHCs.initiation + "_FH_RK' = 1.0"
    new_CHCs.consecution = CHCs.consecution + "_FH_RK' = _FH_RK * Root"
    new_CHCs.safety = CHCs.safety + "_FH_RK' = _FH_RK * Root"
    RETURN new_CHCs
END FUNCTION

FUNCTION addClosedFormsToInvariant(Invariant, Closed_Forms, Roots)
    FOR EACH Root in Roots:
        IF Root between 0 and 1
            Invariant = Invariant + "_FH_RK >= 0 && _FH_RK <= 1.0"
        ELSE IF Root >= 1
            Invariant = Invariant + "_FH_RK >= 1.0"
        ELSE IF Root <= 0
            TO BE DETERMINED (cyclical case?)
        
    FOR EACH Closed_Form in Closed_Forms:
        IF there are multiple closed forms for an independent variable THEN:
            INDEX = 0
            WHILE INDEX < Closed_Form[_FH_N]
                Invariant = Invariant + "(i > INDEX) => _FH_N = Closed_Form[_FH_N, INDEX]"
                INDEX += 1
            END WHILE
        ELSE:
            Invariant = Invariant + "_FH_N = Closed_Form[_FH_N]"
    END FOR
END FUNCTION

FUNCTION getUpperBoundGuessForRootAtIndex(Root, Index):
    NOTE: This is only done because it was observed to be the intervals found by Z3, but I currently
    don't see a reason why the intervals couldn't be tighter. So, it might be smarter to just first
    assume the upper bound is the exact value.
    Upperbound = the average value between the previous value of ROOT at Index INDEX-1 and Root at INDEX
    RETURN Upperbound
END FUNCTION

FUNCTION main(chc_file)
    CHCs = getCHCs(chc_file)
    Independent_variables[] = getIndependentVariables(CHCs)
    Safety_Property = getSafetyProperty(CHCs)
    String POLAR_input = getPolarFileFromCHCs(CHCs)

    Roots[], Closed_Forms[] = runPolarScript(POLAR_input, Independent_Variables)
    
    If we are assuming that the CHCs represent an affine loop, then all
    closed forms of each independent variable will look like the following

    x_k = a_0 * (r_0 ** i) + a_1 * (r_1 ** i) + ...

    IF safetyPropertyCantHoldWithGivenClosedForm(Safety_Property, Roots, Closed_Forms) THEN:
        RETURN unsat
    
    FOR EACH Root in Roots:
        CHCs_Prime = addAuxilaryVariable(CHCs, Root)
    
    addClosedFormsToInvariant(Invariant, Closed_Forms, Roots)

    MAX = getMaxIndexIfExists(Safety Property)

    IF InvariantIsInductive(Invariant, CHCs):
        RETURN sat, Invariant

    (check to see if stating inequalities between roots works)
    
    COUNTER = 0
    WHILE Inductive Invariant is not found /\ COUNTER <= MAX:
        FOR EACH Root in Roots:
            Upper_Bound = getUpperBoundGuessForRootAtIndex(Root, COUNTER)
            Lemma = "(i > COUNTER) => (Root < Upper_Bound)"
            WHILE Invariant /\ Lemma Does Not Pass both Initiation and Consecution DO:
                Upper_Bound = Upper_Bound + EPSILON
                Lemma = "(i > COUNTER) => (Root < Upper_Bound)"
            END WHILE
            Invariant = Invariant /\ Lemma
            IF InvariantImpliesSafety(Invariant):
                RETURN sat, Invariant
        COUNTER += 1
    END WHILE

END FUNCTION

END
        