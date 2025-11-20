;    First, determine if any of the variables in the safety property must be bounded between
;    a max and a min. If so, the roots associated with that variable, or the independent variable that
;    determines the value of the variable in the safety property, should be between 0 and 1 always.
;    If it isn't, we already know that the property won't hold forever. Unless the property specifies
;    that it is only interested in determining if it is bounded for a small section of indices and not
;    for all indices greater than some INDEX, end it here and return TRUE.

;    IF the variable only has 1 bound:
;        IF the bound is a maximum and the root(s) is(are) greater than 1 and the coefficient(s) is(are) positive
;            RETURN True
;        IF the bound is a minimum and the root(s) is(are) greater than 1 and the coefficient(s) is(are) negative
;            RETURN True
    
;    Note that the coefficient is question is the coefficients that are in front of all instances of
;    the root in question, and the root(s) are the roots associated with the independent variable that
;    determines the value in the safety property.

;    ELSE
;        RETURN False

; First thing to do is do a scan of the Bad property and determine which variables
; have inequalities. How can this be done?

; Let's say the Bad property is by default a conjunction of inequalities.
; Let's be even more specific and say that it is a conjunction of inequalities where
; each inequality only contains one variable.
; Ex: (x0 > 50) AND (~(x1 < 15.3) OR (x2 > 10.0)) and (x4 < 10.2) and (~(x1 < 15.3) OR (x2 < 20.0))

; For each variable, get the dominant root with it's coefficient.

; If the dominant is is less than 1, then it converges and it's equilibrium point is
; the closed form with all roots set to 0.

; If the dominant root's absolute value is greater than 1, then it diverges and it's 
; equilibrium point is either infinity or negative infinity, depending on the sign of 
; the coefficient.

; It'll have to be a two step dance.
; 1) First, find the simplified form of the safety property by using quantifier
; elimination on the index variable.
; 2) Then, use the closed forms and try to find a maximum if the root is greater than 1
;    and just set it so 0 if the root is less than 1.
; If the maximum is found, then the property does not hold because there must be a max.

; How about, for the time being, we don't worry about doing this safety check. 

; Also, I forgot why I thought this, but maybe we would benefit from
; assuming it's not oscillatory.

; Just use the Asymptotic behavior of the closed form.

(set-logic LRA) ; Linear Real Arithmetic supports QE

; Declare variables
(declare-const i Real)
(declare-const x Real)

; Assert the quantified formula
(assert (forall ((i Real)) (=> (> i 10) (and (>= x 0) (<= x 20)))))

; Apply the quantifier elimination tactic
(apply (then qe ctx-simplify))