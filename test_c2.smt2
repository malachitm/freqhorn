(set-option :pp.decimal true)
(set-logic HORN)
(declare-fun Inv (Int Bool Int Int) Bool)
(assert (forall 
	((step Int) (curr Bool) (drop Int) (max Int))
	(=>
		(and
			(= step 0)
			(= curr (ite (< 0 drop) true false))
            (<= 0 drop)
            (< 0 max)
            (<= drop max)
		)
		(Inv step curr drop max))
))
(assert (forall 
	((step Int) (curr Bool) (drop Int) (max Int)
     (step0 Int) (curr0 Bool)
	)
	(=> 
		(and
			(Inv step curr drop max)
            (= step0 (ite (>= step max) 0 (+ step 1)))
            (= curr0 (ite (< step0 drop) true false))
		)
		(Inv step0 curr0 drop max))
))
(assert (forall 
	((step Int) (curr Bool) (drop Int) (max Int))
	(=> 
		(and
            (Inv step curr drop max)
            (not (and 
                (= curr (ite (= drop max) true curr))
                (= curr (ite (= drop 0) false curr))
            ))
		)
		false)
))
(check-sat)
