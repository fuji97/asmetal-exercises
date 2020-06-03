asm PopulationAgent

import ../Libs/StandardLibrary

signature:
	dynamic domain Person subsetof Agent
	enum domain Gender = {MALE | FEMALE}
	dynamic controlled gender: Person -> Gender
	dynamic controlled age: Person -> Natural
	dynamic controlled alive: Person -> Boolean
	
	dynamic controlled father: Person -> Person
	dynamic controlled mother: Person -> Person
	
	static male1: Person
	static female1: Person	
	
definitions:
	rule r_Reproduce =
		if (gender(self) = FEMALE and
			age(self) >= 13n and age(self) <= 50n) then
			choose $x in {1 : 100} with true do
				if ($x <= 30) then
					choose $father in Person with alive($father) and gender($father) = MALE and age($father) >= 13n do
						extend Person with $child do
							choose $g in Gender with true do
								par
									gender($child) := $g
									age($child) := 0n
									alive($child) := true
									father($child) := $father
									mother($child) := self
								endpar
				endif
		endif
		
	rule r_Dead =
		choose $x in {1 : 100} with true do
			if ($x <= 5) then
				alive(self) := false
			endif
			
	rule r_LifeRule =
		par
			age(self) := age(self) + 1n
			r_Reproduce[]
			r_Dead[]
		endpar
			
	main rule r_Main =
		forall $p in Person with alive($p) do
			program($p)
			
default init s0:
	function alive($p in Person) = true
	
	function gender($p in Person) =
		if ($p = male1) then
			MALE
		else
			FEMALE
		endif
	
	function age($p in Person) = 13n
	
	agent Person:
		r_LifeRule[]
