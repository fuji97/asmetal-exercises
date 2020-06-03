asm Euclide

import ../Libs/StandardLibrary

signature:
	dynamic monitored iA : Integer
	dynamic monitored iB : Integer
	dynamic controlled a : Integer
	dynamic controlled b : Integer
	
definitions:
	
	rule r_setUp = par
		if a = undef then
			a := iA
		endif
		if b = undef then
			b := iB
		endif
	endpar
	
	rule r_executeStep = 
		if not (a = b) then
			if a > b then
				a := a - b
			else
				b := b - a
			endif
		endif
		
	main rule r_main = seq
		// Check if undef and set them
		r_setUp[]
		r_executeStep[]
	endseq
		
	default init s0:
		function a = undef
		function b = undef